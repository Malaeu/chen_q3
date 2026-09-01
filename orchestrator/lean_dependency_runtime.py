#!/usr/bin/env python3
"""Read-only Lean declaration dependency inspection for node-registry v10.

The production path feeds a generated Meta probe to ``lake env lean --stdin``;
it never creates a Lean file and never trusts textual theorem-name matches.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import subprocess
import unicodedata
from collections import deque
from collections.abc import Iterable, Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any

SCHEMA = "q3_lean_dependency_snapshot.v1"
ALGORITHM_VERSION = "LEAN_EXPR_USED_CONSTANTS_V1"
EXPR_FINGERPRINT_ALGORITHM = "LEAN_EXPR_HASH_V1"
ROW_PREFIX = "Q3_NODE_DEP_JSON "
MODULE_ROW_PREFIX = "Q3_NODE_MODULE_JSON "
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
MAX_NAME_UTF8_BYTES = 1024
PROJECT_SOURCE_ROOT = "q3.lean.aristotle/Q3"
PROJECT_SOURCE_BASELINE_ALGORITHM = "PATH_TAB_CONTENT_SHA256_NEWLINE_V1"
HOLE_RE = re.compile(r"(?<![A-Za-z0-9_'])(?:sorry|admit|exact\?)(?![A-Za-z0-9_'])")
BUILD_INPUT_PATHS = (
    "q3.lean.aristotle/lean-toolchain",
    "q3.lean.aristotle/lakefile.toml",
    "q3.lean.aristotle/lake-manifest.json",
)


class LeanDependencyError(RuntimeError):
    """Fail-closed dependency-probe error."""


def _name(value: str) -> str:
    if not isinstance(value, str):
        raise LeanDependencyError(f"LEAN_DEPENDENCY_INVALID_NAME: {value!r}")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise LeanDependencyError(
            f"LEAN_DEPENDENCY_INVALID_NAME: {value!r}"
        ) from exc
    if len(encoded) > MAX_NAME_UTF8_BYTES or not NAME_RE.fullmatch(value):
        raise LeanDependencyError(f"LEAN_DEPENDENCY_INVALID_NAME: {value!r}")
    return value


def _is_lean_letter_like(value: str) -> bool:
    codepoint = ord(value)
    return (
        (0x3B1 <= codepoint <= 0x3C9 and codepoint != 0x3BB)
        or (0x391 <= codepoint <= 0x3A9 and codepoint not in {0x3A0, 0x3A3})
        or 0x3CA <= codepoint <= 0x3FB
        or 0x1F00 <= codepoint <= 0x1FFE
        or 0x2100 <= codepoint <= 0x214F
        or 0x1D49C <= codepoint <= 0x1D59F
        or (0x00C0 <= codepoint <= 0x00FF and codepoint not in {0x00D7, 0x00F7})
        or 0x0100 <= codepoint <= 0x017F
    )


def _is_lean_subscript_alnum(value: str) -> bool:
    codepoint = ord(value)
    return (
        0x2080 <= codepoint <= 0x2089
        or 0x2090 <= codepoint <= 0x209C
        or 0x1D62 <= codepoint <= 0x1D6A
        or codepoint == 0x2C7C
    )


def _is_lean_id_first(value: str) -> bool:
    return (
        "A" <= value <= "Z"
        or "a" <= value <= "z"
        or value == "_"
        or _is_lean_letter_like(value)
    )


def _is_lean_id_rest(value: str) -> bool:
    return (
        _is_lean_id_first(value)
        or "0" <= value <= "9"
        or value in "_'!?"
        or _is_lean_subscript_alnum(value)
    )


def _environment_name_syntax_valid(value: str) -> bool:
    """Mirror the round-trippable subset of Lean's ``String.toName`` grammar."""

    index = 0
    while index < len(value):
        current = value[index]
        if current == "«":
            closing = value.find("»", index + 1)
            if closing < 0:
                return False
            index = closing + 1
        elif "0" <= current <= "9":
            if current == "0" and index + 1 < len(value) and "0" <= value[index + 1] <= "9":
                return False
            index += 1
            while index < len(value) and "0" <= value[index] <= "9":
                index += 1
        elif _is_lean_id_first(current):
            index += 1
            while index < len(value) and _is_lean_id_rest(value[index]):
                index += 1
        else:
            return False
        if index == len(value):
            return True
        if value[index] != "." or index + 1 == len(value):
            return False
        index += 1
    return False


def _environment_name(value: str) -> str:
    """Validate bounded ``Name.toString`` data emitted by the Meta probe.

    Unlike caller-controlled module/theorem selectors, environment names may
    contain Lean identifier Unicode and numeric private-name components.  They
    are still normalized, bounded, control-free data and are never interpolated
    into Lean syntax as identifiers.
    """

    try:
        encoded = value.encode("utf-8") if isinstance(value, str) else b""
    except UnicodeEncodeError:
        encoded = b""
    if (
        not isinstance(value, str)
        or not value
        or not encoded
        or len(encoded) > MAX_NAME_UTF8_BYTES
        or unicodedata.normalize("NFC", value) != value
        or any(
            character.isspace()
            or unicodedata.category(character).startswith("C")
            for character in value
        )
        or not _environment_name_syntax_valid(value)
    ):
        raise LeanDependencyError(f"LEAN_DEPENDENCY_INVALID_ENVIRONMENT_NAME: {value!r}")
    return value


def _lean_string_array(values: Sequence[str]) -> str:
    """Encode names as data; ``String.toName`` performs the Lean-side round trip."""

    return ", ".join(json.dumps(_environment_name(value)) for value in values)


def _expr_fingerprint(value: object, *, allow_none: bool = False) -> dict[str, str] | None:
    if value is None and allow_none:
        return None
    if (
        not isinstance(value, Mapping)
        or set(value) != {"algorithm", "value"}
        or value.get("algorithm") != EXPR_FINGERPRINT_ALGORITHM
        or not isinstance(value.get("value"), str)
        or not value["value"].isdigit()
    ):
        raise LeanDependencyError("LEAN_DEPENDENCY_EXPRESSION_FINGERPRINT_INVALID")
    return {"algorithm": EXPR_FINGERPRINT_ALGORITHM, "value": value["value"]}


def graph_probe_source(
    import_modules: Sequence[str], *, project_module_prefixes: Sequence[str] = ("Q3",)
) -> str:
    """Return a Meta probe which emits exact direct project declaration edges."""

    modules = sorted({_name(value) for value in import_modules})
    if not modules:
        raise LeanDependencyError("LEAN_DEPENDENCY_IMPORT_SET_EMPTY")
    imports = "\n".join(f"import {module}" for module in modules)
    prefixes = ", ".join(
        json.dumps(_name(value)) for value in sorted(set(project_module_prefixes))
    )
    if not prefixes:
        raise LeanDependencyError("LEAN_DEPENDENCY_PROJECT_PREFIX_SET_EMPTY")
    return f"""{imports}
import Lean

open Lean Elab Command

private def moduleNameFor? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

private def typeRefsOf (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants

private def valueRefsOf (ci : ConstantInfo) : Array Name :=
  match ci.value? true with
  | some value => value.getUsedConstants
  | none => #[]

private def declarationsForModule (env : Environment) (m : Name) : Array Name :=
  match env.header.moduleNames.findIdx? (· == m) with
  | some idx => env.header.moduleData[idx]!.constNames
  | none => #[]

run_cmd do
  let env ← getEnv
  let projectPrefixes : Array String := #[{prefixes}]
  let projectModules := env.header.moduleNames.filter (fun m =>
    projectPrefixes.any (fun pfx => m.toString == pfx ||
      m.toString.startsWith (pfx ++ ".")))
  let modules : Std.HashSet Name := Std.HashSet.ofList projectModules.toList
  for m in projectModules do
    let row := Json.mkObj [
      ("kind", toJson "MODULE"),
      ("module", toJson m.toString)
    ]
    logInfo m!"{MODULE_ROW_PREFIX}{{row.compress}}"
  let roots := projectModules.foldl
    (fun acc m => acc ++ declarationsForModule env m) #[]
  for n in roots do
    let some ci := env.find? n | continue
    let typeRefs := (typeRefsOf ci).filter (fun ref =>
      (moduleNameFor? env ref).any modules.contains)
    let valueRefs := (valueRefsOf ci).filter (fun ref =>
      (moduleNameFor? env ref).any modules.contains)
    let refs := typeRefs ++ valueRefs
    let row := Json.mkObj [
      ("kind", toJson "GRAPH"),
      ("name", toJson n.toString),
      ("module", toJson (((moduleNameFor? env n).map toString).getD "")),
      ("direct_refs", toJson (refs.map (·.toString) |>.toList)),
      ("type_refs", toJson (typeRefs.map (·.toString) |>.toList)),
      ("value_refs", toJson (valueRefs.map (·.toString) |>.toList))
    ]
    logInfo m!"{ROW_PREFIX}{{row.compress}}"
"""


def metadata_probe_source(
    import_modules: Sequence[str],
    declarations: Sequence[str],
    *,
    semantic_declarations: Sequence[str] = (),
) -> str:
    """Return bounded structural fingerprints and axiom closures.

    Theorem proof values are never rendered or emitted.  A value fingerprint is
    emitted only for an explicitly selected semantic definition.
    """

    modules = sorted({_name(value) for value in import_modules})
    names = sorted({_environment_name(value) for value in declarations})
    semantic_names = sorted({_name(value) for value in semantic_declarations})
    if not set(semantic_names) <= set(names):
        raise LeanDependencyError("LEAN_DEPENDENCY_SEMANTIC_DECLARATION_SCOPE_INVALID")
    if not modules or not names:
        raise LeanDependencyError("LEAN_DEPENDENCY_METADATA_INPUT_EMPTY")
    imports = "\n".join(f"import {module}" for module in modules)
    declaration_names = _lean_string_array(names)
    semantic_declaration_names = _lean_string_array(semantic_names)
    return f"""{imports}
import Lean

open Lean Elab Command

private def moduleNameFor? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

private def refsOf (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  match ci.value? true with
  | some value => fromType ++ value.getUsedConstants
  | none => fromType

private def fingerprint (value : Expr) : Json :=
  Json.mkObj [
    ("algorithm", toJson "{EXPR_FINGERPRINT_ALGORITHM}"),
    ("value", toJson (toString (hash value)))
  ]

private def declarationKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE_DEFINITION"
  | .quotInfo _ => "QUOTIENT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

private def semanticValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo val => some val.value
  | .opaqueInfo val => some val.value
  | _ => none

private partial def axiomClosure
    (env : Environment) (n : Name) : StateM (Std.HashSet Name) (Array Name) := do
  if (← get).contains n then return #[]
  modify (·.insert n)
  let some ci := env.find? n | return #[]
  if ci.isAxiom then return #[n]
  let mut out := #[]
  for ref in refsOf ci do
    out := out ++ (← axiomClosure env ref)
  return out

run_cmd do
  let env ← getEnv
  let declarationNames : Array Name :=
    (#[{declaration_names}] : Array String).map String.toName
  let semanticNames : Std.HashSet Name :=
    Std.HashSet.ofList ((#[{semantic_declaration_names}] : Array String).map String.toName).toList
  for n in declarationNames do
    let some ci := env.find? n | throwError m!"LEAN_DEPENDENCY_DECLARATION_MISSING: {{n}}"
    let axioms := (axiomClosure env n).run {{}} |>.1.map (·.toString) |>.toList
    let row := Json.mkObj [
      ("kind", toJson "METADATA"),
      ("name", toJson n.toString),
      ("module", toJson (((moduleNameFor? env n).map toString).getD "")),
      ("declaration_kind", toJson (declarationKind ci)),
      ("type_fingerprint", fingerprint ci.type),
      ("value_fingerprint", if semanticNames.contains n then
        match semanticValue? ci with
        | some value => fingerprint value
        | none => Json.null
      else Json.null),
      ("axioms", toJson axioms)
    ]
    logInfo m!"{ROW_PREFIX}{{row.compress}}"
"""


def parse_probe_output(output: str, *, expected_kind: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in output.splitlines():
        marker = line.find(ROW_PREFIX)
        if marker < 0:
            continue
        try:
            row = json.loads(line[marker + len(ROW_PREFIX) :])
        except json.JSONDecodeError as exc:
            raise LeanDependencyError("LEAN_DEPENDENCY_OUTPUT_INVALID_JSON") from exc
        if not isinstance(row, dict) or row.get("kind") != expected_kind:
            raise LeanDependencyError("LEAN_DEPENDENCY_OUTPUT_INVALID_ROW")
        rows.append(row)
    if not rows:
        raise LeanDependencyError(f"LEAN_DEPENDENCY_OUTPUT_EMPTY: {expected_kind}")
    return rows


def parse_module_output(output: str) -> list[str]:
    modules: list[str] = []
    for line in output.splitlines():
        marker = line.find(MODULE_ROW_PREFIX)
        if marker < 0:
            continue
        try:
            row = json.loads(line[marker + len(MODULE_ROW_PREFIX) :])
        except json.JSONDecodeError as exc:
            raise LeanDependencyError("LEAN_DEPENDENCY_MODULE_OUTPUT_INVALID_JSON") from exc
        if (
            not isinstance(row, dict)
            or set(row) != {"kind", "module"}
            or row.get("kind") != "MODULE"
        ):
            raise LeanDependencyError("LEAN_DEPENDENCY_MODULE_OUTPUT_INVALID_ROW")
        modules.append(_name(str(row.get("module", ""))))
    if not modules:
        raise LeanDependencyError("LEAN_DEPENDENCY_MODULE_OUTPUT_EMPTY")
    if len(modules) != len(set(modules)):
        raise LeanDependencyError("LEAN_DEPENDENCY_MODULE_OUTPUT_DUPLICATE")
    return sorted(modules)


def _canonical_relative_path(value: str) -> PurePosixPath:
    if not isinstance(value, str):
        raise LeanDependencyError(f"LEAN_DEPENDENCY_PATH_INVALID: {value!r}")
    pure = PurePosixPath(value)
    if (
        not value
        or unicodedata.normalize("NFC", value) != value
        or pure.is_absolute()
        or pure.as_posix() != value
        or "\\" in value
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise LeanDependencyError(f"LEAN_DEPENDENCY_PATH_INVALID: {value!r}")
    return pure


def _stat_identity(value: os.stat_result, *, include_bytes: bool) -> tuple[int, ...]:
    identity = (value.st_dev, value.st_ino, stat.S_IFMT(value.st_mode))
    if include_bytes:
        return (*identity, value.st_size, value.st_mtime_ns)
    return identity


def _path_state(
    repo: Path,
    rel: str,
    *,
    final_kind: str,
    error_code: str,
) -> tuple[tuple[int, ...], ...]:
    pure = _canonical_relative_path(rel)
    current = repo
    states: list[tuple[int, ...]] = []
    try:
        for index, part in enumerate(pure.parts):
            current = current / part
            value = current.lstat()
            final = index == len(pure.parts) - 1
            if stat.S_ISLNK(value.st_mode):
                raise OSError("symlink component")
            if final:
                expected = (
                    stat.S_ISREG(value.st_mode)
                    if final_kind == "file"
                    else stat.S_ISDIR(value.st_mode)
                )
                if not expected:
                    raise OSError("wrong final path kind")
            elif not stat.S_ISDIR(value.st_mode):
                raise OSError("non-directory parent")
            states.append(_stat_identity(value, include_bytes=final and final_kind == "file"))
        resolved = current.resolve(strict=True)
        if not resolved.is_relative_to(repo) or resolved != current:
            raise OSError("path escapes canonical repository")
    except (OSError, RuntimeError) as exc:
        raise LeanDependencyError(f"{error_code}: {rel}") from exc
    return tuple(states)


def _read_without_symlinks(repo: Path, pure: PurePosixPath, *, error_code: str) -> bytes:
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    file_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    directory_fd: int | None = None
    file_fd: int | None = None
    try:
        directory_fd = os.open(repo, directory_flags)
        for part in pure.parts[:-1]:
            next_fd = os.open(part, directory_flags, dir_fd=directory_fd)
            os.close(directory_fd)
            directory_fd = next_fd
        file_fd = os.open(pure.parts[-1], file_flags, dir_fd=directory_fd)
        before = os.fstat(file_fd)
        if not stat.S_ISREG(before.st_mode):
            raise OSError("not a regular file")
        with os.fdopen(file_fd, "rb", closefd=True) as stream:
            file_fd = None
            payload = stream.read()
            after = os.fstat(stream.fileno())
        if _stat_identity(before, include_bytes=True) != _stat_identity(
            after, include_bytes=True
        ):
            raise OSError("opened file mutated while reading")
        return payload
    except OSError as exc:
        raise LeanDependencyError(f"{error_code}: {pure.as_posix()}") from exc
    finally:
        if file_fd is not None:
            os.close(file_fd)
        if directory_fd is not None:
            os.close(directory_fd)


def _read_repo_file_stable(
    repo: Path,
    rel: str,
    *,
    invalid_code: str,
    mutation_code: str,
) -> tuple[bytes, tuple[tuple[int, ...], ...]]:
    pure = _canonical_relative_path(rel)
    before = _path_state(repo, rel, final_kind="file", error_code=invalid_code)
    payload = _read_without_symlinks(repo, pure, error_code=invalid_code)
    try:
        after = _path_state(repo, rel, final_kind="file", error_code=mutation_code)
    except LeanDependencyError as exc:
        raise LeanDependencyError(f"{mutation_code}: {rel}") from exc
    if after != before:
        raise LeanDependencyError(f"{mutation_code}: {rel}")
    return payload, before


def _lean_root_before(repo: Path) -> tuple[Path, tuple[tuple[int, ...], ...]]:
    root = repo.resolve()
    state = _path_state(
        root,
        "q3.lean.aristotle",
        final_kind="dir",
        error_code="LEAN_DEPENDENCY_PROJECT_ROOT_INVALID",
    )
    return root / "q3.lean.aristotle", state


def _assert_lean_root_unchanged(
    repo: Path, before: tuple[tuple[int, ...], ...]
) -> None:
    after = _path_state(
        repo.resolve(),
        "q3.lean.aristotle",
        final_kind="dir",
        error_code="LEAN_DEPENDENCY_PROJECT_ROOT_MUTATED",
    )
    if after != before:
        raise LeanDependencyError("LEAN_DEPENDENCY_PROJECT_ROOT_MUTATED")


def _process_text(value: object) -> str:
    return value if isinstance(value, str) else ""


def _process_receipt(
    proc: subprocess.CompletedProcess[str], command: Sequence[str], *, source: str | None = None
) -> dict[str, Any]:
    stdout = _process_text(proc.stdout)
    stderr = _process_text(proc.stderr)
    receipt: dict[str, Any] = {
        "command": list(command),
        "returncode": proc.returncode,
        "stdout_sha256": hashlib.sha256(stdout.encode("utf-8")).hexdigest(),
        "stderr_sha256": hashlib.sha256(stderr.encode("utf-8")).hexdigest(),
    }
    if source is not None:
        receipt["stdin_sha256"] = hashlib.sha256(source.encode("utf-8")).hexdigest()
    return receipt


def _failure_output(proc: subprocess.CompletedProcess[str]) -> str:
    output = _process_text(proc.stdout) + "\n" + _process_text(proc.stderr)
    return output.replace("\r\n", "\n").replace("\r", "\n")[-2000:]


def _run_source(repo: Path, source: str, *, timeout: int) -> tuple[str, dict[str, Any]]:
    lean_root, root_state = _lean_root_before(repo)
    command = ["lake", "env", "lean", "--stdin"]
    try:
        env = dict(os.environ)
        env.pop("LD_LIBRARY_PATH", None)
        proc = subprocess.run(
            command,
            cwd=lean_root,
            env=env,
            input=source,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise LeanDependencyError("LEAN_DEPENDENCY_PROBE_TIMEOUT") from exc
    except (OSError, subprocess.SubprocessError) as exc:
        raise LeanDependencyError("LEAN_DEPENDENCY_PROBE_UNAVAILABLE") from exc
    _assert_lean_root_unchanged(repo, root_state)
    output = _process_text(proc.stdout) + "\n" + _process_text(proc.stderr)
    if proc.returncode:
        raise LeanDependencyError(
            f"LEAN_DEPENDENCY_PROBE_FAILED: returncode={proc.returncode}; {_failure_output(proc)}"
        )
    return output, _process_receipt(proc, command, source=source)


def _run_build(repo: Path, modules: Sequence[str], *, timeout: int) -> dict[str, Any]:
    """Materialize fresh oleans for every imported project root before Meta inspection."""

    lean_root, root_state = _lean_root_before(repo)
    command = ["lake", "build", *sorted({_name(module) for module in modules})]
    env = dict(os.environ)
    env.pop("LD_LIBRARY_PATH", None)
    try:
        proc = subprocess.run(
            command,
            cwd=lean_root,
            env=env,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise LeanDependencyError("LEAN_DEPENDENCY_BUILD_TIMEOUT") from exc
    except (OSError, subprocess.SubprocessError) as exc:
        raise LeanDependencyError("LEAN_DEPENDENCY_BUILD_UNAVAILABLE") from exc
    _assert_lean_root_unchanged(repo, root_state)
    if proc.returncode:
        raise LeanDependencyError(
            f"LEAN_DEPENDENCY_BUILD_FAILED: returncode={proc.returncode}; {_failure_output(proc)}"
        )
    return _process_receipt(proc, command)


def _source_evidence(
    repo: Path, source_paths: Sequence[str], *, scan_holes: bool = True
) -> tuple[list[dict[str, str]], list[dict[str, Any]]]:
    fingerprints: list[dict[str, str]] = []
    holes: list[dict[str, Any]] = []
    if list(source_paths) != sorted(set(source_paths)):
        raise LeanDependencyError("LEAN_DEPENDENCY_SOURCE_MAP_INVALID: order_or_duplicate")
    for rel in source_paths:
        payload, _state = _read_repo_file_stable(
            repo,
            rel,
            invalid_code="LEAN_DEPENDENCY_SOURCE_MAP_INVALID",
            mutation_code="LEAN_DEPENDENCY_SOURCE_MAP_MUTATED_DURING_READ",
        )
        fingerprints.append({"path": rel, "sha256": hashlib.sha256(payload).hexdigest()})
        if scan_holes:
            try:
                text = payload.decode("utf-8")
            except UnicodeError as exc:
                raise LeanDependencyError(
                    f"LEAN_DEPENDENCY_SOURCE_MAP_INVALID: {rel}"
                ) from exc
            for line_no, line in enumerate(text.splitlines(), 1):
                if HOLE_RE.search(line):
                    holes.append({"path": rel, "line": line_no})
    return fingerprints, holes


def _project_source_paths(repo: Path) -> list[str]:
    """List the complete on-disk ``Q3/**/*.lean`` surface without following links."""

    root = repo.resolve()
    _path_state(
        root,
        PROJECT_SOURCE_ROOT,
        final_kind="dir",
        error_code="LEAN_DEPENDENCY_PROJECT_SOURCE_SURFACE_INVALID",
    )
    start = root / PROJECT_SOURCE_ROOT
    pending: list[tuple[Path, PurePosixPath]] = [
        (start, PurePosixPath(PROJECT_SOURCE_ROOT))
    ]
    paths: list[str] = []
    try:
        while pending:
            directory, relative = pending.pop()
            with os.scandir(directory) as iterator:
                entries = sorted(iterator, key=lambda entry: entry.name)
            for entry in entries:
                child_relative = relative / entry.name
                if entry.is_symlink():
                    raise OSError("symlink in project source surface")
                if entry.is_dir(follow_symlinks=False):
                    pending.append((Path(entry.path), child_relative))
                elif entry.is_file(follow_symlinks=False):
                    if entry.name.endswith(".lean"):
                        paths.append(
                            _canonical_relative_path(child_relative.as_posix()).as_posix()
                        )
                elif entry.name.endswith(".lean"):
                    raise OSError("non-regular Lean source")
    except (OSError, RuntimeError) as exc:
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_PROJECT_SOURCE_SURFACE_INVALID"
        ) from exc
    paths.sort()
    if not paths or len(paths) != len(set(paths)):
        raise LeanDependencyError("LEAN_DEPENDENCY_PROJECT_SOURCE_SURFACE_INVALID")
    return paths


def _project_source_snapshot(
    repo: Path, *, error_code: str
) -> tuple[list[str], list[dict[str, str]]]:
    """Read one stable exact-byte snapshot of the full Q3 source surface."""

    try:
        paths_before = _project_source_paths(repo)
        fingerprints, _holes = _source_evidence(
            repo, paths_before, scan_holes=False
        )
        paths_after = _project_source_paths(repo)
    except LeanDependencyError as exc:
        raise LeanDependencyError(error_code) from exc
    if paths_after != paths_before:
        raise LeanDependencyError(error_code)
    return paths_before, fingerprints


def _source_tree_sha256(fingerprints: Sequence[Mapping[str, str]]) -> str:
    payload = "".join(
        f"{row['path']}\t{row['sha256']}\n" for row in fingerprints
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _build_input_evidence(repo: Path) -> dict[str, dict[str, str]]:
    evidence: dict[str, dict[str, str]] = {}
    for rel in BUILD_INPUT_PATHS:
        payload, _state = _read_repo_file_stable(
            repo,
            rel,
            invalid_code="LEAN_DEPENDENCY_BUILD_INPUT_INVALID",
            mutation_code="LEAN_DEPENDENCY_BUILD_INPUT_MUTATED_DURING_READ",
        )
        evidence[PurePosixPath(rel).name] = {
            "path": rel,
            "sha256": hashlib.sha256(payload).hexdigest(),
        }
    return evidence


def _paths_to_targets(
    adjacency: Mapping[str, Sequence[str]], targets: set[str]
) -> dict[tuple[str, str, str], list[str]]:
    """Return one canonical shortest path for every distinct first-hop port."""

    def from_first_hop(start: str, *, blocked: str | None = None) -> dict[str, list[str]]:
        found: dict[str, list[str]] = {}
        queue: deque[tuple[str, list[str]]] = deque([(start, [start])])
        seen = {start}
        while queue:
            current, path = queue.popleft()
            if current in targets:
                found.setdefault(current, path)
            for ref in sorted(set(adjacency.get(current, ()))):
                if ref == blocked or ref in seen:
                    continue
                seen.add(ref)
                queue.append((ref, path + [ref]))
        return found

    cache: dict[str, dict[str, list[str]]] = {}
    paths: dict[tuple[str, str, str], list[str]] = {}
    for consumer in sorted(adjacency):
        for first_hop in sorted(set(adjacency.get(consumer, ()))):
            if first_hop == consumer:
                continue
            if first_hop not in cache:
                cache[first_hop] = from_first_hop(first_hop)
            first_paths = cache[first_hop]
            for target, tail in first_paths.items():
                if target == consumer:
                    continue
                if consumer in tail:
                    tail = from_first_hop(first_hop, blocked=consumer).get(target, [])
                    if not tail:
                        continue
                paths[(consumer, target, first_hop)] = [consumer, *tail]
    return paths


def _canonical_graph_rows(
    graph_rows: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Validate and deterministically deduplicate graph declarations.

    Multiple import roots can make Lean emit the same declaration more than
    once.  Only byte-equal semantic rows are aliases of that one declaration;
    any conflicting repeat is evidence drift and remains fatal.
    """

    rows_by_name: dict[str, dict[str, Any]] = {}
    payloads_by_name: dict[str, bytes] = {}
    for row in graph_rows:
        if set(row) != {
            "kind",
            "name",
            "module",
            "direct_refs",
            "type_refs",
            "value_refs",
        } or row.get("kind") != "GRAPH":
            raise LeanDependencyError("LEAN_DEPENDENCY_GRAPH_ROW_INVALID")
        name = _environment_name(row.get("name"))
        module = _name(row.get("module"))
        refs = row.get("direct_refs")
        type_values = row.get("type_refs")
        value_values = row.get("value_refs")
        if not all(
            isinstance(values, list)
            and all(isinstance(ref, str) for ref in values)
            for values in (refs, type_values, value_values)
        ):
            raise LeanDependencyError("LEAN_DEPENDENCY_GRAPH_ROW_INVALID")
        canonical = {
            "kind": "GRAPH",
            "name": name,
            "module": module,
            "direct_refs": [_environment_name(ref) for ref in refs],
            "type_refs": [_environment_name(ref) for ref in type_values],
            "value_refs": [_environment_name(ref) for ref in value_values],
        }
        if set(canonical["direct_refs"]) != set(canonical["type_refs"]) | set(
            canonical["value_refs"]
        ):
            raise LeanDependencyError("LEAN_DEPENDENCY_GRAPH_REFERENCE_SURFACE_DRIFT")
        payload = json.dumps(
            canonical,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        if name in rows_by_name:
            if payload != payloads_by_name[name]:
                raise LeanDependencyError(
                    "LEAN_DEPENDENCY_GRAPH_DECLARATION_DUPLICATE_CONFLICT"
                )
            continue
        rows_by_name[name] = canonical
        payloads_by_name[name] = payload
    return [rows_by_name[name] for name in sorted(rows_by_name)]


def snapshot_from_rows(
    graph_rows: Sequence[Mapping[str, Any]],
    metadata_rows: Sequence[Mapping[str, Any]],
    *,
    import_modules: Sequence[str],
    target_declarations: Sequence[str],
    semantic_declarations: Sequence[str] = (),
) -> dict[str, Any]:
    adjacency: dict[str, list[str]] = {}
    modules: dict[str, str] = {}
    type_refs: dict[str, set[str]] = {}
    value_refs: dict[str, set[str]] = {}
    for row in _canonical_graph_rows(graph_rows):
        name = row["name"]
        direct = set(row["direct_refs"])
        type_set = set(row["type_refs"])
        value_set = set(row["value_refs"])
        adjacency[name] = sorted(direct)
        type_refs[name] = type_set
        value_refs[name] = value_set
        modules[name] = row["module"]
    targets = {_name(value) for value in target_declarations}
    semantic = {_name(value) for value in semantic_declarations}
    if not targets:
        raise LeanDependencyError("LEAN_DEPENDENCY_TARGET_SET_EMPTY")
    missing = (targets | semantic) - adjacency.keys()
    if missing:
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_TARGET_MISSING: " + ",".join(sorted(missing))
        )
    paths = _paths_to_targets(adjacency, targets)
    unmappable_consumers = sorted(
        {
            consumer
            for consumer, _target, _first_hop in paths
            if not NAME_RE.fullmatch(consumer)
        }
    )
    if unmappable_consumers:
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_NONCANONICAL_CONSUMER_UNMAPPABLE: "
            + ",".join(unmappable_consumers)
        )
    relevant = targets | semantic | {
        consumer for consumer, _target, _first_hop in paths
    }
    metadata: dict[str, dict[str, Any]] = {}
    for row in metadata_rows:
        if set(row) != {
            "kind",
            "name",
            "module",
            "declaration_kind",
            "type_fingerprint",
            "value_fingerprint",
            "axioms",
        } or row.get("kind") != "METADATA":
            raise LeanDependencyError("LEAN_DEPENDENCY_METADATA_ROW_INVALID")
        name = _environment_name(str(row.get("name", "")))
        if name in metadata:
            raise LeanDependencyError("LEAN_DEPENDENCY_METADATA_DECLARATION_DUPLICATE")
        metadata[name] = dict(row)
    if set(metadata) != relevant:
        raise LeanDependencyError("LEAN_DEPENDENCY_METADATA_INCOMPLETE")

    def hypothesis_port(consumer: str, direct_reference: str) -> dict[str, str]:
        in_type = direct_reference in type_refs[consumer]
        in_value = direct_reference in value_refs[consumer]
        if in_type and in_value:
            surface = "ELABORATED_TYPE_AND_VALUE"
        elif in_type:
            surface = "ELABORATED_TYPE"
        elif in_value:
            surface = "ELABORATED_VALUE"
        else:
            raise LeanDependencyError("LEAN_DEPENDENCY_HYPOTHESIS_PORT_MISSING")
        return {"surface": surface, "direct_reference": direct_reference}

    declarations: list[dict[str, Any]] = []
    for name in sorted(relevant):
        row = metadata[name]
        module = _name(str(row.get("module", "")))
        if module != modules[name]:
            raise LeanDependencyError("LEAN_DEPENDENCY_METADATA_MODULE_DRIFT")
        declaration_kind = row.get("declaration_kind")
        if declaration_kind not in {
            "AXIOM",
            "DEFINITION",
            "THEOREM",
            "OPAQUE_DEFINITION",
            "QUOTIENT",
            "INDUCTIVE",
            "CONSTRUCTOR",
            "RECURSOR",
        }:
            raise LeanDependencyError("LEAN_DEPENDENCY_DECLARATION_KIND_INVALID")
        type_fingerprint = _expr_fingerprint(row.get("type_fingerprint"))
        value_fingerprint = _expr_fingerprint(
            row.get("value_fingerprint"), allow_none=True
        )
        if (name in semantic) != (value_fingerprint is not None) or (
            name in semantic
            and declaration_kind not in {"DEFINITION", "OPAQUE_DEFINITION"}
        ):
            raise LeanDependencyError("LEAN_DEPENDENCY_SEMANTIC_VALUE_FINGERPRINT_INVALID")
        axioms = row.get("axioms")
        if not isinstance(axioms, list) or not all(
            isinstance(axiom, str) for axiom in axioms
        ):
            raise LeanDependencyError("LEAN_DEPENDENCY_AXIOM_ROW_INVALID")
        declarations.append(
            {
                "name": name,
                "module": module,
                "declaration_kind": declaration_kind,
                "direct_refs": adjacency[name],
                "type_refs": sorted(type_refs[name]),
                "value_refs": sorted(value_refs[name]),
                "type_fingerprint": type_fingerprint,
                "value_fingerprint": value_fingerprint,
                "axioms": sorted(set(axioms)),
            }
        )

    return {
        "schema": SCHEMA,
        "algorithm_version": ALGORITHM_VERSION,
        "import_modules": sorted({_name(value) for value in import_modules}),
        "target_declarations": sorted(targets),
        "semantic_declarations": sorted(semantic),
        "expression_fingerprint_contract": {
            "algorithm": EXPR_FINGERPRINT_ALGORITHM,
            "bounded": True,
            "cryptographic": False,
            "threat_model": "ACCIDENTAL_DRIFT_ONLY",
            "toolchain_binding": "runtime_evidence.build_inputs.lean-toolchain.sha256",
        },
        "declarations": declarations,
        "consumptions": [
            {
                "consumer": consumer,
                "theorem": target,
                "relation": "DIRECT" if len(path) == 2 else "TRANSITIVE",
                "path": path,
                "hypothesis_port": hypothesis_port(consumer, first_hop),
            }
            for (consumer, target, first_hop), path in sorted(paths.items())
        ],
    }


def inspect_dependencies(
    repo: Path | str,
    *,
    import_modules: Iterable[str],
    target_declarations: Iterable[str],
    semantic_declarations: Iterable[str] = (),
    timeout: int = 900,
) -> dict[str, Any]:
    """Run the two-pass temporary Meta probe and return a closed snapshot."""

    repo_path = Path(repo).resolve()
    modules = sorted({_name(value) for value in import_modules})
    targets = sorted({_name(value) for value in target_declarations})
    semantic = sorted({_name(value) for value in semantic_declarations})
    if not modules or not targets:
        raise LeanDependencyError("LEAN_DEPENDENCY_INSPECTION_INPUT_EMPTY")
    root_source_paths = sorted({
        "q3.lean.aristotle/" + _name(module).replace(".", "/") + ".lean"
        for module in modules
        if module == "Q3" or module.startswith("Q3.")
    })
    if not root_source_paths:
        raise LeanDependencyError("LEAN_DEPENDENCY_PROJECT_IMPORT_SET_EMPTY")
    build_inputs_before = _build_input_evidence(repo_path)
    project_source_paths, project_source_fingerprints = _project_source_snapshot(
        repo_path,
        error_code="LEAN_DEPENDENCY_PROJECT_SOURCE_BASELINE_INVALID",
    )
    if not set(root_source_paths) <= set(project_source_paths):
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_ROOT_SOURCE_OUTSIDE_PROJECT_BASELINE"
        )
    prebuild_root_source_fingerprints, prebuild_holes = _source_evidence(
        repo_path, root_source_paths
    )
    if prebuild_holes:
        raise LeanDependencyError("LEAN_DEPENDENCY_PREBUILD_SOURCE_HOLE_PRESENT")
    project_fingerprints_by_path = {
        row["path"]: row for row in project_source_fingerprints
    }
    if prebuild_root_source_fingerprints != [
        project_fingerprints_by_path[path] for path in root_source_paths
    ]:
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_PROJECT_SOURCE_MUTATED_BEFORE_BUILD"
        )
    build_run = _run_build(repo_path, modules, timeout=timeout)
    postbuild_project_paths, postbuild_project_fingerprints = _project_source_snapshot(
        repo_path,
        error_code="LEAN_DEPENDENCY_PROJECT_SOURCE_MUTATED_DURING_BUILD",
    )
    if (
        postbuild_project_paths != project_source_paths
        or postbuild_project_fingerprints != project_source_fingerprints
    ):
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_PROJECT_SOURCE_MUTATED_DURING_BUILD"
        )
    graph_output, graph_run = _run_source(repo_path, graph_probe_source(modules), timeout=timeout)
    graph_rows = _canonical_graph_rows(
        parse_probe_output(graph_output, expected_kind="GRAPH")
    )
    closure_modules = parse_module_output(graph_output)
    adjacency = {
        _environment_name(str(row["name"])): [
            _environment_name(str(ref)) for ref in row["direct_refs"]
        ]
        for row in graph_rows
    }
    paths = _paths_to_targets(adjacency, set(targets))
    relevant = set(targets) | set(semantic) | {
        consumer for consumer, _target, _first_hop in paths
    }
    source_paths = [
        "q3.lean.aristotle/" + module.replace(".", "/") + ".lean"
        for module in closure_modules
    ]
    if not set(source_paths) <= set(project_source_paths):
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_IMPORT_CLOSURE_OUTSIDE_PREBUILD_BASELINE"
        )
    source_fingerprints_before, holes = _source_evidence(repo_path, source_paths)
    metadata_output, metadata_run = _run_source(
        repo_path,
        metadata_probe_source(
            modules,
            sorted(relevant),
            semantic_declarations=semantic,
        ),
        timeout=timeout,
    )
    metadata_rows = parse_probe_output(metadata_output, expected_kind="METADATA")
    source_fingerprints_after, holes_after = _source_evidence(repo_path, source_paths)
    if source_fingerprints_after != source_fingerprints_before or holes_after != holes:
        raise LeanDependencyError("LEAN_DEPENDENCY_SOURCE_MAP_MUTATED_DURING_PROBE")
    final_project_paths, final_project_fingerprints = _project_source_snapshot(
        repo_path,
        error_code="LEAN_DEPENDENCY_PROJECT_SOURCE_MUTATED_DURING_INSPECTION",
    )
    if (
        final_project_paths != project_source_paths
        or final_project_fingerprints != project_source_fingerprints
    ):
        raise LeanDependencyError(
            "LEAN_DEPENDENCY_PROJECT_SOURCE_MUTATED_DURING_INSPECTION"
        )
    build_inputs_after = _build_input_evidence(repo_path)
    if build_inputs_after != build_inputs_before:
        raise LeanDependencyError("LEAN_DEPENDENCY_BUILD_INPUT_MUTATED_DURING_INSPECTION")
    snapshot = snapshot_from_rows(
        graph_rows,
        metadata_rows,
        import_modules=modules,
        target_declarations=targets,
        semantic_declarations=semantic,
    )
    source_map_sha256 = hashlib.sha256(
        json.dumps(
            source_fingerprints_after, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()
    actions = [
        {
            "name": name,
            "command": list(run["command"]),
            "exit_code": run["returncode"],
            **(
                {"stdin_sha256": run["stdin_sha256"]}
                if "stdin_sha256" in run
                else {}
            ),
            "stdout_sha256": run["stdout_sha256"],
            "stderr_sha256": run["stderr_sha256"],
        }
        for name, run in (
            ("build", build_run),
            ("graph", graph_run),
            ("metadata", metadata_run),
        )
    ]
    declaration_map = {row["name"]: row for row in snapshot["declarations"]}
    theorem_axioms = {
        theorem: declaration_map[theorem]["axioms"] for theorem in targets
    }
    dependency_digest = hashlib.sha256(
        json.dumps(
            snapshot["consumptions"], sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()
    snapshot["runtime_evidence"] = {
        "build_run": build_run,
        "graph_run": graph_run,
        "metadata_run": metadata_run,
        "build_inputs": build_inputs_after,
        "import_closure_modules": closure_modules,
        "source_paths": source_paths,
        "root_source_paths": root_source_paths,
        "prebuild_root_source_fingerprints": prebuild_root_source_fingerprints,
        "project_source_baseline": {
            "root_path": PROJECT_SOURCE_ROOT,
            "file_count": len(project_source_paths),
            "algorithm": PROJECT_SOURCE_BASELINE_ALGORITHM,
            "tree_sha256": _source_tree_sha256(project_source_fingerprints),
        },
        "source_fingerprints": source_fingerprints_after,
        "source_map_sha256": source_map_sha256,
        "holes": holes,
        "validation_evidence": {
            "toolchain": build_inputs_after["lean-toolchain"],
            "build_inputs": build_inputs_after,
            "modules": modules,
            "theorem_ids": targets,
            "semantic_declarations": semantic,
            "import_closure_modules": closure_modules,
            "actions": actions,
            "hole_scan": {
                "patterns": ["sorry", "admit", "exact?"],
                "status": "PASS" if not holes else "FAIL",
                "findings": holes,
            },
            "theorem_axioms": theorem_axioms,
            "dependency_result": {
                "status": "EXACT",
                "edge_count": len(snapshot["consumptions"]),
                "sha256": dependency_digest,
            },
            "source_map_sha256": source_map_sha256,
        },
    }
    return snapshot


def validate_candidate_sources(
    repo: Path | str, source_paths: Iterable[str], *, timeout: int = 900
) -> list[dict[str, Any]]:
    """Compile exact dirty Lean bytes directly; imported dependencies remain explicit."""

    repo_path = Path(repo).resolve()
    lean_root, root_state = _lean_root_before(repo_path)
    receipts: list[dict[str, Any]] = []
    env = dict(os.environ)
    env.pop("LD_LIBRARY_PATH", None)
    prefix = "q3.lean.aristotle/"
    candidates = sorted(set(source_paths))
    baselines: dict[str, tuple[bytes, tuple[tuple[int, ...], ...], str]] = {}
    for rel in candidates:
        _canonical_relative_path(rel)
        if (
            not rel.startswith(prefix)
            or not rel.endswith(".lean")
        ):
            raise LeanDependencyError(f"LEAN_DEPENDENCY_CANDIDATE_PATH_INVALID: {rel}")
        before_bytes, before_state = _read_repo_file_stable(
            repo_path,
            rel,
            invalid_code="LEAN_DEPENDENCY_CANDIDATE_PATH_INVALID",
            mutation_code="LEAN_DEPENDENCY_CANDIDATE_PATH_MUTATED_DURING_CHECK",
        )
        try:
            source_text = before_bytes.decode("utf-8")
        except UnicodeError as exc:
            raise LeanDependencyError(f"LEAN_DEPENDENCY_CANDIDATE_PATH_INVALID: {rel}") from exc
        if HOLE_RE.search(source_text):
            raise LeanDependencyError(f"LEAN_DEPENDENCY_CANDIDATE_HOLE_PRESENT: {rel}")
        baselines[rel] = (
            before_bytes,
            before_state,
            hashlib.sha256(before_bytes).hexdigest(),
        )

    candidate_set = [
        {"path": rel, "sha256": baselines[rel][2]} for rel in candidates
    ]
    candidate_set_sha256 = hashlib.sha256(
        json.dumps(candidate_set, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()

    def assert_candidate_set_unchanged() -> None:
        for candidate_rel in candidates:
            payload, state = _read_repo_file_stable(
                repo_path,
                candidate_rel,
                invalid_code="LEAN_DEPENDENCY_CANDIDATE_PATH_MUTATED_DURING_CHECK",
                mutation_code="LEAN_DEPENDENCY_CANDIDATE_PATH_MUTATED_DURING_CHECK",
            )
            before_payload, before_state, before_sha256 = baselines[candidate_rel]
            if (
                state != before_state
                or payload != before_payload
                or hashlib.sha256(payload).hexdigest() != before_sha256
            ):
                raise LeanDependencyError(
                    "LEAN_DEPENDENCY_CANDIDATE_BYTES_MUTATED_DURING_CHECK"
                )

    for rel in candidates:
        assert_candidate_set_unchanged()
        command = ["lake", "env", "lean", rel[len(prefix) :]]
        try:
            proc = subprocess.run(
                command,
                cwd=lean_root,
                env=env,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            raise LeanDependencyError("LEAN_DEPENDENCY_CANDIDATE_COMPILE_TIMEOUT") from exc
        except (OSError, subprocess.SubprocessError) as exc:
            raise LeanDependencyError("LEAN_DEPENDENCY_CANDIDATE_COMPILE_UNAVAILABLE") from exc
        _assert_lean_root_unchanged(repo_path, root_state)
        assert_candidate_set_unchanged()
        if proc.returncode:
            raise LeanDependencyError(
                "LEAN_DEPENDENCY_CANDIDATE_COMPILE_FAILED: "
                f"returncode={proc.returncode}; {_failure_output(proc)}"
            )
        receipt = _process_receipt(proc, command)
        receipt.update(
            {
                "path": rel,
                "bytes_sha256": baselines[rel][2],
                "candidate_set": candidate_set,
                "candidate_set_sha256": candidate_set_sha256,
            }
        )
        receipts.append(receipt)
    assert_candidate_set_unchanged()
    return receipts
