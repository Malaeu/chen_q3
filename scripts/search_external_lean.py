#!/usr/bin/env python3
"""Read-only term search over the enabled external Lean registry."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import time
from pathlib import Path
from types import ModuleType
from typing import Any

REPO = Path(__file__).resolve().parents[1]
ATOM_DESCRIBE = REPO / "docs" / "cartographer" / "atom_describe.py"
SCHEMA = "q3_external_lean_search.v2"
GREEN_BOUNDARY = "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE"
INCOMPLETE_BOUNDARY = "INCOMPLETE_EXTERNAL_LEAN_SEARCH"
PROVENANCE_CLASSES = {"SOURCE_DECLARED", "GENERATED_OR_DERIVED"}
DECLARATION_RE = re.compile(
    r"^\s*(?:@\[[^]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|constant)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
DECLARATION_START_RE = re.compile(
    r"^\s*(?:@\[[^]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|constant)\b"
)


class SearchIncomplete(RuntimeError):
    """The configured source denominator could not be searched completely."""


def _sha256_text(value: str | None) -> str | None:
    return None if value is None else hashlib.sha256(value.encode("utf-8")).hexdigest()


def _canonical_hash(value: object) -> str:
    raw = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _remaining(deadline: float) -> float:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise SearchIncomplete("monotonic external-search budget exhausted")
    return remaining


def _run_git(root: Path, args: list[str], deadline: float) -> str:
    proc = subprocess.run(
        ["git", "-C", str(root), *args],
        capture_output=True,
        text=True,
        check=False,
        timeout=_remaining(deadline),
    )
    if proc.returncode != 0:
        raise SearchIncomplete(proc.stderr.strip() or proc.stdout.strip() or "git failed")
    return proc.stdout.strip()


def _lean_files(root: Path, deadline: float) -> list[Path]:
    files: list[Path] = []
    stack = [root]
    while stack:
        _remaining(deadline)
        current = stack.pop()
        try:
            entries = sorted(os.scandir(current), key=lambda row: row.name)
        except OSError as exc:
            raise SearchIncomplete(f"cannot scan {current}: {exc}") from exc
        for entry in entries:
            _remaining(deadline)
            if entry.is_symlink():
                raise SearchIncomplete(
                    f"symlink in searched source denominator: {entry.path}"
                )
            if entry.is_dir(follow_symlinks=False):
                stack.append(Path(entry.path))
            elif entry.is_file(follow_symlinks=False) and entry.name.endswith(".lean"):
                files.append(Path(entry.path))
    return sorted(files, key=lambda path: path.relative_to(root).as_posix())


def _manifest_hash(root: Path, files: list[Path], deadline: float) -> str:
    rows: list[dict[str, str]] = []
    for path in files:
        _remaining(deadline)
        if path.is_symlink() or not path.is_file():
            raise SearchIncomplete(f"searched source changed type: {path}")
        rows.append(
            {
                "path": path.relative_to(root).as_posix(),
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
        )
    return _canonical_hash(rows)


def _content_identity(root: Path, deadline: float) -> tuple[dict[str, Any], list[Path]]:
    if root.is_symlink():
        raise SearchIncomplete(f"external Lean root is a symlink: {root}")
    try:
        canonical = root.resolve(strict=True)
    except OSError as exc:
        raise SearchIncomplete(f"external Lean root is unavailable: {root}: {exc}") from exc
    if not canonical.is_dir():
        raise SearchIncomplete(f"external Lean root is not a directory: {root}")
    root_stat = canonical.stat()
    files = _lean_files(canonical, deadline)
    identity: dict[str, Any] = {
        "canonical_root": str(canonical),
        "root_device": root_stat.st_dev,
        "root_inode": root_stat.st_ino,
        "searched_regular_source_count": len(files),
        "lean_manifest_sha256": _manifest_hash(canonical, files, deadline),
    }
    try:
        top = Path(_run_git(canonical, ["rev-parse", "--show-toplevel"], deadline)).resolve(
            strict=True
        )
        rel = canonical.relative_to(top).as_posix() or "."
    except (OSError, ValueError, SearchIncomplete):
        identity["kind"] = "NON_GIT_MANIFEST"
        return identity, files
    status = _run_git(
        canonical,
        ["status", "--porcelain=v1", "--untracked-files=all", "--", rel],
        deadline,
    )
    dirty_lean = sorted(line for line in status.splitlines() if ".lean" in line.casefold())
    if dirty_lean:
        raise SearchIncomplete("dirty or untracked Lean source: " + "; ".join(dirty_lean[:8]))
    identity.update(
        {
            "kind": "GIT_TREE_AND_CLEAN_LEAN",
            "git_top_level": str(top),
            "git_head": _run_git(canonical, ["rev-parse", "HEAD"], deadline),
            "git_root_relative_path": rel,
            "git_head_object_id": _run_git(
                canonical, ["rev-parse", "HEAD" if rel == "." else f"HEAD:{rel}"], deadline
            ),
            "lean_status_clean": True,
        }
    )
    return identity, files


def _registry_module() -> ModuleType:
    spec = importlib.util.spec_from_file_location("q3_external_lean_registry", ATOM_DESCRIBE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {ATOM_DESCRIBE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _load_bases() -> tuple[list[str], list[tuple[str, Path]]]:
    module = _registry_module()
    return module.enabled_base_ids(), module.load_bases()


def query_terms(query: str) -> list[str]:
    seen: set[str] = set()
    terms: list[str] = []
    for token in re.findall(r"[A-Za-z][A-Za-z0-9_'.-]{2,}", query):
        folded = token.casefold()
        if folded not in seen:
            seen.add(folded)
            terms.append(token)
    if not terms:
        for token in re.findall(r"\S{3,}", query):
            cleaned = token.strip(".,;:!?()[]{}\"'`")
            folded = cleaned.casefold()
            if len(cleaned) >= 3 and folded not in seen:
                seen.add(folded)
                terms.append(cleaned)
    return terms


def search_registry(
    query: str,
    *,
    candidate: str | None = None,
    candidate_provenance: str | None = None,
    budget_seconds: float = 15.0,
    bases: list[tuple[str, Path]] | None = None,
    enabled_ids: list[str] | None = None,
    max_matches: int = 20,
) -> dict[str, object]:
    started = time.monotonic()
    deadline = started + max(0.001, budget_seconds)
    errors: list[str] = []
    if candidate_provenance is not None and candidate_provenance not in PROVENANCE_CLASSES:
        errors.append(f"unknown candidate provenance: {candidate_provenance}")
    if bases is None:
        try:
            expected, resolved = _load_bases()
        except Exception as exc:
            expected, resolved = [], []
            errors.append(f"registry: {exc}")
    else:
        resolved = bases
        expected = list(enabled_ids) if enabled_ids is not None else [row[0] for row in bases]
    terms = query_terms(query)
    matches: list[dict[str, object]] = []
    queried: list[str] = []
    base_results: list[dict[str, Any]] = []
    returned_ids = [base_id for base_id, _ in resolved]
    duplicates = sorted({base_id for base_id in returned_ids if returned_ids.count(base_id) > 1})
    if duplicates:
        errors.append(f"ambiguous resolved base ids: {', '.join(duplicates)}")
    missing = sorted(set(expected) - set(returned_ids))
    unexpected = sorted(set(returned_ids) - set(expected))
    if missing:
        errors.append(f"enabled bases not resolved: {', '.join(missing)}")
    if unexpected:
        errors.append(f"resolved bases not enabled: {', '.join(unexpected)}")
    if not terms:
        errors.append("query has no searchable Lean identifier")

    if terms and not (duplicates or missing or unexpected):
        seen: set[str] = set()
        folded_terms = [term.casefold() for term in terms]
        query_names = set(folded_terms)
        candidate_tail = candidate.rsplit(".", 1)[-1].casefold() if candidate else None
        for base_id, root in resolved:
            if base_id in seen:
                continue
            seen.add(base_id)
            try:
                before, files = _content_identity(root, deadline)
                canonical = Path(str(before["canonical_root"]))
                exact_lines: list[str] = []
                uncertain_lines: list[str] = []
                for source in files:
                    _remaining(deadline)
                    rel = source.relative_to(canonical).as_posix()
                    try:
                        lines = source.read_text(encoding="utf-8").splitlines()
                    except (OSError, UnicodeError) as exc:
                        raise SearchIncomplete(f"cannot decode {source}: {exc}") from exc
                    for line_number, snippet in enumerate(lines, start=1):
                        _remaining(deadline)
                        folded = snippet.casefold()
                        declaration = DECLARATION_RE.match(snippet)
                        if len(matches) < max_matches and any(
                            term in folded for term in folded_terms
                        ):
                            declaration_name = declaration.group("name") if declaration else None
                            match_kind = "TEXT_CANDIDATE"
                            if declaration_name and (
                                declaration_name.casefold() in query_names
                                or declaration_name.rsplit(".", 1)[-1].casefold()
                                in query_names
                            ):
                                match_kind = "EXACT_DECLARATION"
                            matches.append(
                                {
                                    "base_id": base_id,
                                    "path": rel,
                                    "line": line_number,
                                    "match_kind": match_kind,
                                    "declaration_name": declaration_name,
                                    "snippet": snippet[:240],
                                }
                            )
                        if candidate_tail and candidate_tail in folded:
                            if declaration is not None:
                                declared_tail = (
                                    declaration.group("name")
                                    .rsplit(".", 1)[-1]
                                    .casefold()
                                )
                                if declared_tail == candidate_tail:
                                    exact_lines.append(f"{rel}:{line_number}:{snippet}")
                            elif DECLARATION_START_RE.match(snippet) or re.match(
                                r"^\s*(?:macro|syntax|elab)\b", snippet
                            ):
                                uncertain_lines.append(f"{rel}:{line_number}:{snippet}")
                after, after_files = _content_identity(root, deadline)
                if before != after or len(files) != len(after_files):
                    raise SearchIncomplete("source identity changed during search")
                exact_result: dict[str, Any] | None = None
                if candidate is not None:
                    bound_lines = sorted(exact_lines)
                    status = (
                        "INCOMPLETE"
                        if uncertain_lines
                        else ("PRESENT" if bound_lines else "ABSENT")
                    )
                    exact_result = {
                        "status": status,
                        "searched_regular_source_count": len(files),
                        "match_count": len(bound_lines),
                        "match_digest": _canonical_hash(bound_lines),
                        "displayed_matches": bound_lines[:20],
                        "uncertain_count": len(uncertain_lines),
                        "boundary": (
                            "SOURCE_DECLARATION_LOOKUP_UNCERTAIN"
                            if uncertain_lines
                            else (
                                "SOURCE_DECLARATION_PRESENT"
                                if bound_lines
                                else "SOURCE_DECLARATION_ABSENCE"
                            )
                        ),
                    }
                    if uncertain_lines:
                        errors.append(f"{base_id}: exact candidate lookup uncertain")
                base_results.append(
                    {
                        "base_id": base_id,
                        "canonical_root": str(canonical),
                        "identity_before": before,
                        "identity_after": after,
                        "searched_regular_source_count": len(files),
                        "exact_candidate": exact_result,
                    }
                )
                queried.append(base_id)
            except (OSError, RuntimeError, SearchIncomplete, subprocess.TimeoutExpired) as exc:
                errors.append(f"{base_id}: {exc}")
    registry_rows = [
        (str(row["base_id"]), str(row["canonical_root"])) for row in base_results
    ]
    return {
        "schema": SCHEMA,
        "query": query,
        "query_sha256": _sha256_text(query),
        "candidate": candidate,
        "candidate_sha256": _sha256_text(candidate),
        "candidate_provenance": candidate_provenance,
        "budget_seconds": budget_seconds,
        "registry_sha256": _canonical_hash({"enabled": expected, "resolved": registry_rows}),
        "enabled_bases": expected,
        "bases_queried": queried,
        "terms": terms,
        "matches": matches,
        "base_results": base_results,
        "errors": errors,
        "boundary": INCOMPLETE_BOUNDARY if errors else GREEN_BOUNDARY,
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def validate_receipt(
    payload: object,
    *,
    expected_query: str,
    expected_candidate: str | None = None,
    expected_candidate_provenance: str | None = None,
    max_budget_seconds: float = 15.0,
    revalidate_current_roots: bool = True,
) -> tuple[bool, list[str]]:
    """Validate binding and, by default, re-observe every searched source root."""
    errors: list[str] = []
    digest_re = re.compile(r"^[0-9a-f]{64}$")
    if not isinstance(payload, dict):
        return False, ["external receipt is not an object"]
    if payload.get("schema") != SCHEMA:
        errors.append("external receipt schema mismatch")
    if payload.get("query") != expected_query or payload.get(
        "query_sha256"
    ) != _sha256_text(expected_query):
        errors.append("external receipt query binding mismatch")
    budget = payload.get("budget_seconds")
    if not isinstance(budget, (int, float)) or budget <= 0 or budget > max_budget_seconds:
        errors.append("external receipt budget is invalid")
    enabled = payload.get("enabled_bases")
    queried = payload.get("bases_queried")
    rows = payload.get("base_results")
    if not isinstance(enabled, list) or not isinstance(queried, list) or not isinstance(rows, list):
        return False, errors + ["external receipt denominator fields are malformed"]
    row_ids = [row.get("base_id") for row in rows if isinstance(row, dict)]
    if enabled != queried or enabled != row_ids or len(enabled) != len(set(enabled)):
        errors.append("external receipt enabled/resolved/queried denominator mismatch")
    registry_rows = [
        (str(row.get("base_id")), str(row.get("canonical_root")))
        for row in rows
        if isinstance(row, dict)
    ]
    if payload.get("registry_sha256") != _canonical_hash(
        {"enabled": enabled, "resolved": registry_rows}
    ):
        errors.append("external receipt registry binding mismatch")
    if payload.get("errors") != [] or payload.get("boundary") != GREEN_BOUNDARY:
        errors.append("external receipt reports incomplete search")
    if not isinstance(payload.get("matches"), list) or not isinstance(
        payload.get("terms"), list
    ):
        errors.append("external receipt result fields are malformed")
    candidate_value = payload.get("candidate")
    candidate = candidate_value if isinstance(candidate_value, str) else None
    if payload.get("candidate_sha256") != _sha256_text(candidate):
        errors.append("external receipt candidate binding mismatch")
    provenance = payload.get("candidate_provenance")
    if provenance is not None and provenance not in PROVENANCE_CLASSES:
        errors.append("external receipt candidate provenance is invalid")
    if expected_candidate is not None and candidate != expected_candidate:
        errors.append("external receipt exact candidate replay mismatch")
    if (
        expected_candidate_provenance is not None
        and provenance != expected_candidate_provenance
    ):
        errors.append("external receipt candidate provenance replay mismatch")
    deadline = time.monotonic() + max(0.001, max_budget_seconds)
    for row in rows:
        if not isinstance(row, dict):
            errors.append("external receipt base row is malformed")
            continue
        before, after = row.get("identity_before"), row.get("identity_after")
        if not isinstance(before, dict) or before != after:
            errors.append(f"{row.get('base_id')}: pre/post identity mismatch")
            continue
        if row.get("canonical_root") != before.get("canonical_root"):
            errors.append(f"{row.get('base_id')}: canonical root binding mismatch")
        if (
            before.get("kind") not in {"GIT_TREE_AND_CLEAN_LEAN", "NON_GIT_MANIFEST"}
            or not isinstance(before.get("searched_regular_source_count"), int)
            or before.get("searched_regular_source_count")
            != row.get("searched_regular_source_count")
            or not isinstance(before.get("lean_manifest_sha256"), str)
            or digest_re.fullmatch(str(before.get("lean_manifest_sha256"))) is None
            or not isinstance(before.get("root_device"), int)
            or not isinstance(before.get("root_inode"), int)
        ):
            errors.append(f"{row.get('base_id')}: content identity is malformed")
        exact = row.get("exact_candidate")
        if candidate is not None and (
            not isinstance(exact, dict) or exact.get("status") not in {"PRESENT", "ABSENT"}
        ):
            errors.append(f"{row.get('base_id')}: exact candidate result incomplete")
        if isinstance(exact, dict):
            exact_status = exact.get("status")
            match_count = exact.get("match_count")
            expected_boundary = {
                "PRESENT": "SOURCE_DECLARATION_PRESENT",
                "ABSENT": "SOURCE_DECLARATION_ABSENCE",
            }.get(str(exact_status))
            if (
                not isinstance(match_count, int)
                or match_count < 0
                or not isinstance(exact.get("match_digest"), str)
                or digest_re.fullmatch(str(exact.get("match_digest"))) is None
                or not isinstance(exact.get("displayed_matches"), list)
                or exact.get("boundary") != expected_boundary
                or exact.get("uncertain_count") != 0
                or (exact_status == "ABSENT" and match_count != 0)
                or (exact_status == "PRESENT" and match_count < 1)
            ):
                errors.append(f"{row.get('base_id')}: exact candidate metadata malformed")
        if isinstance(exact, dict) and exact.get("searched_regular_source_count") != row.get(
            "searched_regular_source_count"
        ):
            errors.append(f"{row.get('base_id')}: exact candidate denominator mismatch")
        if revalidate_current_roots and isinstance(row.get("canonical_root"), str):
            try:
                current, _ = _content_identity(Path(row["canonical_root"]), deadline)
            except Exception as exc:
                errors.append(f"{row.get('base_id')}: current identity unavailable: {exc}")
            else:
                if current != after:
                    errors.append(f"{row.get('base_id')}: source identity changed after receipt")
    return not errors, errors


def load_secure_receipt(
    path: Path,
    *,
    expected_query: str,
    validate_configured_registry: bool = True,
) -> tuple[dict[str, Any] | None, list[str]]:
    """Load one private, non-repository receipt and validate its live bindings."""
    errors: list[str] = []
    try:
        resolved = path.resolve(strict=True)
        if resolved.is_relative_to(REPO.resolve()):
            errors.append("external receipt must be outside the repository")
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode):
            errors.append("external receipt is not a regular file")
        if info.st_uid != os.getuid():
            errors.append("external receipt owner mismatch")
        if stat.S_IMODE(info.st_mode) != 0o600:
            errors.append("external receipt mode must be 0600")
        with os.fdopen(descriptor, "r", encoding="utf-8") as handle:
            payload = json.load(handle)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        return None, errors + [f"external receipt unreadable: {exc}"]
    valid, validation_errors = validate_receipt(payload, expected_query=expected_query)
    errors.extend(validation_errors)
    if validate_configured_registry and isinstance(payload, dict):
        try:
            expected_ids, configured = _load_bases()
            configured_rows = [
                (base_id, str(root.resolve(strict=True))) for base_id, root in configured
            ]
        except Exception as exc:
            errors.append(f"configured external registry unavailable: {exc}")
        else:
            receipt_rows = [
                (str(row.get("base_id")), str(row.get("canonical_root")))
                for row in payload.get("base_results", [])
                if isinstance(row, dict)
            ]
            if payload.get("enabled_bases") != expected_ids or receipt_rows != configured_rows:
                errors.append("external receipt does not match current configured registry")
    return (payload if isinstance(payload, dict) else None), errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("query")
    parser.add_argument("--max-matches", type=int, default=20)
    parser.add_argument("--budget-seconds", type=float, default=3.0)
    parser.add_argument("--candidate")
    parser.add_argument(
        "--candidate-provenance", choices=sorted(PROVENANCE_CLASSES)
    )
    parser.add_argument("--validate-receipt", type=Path)
    args = parser.parse_args()
    if args.validate_receipt is not None:
        payload, errors = load_secure_receipt(
            args.validate_receipt, expected_query=args.query
        )
        if errors or payload is None:
            print(
                json.dumps(
                    {
                        "schema": SCHEMA,
                        "query": args.query,
                        "errors": errors,
                        "boundary": INCOMPLETE_BOUNDARY,
                    },
                    ensure_ascii=False,
                    indent=2,
                    sort_keys=True,
                )
            )
            return 2
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
        return 0
    payload = search_registry(
        args.query,
        candidate=args.candidate,
        candidate_provenance=args.candidate_provenance,
        budget_seconds=args.budget_seconds,
        max_matches=args.max_matches,
    )
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 2 if payload["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
