#!/usr/bin/env python3
"""Generic fail-closed direct type-fit over the local Lean environment index."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from types import ModuleType
from typing import Any

REPO = Path(__file__).resolve().parents[3]
LEAN_ROOT = REPO / "q3.lean.aristotle"
BUILD_LIB = LEAN_ROOT / ".lake" / "build" / "lib" / "lean"
PACKAGES_ROOT = LEAN_ROOT / ".lake" / "packages"
ENV_INDEX = REPO / "docs" / "cartographer" / "lean_env" / "env_index.jsonl"
ATOM_DESCRIBE = REPO / "docs" / "cartographer" / "atom_describe.py"
ENVDUMP = REPO / "docs" / "cartographer" / "lean_env" / "envdump.py"
ENVDUMP_COMMAND = "python3 docs/cartographer/lean_env/envdump.py --timeout 3600"
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
DECLARATION_RE = re.compile(
    r"^\s*(?:@\[[^]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|structure|class|inductive|instance)\b",
    re.MULTILINE,
)


class FitError(ValueError):
    """A stable fail-closed comparator error."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code
        self.detail = detail


def _load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise FitError("ENVIRONMENT_UNAVAILABLE", f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_index(path: Path = ENV_INDEX) -> dict[str, dict[str, Any]]:
    module = _load_module("q3_fit_atom_describe", ATOM_DESCRIBE)
    try:
        return module.load_env_index(path)
    except Exception as exc:
        raise FitError("ENVIRONMENT_INDEX_INVALID", str(exc)) from exc


def resolve_declaration(
    requested: str, index: dict[str, dict[str, Any]]
) -> tuple[str, dict[str, Any]]:
    """Resolve a full name or one unique basename; ambiguity is never guessed."""
    if requested in index:
        return requested, index[requested]
    basename = requested.rsplit(".", 1)[-1]
    candidates = sorted(
        name for name in index if name.rsplit(".", 1)[-1] == basename
    )
    if not candidates:
        raise FitError("DECLARATION_NOT_FOUND", requested)
    if len(candidates) != 1:
        raise FitError(
            "DECLARATION_AMBIGUOUS",
            f"{requested}: {', '.join(candidates[:12])}",
        )
    name = candidates[0]
    return name, index[name]


def source_declaration_candidates(requested: str) -> list[dict[str, Any]]:
    """Check compatible Lean core, mathlib, and Q3 sources before name absence."""
    module = _load_module("q3_fit_atom_source", ATOM_DESCRIBE)
    env = os.environ.copy()
    env.pop("LD_LIBRARY_PATH", None)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "--print-prefix"],
            cwd=LEAN_ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise FitError("SOURCE_DENOMINATOR_INCOMPLETE", str(exc)) from exc
    core = Path(proc.stdout.strip()) / "src" / "lean"
    try:
        package_roots = tuple(
            (f"package:{path.name}", path)
            for path in sorted(PACKAGES_ROOT.iterdir())
            if path.is_dir() and path.name != "mathlib"
        ) if PACKAGES_ROOT.is_dir() else ()
    except OSError as exc:
        raise FitError("SOURCE_DENOMINATOR_INCOMPLETE", str(exc)) from exc
    roots = (
        ("lean-core", core),
        ("mathlib", module.MATHLIB),
        *package_roots,
        ("ours", module.OURS),
    )
    unavailable = [source_id for source_id, root in roots if not root.is_dir()]
    if proc.returncode != 0 or unavailable:
        raise FitError(
            "SOURCE_DENOMINATOR_INCOMPLETE",
            f"unavailable source roots: {', '.join(unavailable) or proc.stderr.strip()}",
        )
    candidates: list[dict[str, Any]] = []
    for source_id, root in roots:
        found = module.find_declaration(requested, root)
        if found is not None:
            candidates.append({"source": source_id, **found})
    return candidates


def _source_has_declaration(path: Path) -> bool:
    try:
        return DECLARATION_RE.search(path.read_text(encoding="utf-8")) is not None
    except (OSError, UnicodeDecodeError):
        return True


def environment_freshness(
    *,
    index_path: Path = ENV_INDEX,
    prefix: str = "Q3.Proofs.RouteB",
) -> dict[str, Any]:
    """Bind the index to the complete current source/build environment."""
    try:
        index = load_index(index_path)
        envdump = _load_module("q3_fit_envdump", ENVDUMP)
        selected, source_modules, never_built, orphaned, stale = envdump.module_selection(
            prefix, 0
        )
    except (FitError, OSError, ValueError) as exc:
        return {
            "status": "INCOMPLETE",
            "errors": [str(exc)],
            "refresh_command": ENVDUMP_COMMAND,
        }

    indexed_modules = {
        str(row["file"])
        for row in index.values()
        if isinstance(row.get("file"), str) and str(row["file"]).startswith(prefix)
    }
    modules_with_declarations: set[str] = set()
    newer_sources: list[str] = []
    newer_oleans: list[str] = []
    try:
        index_mtime_ns = index_path.stat().st_mtime_ns
    except OSError as exc:
        return {
            "status": "INCOMPLETE",
            "errors": [f"environment index disappeared during validation: {exc}"],
            "refresh_command": ENVDUMP_COMMAND,
        }
    for module_name in source_modules:
        rel = Path(*module_name.split("."))
        source = LEAN_ROOT / rel.with_suffix(".lean")
        if _source_has_declaration(source):
            modules_with_declarations.add(module_name)
        if source.stat().st_mtime_ns > index_mtime_ns:
            newer_sources.append(module_name)
    for module_name in selected:
        rel = Path(*module_name.split("."))
        olean = BUILD_LIB / rel.with_suffix(".olean")
        if olean.stat().st_mtime_ns > index_mtime_ns:
            newer_oleans.append(module_name)

    missing_from_index = sorted(modules_with_declarations - indexed_modules)
    errors: list[str] = []
    if never_built:
        errors.append(f"never-built Route B modules: {len(never_built)}")
    if stale:
        errors.append(f"stale Route B .olean modules: {len(stale)}")
    if missing_from_index:
        errors.append(
            f"source modules with declarations absent from env index: {len(missing_from_index)}"
        )
    if newer_sources:
        errors.append(f"Route B sources newer than env index: {len(newer_sources)}")
    if newer_oleans:
        errors.append(f"Route B .olean files newer than env index: {len(newer_oleans)}")
    try:
        index_display = str(index_path.relative_to(REPO))
    except ValueError:
        index_display = str(index_path)
    return {
        "status": "PASS" if not errors else "INCOMPLETE",
        "prefix": prefix,
        "index": index_display,
        "index_declarations": len(index),
        "source_modules": len(source_modules),
        "built_current_modules": len(selected),
        "modules_with_declarations": len(modules_with_declarations),
        "indexed_modules": len(indexed_modules),
        "never_built": never_built,
        "stale_oleans": stale,
        "orphaned_oleans": orphaned,
        "missing_from_index": missing_from_index,
        "sources_newer_than_index": newer_sources,
        "oleans_newer_than_index": newer_oleans,
        "errors": errors,
        "refresh_command": ENVDUMP_COMMAND if errors else None,
    }


def declaration_properties(name: str, row: dict[str, Any]) -> dict[str, Any]:
    return {
        "name": name,
        "module": row["file"],
        "elaborated_type": row["type"],
        "levelParams": row["levelParams"],
        "axioms": row["axioms"],
        "isPrivate": row["isPrivate"],
        "isUnsafe": row["isUnsafe"],
    }


def _harness_source(
    candidate_name: str,
    candidate: dict[str, Any],
    target: dict[str, Any],
) -> str:
    imports = sorted({str(candidate["file"]), str(target["file"])})
    levels = sorted(
        {
            str(level)
            for level in [*candidate.get("levelParams", []), *target.get("levelParams", [])]
            if isinstance(level, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", level)
        }
    )
    parts = [*(f"import {module}" for module in imports), ""]
    if levels:
        parts.extend((f"universe {' '.join(levels)}", ""))
    parts.extend(
        (
            f"example : {target['type']} := by",
            f"  exact {candidate_name}",
            "",
        )
    )
    return "\n".join(parts)


def direct_type_fit(
    candidate_requested: str,
    target_requested: str,
    *,
    index_path: Path = ENV_INDEX,
    timeout: int = 600,
) -> dict[str, Any]:
    freshness = environment_freshness(index_path=index_path)
    if freshness.get("status") != "PASS":
        return {
            "status": "INCOMPLETE",
            "environment": freshness,
            "refresh_command": ENVDUMP_COMMAND,
        }
    index = load_index(index_path)
    try:
        candidate_name, candidate = resolve_declaration(candidate_requested, index)
        target_name, target = resolve_declaration(target_requested, index)
    except FitError as exc:
        return {
            "status": "INCOMPLETE",
            "environment": freshness,
            "error": {"code": exc.code, "detail": exc.detail},
        }

    candidate_props = declaration_properties(candidate_name, candidate)
    target_props = declaration_properties(target_name, target)
    disqualifiers: list[str] = []
    if candidate["isPrivate"]:
        disqualifiers.append("candidate is private")
    if candidate["isUnsafe"]:
        disqualifiers.append("candidate is unsafe")
    extra_axioms = sorted(set(candidate["axioms"]) - STANDARD_AXIOMS)
    if extra_axioms:
        disqualifiers.append(f"candidate has nonstandard axioms: {', '.join(extra_axioms)}")
    if target["isPrivate"]:
        disqualifiers.append("target is private")
    if disqualifiers:
        return {
            "status": "REJECTED",
            "environment": freshness,
            "candidate": candidate_props,
            "target": target_props,
            "diagnostic": "; ".join(disqualifiers),
        }

    source = _harness_source(candidate_name, candidate, target)
    with tempfile.TemporaryDirectory(prefix="q3-direct-type-fit-") as temp_dir:
        harness = Path(temp_dir) / "DirectTypeFit.lean"
        harness.write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env.pop("LD_LIBRARY_PATH", None)
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(harness)],
                cwd=LEAN_ROOT,
                env=env,
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            return {
                "status": "INCOMPLETE",
                "environment": freshness,
                "candidate": candidate_props,
                "target": target_props,
                "diagnostic": f"Lean direct type-fit timed out after {exc.timeout}s",
            }
    diagnostic = "\n".join(part for part in (proc.stdout.strip(), proc.stderr.strip()) if part)
    return {
        "status": "EXACT_FIT" if proc.returncode == 0 else "REJECTED",
        "environment": freshness,
        "candidate": candidate_props,
        "target": target_props,
        "command": "env -u LD_LIBRARY_PATH lake env lean <temporary-harness>",
        "returncode": proc.returncode,
        "diagnostic": diagnostic[-12000:],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--env-index", type=Path, default=ENV_INDEX)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    payload = direct_type_fit(
        args.candidate,
        args.target,
        index_path=args.env_index,
        timeout=args.timeout,
    )
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 2 if payload["status"] == "INCOMPLETE" else 0


if __name__ == "__main__":
    raise SystemExit(main())
