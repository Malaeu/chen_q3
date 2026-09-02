#!/usr/bin/env python3
"""One fail-closed shelf -> properties -> direct Lean type-fit preflight."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from types import ModuleType
from typing import Any

REPO = Path(__file__).resolve().parents[1]
ASK = REPO / "ask.sh"
SEARCH_EXTERNAL = REPO / "scripts" / "search_external_lean.py"
FIT = REPO / "docs" / "cartographer" / "comparator" / "fit.py"
SCHEMA = "q3_supplier_preflight.v1"
EXTERNAL_SCHEMA = "q3_external_lean_search.v2"
PROVENANCE_CLASSES = frozenset({"SOURCE_DECLARED", "GENERATED_OR_DERIVED"})
STATUS_EXIT = {
    "CANDIDATE_ONLY": 0,
    "EXACT_FIT": 0,
    "REJECTED": 0,
    "FOREIGN_UNVERIFIED": 0,
    "COMPLETE_ABSENCE": 1,
    "INCOMPLETE": 2,
}
BOUNDARY = (
    "TEXT_OR_SEMANTIC_MATCHES_ARE_CANDIDATES;_ONLY_DIRECT_LEAN_TYPECHECK_"
    "WITH_STANDARD_AXIOMS_ESTABLISHES_EXACT_FIT"
)
SOURCE_ABSENCE_SCOPE = "SOURCE_DECLARATION_ABSENCE"


def _load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _strict_json_object(raw: str) -> dict[str, Any]:
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError("JSON root is not an object")
    return value


def run_external(
    query: str,
    *,
    candidate: str | None,
    candidate_provenance: str | None,
    timeout: float = 20.0,
) -> dict[str, Any]:
    """Run the complete external denominator exactly once."""
    command = [
        sys.executable,
        str(SEARCH_EXTERNAL),
        query,
        "--budget-seconds",
        "15",
    ]
    if candidate is not None:
        command.extend(("--candidate", candidate))
        if candidate_provenance is not None:
            command.extend(("--candidate-provenance", candidate_provenance))
    started = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "returncode": None,
            "stdout": "",
            "stderr": str(exc),
            "duration_ms": round((time.monotonic() - started) * 1000),
            "payload": None,
            "error": f"external Lean search unavailable: {exc}",
        }
    error: str | None = None
    payload: dict[str, Any] | None = None
    try:
        payload = _strict_json_object(proc.stdout)
    except (json.JSONDecodeError, ValueError) as exc:
        error = f"external Lean search emitted invalid JSON: {exc}"
    if payload is not None:
        try:
            search_external = _load_module("q3_search_external_lean", SEARCH_EXTERNAL)
            valid, validation_errors = search_external.validate_receipt(
                payload,
                expected_query=query,
                expected_candidate=candidate,
                expected_candidate_provenance=candidate_provenance,
                revalidate_current_roots=False,
            )
        except Exception as exc:
            error = f"external Lean search validator unavailable: {exc}"
        else:
            if not valid:
                error = "external Lean search receipt invalid: " + "; ".join(
                    validation_errors
                )
    if payload is not None and bool(payload.get("errors")) == (proc.returncode == 0):
        error = "external Lean search exit/status mismatch"
    return {
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "duration_ms": round((time.monotonic() - started) * 1000),
        "payload": payload,
        "error": error,
    }


def _secure_receipt(raw: str) -> Path:
    fd, name = tempfile.mkstemp(prefix="q3-external-lean-", suffix=".json")
    path = Path(name)
    try:
        os.fchmod(fd, stat.S_IRUSR | stat.S_IWUSR)
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
    except Exception:
        path.unlink(missing_ok=True)
        raise
    return path


def run_shelf(
    query: str, *, external_receipt: Path, timeout: int = 60
) -> dict[str, Any]:
    try:
        proc = subprocess.run(
            [
                str(ASK),
                "--deep",
                "--external-receipt",
                str(external_receipt),
                query,
            ],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        return {
            "status": "INCOMPLETE",
            "returncode": None,
            "transcript": "",
            "error": f"complete shelf timed out after {exc.timeout}s",
        }
    status = {0: "HITS", 1: "SHELF_ABSENCE", 2: "INCOMPLETE"}.get(
        proc.returncode, "INCOMPLETE"
    )
    transcript = "\n".join(
        part for part in (proc.stdout.rstrip(), proc.stderr.rstrip()) if part
    )
    return {
        "status": status,
        "returncode": proc.returncode,
        "transcript": transcript[-30000:],
    }


def _external_exact_results(external: dict[str, Any]) -> list[dict[str, Any]]:
    rows = external.get("base_results")
    if not isinstance(rows, list):
        return []
    return [
        row["exact_candidate"]
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("exact_candidate"), dict)
    ]


def _external_complete(external: dict[str, Any]) -> bool:
    enabled = external.get("enabled_bases")
    queried = external.get("bases_queried")
    return (
        external.get("schema") == EXTERNAL_SCHEMA
        and isinstance(enabled, list)
        and isinstance(queried, list)
        and len(enabled) == len(set(enabled))
        and set(enabled) == set(queried)
        and external.get("errors") == []
        and external.get("boundary")
        == "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE"
    )


def _external_candidate_present(external: dict[str, Any]) -> bool:
    return any(
        row.get("status") == "PRESENT" for row in _external_exact_results(external)
    )


def _external_source_absent(external: dict[str, Any]) -> bool:
    results = _external_exact_results(external)
    enabled = external.get("enabled_bases")
    return (
        _external_complete(external)
        and isinstance(enabled, list)
        and len(results) == len(enabled)
        and all(
            row.get("status") == "ABSENT"
            and row.get("boundary") == SOURCE_ABSENCE_SCOPE
            and isinstance(row.get("searched_regular_source_count"), int)
            for row in results
        )
    )


def _base_payload(
    query: str,
    candidate: str | None,
    target: str | None,
    candidate_provenance: str | None,
) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "query": query,
        "candidate_requested": candidate,
        "target_requested": target,
        "candidate_provenance": candidate_provenance,
        "shelf": None,
        "external_lean": None,
        "environment": None,
        "status": "INCOMPLETE",
        "reason": "preflight did not complete",
        "boundary": BOUNDARY,
        "candidate": None,
        "comparison": None,
        "foreign_candidate": [],
        "source_candidates": [],
        "prose_candidates_present": False,
        "source_absence_scope": None,
    }


def run_preflight(
    query: str,
    *,
    candidate: str | None = None,
    target: str | None = None,
    candidate_provenance: str | None = None,
) -> dict[str, Any]:
    payload = _base_payload(query, candidate, target, candidate_provenance)
    if candidate_provenance is not None and candidate_provenance not in PROVENANCE_CLASSES:
        payload["reason"] = "candidate provenance class is invalid"
        return payload

    external_run = run_external(
        query,
        candidate=candidate,
        candidate_provenance=candidate_provenance,
    )
    external = external_run.get("payload")
    if not isinstance(external, dict):
        payload["external_lean"] = {
            "schema": EXTERNAL_SCHEMA,
            "errors": [external_run.get("error") or "external Lean search failed"],
        }
        payload["reason"] = "enabled external-base denominator failed"
        return payload
    payload["external_lean"] = external

    receipt: Path | None = None
    try:
        receipt = _secure_receipt(str(external_run["stdout"]))
        shelf = run_shelf(query, external_receipt=receipt)
    except (OSError, ValueError) as exc:
        payload["reason"] = f"secure external receipt unavailable: {exc}"
        return payload
    finally:
        if receipt is not None:
            receipt.unlink(missing_ok=True)
    payload["shelf"] = shelf

    if external_run.get("error") or not _external_complete(external):
        payload["reason"] = "enabled external-base denominator failed"
        return payload
    if shelf["status"] == "INCOMPLETE":
        payload["reason"] = "complete deep shelf denominator failed"
        return payload
    if candidate is None:
        if shelf["status"] == "SHELF_ABSENCE":
            payload["reason"] = "PRECISE_CANDIDATE_REQUIRED_FOR_COMPLETE_ABSENCE"
        else:
            payload["status"] = "CANDIDATE_ONLY"
            payload["reason"] = "search produced recall candidates; no precise candidate supplied"
        return payload

    try:
        fit = _load_module("q3_supplier_fit", FIT)
        environment = fit.environment_freshness()
    except Exception as exc:
        payload["environment"] = {
            "status": "INCOMPLETE",
            "errors": [f"local fit runtime unavailable: {exc}"],
        }
        payload["reason"] = "local elaborated environment could not be inspected"
        return payload
    payload["environment"] = environment
    if environment.get("status") != "PASS":
        payload["reason"] = "local elaborated environment is stale or incomplete"
        return payload

    try:
        index = fit.load_index()
        candidate_name, candidate_row = fit.resolve_declaration(candidate, index)
    except fit.FitError as exc:
        if getattr(exc, "code", "") != "DECLARATION_NOT_FOUND":
            payload["reason"] = f"candidate unresolved: {exc}"
            return payload
        if _external_candidate_present(external):
            payload["status"] = "FOREIGN_UNVERIFIED"
            payload["foreign_candidate"] = [
                row
                for row in _external_exact_results(external)
                if row.get("status") == "PRESENT"
            ]
            payload["reason"] = (
                "foreign source declaration exists outside the compatible local Lean environment"
            )
            return payload
        try:
            source_candidates = fit.source_declaration_candidates(candidate)
        except fit.FitError as source_exc:
            payload["reason"] = f"source denominator incomplete: {source_exc}"
            return payload
        payload["source_candidates"] = source_candidates
        if source_candidates:
            payload["status"] = "CANDIDATE_ONLY"
            payload["reason"] = (
                "an exact local source declaration exists outside the fresh Route B index"
            )
            return payload
        if candidate_provenance != "SOURCE_DECLARED":
            payload["reason"] = "ELABORATED_EXTERNAL_DECLARATION_LOOKUP_REQUIRED"
            return payload
        if not _external_source_absent(external):
            payload["reason"] = "external source-declaration denominator is incomplete or present"
            return payload
        payload["status"] = "COMPLETE_ABSENCE"
        payload["reason"] = (
            "SOURCE_DECLARATION_ABSENCE: the explicit declaration is absent from every "
            "validated regular Lean source denominator; this is not global elaborated or "
            "semantic absence"
        )
        payload["prose_candidates_present"] = shelf["status"] == "HITS"
        payload["source_absence_scope"] = SOURCE_ABSENCE_SCOPE
        return payload

    payload["candidate"] = fit.declaration_properties(candidate_name, candidate_row)
    if target is None:
        payload["status"] = "CANDIDATE_ONLY"
        payload["reason"] = "candidate properties resolved; exact target not supplied"
        return payload

    comparison = fit.direct_type_fit(candidate, target)
    payload["comparison"] = comparison
    comparison_status = comparison.get("status")
    if comparison_status not in {"EXACT_FIT", "REJECTED", "INCOMPLETE"}:
        payload["reason"] = "direct type-fit emitted an invalid status"
        return payload
    payload["status"] = comparison_status
    payload["reason"] = {
        "INCOMPLETE": "direct type-fit could not be completed",
        "REJECTED": "Lean or the suitability gates rejected the candidate",
        "EXACT_FIT": "exact target type accepted the candidate in a fresh harness",
    }[comparison_status]
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", required=True)
    parser.add_argument("--candidate")
    parser.add_argument("--target")
    parser.add_argument("--candidate-provenance", choices=sorted(PROVENANCE_CLASSES))
    args = parser.parse_args()
    payload = run_preflight(
        args.query,
        candidate=args.candidate,
        target=args.target,
        candidate_provenance=args.candidate_provenance,
    )
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return STATUS_EXIT[payload["status"]]


if __name__ == "__main__":
    raise SystemExit(main())
