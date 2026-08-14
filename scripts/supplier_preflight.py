#!/usr/bin/env python3
"""One fail-closed shelf -> properties -> direct Lean type-fit preflight."""

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
from pathlib import Path
from types import ModuleType
from typing import Any

REPO = Path(__file__).resolve().parents[1]
ASK = REPO / "ask.sh"
SEARCH_EXTERNAL = REPO / "scripts" / "search_external_lean.py"
FIT = REPO / "docs" / "cartographer" / "comparator" / "fit.py"
BOUNDARY = (
    "TEXT_OR_SEMANTIC_MATCHES_ARE_CANDIDATES;_ONLY_DIRECT_LEAN_TYPECHECK_"
    "WITH_STANDARD_AXIOMS_ESTABLISHES_EXACT_FIT"
)


def _load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_shelf(query: str, *, timeout: int = 300) -> dict[str, Any]:
    try:
        proc = subprocess.run(
            [str(ASK), query],
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
    status = {0: "HITS", 1: "COMPLETE_ABSENCE", 2: "INCOMPLETE"}.get(
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


def _foreign_exact_match(
    candidate: str, external: dict[str, Any]
) -> list[dict[str, Any]]:
    basename = candidate.rsplit(".", 1)[-1].casefold()
    return [
        row
        for row in external.get("matches", [])
        if row.get("match_kind") == "EXACT_DECLARATION"
        and isinstance(row.get("declaration_name"), str)
        and str(row["declaration_name"]).rsplit(".", 1)[-1].casefold() == basename
    ]


def run_preflight(
    query: str,
    *,
    candidate: str | None = None,
    target: str | None = None,
) -> dict[str, Any]:
    shelf = run_shelf(query)
    try:
        search_external = _load_module("q3_supplier_external", SEARCH_EXTERNAL)
        external = search_external.search_registry(query)
    except Exception as exc:
        external = {
            "enabled_bases": [],
            "bases_queried": [],
            "matches": [],
            "errors": [f"external registry unavailable: {exc}"],
        }
    try:
        fit = _load_module("q3_supplier_fit", FIT)
        environment = fit.environment_freshness()
    except Exception as exc:
        return {
            "schema": "q3_supplier_preflight.v1",
            "query": query,
            "candidate_requested": candidate,
            "target_requested": target,
            "shelf": shelf,
            "external_lean": external,
            "environment": {
                "status": "INCOMPLETE",
                "errors": [f"local fit runtime unavailable: {exc}"],
            },
            "status": "INCOMPLETE",
            "reason": "local elaborated environment could not be inspected",
            "boundary": BOUNDARY,
        }
    payload: dict[str, Any] = {
        "schema": "q3_supplier_preflight.v1",
        "query": query,
        "candidate_requested": candidate,
        "target_requested": target,
        "shelf": shelf,
        "external_lean": external,
        "environment": environment,
        "status": "INCOMPLETE",
        "boundary": BOUNDARY,
    }
    if shelf["status"] == "INCOMPLETE" or external.get("errors"):
        payload["reason"] = "complete shelf or enabled external-base denominator failed"
        return payload
    if environment.get("status") != "PASS":
        payload["reason"] = "local elaborated environment is stale or incomplete"
        payload["refresh_command"] = environment.get("refresh_command")
        return payload
    if candidate is None:
        if shelf["status"] == "COMPLETE_ABSENCE" and not external.get("matches"):
            payload["status"] = "COMPLETE_ABSENCE"
            payload["reason"] = "all shelf layers and every enabled external base completed"
        else:
            payload["status"] = "CANDIDATE_ONLY"
            payload["reason"] = (
                "search produced recall candidates; no candidate/target pair supplied"
            )
        return payload

    try:
        index = fit.load_index()
        candidate_name, candidate_row = fit.resolve_declaration(candidate, index)
    except fit.FitError as exc:
        foreign = _foreign_exact_match(candidate, external)
        if foreign:
            payload["status"] = "FOREIGN_UNVERIFIED"
            payload["foreign_candidate"] = foreign
            payload["reason"] = (
                "foreign declaration is textually exact but is outside the compatible local "
                "Lean environment"
            )
        elif getattr(exc, "code", "") == "DECLARATION_NOT_FOUND":
            try:
                source_candidates = fit.source_declaration_candidates(candidate)
            except fit.FitError as source_exc:
                payload["reason"] = f"source denominator incomplete: {source_exc}"
                return payload
            if source_candidates:
                payload["status"] = "CANDIDATE_ONLY"
                payload["source_candidates"] = source_candidates
                payload["reason"] = (
                    "an exact Q3/mathlib source declaration exists outside the fresh "
                    "Route B environment index; properties and direct fit are not verified"
                )
            else:
                payload["status"] = "COMPLETE_ABSENCE"
                payload["reason"] = (
                    "candidate declaration is absent from the complete local Route B "
                    "environment, Lean core/Q3/dependency source trees, and every enabled external "
                    "Lean base; prose retrieval candidates, if any, do not establish a "
                    "declaration"
                )
                payload["prose_candidates_present"] = shelf["status"] == "HITS"
        else:
            payload["reason"] = f"candidate unresolved: {exc}"
        return payload
    payload["candidate"] = fit.declaration_properties(candidate_name, candidate_row)
    if target is None:
        payload["status"] = "CANDIDATE_ONLY"
        payload["reason"] = "candidate properties resolved; exact target not supplied"
        return payload

    comparison = fit.direct_type_fit(candidate, target)
    payload["comparison"] = comparison
    payload["status"] = comparison["status"]
    if comparison["status"] == "INCOMPLETE":
        payload["reason"] = "direct type-fit could not be completed"
    elif comparison["status"] == "REJECTED":
        payload["reason"] = "Lean or the suitability gates rejected the candidate"
    else:
        payload["reason"] = "exact target type accepted the candidate in a fresh harness"
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", required=True)
    parser.add_argument("--candidate")
    parser.add_argument("--target")
    args = parser.parse_args()
    payload = run_preflight(args.query, candidate=args.candidate, target=args.target)
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    if payload["status"] == "INCOMPLETE":
        return 2
    if payload["status"] == "COMPLETE_ABSENCE":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
