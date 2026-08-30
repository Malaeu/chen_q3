#!/usr/bin/env python3
"""Fail-closed checks and plants for consumer-first research dependencies."""

from __future__ import annotations

import argparse
import copy
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import research_dependency_contract, session_briefing

PROMPTS = (
    "docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md",
    "docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md",
    "q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/proshka/PROSHKA_SYSTEM_PROMPT_v2.md",
)
PROMPT_MARKERS = (
    "SOURCE-LOCKED REQUEST INTAKE", "CONSUMER-FIRST DEPENDENCY CONTRACT",
    "DOWNSTREAM_CONSUMER", "ACTUAL_CONSUMER_REQUIREMENT",
    "ORIGINAL_OBJECT_IS", "KNOWN_WEAKER_INTERFACES",
    "FAILURE_TYPE", "EPISTEMIC_STATUS", "MATHEMATICALLY_DEAD requires",
)
SEMANTIC_EXCLUSIONS = (
    "q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md",
    "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/**",
    "q3.lean.aristotle/ACTIVE/pipeline/PROBLEM_SOLVER_PROMPT_RU.md",
    "q3.lean.aristotle/ACTIVE/COGNITIVE_GOVERNOR.md",
)


def check(repo: Path) -> None:
    session_briefing.validate_registry(repo)
    blobs = [(repo / rel).read_bytes() for rel in PROMPTS]
    if len(set(blobs)) != 1:
        raise RuntimeError("PROSHKA_PROMPT_MIRROR_DRIFT")
    text = blobs[0].decode("utf-8")
    for marker in PROMPT_MARKERS:
        if marker not in text:
            raise RuntimeError(f"PROSHKA_CONSUMER_FIRST_MARKER_MISSING:{marker}")
    if "Answer every entry" in text or "ARSENAL_MANDATE_*" in text:
        raise RuntimeError("PROSHKA_SELF_SELECTION_STALE")
    corpus = (repo / "scripts/q3_docs_corpus.py").read_text(encoding="utf-8")
    for rel in SEMANTIC_EXCLUSIONS:
        if rel not in corpus:
            raise RuntimeError(f"SEMANTIC_STALE_SURFACE_NOT_EXCLUDED:{rel}")


def plants(repo: Path) -> None:
    row = copy.deepcopy(session_briefing.validate_registry(repo)["debts"][0])
    research_dependency_contract.validate(row)
    for failure in ("NO_SOURCE", "FORMALIZATION_COST"):
        planted = copy.deepcopy(row)
        planted["epistemic_status"] = "MATHEMATICALLY_DEAD"
        planted["failure_type"] = failure
        try:
            research_dependency_contract.validate(planted)
        except research_dependency_contract.DependencyContractError:
            pass
        else:
            raise RuntimeError(f"PLANT_SURVIVED:{failure}_AS_DEAD")
    planted = copy.deepcopy(row)
    planted["original_object_is"] = "PROVED_NECESSARY"
    planted["necessity_evidence"] = []
    try:
        research_dependency_contract.validate(planted)
    except research_dependency_contract.DependencyContractError:
        pass
    else:
        raise RuntimeError("PLANT_SURVIVED:NECESSITY_WITHOUT_EVIDENCE")
    planted = copy.deepcopy(row)
    planted["epistemic_status"] = "MATHEMATICALLY_DEAD"
    planted["failure_type"] = "COUNTEREXAMPLE"
    planted["death_evidence"] = ["pinned-counterexample-ref"]
    research_dependency_contract.validate(planted)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("check", "plants"))
    parser.add_argument("--root", type=Path, default=REPO)
    args = parser.parse_args()
    try:
        (check if args.command == "check" else plants)(args.root.resolve())
    except Exception as exc:
        print(f"RESEARCH_DEPENDENCY_GATE_FAIL:{exc}", file=sys.stderr)
        return 2
    print(f"RESEARCH_DEPENDENCY_{args.command.upper()}_PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
