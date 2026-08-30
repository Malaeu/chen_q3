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

from orchestrator import (
    research_dependency_contract,
    research_dependency_projection,
    rigid_dependency_scan,
    session_briefing,
)
from scripts import q3_docs_corpus

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


def validate_semantic_exclusions(repo: Path) -> None:
    """Validate the selected corpus, not the selector source-code spelling."""
    selected = {
        path.relative_to(repo).as_posix()
        for path in q3_docs_corpus.collect_sources(repo)
    }
    for pattern in SEMANTIC_EXCLUSIONS:
        leaked = sorted(rel for rel in selected if q3_docs_corpus.matches_any(rel, (pattern,)))
        if leaked:
            raise RuntimeError(
                f"SEMANTIC_STALE_SURFACE_SELECTED:{pattern}:{','.join(leaked[:5])}"
            )


def check(repo: Path) -> None:
    session_briefing.validate_registry(repo)
    projection = repo / research_dependency_projection.OUTPUT
    if not projection.is_file() or projection.read_bytes() != research_dependency_projection.render(repo):
        raise RuntimeError("RESEARCH_DEPENDENCY_PROJECTION_STALE")
    blobs = [(repo / rel).read_bytes() for rel in PROMPTS]
    if len(set(blobs)) != 1:
        raise RuntimeError("PROSHKA_PROMPT_MIRROR_DRIFT")
    text = blobs[0].decode("utf-8")
    for marker in PROMPT_MARKERS:
        if marker not in text:
            raise RuntimeError(f"PROSHKA_CONSUMER_FIRST_MARKER_MISSING:{marker}")
    if "Answer every entry" in text or "ARSENAL_MANDATE_*" in text:
        raise RuntimeError("PROSHKA_SELF_SELECTION_STALE")
    validate_semantic_exclusions(repo)
    findings = rigid_dependency_scan.scan_repo(repo)
    if findings:
        preview = "\n".join(item.render() for item in findings[:20])
        suffix = f"\n... and {len(findings) - 20} more" if len(findings) > 20 else ""
        raise RuntimeError(f"RIGID_DEPENDENCY_SCAN_FAILED\n{preview}{suffix}")


def plants(repo: Path) -> None:
    row = copy.deepcopy(session_briefing.validate_registry(repo)["debts"][0])
    row.setdefault("failure_scope", "CURRENT_ATTEMPT")
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
    planted["death_evidence"] = [{
        "kind": "COUNTEREXAMPLE",
        "path": "docs/routeB_bus/PLANT.md",
        "commit": "1" * 40,
        "git_blob": "2" * 40,
        "scope": "EXACT_THEOREM_SHAPE",
        "claim": "The planted theorem shape is false.",
    }]
    research_dependency_contract.validate(planted)

    # The contextual scanner plants below exercise prose/template boundaries.

    unjustified = """# Live dependency\nSTATUS: OPEN\nBLOCKED: theorem X\n"""
    if not rigid_dependency_scan.scan_text("live.md", unjustified):
        raise RuntimeError("PLANT_SURVIVED:UNJUSTIFIED_BLOCKED_THEOREM")
    justified = """# Live dependency\nSTATUS: OPEN\nBLOCKED: theorem X\nDOWNSTREAM_CONSUMER: Y\nACTUAL_CONSUMER_REQUIREMENT: C\nORIGINAL_OBJECT_IS: UNKNOWN\nKNOWN_WEAKER_INTERFACES: [Z]\nWEAKER_INTERFACE_PROBE: test Z\nCONSUMER_IMPLICATION: Z => C => Y\n"""
    if rigid_dependency_scan.scan_text("live.md", justified):
        raise RuntimeError("PLANT_REJECTED:JUSTIFIED_CONSUMER_BLOCK")
    generator_bad = "def render():\n    return 'BLOCKED: theorem X'\n"
    if not rigid_dependency_scan.scan_text("generator.py", generator_bad, kind="generator"):
        raise RuntimeError("PLANT_SURVIVED:UNJUSTIFIED_GENERATOR_FIXTURE")
    generator_good = """def render():\n    return '''BLOCKED: theorem X\nDOWNSTREAM_CONSUMER: Y\nACTUAL_CONSUMER_REQUIREMENT: C\nORIGINAL_OBJECT_IS: UNKNOWN\nKNOWN_WEAKER_INTERFACES: Z\nWEAKER_INTERFACE_PROBE: test Z\nCONSUMER_IMPLICATION: Z => C => Y\n'''\n"""
    if rigid_dependency_scan.scan_text("generator.py", generator_good, kind="generator"):
        raise RuntimeError("PLANT_REJECTED:JUSTIFIED_GENERATOR_FIXTURE")
    closed = "# Old dependency\nSTATUS: CLOSED\nBLOCKED: theorem X\n"
    if rigid_dependency_scan.scan_text("old.md", closed):
        raise RuntimeError("PLANT_REJECTED:HISTORICAL_CLOSED_SURFACE")


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
