#!/usr/bin/env python3
"""P057_7: a finite plateau must not promote to an atTop/operator-gap claim."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO = Path(__file__).resolve().parents[3]
PHASE3_SCRIPT = REPO / "docs/routeB_bus/phase3_scripts/ccm_delta_rate_profile.py"
EXPECTED_PHASE3_SHA256 = "60ea1dab2d1d62aa386d69cb3885da4158ac727d2cfb76e2ce0c9e77bd7e1c29"
INFERENCE_PRECEDENT = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB/CompactEvaluationRateTransfer.lean"
EXPECTED_INFERENCE_PRECEDENT_SHA256 = "72fa0e7d39efd60a6970c896a4fba943ed57e933de8b378b834fcc743a9baa1c"
NORMALIZATION_PRECEDENT = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB/NormalizedTrackingRateTransfer.lean"
EXPECTED_NORMALIZATION_PRECEDENT_SHA256 = "5505f05169caf670fb587c7b4f81d2b2d9bda1e2f3874c837afc392dcc5512ed"
TEST_FLOORS = (
    Fraction(1, 2),
    Fraction(1, 10),
    Fraction(1, 1000),
    Fraction(1, 1_000_000),
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_phase3_module():
    actual = sha256(PHASE3_SCRIPT)
    if actual != EXPECTED_PHASE3_SHA256:
        raise SystemExit(f"Phase-3 implementation pin mismatch: {actual}")
    name = "ccm_phase3_pinned_for_p057_7"
    spec = importlib.util.spec_from_file_location(name, PHASE3_SCRIPT)
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load pinned Phase-3 implementation")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


P3 = load_phase3_module()


def synthetic_gap(n_cutoff: int) -> Fraction:
    """Positive sequence with Delta_90 = Delta_120 = 1 and Delta_N -> 0."""
    if n_cutoff <= 120:
        return Fraction(1)
    return Fraction(120, n_cutoff)


def strict_tail_witness(floor: Fraction) -> dict[str, Any]:
    if floor <= 0:
        raise ValueError("floor must be positive")
    n_cutoff = max(121, (120 * floor.denominator) // floor.numerator + 1)
    gap = synthetic_gap(n_cutoff)
    if not 0 < gap < floor:
        raise AssertionError((floor, n_cutoff, gap))
    return {
        "floor": f"{floor.numerator}/{floor.denominator}",
        "witness_N": n_cutoff,
        "Delta_N": f"{gap.numerator}/{gap.denominator}",
        "strictly_positive": True,
        "strictly_below_floor": True,
    }


def build_result() -> dict[str, Any]:
    gap90 = P3.arb(1)
    gap120 = P3.arb(1)
    drift = P3.relative_midpoint_drift(gap90, gap120)
    finite_plateau_pass = bool(drift <= P3.STABILIZATION_RELATIVE_DRIFT)

    sampled_tail_n = (240, 480, 960, 1920)
    sampled_tail = [synthetic_gap(n) for n in sampled_tail_n]
    sampled_tail_strictly_decreasing = all(
        sampled_tail[i + 1] < sampled_tail[i]
        for i in range(len(sampled_tail) - 1)
    )
    sampled_tail_positive = all(value > 0 for value in sampled_tail)
    floor_witnesses = [strict_tail_witness(floor) for floor in TEST_FLOORS]

    # Deliberately wrong implication under test.
    mutant_eventually_atTop_claim = finite_plateau_pass

    # Canonical finite judge boundary retained by the pinned Phase-3 artifact.
    eventually_atTop_claim = False
    continuum_gap_claim = False
    operator_gap_receiver_invoked = False
    plant_fires = mutant_eventually_atTop_claim and not eventually_atTop_claim

    all_pass = all((
        sha256(PHASE3_SCRIPT) == EXPECTED_PHASE3_SHA256,
        sha256(INFERENCE_PRECEDENT) == EXPECTED_INFERENCE_PRECEDENT_SHA256,
        sha256(NORMALIZATION_PRECEDENT) == EXPECTED_NORMALIZATION_PRECEDENT_SHA256,
        finite_plateau_pass,
        sampled_tail_strictly_decreasing,
        sampled_tail_positive,
        all(row["strictly_below_floor"] for row in floor_witnesses),
        not eventually_atTop_claim,
        not continuum_gap_claim,
        not operator_gap_receiver_invoked,
        plant_fires,
    ))

    return {
        "schema": "P057_7FinitePlateauNotAtTop.v1",
        "plant": "P057_7_FINITE_PLATEAU_NOT_ATTOP",
        "status": "PASS" if all_pass else "FAIL",
        "verdict": (
            "P057_7_FINITE_PLATEAU_NOT_ATTOP_FIRED"
            if all_pass
            else "P057_7_FINITE_PLATEAU_NOT_ATTOP_FAILED"
        ),
        "source_lock": {
            "phase3_script": str(PHASE3_SCRIPT.relative_to(REPO)),
            "expected_sha256": EXPECTED_PHASE3_SHA256,
            "observed_sha256": sha256(PHASE3_SCRIPT),
            "pass": sha256(PHASE3_SCRIPT) == EXPECTED_PHASE3_SHA256,
        },
        "inference_precedents": {
            "primary": {
                "path": str(INFERENCE_PRECEDENT.relative_to(REPO)),
                "sha256": sha256(INFERENCE_PRECEDENT),
                "theorem": "fixed_bound_without_vanishing_rate_not_uniform_zero",
                "classification": "PRIMARY_ERROR_CLASS_PRECEDENT_NOT_LITERAL_REUSE",
                "transfer": "PASS",
            },
            "normalization_firewall": {
                "path": str(NORMALIZATION_PRECEDENT.relative_to(REPO)),
                "sha256": sha256(NORMALIZATION_PRECEDENT),
                "theorem": "detector_decay_does_not_imply_relative_decay",
                "classification": "CONDITIONAL_NORMALIZATION_PRECEDENT",
                "transfer": "NOT_LOAD_BEARING_FOR_CURRENT_RAW_GAP_PROFILE",
            },
        },
        "synthetic_sequence": {
            "definition": "Delta_N=1 for N<=120; Delta_N=120/N for N>120",
            "positive_for_all_N": True,
            "Delta_90": "1/1",
            "Delta_120": "1/1",
            "limit_atTop": "0",
            "sampled_tail": [
                {
                    "N": n,
                    "Delta_N": f"{value.numerator}/{value.denominator}",
                }
                for n, value in zip(sampled_tail_n, sampled_tail)
            ],
            "sampled_tail_strictly_decreasing": sampled_tail_strictly_decreasing,
            "floor_witnesses": floor_witnesses,
        },
        "finite_plateau_gate": {
            "N_pair": list(P3.STABILIZATION_PAIR),
            "relative_midpoint_drift": str(drift),
            "threshold": str(P3.STABILIZATION_RELATIVE_DRIFT),
            "pass": finite_plateau_pass,
            "scope": "FINITE_DIAGNOSTIC_ONLY",
        },
        "canonical_judge": {
            "eventually_atTop_claim": eventually_atTop_claim,
            "continuum_gap_claim": continuum_gap_claim,
            "operator_gap_receiver_invoked": operator_gap_receiver_invoked,
        },
        "mutant": {
            "name": "mutant_promote_finite_plateau_to_eventually_atTop",
            "mutated_claim": mutant_eventually_atTop_claim,
            "plant_fires": plant_fires,
        },
        "static_cell_plant_transfer": {
            "classification": "NOT_A_SUBSTITUTE_FOR_P057_7",
            "reason": (
                "Cell-(13,2) orientation and representative-label plants pin a "
                "single finite layout; P057_7 protects a finite-to-atTop implication."
            ),
            "future_mapping_reference": [
                "ccmPrime_plant_offdiag_orientation",
                "ccmNIC_plant_subtraction_orientation",
                "ccmNIC_plant_representative_label_integrity",
            ],
        },
        "boundary": {
            "phase3_script_modified": False,
            "phase3_result_modified": False,
            "lean_modified": False,
            "new_goal_minted": False,
            "route_promotion": False,
            "rh_claimed": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = build_result()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        output = args.output if args.output.is_absolute() else REPO / args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0 if result["status"] == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
