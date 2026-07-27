#!/usr/bin/env python3
"""Executable planted falsifiers A/B/C for the SOFT_2 fork."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "SOFT_2_PLANTED_FALSIFIERS.json"


def classify_tail(spec: dict[str, Any]) -> str:
    required = "forall_phi_forall_eps_exists_R_exists_j0_forall_j_ge_j0"
    if spec["quantifier_order"] != required:
        return "SOFT_JOINT_LIMIT_QUANTIFIER_MISSING"
    if not spec["uniform_combined_tail_proved"]:
        return "SOFT_JOINT_LIMIT_QUANTIFIER_MISSING"
    return "PASS"


def classify_zero_side(spec: dict[str, Any]) -> str:
    if spec["index_kind"] == "POSITIVE_CRITICAL_LINE_ORDINATES" or not spec["complete_multiset"]:
        return "SOFT_CRITICAL_LINE_ZERO_SUM_SMUGGLED"
    return "PASS"


def classify_grid(spec: dict[str, Any]) -> str:
    if (
        spec["sample_error"] <= spec["sample_tolerance"]
        and spec["sup_error_witness"] >= 1 - spec["sample_tolerance"]
        and not spec["uniform_modulus_supplied"]
    ):
        return "D06_GRID_ALIASING_FATAL"
    return "PASS"


def run_plants() -> dict[str, Any]:
    # Plant A: mass sits in shell n=j.  Every fixed head tends to zero, while
    # the illegal per-j cutoff R_j=j hides the moving tail.
    R = 17
    j0 = 23
    witness_j = max(R, j0) + 1
    tail_mass = 1.0 if witness_j > R else 0.0
    plant_a = {
        "quantifier_order": "forall_j_exists_R_j",
        "uniform_combined_tail_proved": False,
        "model": "a[j,n]=1 if n=j else 0",
    }
    code_a = classify_tail(plant_a)

    # Plant B is structured; no string heuristic is used by the judge.
    plant_b = {
        "formula": "2*sum_{gamma>0} H(gamma)",
        "index_kind": "POSITIVE_CRITICAL_LINE_ORDINATES",
        "complete_multiset": False,
    }
    code_b = classify_zero_side(plant_b)

    # Plant C: exact grid aliasing on I=[0,1].
    J = 64
    node_values = [math.sin(math.pi * J * (k / J)) for k in range(J + 1)]
    midpoint_values = [math.sin(math.pi * J * ((k + 0.5) / J)) for k in range(J)]
    plant_c = {
        "function": "f_J(x)=sin(pi*J*x)",
        "J": J,
        "h": 1 / J,
        "sample_error": max(abs(x) for x in node_values),
        "sample_tolerance": 1e-12,
        "sup_error_witness": max(abs(x) for x in midpoint_values),
        "uniform_modulus_supplied": False,
        "derivative_scale": math.pi * J,
    }
    code_c = classify_grid(plant_c)

    expected = {
        "A": "SOFT_JOINT_LIMIT_QUANTIFIER_MISSING",
        "B": "SOFT_CRITICAL_LINE_ZERO_SUM_SMUGGLED",
        "C": "D06_GRID_ALIASING_FATAL",
    }
    observed = {"A": code_a, "B": code_b, "C": code_c}

    controls = {
        "A_correct_quantifier_and_uniform_tail": classify_tail({
            "quantifier_order": "forall_phi_forall_eps_exists_R_exists_j0_forall_j_ge_j0",
            "uniform_combined_tail_proved": True,
        }),
        "B_full_zero_multiset": classify_zero_side({
            "formula": "sum over all nontrivial rho with multiplicity",
            "index_kind": "ALL_NONTRIVIAL_ZEROS_COMPLETE_MULTISET",
            "complete_multiset": True,
        }),
        "C_uniform_modulus_present": classify_grid({
            "sample_error": 0.0,
            "sample_tolerance": 1e-12,
            "sup_error_witness": 0.0,
            "uniform_modulus_supplied": True,
        }),
    }

    return {
        "schema": "route_b_soft_2_planted_falsifiers_v1",
        "status": "ALL_PLANTS_LIVE" if observed == expected else "PLANT_INERT",
        "plants": {
            "A": {
                "input": plant_a,
                "expected_code": expected["A"],
                "observed_code": code_a,
                "fired": code_a == expected["A"],
                "witness": {"fixed_R": R, "j0": j0, "j": witness_j, "tail_mass": tail_mass},
            },
            "B": {
                "input": plant_b,
                "expected_code": expected["B"],
                "observed_code": code_b,
                "fired": code_b == expected["B"],
                "witness": "critical-line ordinates are not the complete nontrivial-zero multiset",
            },
            "C": {
                "input": plant_c,
                "expected_code": expected["C"],
                "observed_code": code_c,
                "fired": code_c == expected["C"],
                "witness": {
                    "max_grid_abs": plant_c["sample_error"],
                    "max_midpoint_abs": plant_c["sup_error_witness"],
                    "derivative_scale": plant_c["derivative_scale"],
                },
            },
        },
        "positive_controls": controls,
        "rh_status": "NOT_RH",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = run_plants()
    if args.write:
        OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
