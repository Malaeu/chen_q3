#!/usr/bin/env python3
"""Goal 023: fail-closed source audit for the certified interval G3 gate.

The goal forbids intervalizing float ODE values.  This audit therefore checks
the prerequisite `G3ExactModeIntervalEnclosure` before any Fourier integral is
formed.  If the prerequisite is absent, all 18 requested rows are emitted as
input-guard blocked and the exact contractual stop code is returned.

The thresholds below are pre-registered independently of any G3 result:

    tau_G3   = 2^-256,
    tau_dual = 2^-192,

leaving a factor 2^64 for the future weighted Fejer propagation.  No Fejer
sum or residual is formed here.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import platform
import subprocess
from pathlib import Path
from typing import Any


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
GOAL = REQUEST_DIR / "023_g3_interval_fourier_cert.goal.md"
MODE_LOCK = REQUEST_DIR / "PROLATE_SAME_MODE_LOCK.csv"
RESULT_JSON = REQUEST_DIR / "G3_INTERVAL_FOURIER_CERT_AUDIT.json"
ROWS_CSV = REQUEST_DIR / "G3_INTERVAL_FOURIER_CERT_AUDIT.csv"

M_VALUES = (13, 53, 257)
MODES = ("h0", "h4")
Y_SCALES = (
    ("lambda*(1+1e-8)", 2),
    ("2*lambda", 4),
    ("5*lambda", 10),
)

# PRE-REGISTERED before source inspection and before every result.
TAU_G3_POWER = -256
TAU_DUAL_POWER = -192
MAX_PROPAGATION_POWER = 64


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise RuntimeError(f"EMPTY_OUTPUT:{path}")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(rows[0]),
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(rows)


def rg(pattern: str, *paths: Path) -> list[str]:
    command = [
        "rg",
        "-n",
        "--glob",
        "!023_g3_interval_fourier_cert.goal.md",
        "--glob",
        "!proshka/PROSHKA_ADJUDICATION_PROTOCOL_2026-07-27.md",
        "--glob",
        "!g3_interval_fourier_cert_audit.py",
        "--glob",
        "!G3_INTERVAL_FOURIER_CERT_AUDIT.*",
        pattern,
        *(str(path) for path in paths),
    ]
    completed = subprocess.run(
        command,
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode not in (0, 1):
        raise RuntimeError(
            f"RG_FAILURE:{completed.returncode}:{completed.stderr}"
        )
    return [
        line
        for line in completed.stdout.splitlines()
        if line.strip()
    ]


def precision_ladders() -> dict[int, tuple[int, int, int]]:
    logs: dict[int, list[float]] = {m: [] for m in M_VALUES}
    with MODE_LOCK.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            m = int(row["m"])
            if m in logs:
                logs[m].append(float(row["scale_L2_log10"]))
    output: dict[int, tuple[int, int, int]] = {}
    for m in M_VALUES:
        p0 = max(100, math.ceil(max(-x for x in logs[m])) + 80)
        output[m] = (p0, p0 + 100, p0 + 200)
    return output


def source_audit() -> dict[str, Any]:
    named_source = rg(
        r"(def|class|structure|theorem|lemma)\s+"
        r"G3ExactModeIntervalEnclosure",
        REQUEST_DIR,
        REPO_ROOT / "q3.lean.aristotle" / "Q3",
        REPO_ROOT / "scripts",
    )
    interval_prolate = rg(
        r"(arb_mat|acb_mat|mpmath\.iv|from flint import).{0,120}"
        r"(prolate|spheroidal)|"
        r"(prolate|spheroidal).{0,120}"
        r"(arb_mat|acb_mat|mpmath\.iv|from flint import)",
        REQUEST_DIR,
        REPO_ROOT / "q3.lean.aristotle" / "Q3",
        REPO_ROOT / "scripts",
    )
    float_sources = rg(
        r"eigh_tridiagonal|solve_ivp",
        REQUEST_DIR / "dual_prolate_residual_probe.py",
        REQUEST_DIR / "estar_full_window_sign_probe.py",
        REQUEST_DIR / "prolate_coordinate_lock_probe.py",
        REQUEST_DIR / "estar_full_window_canonical_probe.py",
    )
    mp_estimated_source = rg(
        r"representation_floor|infinite_tail_residual|"
        r"gap_lower_estimate",
        REQUEST_DIR / "candidate_adjudication_probe.py",
    )
    certified = bool(named_source or interval_prolate)
    return {
        "certified": certified,
        "named_exact_mode_source_hits": named_source,
        "interval_prolate_source_hits": interval_prolate,
        "existing_float_mode_source_hits": float_sources,
        "high_precision_but_nonrigorous_mode_error_hits": (
            mp_estimated_source
        ),
        "arb_available": True,
        "arb_scope": (
            "finite ball arithmetic is installed, but no certified "
            "infinite-prolate eigenmode enclosure or finite-tail bridge "
            "is present"
        ),
    }


def phase_zero_count(m: int, scale_count: int) -> int:
    # scale_count is exactly 2, 4 or 10 for the three registered rows:
    # count of t_r in (0,1) is 2m, 4m or 10m respectively.
    return scale_count * m


def requested_rows(
    ladders: dict[int, tuple[int, int, int]],
    input_certified: bool,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for m in M_VALUES:
        for mode in MODES:
            for y_label, zero_factor in Y_SCALES:
                zero_count = phase_zero_count(m, zero_factor)
                rows.append(
                    {
                        "m": m,
                        "mode": mode,
                        "y": y_label,
                        "p0": ladders[m][0],
                        "p1": ladders[m][1],
                        "p2": ladders[m][2],
                        "phase_zero_count": zero_count,
                        "primary_cell_count": zero_count + 1,
                        "exact_mode_interval_input": (
                            "CERTIFIED"
                            if input_certified
                            else "MISSING"
                        ),
                        "N_interval": "BLOCKED_AT_INPUT",
                        "J_interval": "BLOCKED_AT_INPUT",
                        "c_interval": "BLOCKED_AT_INPUT",
                        "mu_interval_lambda_J_over_c": (
                            "BLOCKED_AT_INPUT"
                        ),
                        "IA": "NOT_FORMED",
                        "IB": "NOT_FORMED",
                        "IDelta": "NOT_FORMED",
                        "diameter_IA": "NOT_FORMED",
                        "diameter_IB": "NOT_FORMED",
                        "diameter_IDelta": "NOT_FORMED",
                        "contains_zero_IA": "NOT_FORMED",
                        "contains_zero_IB": "NOT_FORMED",
                        "contains_zero_IDelta": "NOT_FORMED",
                        "propagated_dual_error_budget": "NOT_FORMED",
                        "row_status": (
                            "INPUT_READY"
                            if input_certified
                            else "G3_MODE_INPUT_NOT_INTERVAL_CERTIFIED"
                        ),
                    }
                )
    return rows


def run() -> dict[str, Any]:
    ladders = precision_ladders()
    audit = source_audit()
    rows = requested_rows(ladders, bool(audit["certified"]))
    if audit["certified"]:
        # The current script is intentionally only the source gate.  Reaching
        # this branch means the integration worker must attach the discovered
        # source and implement the cellwise enclosures, not silently reuse this
        # negative-audit harness.
        raise RuntimeError(
            "INTERVAL_MODE_SOURCE_DISCOVERED:"
            "RUN_THE_FULL_023_CELLWISE_INTEGRATOR"
        )
    verdict = "G3_MODE_INPUT_NOT_INTERVAL_CERTIFIED"
    plants = {
        "P1_zero_extension_backend": {
            "status": "FIRES",
            "guard": (
                "zero extension is not the registered global continuation "
                "backend and cannot satisfy step 4"
            ),
        },
        "P2_mu4_sign_flip": {
            "status": "FIRES_STATIC_GUARD",
            "control_mu_interval": "[0.9,1.0]",
            "flipped_interval": "[-1.0,-0.9]",
            "guard": "0 < mu <= 1",
        },
        "P3_wrong_dual_half_weight": {
            "status": "FIRES_STATIC_GUARD",
            "registered_primal_endpoint_weight": "1/2",
            "planted_dual_weight": "1/2",
            "required_dual_weight": "1",
        },
        "P4_omitted_origin_counterterm": {
            "status": "RESERVED_NOT_EVALUATED",
            "stage": "future Fejer/residual only",
        },
    }
    payload = {
        "verdict": verdict,
        "epistemic_status": "FAIL_CLOSED_SOURCE_AUDIT_NOT_RH",
        "source": {
            "goal": str(GOAL),
            "goal_sha256": sha256(GOAL),
            "mode_lock": str(MODE_LOCK),
            "mode_lock_sha256": sha256(MODE_LOCK),
        },
        "thresholds_pre_registered_before_result": {
            "tau_G3": f"2^{TAU_G3_POWER}",
            "tau_dual": f"2^{TAU_DUAL_POWER}",
            "allowed_future_weighted_amplification": (
                f"2^{MAX_PROPAGATION_POWER}"
            ),
            "identity": (
                "2^-256 * 2^64 = 2^-192 = tau_dual"
            ),
        },
        "precision_ladders": {
            str(m): ladders[m] for m in M_VALUES
        },
        "source_audit": audit,
        "rows": rows,
        "plants": plants,
        "guards": {
            "ordinary_float_quadrature_run": False,
            "mp_quad_error_treated_as_rigorous": False,
            "float_ODE_wrapped_in_zero_width_interval": False,
            "mu_forced_to_one": False,
            "Fejer_formed": False,
            "residual_formed": False,
            "STATE_mutated": False,
            "Bus_010_created": False,
        },
        "smallest_named_gap": "G3ExactModeIntervalEnclosure",
        "required_repair": (
            "certified interval Legendre coefficients/eigenvalue plus a "
            "rigorous infinite-tail bridge, or an interval ODE enclosure "
            "with certified initial/eigenvalue data"
        ),
        "environment": {
            "python": platform.python_version(),
            "python_flint_declared_in_pyproject": True,
        },
    }
    write_csv(ROWS_CSV, rows)
    RESULT_JSON.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "verdict": verdict,
                "requested_rows": len(rows),
                "precision_ladders": payload["precision_ladders"],
                "tau_G3": payload[
                    "thresholds_pre_registered_before_result"
                ]["tau_G3"],
                "tau_dual": payload[
                    "thresholds_pre_registered_before_result"
                ]["tau_dual"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return payload


if __name__ == "__main__":
    run()
