#!/usr/bin/env python3
"""Rigorous N-stabilized CCM sectional-gap profile for Goal 057 Phase 3."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import sys
import time
from pathlib import Path
from typing import Any

from flint import acb, arb, arb_mat, ctx


REPO = Path(__file__).resolve().parents[3]
PHASE2_SCRIPT = REPO / "docs/routeB_bus/phase2_scripts/ccm_beta_n_profile.py"
EXPECTED_PHASE2_SHA256 = "851db5963b4ad012cc3746b2827931b1beedad0b931676d2b40f4cb9ca774f72"

M_GRID = (12, 13, 14)
N_LADDER = (60, 90, 120)
PRECISIONS = (120, 240)
STABILIZATION_PAIR = (90, 120)
STABILIZATION_RELATIVE_DRIFT = arb("0.01")
PRODUCTION_EIGEN_ALGORITHM = "vdhoeven_mourrain"
VALIDATION_EIGEN_ALGORITHM = "rump"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_phase2_module():
    actual = sha256(PHASE2_SCRIPT)
    if actual != EXPECTED_PHASE2_SHA256:
        raise SystemExit(f"Phase-2 implementation pin mismatch: {actual}")
    name = "ccm_phase2_pinned"
    spec = importlib.util.spec_from_file_location(name, PHASE2_SCRIPT)
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load pinned Phase-2 implementation")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


P2 = load_phase2_module()
P1 = P2.P1


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    for divisor in range(2, math.isqrt(value) + 1):
        if value % divisor == 0:
            return False
    return True


def prime_powers_up_to(limit: int) -> tuple[tuple[int, int], ...]:
    rows = []
    for value in range(2, limit + 1):
        for prime in range(2, value + 1):
            if not is_prime(prime):
                continue
            power = prime
            while power < value:
                power *= prime
            if power == value:
                rows.append((value, prime))
                break
    return tuple(rows)


class CCMArbBuilderMN(P2.CCMArbBuilderN):
    def __init__(self, m_value: int, n_cutoff: int) -> None:
        self.m_value = m_value
        self.n_cutoff = n_cutoff
        self.pi = arb.pi()
        self.L = arb(m_value).log()
        self.z = arb(1) / (m_value * m_value)
        self.exp_minus_L_over_2 = arb(1) / arb(m_value).sqrt()
        self.I = acb(0, 1)
        self.exp_correction = self._exp_correction()
        self.constant = (
            arb.const_euler() + (4 * self.pi * (m_value - 1) / (m_value + 1)).log()
        ) / 2
        self.alpha = {n: self._alpha(n) for n in range(n_cutoff + 1)}
        self.beta = {n: self._beta(n) for n in range(n_cutoff + 1)}
        self.gamma = {n: self._gamma(n) for n in range(n_cutoff + 1)}
        self.prime_powers = prime_powers_up_to(m_value)
        self.log_prime = {p: arb(p).log() for _, p in self.prime_powers}
        self.log_k = {k: arb(k).log() for k, _ in self.prime_powers}

    def prime(self, n: int, m: int) -> arb:
        total = arb(0)
        for k, prime in self.prime_powers:
            total += self.log_prime[prime] / arb(k).sqrt() * self.q_nm(n, m, self.log_k[k])
        return total


def ordered_real_eigenvalues(matrix: arb_mat, algorithm: str) -> tuple[list[arb], dict[str, Any]]:
    started = time.time()
    eigenvalues = matrix.eig(algorithm=algorithm)
    if len(eigenvalues) != matrix.nrows():
        raise RuntimeError("Arb did not isolate the complete spectrum")
    ordered = sorted(eigenvalues, key=lambda z: float(z.real.mid()))
    for value in ordered:
        if 0 not in value.imag:
            raise RuntimeError(f"Hermitian eigenvalue enclosure missed the real axis: {value}")
    return [value.real for value in ordered], {
        "algorithm": algorithm,
        "eigenvalue_count": len(ordered),
        "elapsed_seconds": time.time() - started,
        "max_imaginary_ball": str(max((abs(value.imag) for value in ordered), key=lambda x: float(x.upper()))),
    }


def min_with_label(left: arb, left_label: str, right: arb, right_label: str) -> tuple[arb, str]:
    if left.upper() < right.lower():
        return left, left_label
    if right.upper() < left.lower():
        return right, right_label
    raise RuntimeError(f"competitor intervals overlap: {left_label}={left}, {right_label}={right}")


def endpoint_payload(value: arb) -> dict[str, str]:
    return {
        **P1.bounds(value),
        "model_midpoint": str(value.mid()),
        "endpoint_error_radius": str(value.rad()),
        "relative_accuracy_bits": str(value.rel_accuracy_bits()),
    }


def run_cell(m_value: int, n_cutoff: int, dps: int, algorithm: str) -> dict[str, Any]:
    ctx.dps = dps
    ctx.threads = 1
    started = time.time()
    builder = CCMArbBuilderMN(m_value, n_cutoff)
    even, odd, samples = builder.parity_blocks()
    even_values, even_meta = ordered_real_eigenvalues(even, algorithm)
    odd_values, odd_meta = ordered_real_eigenvalues(odd, algorithm)
    even1, even2, odd1 = even_values[0], even_values[1], odd_values[0]
    if not even1.upper() < even2.lower() or not even1.upper() < odd1.lower():
        raise RuntimeError("even ground is not interval-isolated from both competitors")

    competitor, controlling_sector = min_with_label(even2, "NEXT_EVEN", odd1, "ODD_GROUND")
    global_gap = competitor - even1
    even_gap = even2 - even1
    odd_gap = odd1 - even1
    sector_radius = global_gap / 2
    if not global_gap.lower() > 0 or not sector_radius.lower() > 0:
        raise RuntimeError("sectional gap/radius is not certified positive")

    err_low = even1.rad()
    err_high = competitor.rad()
    model_gap = competitor.mid() - even1.mid()
    perturbative_floor = model_gap - err_low - err_high
    if not perturbative_floor.lower() > 0:
        raise RuntimeError("endpoint error budget consumed the finite model gap")

    return {
        "m": m_value,
        "lambda": f"sqrt({m_value})",
        "N": n_cutoff,
        "dimension": 2 * n_cutoff + 1,
        "dps": dps,
        "elapsed_seconds": time.time() - started,
        "prime_powers": [k for k, _ in builder.prime_powers],
        "basis_order": f"{-n_cutoff}..{n_cutoff}",
        "L_equals_log_m": P1.bounds(builder.L),
        "even_ground": endpoint_payload(even1),
        "next_even": endpoint_payload(even2),
        "odd_ground": endpoint_payload(odd1),
        "controlling_sector": controlling_sector,
        "even_gap": P1.bounds(even_gap),
        "odd_gap": P1.bounds(odd_gap),
        "global_gap": P1.bounds(global_gap),
        "sector_isolation_radius": {
            **P1.bounds(sector_radius),
            "receiver": "Q3.RouteB.sectorIsolationRadius_certificate",
            "labeling": "epsilonPlus1=even_ground; epsilonPlus2=next_even; epsilonMinus1=odd_ground",
        },
        "perturbative_true_gap_payload": {
            "receiver": "Q3.RouteB.true_gap_lower_of_abs_endpoint_perturbations",
            "scope": "exact_finite_CCM_endpoints_only_after_Lean_ball_import",
            "modelLow": str(even1.mid()),
            "modelHigh": str(competitor.mid()),
            "errLow": str(err_low),
            "errHigh": str(err_high),
            "floor": str(perturbative_floor),
            "budget_strictly_positive": True,
            "finite_to_continuum": False,
            "eventually_atTop": False,
        },
        "even_spectrum_meta": even_meta,
        "odd_spectrum_meta": odd_meta,
        "matrix_entry_samples": samples,
        "interval_gap_pass": True,
    }


def overlap_field(first: dict[str, Any], second: dict[str, Any], field: str) -> bool:
    return P1.intervals_overlap(first[field], second[field])


def cross_precision(first: dict[str, Any], second: dict[str, Any]) -> dict[str, bool]:
    checks = {
        field: overlap_field(first, second, field)
        for field in (
            "even_ground",
            "next_even",
            "odd_ground",
            "even_gap",
            "odd_gap",
            "global_gap",
            "sector_isolation_radius",
        )
    }
    checks["controlling_sector"] = first["controlling_sector"] == second["controlling_sector"]
    checks["matrix_entry_samples"] = all(
        P1.intervals_overlap(first["matrix_entry_samples"][key], second["matrix_entry_samples"][key])
        for key in first["matrix_entry_samples"]
    )
    return checks


def relative_midpoint_drift(left: arb, right: arb) -> arb:
    denominator = max(abs(left.mid()), abs(right.mid()))
    return abs(left.mid() - right.mid()) / denominator


def prolate_proxy(m_value: int) -> arb:
    m = arb(m_value)
    return m ** (arb(9) / 2) * (-4 * arb.pi() * m).exp()


def rate_slope(left_m: int, left: arb, right_m: int, right: arb) -> arb:
    return -(right.log() - left.log()) / (right_m - left_m)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    grid = []
    for m_value in M_GRID:
        n_rows = []
        for n_cutoff in N_LADDER:
            precision_rows = []
            for dps in PRECISIONS:
                print(f"[phase3] m={m_value} N={n_cutoff} dps={dps} start", file=sys.stderr, flush=True)
                row = run_cell(m_value, n_cutoff, dps, PRODUCTION_EIGEN_ALGORITHM)
                precision_rows.append(row)
                print(
                    f"[phase3] m={m_value} N={n_cutoff} dps={dps} "
                    f"sector={row['controlling_sector']} elapsed={row['elapsed_seconds']:.2f}s",
                    file=sys.stderr,
                    flush=True,
                )
            consistency = cross_precision(*precision_rows)
            if not all(consistency.values()):
                raise RuntimeError(f"cross-precision mismatch at m={m_value}, N={n_cutoff}: {consistency}")
            n_rows.append({
                "N": n_cutoff,
                "precision_doubling": precision_rows,
                "cross_precision_consistency": consistency,
                "retained_precision_dps": PRECISIONS[-1],
                "retained": precision_rows[-1],
            })

        by_n = {row["N"]: row["retained"] for row in n_rows}
        gap90 = arb(by_n[STABILIZATION_PAIR[0]]["global_gap"]["ball"])
        gap120 = arb(by_n[STABILIZATION_PAIR[1]]["global_gap"]["ball"])
        drift = relative_midpoint_drift(gap90, gap120)
        stabilization = {
            "N_pair": list(STABILIZATION_PAIR),
            "cross_precision_consistent_at_both_N": all(
                all(row["cross_precision_consistency"].values())
                for row in n_rows
                if row["N"] in STABILIZATION_PAIR
            ),
            "relative_midpoint_drift": str(drift),
            "threshold": str(STABILIZATION_RELATIVE_DRIFT),
            "pass": bool(drift <= STABILIZATION_RELATIVE_DRIFT),
        }
        grid.append({
            "m": m_value,
            "N_ladder": n_rows,
            "stabilization": stabilization,
            "slope_endpoint": by_n[STABILIZATION_PAIR[1]],
        })

    # Independent retained-cell solver validation at N=120.
    validation = []
    for m_value in M_GRID:
        print(f"[phase3] validation rump m={m_value} N=120 dps=240 start", file=sys.stderr, flush=True)
        slow = run_cell(m_value, 120, 240, VALIDATION_EIGEN_ALGORITHM)
        fast = next(row["slope_endpoint"] for row in grid if row["m"] == m_value)
        checks = {
            field: overlap_field(fast, slow, field)
            for field in ("even_ground", "next_even", "odd_ground", "global_gap", "sector_isolation_radius")
        }
        checks["controlling_sector"] = fast["controlling_sector"] == slow["controlling_sector"]
        validation.append({"m": m_value, "checks": checks, "all_pass": all(checks.values())})
        print(f"[phase3] validation rump m={m_value} pass={all(checks.values())}", file=sys.stderr, flush=True)

    stabilized = [row for row in grid if row["stabilization"]["pass"]]
    gap_rates = []
    proxy_rates = []
    for left, right in zip(stabilized, stabilized[1:]):
        left_gap = arb(left["slope_endpoint"]["global_gap"]["ball"])
        right_gap = arb(right["slope_endpoint"]["global_gap"]["ball"])
        gap_rates.append({
            "m_pair": [left["m"], right["m"]],
            "sigma_Delta": P1.bounds(rate_slope(left["m"], left_gap, right["m"], right_gap)),
        })
        left_proxy = prolate_proxy(left["m"])
        right_proxy = prolate_proxy(right["m"])
        proxy_rates.append({
            "m_pair": [left["m"], right["m"]],
            "sigma_prolate_proxy": P1.bounds(rate_slope(left["m"], left_proxy, right["m"], right_proxy)),
        })

    cumulative = []
    for row in stabilized:
        gap = arb(row["slope_endpoint"]["global_gap"]["ball"])
        proxy = prolate_proxy(row["m"])
        cumulative.append({
            "m": row["m"],
            "N": STABILIZATION_PAIR[1],
            "global_gap": P1.bounds(gap),
            "r_Delta": P1.bounds(-gap.log() / row["m"]),
            "prolate_proxy": P1.bounds(proxy),
            "r_prolate_proxy": P1.bounds(-proxy.log() / row["m"]),
        })

    all_cells_pass = all(
        all(all(nrow["cross_precision_consistency"].values()) for nrow in mrow["N_ladder"])
        for mrow in grid
    )
    all_validation_pass = all(row["all_pass"] for row in validation)
    result = {
        "schema": "CCMSectionalGapRateProfile.v1",
        "verdict": "CCM_DELTA_RATE_PROFILE_FINITE_INTERVAL_PASS_RATE_UNRESOLVED"
        if all_cells_pass and all_validation_pass
        else "CCM_DELTA_RATE_PROFILE_INCONCLUSIVE",
        "rate_class": "DELTA_RATE_UNRESOLVED",
        "route": "CHALLENGER_NOT_RH",
        "promotion": "FORBIDDEN",
        "precommit": {
            "lambda_squared_grid": list(M_GRID),
            "N_ladder_at_each_lambda": list(N_LADDER),
            "precision_dps": list(PRECISIONS),
            "stabilization_pair": list(STABILIZATION_PAIR),
            "stabilization_relative_midpoint_drift_threshold": "0.01",
            "exclude_unstabilized_lambda_from_slope_fit": True,
        },
        "implementation": {
            "phase2_script": str(PHASE2_SCRIPT.relative_to(REPO)),
            "phase2_script_sha256": EXPECTED_PHASE2_SHA256,
            "python_flint_version": __import__("flint").__version__,
            "production_eigen_algorithm": PRODUCTION_EIGEN_ALGORITHM,
            "independent_validation_eigen_algorithm": VALIDATION_EIGEN_ALGORITHM,
        },
        "grid": grid,
        "stabilized_m_values": [row["m"] for row in stabilized],
        "gap_local_rates": gap_rates,
        "prolate_proxy_local_rates": proxy_rates,
        "cumulative_rates": cumulative,
        "actual_trial_numerator": {
            "status": "UNAVAILABLE_SOURCE_TARGET_BRIDGE_OPEN",
            "sigma_num": None,
            "log_numerator_over_Delta": None,
            "prolate_proxy_substituted": False,
        },
        "retained_N120_rump_validation": validation,
        "all_interval_cells_pass": all_cells_pass,
        "all_independent_validation_pass": all_validation_pass,
        "eventually_atTop_claim": False,
        "continuum_gap_claim": False,
        "semantic_boundary": "finite_sectional_gap_profile_only; actual_numerator_open; not_SlotH2a; not_RH",
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        output = args.output if args.output.is_absolute() else REPO / args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0 if all_cells_pass and all_validation_pass else 2


if __name__ == "__main__":
    raise SystemExit(main())
