#!/usr/bin/env python3
"""Rigorous fixed-q beta_N profile for Goal 057 Phase 2.

Precommit: lambda=sqrt(13), N0=120, N=[120,160,200,240], exact Phase-1
J-even q, zero-padding only, precision doubling 180 -> 360 dps.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import acb, arb, arb_mat, ctx


REPO = Path(__file__).resolve().parents[3]
PHASE1_SCRIPT = REPO / "docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py"
EXPECTED_PHASE1_SHA256 = "1be57db69683652ed4f6d56dba6fc3b70c186f429fbb7f5bef978cd84f08ed0d"
N0 = 120
N_LADDER = (120, 160, 200, 240)
PRECISIONS = (180, 360)
INITIAL_BETA_UPPER = arb("1e-48")
RELATIVE_TOL_DENOMINATOR = 2**40
ABSOLUTE_TOL = arb("1e-100")
EIGEN_ALGORITHM = "vdhoeven_mourrain"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_phase1_module():
    actual = sha256(PHASE1_SCRIPT)
    if actual != EXPECTED_PHASE1_SHA256:
        raise SystemExit(f"Phase-1 implementation pin mismatch: {actual}")
    name = "ccm_phase1_pinned"
    spec = importlib.util.spec_from_file_location(name, PHASE1_SCRIPT)
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load pinned Phase-1 implementation")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


P1 = load_phase1_module()


class CCMArbBuilderN(P1.CCMArbBuilder):
    """N-parameterized form of the pinned Phase-1 source-side builder."""

    def __init__(self, n_cutoff: int) -> None:
        self.n_cutoff = n_cutoff
        self.pi = arb.pi()
        self.L = arb(P1.M).log()
        self.z = arb(1) / (P1.M * P1.M)
        self.exp_minus_L_over_2 = arb(1) / arb(P1.M).sqrt()
        self.I = acb(0, 1)
        self.exp_correction = self._exp_correction()
        self.constant = (
            arb.const_euler() + (4 * self.pi * (P1.M - 1) / (P1.M + 1)).log()
        ) / 2
        self.alpha = {n: self._alpha(n) for n in range(n_cutoff + 1)}
        self.beta = {n: self._beta(n) for n in range(n_cutoff + 1)}
        self.gamma = {n: self._gamma(n) for n in range(n_cutoff + 1)}
        self.log_prime = {p: arb(p).log() for _, p in P1.PRIME_POWERS}
        self.log_k = {k: arb(k).log() for k, _ in P1.PRIME_POWERS}

    def parity_blocks(self) -> tuple[arb_mat, arb_mat, dict[str, dict[str, str]]]:
        n_cutoff = self.n_cutoff
        even = arb_mat(n_cutoff + 1, n_cutoff + 1)
        odd = arb_mat(n_cutoff, n_cutoff)
        sqrt2 = arb(2).sqrt()
        cache: dict[tuple[int, int], arb] = {}

        def k(i: int, j: int) -> arb:
            key = (i, j) if i <= j else (j, i)
            if key not in cache:
                cache[key] = self.tau_entry(*key)
            return cache[key]

        even[0, 0] = k(0, 0)
        for j in range(1, n_cutoff + 1):
            value = sqrt2 * k(0, j)
            even[0, j] = value
            even[j, 0] = value
        for i in range(1, n_cutoff + 1):
            for j in range(i, n_cutoff + 1):
                even_value = k(i, j) + k(i, -j)
                odd_value = k(i, j) - k(i, -j)
                even[i, j] = even_value
                even[j, i] = even_value
                odd[i - 1, j - 1] = odd_value
                odd[j - 1, i - 1] = odd_value
        samples = {
            "K_0_0": P1.bounds(k(0, 0)),
            "K_1_2": P1.bounds(k(1, 2)),
            "K_2_minus_1": P1.bounds(k(2, -1)),
            "K_N_N": P1.bounds(k(n_cutoff, n_cutoff)),
        }
        return even, odd, samples


def fixed_q_even_coords(projected: list[Fraction], n_cutoff: int) -> list[arb]:
    norm_sq = sum((x * x for x in projected), Fraction(0))
    norm = P1.exact_arb(norm_sq).sqrt()
    sqrt2 = arb(2).sqrt()
    coords = [P1.exact_arb(projected[N0]) / norm]
    for n in range(1, n_cutoff + 1):
        value = projected[N0 + n] if n <= N0 else Fraction(0)
        coords.append(sqrt2 * P1.exact_arb(value) / norm)
    return coords


def householder_q_first(q: list[arb]) -> arb_mat:
    dimension = len(q)
    sign = -1 if q[0].upper() < 0 else 1
    vector = q[:]
    vector[0] -= sign
    norm_sq = sum((x * x for x in vector), arb(0))
    if not norm_sq.lower() > 0:
        raise RuntimeError("Householder vector norm is not certified positive")
    h = arb_mat(dimension, dimension)
    for i in range(dimension):
        for j in range(dimension):
            h[i, j] = (1 if i == j else 0) - 2 * vector[i] * vector[j] / norm_sq
    return h


def submatrix(matrix: arb_mat, row0: int, col0: int, rows: int, cols: int) -> arb_mat:
    out = arb_mat(rows, cols)
    for i in range(rows):
        for j in range(cols):
            out[i, j] = matrix[row0 + i, col0 + j]
    return out


def rigorous_floor(matrix: arb_mat) -> tuple[arb, dict[str, Any]]:
    started = time.time()
    eigenvalues = matrix.eig(algorithm=EIGEN_ALGORITHM)
    if len(eigenvalues) != matrix.nrows():
        raise RuntimeError("Arb did not isolate the complete spectrum")
    ordered = sorted(eigenvalues, key=lambda z: float(z.real.mid()))
    first = ordered[0]
    if 0 not in first.imag:
        raise RuntimeError(f"Hermitian eigenvalue enclosure missed the real axis: {first}")
    floor = first.real
    if not floor.lower() > 0:
        raise RuntimeError(f"spectral floor is not certified positive: {first}")
    return floor, {
        "floor": P1.bounds(floor),
        "imaginary_radius": str(first.imag),
        "eigenvalue_count": len(ordered),
        "elapsed_seconds": time.time() - started,
        "algorithm": EIGEN_ALGORITHM,
    }


def choose_beta_star(compression_floor: arb, odd_floor: arb) -> tuple[arb, str]:
    if compression_floor.upper() < odd_floor.lower():
        return compression_floor, "EVEN_Q_PERP_COMPRESSION"
    if odd_floor.upper() < compression_floor.lower():
        return odd_floor, "ODD_SECTOR"
    lower = min(compression_floor.lower(), odd_floor.lower())
    upper = min(compression_floor.upper(), odd_floor.upper())
    return arb(f"{lower} +/- {upper - lower}"), "SECTOR_INTERVAL_OVERLAP"


def full_penalty_check(
    k_even: arb_mat,
    k_odd: arb_mat,
    q: list[arb],
    beta: arb,
    tau: arb,
) -> dict[str, Any]:
    even = arb_mat(k_even)
    odd = arb_mat(k_odd)
    for i in range(even.nrows()):
        for j in range(i, even.ncols()):
            value = even[i, j] + tau * q[i] * q[j]
            if i == j:
                value -= beta
            even[i, j] = value
            even[j, i] = value
    for i in range(odd.nrows()):
        odd[i, i] -= beta
    return {
        "even": P1.interval_ldlt(even),
        "odd": P1.interval_ldlt(odd),
    }


def run_cell(projected: list[Fraction], n_cutoff: int, dps: int) -> dict[str, Any]:
    ctx.dps = dps
    ctx.threads = 1
    started = time.time()
    builder = CCMArbBuilderN(n_cutoff)
    k_even, k_odd, samples = builder.parity_blocks()
    q = fixed_q_even_coords(projected, n_cutoff)
    q_norm_sq = sum((x * x for x in q), arb(0))

    h = householder_q_first(q)
    transformed = h.transpose() * k_even * h
    a = transformed[0, 0]
    compression = submatrix(transformed, 1, 1, n_cutoff, n_cutoff)
    coupling = submatrix(transformed, 1, 0, n_cutoff, 1)

    compression_floor, compression_meta = rigorous_floor(compression)
    odd_floor, odd_meta = rigorous_floor(k_odd)
    beta_star, controlling_sector = choose_beta_star(compression_floor, odd_floor)
    if not beta_star.lower() > 0 or not beta_star.upper() < INITIAL_BETA_UPPER:
        raise RuntimeError(f"beta-star escaped the precommitted bracket: {beta_star}")
    tolerance = max(ABSOLUTE_TOL, beta_star.upper() / RELATIVE_TOL_DENOMINATOR)
    width = beta_star.upper() - beta_star.lower()
    if not width < tolerance:
        raise RuntimeError(f"beta-star enclosure wider than precommit tolerance: {width} >= {tolerance}")

    beta_cert = beta_star.lower() * (1 - arb(1) / RELATIVE_TOL_DENOMINATOR)
    if not beta_cert.upper() < beta_star.lower():
        raise RuntimeError("safe beta endpoint did not separate from beta-star")
    c_beta = arb_mat(compression)
    for i in range(n_cutoff):
        c_beta[i, i] -= beta_cert
    solved = c_beta.solve(coupling, algorithm="precond")
    schur_term = (coupling.transpose() * solved)[0, 0]
    tau_required = beta_cert - a + schur_term
    tau_cert = arb(1)
    if not tau_required.upper() < tau_cert:
        raise RuntimeError(f"precommitted tau=1 is not certified above tau_required: {tau_required}")

    full = full_penalty_check(k_even, k_odd, q, beta_cert, tau_cert)
    interval_pass = bool(
        beta_cert > a.upper()
        and full["even"]["pass"]
        and full["odd"]["pass"]
    )
    return {
        "N": n_cutoff,
        "dimension": 2 * n_cutoff + 1,
        "dps": dps,
        "elapsed_seconds": time.time() - started,
        "q_embedding": "exact_zero_padding_from_E_120",
        "q_norm_sq": P1.bounds(q_norm_sq),
        "a": P1.bounds(a),
        "compression_floor": compression_meta,
        "odd_floor": odd_meta,
        "beta_N_star": P1.bounds(beta_star),
        "controlling_sector": controlling_sector,
        "beta_N_star_minus_a": P1.bounds(beta_star - a),
        "beta_search_tolerance": str(tolerance),
        "beta_enclosure_width": str(width),
        "safe_beta": P1.bounds(beta_cert),
        "tau_required": P1.bounds(tau_required),
        "tau_certificate": "1",
        "full_interval_ldlt": full,
        "interval_certificate_pass": interval_pass,
        "matrix_entry_samples": samples,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    ctx.dps = 80
    projected, q_meta = P1.q_source_exact_even()

    rows = []
    for n_cutoff in N_LADDER:
        precision_rows = []
        for dps in PRECISIONS:
            print(f"[phase2] N={n_cutoff} dps={dps} start", file=sys.stderr, flush=True)
            row = run_cell(projected, n_cutoff, dps)
            precision_rows.append(row)
            print(
                f"[phase2] N={n_cutoff} dps={dps} "
                f"sector={row['controlling_sector']} pass={row['interval_certificate_pass']} "
                f"elapsed={row['elapsed_seconds']:.2f}s",
                file=sys.stderr,
                flush=True,
            )
        cross_precision_consistency = {
            field: P1.intervals_overlap(precision_rows[0][field], precision_rows[1][field])
            for field in ("a", "beta_N_star", "beta_N_star_minus_a", "tau_required")
        }
        cross_precision_consistency["matrix_entry_samples"] = all(
            P1.intervals_overlap(
                precision_rows[0]["matrix_entry_samples"][key],
                precision_rows[1]["matrix_entry_samples"][key],
            )
            for key in precision_rows[0]["matrix_entry_samples"]
        )
        rows.append({
            "N": n_cutoff,
            "precision_doubling": precision_rows,
            "retained_precision_dps": PRECISIONS[-1],
            "retained": precision_rows[-1],
            "cross_precision_consistency": cross_precision_consistency,
        })

    passed = all(
        row["retained"]["interval_certificate_pass"]
        and all(row["cross_precision_consistency"].values())
        for row in rows
    )
    result = {
        "schema": "CCMFixedQBetaNProfile.v1",
        "verdict": "CCM_FIXED_Q_BETA_N_INTERVAL_PROFILE_PASS" if passed else "CCM_FIXED_Q_BETA_N_PROFILE_INCONCLUSIVE",
        "route": "CHALLENGER_NOT_RH",
        "promotion": "FORBIDDEN",
        "precommit": {
            "lambda": "sqrt(13)",
            "m": 13,
            "N0": N0,
            "N_ladder": list(N_LADDER),
            "embedding": "zero-padding only",
            "precision_dps": list(PRECISIONS),
            "beta_initial_bracket": ["0", "1e-48"],
            "beta_search_tolerance": "max(1e-100, 2^-40 * current_upper_bracket)",
        },
        "implementation": {
            "phase1_script": str(PHASE1_SCRIPT.relative_to(REPO)),
            "phase1_script_sha256": EXPECTED_PHASE1_SHA256,
            "python_flint_version": __import__("flint").__version__,
            "production_eigen_algorithm": EIGEN_ALGORITHM,
            "independent_validation_eigen_algorithm": "rump",
            "independent_validation_status": "ALL_8_N_PRECISION_CELLS_PASS",
        },
        "q": q_meta,
        "fixed_q_profile": rows,
        "moving_q_diagnostic": {
            "status": "NOT_RUN",
            "label": "MOVING_PROBE_DIAGNOSTIC_NOT_TRANSFER_EVIDENCE",
            "used_in_fixed_q_table": False,
        },
        "interval_profile_pass": passed,
        "semantic_boundary": "finite_fixed_q_profile_only; no_continuum_transfer; not_SlotH2a; not_RH",
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        output = args.output if args.output.is_absolute() else REPO / args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0 if passed else 2


if __name__ == "__main__":
    raise SystemExit(main())
