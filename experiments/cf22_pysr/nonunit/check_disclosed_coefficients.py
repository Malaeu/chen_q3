#!/usr/bin/env python3
"""Reproduce the disclosed physical mask coefficients for U=48,64.

This computes only F(1), F(p), F(pbar), F(p*pbar), and their Möbius
differences on the physical u-family. It does not evaluate the raw mean or
the full C panel.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
HELPER_PATH = ROOT / "experiments/cf22_pysr/evaluate.py"
OWNER_PATH = ROOT / "experiments/cf22_pysr/nonunit/OWNER_REQUEST.txt"
PLAN_PATH = ROOT / "experiments/cf22_pysr/nonunit/plan.json"
Q07_PATH = ROOT / "docs/literature/openai_math_2026-10-07/PROSHKA_VERDICT_FULL_CUSP_PAIR_Q07.md"
OUTPUT_PATH = Path(__file__).resolve().with_name("disclosed_coefficients.json")


def load_helpers():
    spec = importlib.util.spec_from_file_location("cf22_evaluate_helpers", HELPER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load evaluator helpers: {HELPER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def outward_interval(helper: Any, value: Any) -> dict[str, str]:
    lo, hi, endpoints = helper.ball_endpoints(value, digits=55)
    return {
        "lower": endpoints["lower"],
        "upper": endpoints["upper"],
        "lower_rational": f"{lo.numerator}/{lo.denominator}",
        "upper_rational": f"{hi.numerator}/{hi.denominator}",
        "midpoint_display_only": helper.ball_midpoint_decimal(value, digits=55),
    }


def support_payload(n_rows: list[Any], u_rows: list[Any], masks: list[dict[str, Any]]) -> str:
    payload = {
        "n": [
            [row.q, [(*prime, exponent) for prime, exponent in row.factors]]
            for row in n_rows
        ],
        "u": [
            [row.z[0], row.z[1], row.q, [(*prime, exponent) for prime, exponent in row.factors]]
            for row in u_rows
        ],
        "masks": masks,
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def compute_for_u(helper: Any, U: int, orientation: int, precision: int) -> dict[str, Any]:
    from flint import arb

    helper.ctx.prec = precision
    helper.BOUNDARY_PRECISIONS.clear()
    ell = Fraction(113, 100)
    L = helper.rational_exponent(U, ell)
    one_over_L = 1 / L

    # The two split prime ideals over 7 are kept distinct even though their
    # norms agree. The source enumerator returns their primary generators.
    split7 = helper.split_generators(7)
    if len(split7) != 2:
        raise ArithmeticError("the two prime ideals above 7 were not both enumerated")
    p, pbar = split7
    mask_rows = [
        {"id": "1", "norm": 1, "factors": []},
        {"id": "p", "norm": 7, "factors": [[*p, 1]]},
        {"id": "pbar", "norm": 7, "factors": [[*pbar, 1]]},
        {"id": "p_pbar", "norm": 49, "factors": [[*p, 1], [*pbar, 1]]},
    ]
    masks = [
        (mask_rows[0], ()),
        (mask_rows[1], ((p, 1),)),
        (mask_rows[2], ((pbar, 1),)),
        (mask_rows[3], ((p, 1), (pbar, 1))),
    ]

    u_limit = (3 * U) // 2
    u_rows: list[Any] = []
    rho_by_z: dict[tuple[int, int], Any] = {}
    for row in helper.elements_up_to(u_limit):
        if not helper.sixthfree(row.factors):
            continue
        rho = helper.rho_weight(row.q, U, precision)
        if rho > 0:
            u_rows.append(row)
            rho_by_z[row.z] = rho
    if not u_rows:
        raise ArithmeticError(f"empty physical support at U={U}")
    S_rho = sum((rho_by_z[row.z] for row in u_rows), arb(0))
    if not S_rho > 0:
        raise ArithmeticError(f"nonpositive physical mass at U={U}")

    n_limit = helper.certified_ceil(helper.arb_fraction(Fraction(3, 2)) * L)
    n_all = helper.ideals_up_to(n_limit)
    n_rows: list[Any] = []
    W_by_f: list[Any] = []
    mu_by_n: list[int] = []
    for row in n_all:
        if not helper.good_ideal(row.factors):
            continue
        if helper.compare_integer_scaled_power(
            row.q, U, ell, Fraction(1, 2), precision
        ) <= 0:
            continue
        if helper.compare_integer_scaled_power(
            row.q, U, ell, Fraction(3, 2), precision
        ) >= 0:
            continue
        n_rows.append(row)
        W_by_f.append(helper.W_weight(row.q, U, ell, precision))
        mu_by_n.append(helper.mu(row.factors))
    if not n_rows:
        raise ArithmeticError(f"empty source column support at U={U}")

    active = [i for i, value in enumerate(mu_by_n) if value != 0]
    if not active:
        raise ArithmeticError(f"all source coefficients vanish at U={U}")

    # Cache the zero-extended phase at every physical element. A missing phase
    # is the source's zero mask and is never inverted for orientation -1.
    phase_table = [
        [helper.phase_index(n_rows[i].factors, u.z, orientation) for u in u_rows]
        for i in active
    ]

    # Confirm the character zero mask agrees with ideal coprimality on every
    # active source column and physical element.
    zero_symbol_pairs = 0
    for active_pos, source_index in enumerate(active):
        nf = n_rows[source_index].factors
        for u_index, u in enumerate(u_rows):
            is_unit_phase = phase_table[active_pos][u_index] is not None
            coprime = helper.is_coprime(nf, u.factors)
            if is_unit_phase != coprime:
                raise ArithmeticError(("character/coprimality mask mismatch", U, nf, u.z))
            zero_symbol_pairs += not is_unit_phase

    root = helper.ROOT
    values: dict[str, Any] = {}
    diagonal_terms_by_mask: dict[str, int] = {}
    d_mask_exclusions: dict[str, int] = {}
    for mask_info, d_factors in masks:
        label = mask_info["id"]
        total = arb(0)
        diagonal_terms = 0
        d_exclusions = 0
        for u_index, u in enumerate(u_rows):
            coeffs = [arb(0) for _ in range(6)]
            diagonal = arb(0)
            for active_pos, source_index in enumerate(active):
                nf = n_rows[source_index].factors
                if not helper.is_coprime(nf, d_factors):
                    d_exclusions += 1
                    continue
                mu_n = mu_by_n[source_index]
                phase = phase_table[active_pos][u_index]
                if phase is not None:
                    coeffs[phase] += mu_n * W_by_f[source_index]
                if helper.is_coprime(nf, u.factors):
                    diagonal += (W_by_f[source_index] ** 2) * (mu_n * mu_n) * one_over_L
                    diagonal_terms += 1

            real = sum((coeffs[k] * root[k][0] for k in range(6)), arb(0))
            imag = sum((coeffs[k] * root[k][1] for k in range(6)), arb(0))
            masked_energy = (real * real + real * imag + imag * imag) * one_over_L
            total += rho_by_z[u.z] * (masked_energy - diagonal)

        values[label] = total / S_rho
        diagonal_terms_by_mask[label] = diagonal_terms
        d_mask_exclusions[label] = d_exclusions

    F1 = values["1"]
    Fp = values["p"]
    Fpbar = values["pbar"]
    Fppbar = values["p_pbar"]
    h_p = Fp - F1
    h_pbar = Fpbar - F1
    h_ppbar = Fppbar - Fp - Fpbar + F1

    support_hash = hashlib.sha256(
        support_payload(n_rows, u_rows, [row for row, _ in masks]).encode("utf-8")
    ).hexdigest()
    return {
        "U": U,
        "r": "113/100",
        "ell": "113/100",
        "L": outward_interval(helper, L),
        "orientation": orientation,
        "precision_bits": precision,
        "counts": {
            "physical_elements": len(u_rows),
            "physical_ideal_classes": len({row.factors for row in u_rows}),
            "source_good_ideals_in_W_support": len(n_rows),
            "nonzero_mobius_source_ideals": len(active),
            "zero_symbol_column_element_pairs": zero_symbol_pairs,
            "diagonal_terms_by_mask": diagonal_terms_by_mask,
            "d_mask_exclusions_by_mask": d_mask_exclusions,
        },
        "boundary_precision_checks": {
            "count": len(helper.BOUNDARY_PRECISIONS),
            "maximum_bits": max(helper.BOUNDARY_PRECISIONS, default=precision),
        },
        "S_rho": outward_interval(helper, S_rho),
        "physical_support_sha256": support_hash,
        "F": {key: outward_interval(helper, value) for key, value in values.items()},
        "h": {
            "p_norm7": outward_interval(helper, h_p),
            "pbar_norm7": outward_interval(helper, h_pbar),
            "p_pbar_norm49": outward_interval(helper, h_ppbar),
        },
        "masks": mask_rows,
        "_raw_values": {
            "F": values,
            "h": {"p_norm7": h_p, "pbar_norm7": h_pbar, "p_pbar_norm49": h_ppbar},
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT_PATH)
    args = parser.parse_args()

    helper = load_helpers()
    from flint import ctx

    precision = 192
    ctx.prec = precision
    result_rows = []
    for U in (48, 64):
        plus = compute_for_u(helper, U, 1, precision)
        minus = compute_for_u(helper, U, -1, precision)
        overlap_checks = {
            family: {
                key: plus["_raw_values"][family][key].overlaps(minus["_raw_values"][family][key])
                for key in plus["_raw_values"][family]
            }
            for family in ("F", "h")
        }
        if not all(value for family in overlap_checks.values() for value in family.values()):
            raise ArithmeticError(("orientation conjugacy intervals do not overlap", U, overlap_checks))
        plus.pop("_raw_values")
        minus.pop("_raw_values")
        result_rows.append({
            "U": U,
            "orientation_1": plus,
            "orientation_minus_1": minus,
            "orientation_conjugacy_interval_overlaps": overlap_checks,
        })

    source_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    source_paths = {
        "owner_request": OWNER_PATH,
        "nonunit_plan": PLAN_PATH,
        "evaluator_helpers": HELPER_PATH,
        "q07_source": Q07_PATH,
        "reproduction_script": Path(__file__).resolve(),
    }
    payload = {
        "schema": "cf22-disclosed-physical-coefficients-v1",
        "epistemic_scope": "DISCLOSED_REPRODUCTION_NOT_HOLDOUT",
        "computed_scope": "PHYSICAL_F_AND_MOBIUS_MASK_DIFFERENCES_ONLY",
        "raw_mean_or_full_C_evaluated": False,
        "parameters": {
            "U": [48, 64],
            "r": "113/100",
            "ell": "113/100",
            "L": "U^(113/100)",
            "rho": "exp(1-1/(1-(2*y-2)^2)) on 1/2<y<3/2, zero elsewhere",
            "W": "same as rho",
            "S": "prime ideals above 6 excluded from source columns; nu=1 on good ideals, zero extension",
            "physical_rows": "all sixth-power-free Eisenstein elements, all six unit associates retained",
            "character_zero_extension": "zero if a source prime ideal divides u; never invert zero for orientation -1",
            "precision_bits": precision,
        },
        "prime_ideals_above_7": {
            "p_generator": list(helper.split_generators(7)[0]),
            "pbar_generator": list(helper.split_generators(7)[1]),
            "distinct_same_norm_ideals_preserved": True,
        },
        "rows": result_rows,
        "disclosed_rounded_values_from_owner_request": {
            "U48": {"h_p_and_h_pbar": "0.0028982091", "h_p_pbar_norm49": "0.0014152236"},
            "U64": {"h_p_and_h_pbar": "-0.0074139186", "h_p_pbar_norm49": "-0.0026918993"},
            "status": "rounded disclosure only; not an interval certificate or blind evidence",
        },
        "provenance": {
            "source_commit": source_commit,
            "source_sha256": {name: sha256(path) for name, path in source_paths.items()},
        },
        "limitations": [
            "Physical averages only; no G_H, raw ball, lambda, diagonal full-C return, or new-P panel was evaluated.",
            "Finite specialization only; no cofinal CF22 estimate or theorem closure is claimed.",
        ],
    }

    output_path = args.output.resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("x", encoding="utf-8") as output_file:
        output_file.write(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"wrote {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
