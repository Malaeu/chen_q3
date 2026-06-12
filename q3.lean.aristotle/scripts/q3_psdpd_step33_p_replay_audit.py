#!/usr/bin/env python3
"""Audit whether Step33 P-entry replay can use termwise radius sums.

This script does not prove Lean theorems.  It reuses the Step20 Arb evaluator
for the finite prime profile and checks whether a term-level midpoint/radius
decomposition can fit inside the already imported Step22 P-radius matrix.

The current Lean receiver sums term radii:

  sum_n termRad i j n <= PRadius i j

If the generated Arb term boxes already exceed PRadius before formalization,
then the next proof source should be a direct profile-level hbox or a regenerated
radius payload, not the existing termwise receiver with the current radii.

The `--live-only` mode mirrors the Step33 delta/live receiver: it filters out
prime shifts whose two normalized R arguments are outside the support window.
That mode audits the intended next generated payload contract.
"""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path
from typing import Any

from flint import arb

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    decimal_grid_centers,
    prime_power_shifts_ball,
    r_corr_ball,
    set_precision,
    spline_packet_ball,
)
ROOT = Path(__file__).resolve().parents[1]
SUPPORT_LEFT = Decimal("-2")
SUPPORT_RIGHT = Decimal("2")


@dataclass(frozen=True)
class Block:
    name: str
    k_spline: int
    midpoint_csv: Path
    radius_csv: Path


BLOCKS = {
    "primary": Block(
        name="primary",
        k_spline=11,
        midpoint_csv=ROOT / "docs/insights/q3_psdpd_step22_midpoints_k11.csv",
        radius_csv=ROOT / "docs/insights/q3_psdpd_step22_radii_k11.csv",
    ),
    "control": Block(
        name="control",
        k_spline=9,
        midpoint_csv=ROOT / "docs/insights/q3_psdpd_step22_midpoints_k9.csv",
        radius_csv=ROOT / "docs/insights/q3_psdpd_step22_radii_k9.csv",
    ),
}


def arb_mid_decimal(x: arb) -> Decimal:
    return (arb_lower_decimal(x) + arb_upper_decimal(x)) / Decimal(2)


def arb_mid_rad_decimal(x: arb, digits: int) -> tuple[Decimal, Decimal]:
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)
    mid = (lo + hi) / Decimal(2)
    serialized_mid = Decimal(f"{mid:.{digits}E}")
    rad = max(abs(serialized_mid - lo), abs(hi - serialized_mid))
    rad = rad * Decimal("1.0000000001") + Decimal("1e-80")
    return serialized_mid, rad


def load_p_payload(path: Path, column: str) -> dict[tuple[int, int], Decimal]:
    out: dict[tuple[int, int], Decimal] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["matrix"].strip() != "P":
                continue
            out[(int(row["i"]), int(row["j"]))] = Decimal(row[column])
    return out


def is_live_shift(delta: Decimal, shift: Decimal, ell: Decimal) -> bool:
    minus = (delta - shift) / ell
    plus = (delta + shift) / ell
    minus_dead = minus <= SUPPORT_LEFT or SUPPORT_RIGHT <= minus
    plus_dead = plus <= SUPPORT_LEFT or SUPPORT_RIGHT <= plus
    return not (minus_dead and plus_dead)


def support_status(x: Decimal) -> dict[str, str]:
    if x <= SUPPORT_LEFT:
        return {
            "x": str(x),
            "state": "left_dead",
            "outside_margin": str(SUPPORT_LEFT - x),
            "inside_margin": "0",
        }
    if SUPPORT_RIGHT <= x:
        return {
            "x": str(x),
            "state": "right_dead",
            "outside_margin": str(x - SUPPORT_RIGHT),
            "inside_margin": "0",
        }
    return {
        "x": str(x),
        "state": "live",
        "outside_margin": "0",
        "inside_margin": str(min(x - SUPPORT_LEFT, SUPPORT_RIGHT - x)),
    }


def shift_support_status(
    delta: Decimal, shift: Decimal, ell: Decimal
) -> dict[str, Any]:
    minus = (delta - shift) / ell
    plus = (delta + shift) / ell
    minus_status = support_status(minus)
    plus_status = support_status(plus)
    live = not (
        minus_status["state"] != "live" and plus_status["state"] != "live"
    )
    margins = [
        Decimal(minus_status["outside_margin"])
        if minus_status["state"] != "live"
        else Decimal(minus_status["inside_margin"]),
        Decimal(plus_status["outside_margin"])
        if plus_status["state"] != "live"
        else Decimal(plus_status["inside_margin"]),
    ]
    return {
        "minus": minus_status,
        "plus": plus_status,
        "live": live,
        "nearest_support_margin": str(min(margins)),
    }


def audit_block(
    block: Block,
    *,
    arb_prec: int,
    live_only: bool,
    top_failures: int,
    term_digits: int,
    witness_digits: int,
    include_entries: bool,
    include_terms: bool,
    include_dead_terms: bool,
) -> dict[str, Any]:
    set_precision(arb_prec)

    centers_dec = decimal_grid_centers("3.0", "0.30", "0.25")
    centers_ball = [arb(str(u)) for u in centers_dec]
    centers_dec = [Decimal(str(u)) for u in centers_dec]
    ell_ball = arb("0.30")
    ell_dec = Decimal("0.30")
    shifts = prime_power_shifts_ball("3.0")
    shifts_dec = [arb_mid_decimal(a) for a, _weight, _p, _r_pow in shifts]
    s_k, c_k = spline_packet_ball(block.k_spline)

    p_mid = load_p_payload(block.midpoint_csv, "mid")
    p_rad = load_p_payload(block.radius_csv, "rad")

    n_centers = len(centers_dec)
    n_shifts = len(shifts)

    weight_mid_rad = [
        arb_mid_rad_decimal(weight, witness_digits)
        for _a, weight, _p, _r_pow in shifts
    ]

    raw_mids: dict[tuple[int, int], list[Decimal]] = {}
    raw_rads: dict[tuple[int, int], list[Decimal]] = {}
    raw_rpair_mids: dict[tuple[int, int], list[Decimal]] = {}
    raw_rpair_rads: dict[tuple[int, int], list[Decimal]] = {}
    raw_rminus_mids: dict[tuple[int, int], list[Decimal]] = {}
    raw_rminus_rads: dict[tuple[int, int], list[Decimal]] = {}
    raw_rplus_mids: dict[tuple[int, int], list[Decimal]] = {}
    raw_rplus_rads: dict[tuple[int, int], list[Decimal]] = {}

    for i in range(n_centers):
        for j in range(n_centers):
            d = centers_ball[i] - centers_ball[j]
            d_dec = centers_dec[i] - centers_dec[j]
            mids: list[Decimal] = []
            rads: list[Decimal] = []
            rpair_mids: list[Decimal] = []
            rpair_rads: list[Decimal] = []
            rminus_mids: list[Decimal] = []
            rminus_rads: list[Decimal] = []
            rplus_mids: list[Decimal] = []
            rplus_rads: list[Decimal] = []

            for n, (a, weight, _p, _r_pow) in enumerate(shifts):
                rminus = r_corr_ball(
                    (d - a) / ell_ball, block.k_spline, s_k, c_k
                )
                rplus = r_corr_ball(
                    (d + a) / ell_ball, block.k_spline, s_k, c_k
                )
                rpair = rminus + rplus
                rpair_mid, rpair_rad = arb_mid_rad_decimal(
                    rpair, witness_digits
                )
                status = shift_support_status(d_dec, shifts_dec[n], ell_dec)
                if status["minus"]["state"] == "live":
                    rminus_mid, rminus_rad = arb_mid_rad_decimal(
                        rminus, witness_digits
                    )
                else:
                    rminus_mid, rminus_rad = Decimal(0), Decimal(0)
                if status["plus"]["state"] == "live":
                    rplus_mid, rplus_rad = arb_mid_rad_decimal(
                        rplus, witness_digits
                    )
                else:
                    rplus_mid, rplus_rad = Decimal(0), Decimal(0)
                value = weight * rpair
                mid, rad = arb_mid_rad_decimal(value, term_digits)
                mids.append(mid)
                rads.append(rad)
                rpair_mids.append(rpair_mid)
                rpair_rads.append(rpair_rad)
                rminus_mids.append(rminus_mid)
                rminus_rads.append(rminus_rad)
                rplus_mids.append(rplus_mid)
                rplus_rads.append(rplus_rad)

            raw_mids[(i, j)] = mids
            raw_rads[(i, j)] = rads
            raw_rpair_mids[(i, j)] = rpair_mids
            raw_rpair_rads[(i, j)] = rpair_rads
            raw_rminus_mids[(i, j)] = rminus_mids
            raw_rminus_rads[(i, j)] = rminus_rads
            raw_rplus_mids[(i, j)] = rplus_mids
            raw_rplus_rads[(i, j)] = rplus_rads

    failures = 0
    max_ratio = Decimal(0)
    worst: dict[str, Any] | None = None
    live_counts: list[int] = []
    detailed_failures: list[tuple[Decimal, dict[str, Any]]] = []
    entry_payloads: list[dict[str, Any]] = []
    max_live_center_error = Decimal(0)
    max_all98_center_error = Decimal(0)
    max_full_vs_live_center_error = Decimal(0)

    def sym_term(i: int, j: int, n: int) -> tuple[Decimal, Decimal]:
        mij = raw_mids[(i, j)][n]
        mji = raw_mids[(j, i)][n]
        rij = raw_rads[(i, j)][n]
        rji = raw_rads[(j, i)][n]

        mid = (mij + mji) / Decimal(2)
        rad = max(rij + abs(mij - mid), rji + abs(mji - mid))
        return mid, rad

    def sym_rpair(i: int, j: int, n: int) -> tuple[Decimal, Decimal]:
        mij = raw_rpair_mids[(i, j)][n]
        mji = raw_rpair_mids[(j, i)][n]
        rij = raw_rpair_rads[(i, j)][n]
        rji = raw_rpair_rads[(j, i)][n]

        mid = (mij + mji) / Decimal(2)
        rad = max(rij + abs(mij - mid), rji + abs(mji - mid))
        return mid, rad

    def lean_split_rpair(
        i: int, j: int, n: int
    ) -> tuple[Decimal, Decimal, Decimal, Decimal]:
        # The JSON entry displays delta as center_i - center_j, while Lean's
        # receiver uses center_j - center_i.  Read split witnesses from the
        # reversed raw entry so that rminus/rplus match the Lean target.
        return (
            raw_rminus_mids[(j, i)][n],
            raw_rminus_rads[(j, i)][n],
            raw_rplus_mids[(j, i)][n],
            raw_rplus_rads[(j, i)][n],
        )

    def entry_details(i: int, j: int) -> dict[str, Any]:
        delta = centers_dec[i] - centers_dec[j]
        target_mid = p_mid[(i, j)]
        target_rad = p_rad[(i, j)]
        live_terms: list[dict[str, Any]] = []
        dead_terms: list[dict[str, Any]] = []
        all_terms: list[dict[str, Any]] = []

        for n in range(n_shifts):
            mid, rad = sym_term(i, j, n)
            rpair_mid, rpair_rad = sym_rpair(i, j, n)
            rminus_mid, rminus_rad, rplus_mid, rplus_rad = lean_split_rpair(
                i, j, n
            )
            weight_mid, weight_rad = weight_mid_rad[n]
            status = shift_support_status(delta, shifts_dec[n], ell_dec)
            term = {
                "n": n,
                "shift": str(shifts_dec[n]),
                "mid": str(mid),
                "rad": str(rad),
                "weight_mid": str(weight_mid),
                "weight_rad": str(weight_rad),
                "rpair_mid": str(rpair_mid),
                "rpair_rad": str(rpair_rad),
                "rminus_mid": str(rminus_mid),
                "rminus_rad": str(rminus_rad),
                "rplus_mid": str(rplus_mid),
                "rplus_rad": str(rplus_rad),
                "support": status,
                "_mid": mid,
                "_rad": rad,
                "_boundary_margin": Decimal(status["nearest_support_margin"]),
            }
            all_terms.append(term)
            if status["live"]:
                live_terms.append(term)
            else:
                dead_terms.append(term)

        live_mid = sum(term["_mid"] for term in live_terms)
        live_rad = sum(term["_rad"] for term in live_terms)
        all98_mid = sum(term["_mid"] for term in all_terms)
        all98_rad = sum(term["_rad"] for term in all_terms)

        live_center_error = abs(live_mid - target_mid)
        all98_center_error = abs(all98_mid - target_mid)
        full_vs_live_center_error = abs(all98_mid - live_mid)
        live_radius_requirement = live_rad + live_center_error
        all98_radius_requirement = all98_rad + all98_center_error
        live_radius_excess = live_radius_requirement - target_rad
        all98_radius_excess = all98_radius_requirement - target_rad

        worst_live_terms = sorted(
            live_terms, key=lambda term: term["_rad"], reverse=True
        )[:8]
        nearest_dead_terms = sorted(
            dead_terms, key=lambda term: term["_boundary_margin"]
        )[:8]

        def public_term(
            term: dict[str, Any], *, include_support: bool = True
        ) -> dict[str, Any]:
            out = {
                "n": term["n"],
                "shift": term["shift"],
                "mid": term["mid"],
                "rad": term["rad"],
                "weight_mid": term["weight_mid"],
                "weight_rad": term["weight_rad"],
                "rpair_mid": term["rpair_mid"],
                "rpair_rad": term["rpair_rad"],
                "rminus_mid": term["rminus_mid"],
                "rminus_rad": term["rminus_rad"],
                "rplus_mid": term["rplus_mid"],
                "rplus_rad": term["rplus_rad"],
            }
            if include_support:
                out["support"] = term["support"]
            return out

        details = {
            "block": block.name,
            "i": i,
            "j": j,
            "delta": str(delta),
            "center_sub": str(delta),
            "live_shift_count": len(live_terms),
            "dead_shift_count": len(dead_terms),
            "target_mid": str(target_mid),
            "target_rad": str(target_rad),
            "live_mid": str(live_mid),
            "live_rad_termwise_sum": str(live_rad),
            "all98_mid": str(all98_mid),
            "all98_rad_termwise_sum": str(all98_rad),
            "center_error": str(live_center_error),
            "all98_center_error": str(all98_center_error),
            "radius_excess": str(live_radius_excess),
            "all98_radius_excess": str(all98_radius_excess),
            "live_radius_requirement": str(live_radius_requirement),
            "all98_radius_requirement": str(all98_radius_requirement),
            "full_vs_live_center_error": str(full_vs_live_center_error),
            "mode_radius_excess": str(
                live_radius_excess if live_only else all98_radius_excess
            ),
            "mode_radius_requirement": str(
                live_radius_requirement
                if live_only
                else all98_radius_requirement
            ),
            "worst_contributing_live_terms": [
                public_term(term) for term in worst_live_terms
            ],
            "nearest_dead_terms_to_support_boundary": [
                public_term(term) for term in nearest_dead_terms
            ],
        }
        if include_terms:
            details["live_terms"] = [
                public_term(term, include_support=False) for term in live_terms
            ]
        if include_dead_terms:
            details["dead_terms"] = [public_term(term) for term in dead_terms]
        return details

    for i in range(n_centers):
        for j in range(n_centers):
            details = entry_details(i, j)
            live_count = int(details["live_shift_count"])
            term_radius_sum = Decimal(str(details["mode_radius_requirement"]))
            imported_radius = Decimal(str(details["target_rad"]))
            ratio = (
                term_radius_sum / imported_radius
                if imported_radius != 0
                else Decimal("Infinity")
            )

            if term_radius_sum > imported_radius:
                failures += 1

            live_counts.append(live_count)
            max_live_center_error = max(
                max_live_center_error, Decimal(str(details["center_error"]))
            )
            max_all98_center_error = max(
                max_all98_center_error, Decimal(str(details["all98_center_error"]))
            )
            max_full_vs_live_center_error = max(
                max_full_vs_live_center_error,
                Decimal(str(details["full_vs_live_center_error"])),
            )
            mode_radius_excess = Decimal(str(details["mode_radius_excess"]))
            if mode_radius_excess > 0:
                detailed_failures.append((mode_radius_excess, details))
            if ratio > max_ratio:
                max_ratio = ratio
                worst = details | {"ratio": str(ratio)}
            if include_entries:
                entry_payloads.append(details | {"ratio": str(ratio)})

    detailed_failures.sort(key=lambda item: item[0], reverse=True)

    result = {
        "block": block.name,
        "k_spline": block.k_spline,
        "arb_prec": arb_prec,
        "term_digits": term_digits,
        "witness_digits": witness_digits,
        "n_centers": n_centers,
        "n_shifts": n_shifts,
        "weight_payloads": [
            {
                "n": n,
                "shift": str(shifts_dec[n]),
                "prime": p,
                "exponent": r_pow,
                "mid": str(weight_mid_rad[n][0]),
                "rad": str(weight_mid_rad[n][1]),
            }
            for n, (_a, _weight, p, r_pow) in enumerate(shifts)
        ],
        "live_only": live_only,
        "min_live_terms": min(live_counts) if live_counts else None,
        "max_live_terms": max(live_counts) if live_counts else None,
        "total_live_terms": sum(live_counts),
        "entries": n_centers * n_centers,
        "failed_entries": failures,
        "max_ratio": str(max_ratio),
        "max_live_center_error": str(max_live_center_error),
        "max_all98_center_error": str(max_all98_center_error),
        "max_full_vs_live_center_error": str(max_full_vs_live_center_error),
        "worst": worst,
        "top_failures": [item[1] for item in detailed_failures[:top_failures]],
        "verdict": "termwise_receiver_fits"
        if failures == 0
        else "termwise_receiver_exceeds_imported_P_radius",
    }
    if include_entries:
        result["entry_payloads"] = entry_payloads
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--block",
        choices=["primary", "control", "both"],
        default="both",
    )
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--live-only", action="store_true")
    parser.add_argument("--top-failures", type=int, default=5)
    parser.add_argument(
        "--term-digits",
        type=int,
        default=36,
        help="decimal digits after the point for term midpoint serialization",
    )
    parser.add_argument(
        "--witness-digits",
        type=int,
        default=96,
        help=(
            "decimal digits after the point for auxiliary weight/R-pair "
            "witness serialization"
        ),
    )
    parser.add_argument(
        "--include-entries",
        action="store_true",
        help="include all entry-level aggregate payloads in JSON output",
    )
    parser.add_argument(
        "--include-terms",
        action="store_true",
        help="include live term midpoint/radius payloads for each entry",
    )
    parser.add_argument(
        "--include-dead-terms",
        action="store_true",
        help="include all dead term payloads for support-filter debugging",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    names = ["primary", "control"] if args.block == "both" else [args.block]
    results = [
        audit_block(
            BLOCKS[name],
            arb_prec=args.arb_prec,
            live_only=args.live_only,
            top_failures=args.top_failures,
            term_digits=args.term_digits,
            witness_digits=args.witness_digits,
            include_entries=args.include_entries,
            include_terms=args.include_terms,
            include_dead_terms=args.include_dead_terms,
        )
        for name in names
    ]

    for result in results:
        print(
            f"{result['block']}: {result['failed_entries']}/{result['entries']} "
            f"entries exceed imported P radius; max_ratio={result['max_ratio']}"
        )
        print(
            f"  live_only={result['live_only']} "
            f"live_terms={result['min_live_terms']}..{result['max_live_terms']} "
            f"total_live_terms={result['total_live_terms']}"
        )
        print(
            "  max_center_errors="
            f"live_target:{result['max_live_center_error']} "
            f"all98_target:{result['max_all98_center_error']} "
            f"all98_live:{result['max_full_vs_live_center_error']}"
        )
        worst = result["worst"]
        if worst:
            print(
                "  worst="
                f"({worst['i']},{worst['j']}) "
                f"delta={worst['delta']} "
                f"live={worst['live_shift_count']} "
                f"dead={worst['dead_shift_count']} "
                f"target_rad={worst['target_rad']} "
                f"mode_radius_excess={worst['mode_radius_excess']} "
                f"ratio={worst['ratio']}"
            )
        for entry in result["top_failures"][:3]:
            print(
                "  top_failure="
                f"({entry['i']},{entry['j']}) "
                f"delta={entry['delta']} "
                f"live={entry['live_shift_count']} "
                f"dead={entry['dead_shift_count']} "
                f"radius_excess={entry['radius_excess']} "
                f"full_vs_live_center_error={entry['full_vs_live_center_error']}"
            )

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(results, indent=2) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
