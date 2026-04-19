#!/usr/bin/env python3
"""Numerical witness scan for the PO3 raw manuscript prefix gap shell.

This script evaluates the Lean-side quantity

    po3_suzuki_manuscript_gap_weight a γ

on actual positive zeta-zero ordinates γ = Im(zetazero(n)).
It is intended as a reproducible local probe for the already formalized
`prefix2` / `prefix3` kill criteria in `HBridge_PO3_Shell.lean`.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

import mpmath as mp


@dataclass
class AValueRecord:
    a: float
    weights: list[float]
    sum2: float
    sum3: float


@dataclass
class GridMinimum:
    a: float
    value: float
    abs_value: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--n-zeros",
        type=int,
        default=3,
        help="How many positive zeta-zero ordinates to sample.",
    )
    parser.add_argument(
        "--a-values",
        type=str,
        default="1,1.25,1.5",
        help="Comma-separated list of a-values for direct witness evaluation.",
    )
    parser.add_argument("--grid-min", type=float, default=0.8)
    parser.add_argument("--grid-max", type=float, default=2.0)
    parser.add_argument("--grid-step", type=float, default=0.01)
    parser.add_argument("--dps", type=int, default=80, help="mpmath precision.")
    parser.add_argument(
        "--out-json",
        type=Path,
        default=None,
        help="Optional JSON output path.",
    )
    return parser.parse_args()


def zeta_ordinates(count: int, dps: int) -> list[mp.mpf]:
    mp.mp.dps = dps
    return [mp.im(mp.zetazero(n)) for n in range(1, count + 1)]


def manuscript_prefactor(a: mp.mpf) -> mp.mpf:
    return 2 * mp.pi**2 / (a**3)


def manuscript_alpha_step(a: mp.mpf) -> mp.mpf:
    return mp.pi / a


def manuscript_amp(a: mp.mpf, gamma: mp.mpf) -> mp.mpf:
    return mp.sin(a * gamma) ** 2


def gap_term(c: mp.mpf, gamma: mp.mpf) -> mp.mpf:
    return (
        1 / (((gamma - 2 * c) * (gamma - 3 * c)) * (gamma * (gamma - c)))
        - 1 / (((gamma - c) * (gamma - 2 * c)) * ((gamma - c) * (gamma - 2 * c)))
    )


def gap_weight(a: mp.mpf, gamma: mp.mpf) -> mp.mpf:
    return manuscript_prefactor(a) * manuscript_amp(a, gamma) * gap_term(manuscript_alpha_step(a), gamma)


def near_local_pole(a: mp.mpf, gamma: mp.mpf, eps: mp.mpf) -> bool:
    c = manuscript_alpha_step(a)
    return any(abs(gamma - k * c) < eps for k in (0, 1, 2, 3))


def safe_a(a: mp.mpf, gammas: list[mp.mpf], eps: mp.mpf) -> bool:
    return all(not near_local_pole(a, gamma, eps) for gamma in gammas)


def direct_records(a_values: list[mp.mpf], gammas: list[mp.mpf]) -> list[AValueRecord]:
    records: list[AValueRecord] = []
    for a in a_values:
        weights = [gap_weight(a, gamma) for gamma in gammas]
        sum2 = weights[0] + weights[1] if len(weights) >= 2 else weights[0]
        sum3 = sum2 + weights[2] if len(weights) >= 3 else sum2
        records.append(
            AValueRecord(
                a=float(a),
                weights=[float(w) for w in weights],
                sum2=float(sum2),
                sum3=float(sum3),
            )
        )
    return records


def grid_scan(
    gammas: list[mp.mpf], amin: mp.mpf, amax: mp.mpf, step: mp.mpf
) -> tuple[GridMinimum | None, GridMinimum | None, int]:
    min2: GridMinimum | None = None
    min3: GridMinimum | None = None
    eps = mp.mpf("1e-10")
    samples = 0
    a = amin
    while a <= amax + step / 2:
        if safe_a(a, gammas, eps):
            weights = [gap_weight(a, gamma) for gamma in gammas]
            sum2 = weights[0] + weights[1] if len(weights) >= 2 else weights[0]
            sum3 = sum2 + weights[2] if len(weights) >= 3 else sum2
            abs2 = abs(sum2)
            abs3 = abs(sum3)
            if min2 is None or abs2 < min2.abs_value:
                min2 = GridMinimum(a=float(a), value=float(sum2), abs_value=float(abs2))
            if min3 is None or abs3 < min3.abs_value:
                min3 = GridMinimum(a=float(a), value=float(sum3), abs_value=float(abs3))
            samples += 1
        a += step
    return min2, min3, samples


def format_records(records: list[AValueRecord], gammas: list[mp.mpf]) -> str:
    lines = ["direct witnesses:"]
    for record in records:
        lines.append(f"  a={record.a}")
        for idx, (gamma, weight) in enumerate(zip(gammas, record.weights), start=1):
            lines.append(
                f"    gamma_{idx}={mp.nstr(gamma, 30)} "
                f"weight={mp.nstr(weight, 20)}"
            )
        lines.append(f"    sum2={mp.nstr(record.sum2, 20)}")
        lines.append(f"    sum3={mp.nstr(record.sum3, 20)}")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    a_values = [mp.mpf(part.strip()) for part in args.a_values.split(",") if part.strip()]
    gammas = zeta_ordinates(args.n_zeros, args.dps)
    records = direct_records(a_values, gammas)
    min2, min3, samples = grid_scan(
        gammas,
        mp.mpf(str(args.grid_min)),
        mp.mpf(str(args.grid_max)),
        mp.mpf(str(args.grid_step)),
    )

    print("positive zeta-zero ordinates:")
    for idx, gamma in enumerate(gammas, start=1):
        print(f"  gamma_{idx} = {mp.nstr(gamma, 30)}")
    print()
    print(format_records(records, gammas))
    print()
    print(
        f"grid scan on [{args.grid_min}, {args.grid_max}] "
        f"step={args.grid_step} samples={samples}"
    )
    if min2 is not None:
        print(f"  min |sum2| = {mp.nstr(min2.abs_value, 20)} at a={min2.a}")
        print(f"  value(sum2) = {mp.nstr(min2.value, 20)}")
    if min3 is not None:
        print(f"  min |sum3| = {mp.nstr(min3.abs_value, 20)} at a={min3.a}")
        print(f"  value(sum3) = {mp.nstr(min3.value, 20)}")

    if args.out_json is not None:
        payload = {
            "n_zeros": args.n_zeros,
            "gammas": [str(gamma) for gamma in gammas],
            "direct_records": [asdict(record) for record in records],
            "grid_min_sum2": asdict(min2) if min2 is not None else None,
            "grid_min_sum3": asdict(min3) if min3 is not None else None,
            "grid_samples": samples,
            "grid_range": {
                "min": args.grid_min,
                "max": args.grid_max,
                "step": args.grid_step,
            },
        }
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"\njson written to {args.out_json}")


if __name__ == "__main__":
    main()
