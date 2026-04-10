#!/usr/bin/env python3
"""Radar scan for local real packets versus the Hermite line.

This is a computational reconnaissance tool for the D2g16d barrier. It does
not use the unknown global residues from the paired counterexample. Instead it
asks a narrower geometry question:

For consecutive local windows cut from the real support
    X_a = {a * gamma_n / pi},
where gamma_n are actual zeta-zero ordinates, what is the optimal unit
coefficient vector for the local one-sided Cauchy sample matrix, and how close
is that vector to the Hermite/barycentric line of the same window?
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import mpmath as mp
import numpy as np


@dataclass
class WindowRecord:
    length: int
    start_index: int
    end_index: int
    sample_base: int
    sigma_min: float
    min_gap: float
    diameter: float
    hermite_overlap: float
    hermite_distance: float
    arithmetic_deviation: float
    points: list[float]
    coeff_opt: list[float]
    coeff_hermite: list[float]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--a", type=float, default=1.0, help="Scaling parameter in x_n = a * gamma_n / pi.")
    parser.add_argument("--n-zeros", type=int, default=200, help="How many zeta zeros to sample.")
    parser.add_argument("--lengths", type=str, default="2,3,4", help="Comma-separated packet lengths.")
    parser.add_argument("--top", type=int, default=6, help="How many best windows to print for each length.")
    parser.add_argument("--dps", type=int, default=50, help="mpmath precision used for zeta zeros.")
    parser.add_argument("--out-json", type=Path, default=None, help="Optional path for a JSON dump.")
    return parser.parse_args()


def zeta_ordinates(n_zeros: int, a: float, dps: int) -> np.ndarray:
    mp.mp.dps = dps
    values = []
    scale = mp.mpf(a) / mp.pi
    for n in range(1, n_zeros + 1):
        zero = mp.zetazero(n)
        gamma = mp.im(zero)
        values.append(float(scale * gamma))
    return np.array(values, dtype=float)


def hermite_line(points: np.ndarray) -> np.ndarray:
    weights = np.empty(len(points), dtype=float)
    for i, x_i in enumerate(points):
        prod = 1.0
        for j, x_j in enumerate(points):
            if i == j:
                continue
            prod *= (x_i - x_j)
        weights[i] = 1.0 / prod
    norm = np.linalg.norm(weights)
    return weights / norm


def arithmetic_deviation(points: np.ndarray) -> float:
    if len(points) <= 2:
        return 0.0
    u = points[0]
    h = (points[-1] - points[0]) / (len(points) - 1)
    model = np.array([u + i * h for i in range(len(points))], dtype=float)
    return float(np.max(np.abs(points - model)))


def local_sample_matrix(points: np.ndarray) -> tuple[np.ndarray, int]:
    sample_base = math.floor(points[-1])
    samples = np.array([sample_base + m for m in range(1, len(points) + 1)], dtype=float)
    matrix = np.empty((len(points), len(points)), dtype=float)
    for m, x_m in enumerate(samples):
        matrix[m, :] = 1.0 / (points - x_m)
    return matrix, sample_base


def aligned_smallest_vector(matrix: np.ndarray, hermite: np.ndarray) -> tuple[float, np.ndarray, float, float]:
    _, singular_values, vh = np.linalg.svd(matrix, full_matrices=True)
    coeff = vh[-1, :].astype(float)
    coeff = coeff / np.linalg.norm(coeff)
    overlap_signed = float(np.dot(coeff, hermite))
    if overlap_signed < 0:
        coeff = -coeff
        overlap_signed = -overlap_signed
    overlap = abs(overlap_signed)
    distance = math.sqrt(max(0.0, 1.0 - overlap * overlap))
    return float(singular_values[-1]), coeff, overlap, distance


def scan_length(points: np.ndarray, length: int) -> list[WindowRecord]:
    records: list[WindowRecord] = []
    for start in range(0, len(points) - length + 1):
        window = points[start : start + length]
        matrix, sample_base = local_sample_matrix(window)
        hermite = hermite_line(window)
        sigma, coeff, overlap, distance = aligned_smallest_vector(matrix, hermite)
        gaps = np.diff(window)
        records.append(
            WindowRecord(
                length=length,
                start_index=start + 1,
                end_index=start + length,
                sample_base=sample_base,
                sigma_min=sigma,
                min_gap=float(np.min(gaps)) if len(gaps) else 0.0,
                diameter=float(window[-1] - window[0]),
                hermite_overlap=overlap,
                hermite_distance=distance,
                arithmetic_deviation=arithmetic_deviation(window),
                points=[float(x) for x in window],
                coeff_opt=[float(x) for x in coeff],
                coeff_hermite=[float(x) for x in hermite],
            )
        )
    records.sort(key=lambda rec: (rec.sigma_min, rec.hermite_distance))
    return records


def summarize(records: list[WindowRecord], top: int) -> str:
    lines = []
    for rec in records[:top]:
        lines.append(
            "  "
            f"indices={rec.start_index}-{rec.end_index} "
            f"M={rec.sample_base} "
            f"sigma={rec.sigma_min:.3e} "
            f"gap={rec.min_gap:.3e} "
            f"diam={rec.diameter:.3e} "
            f"overlap={rec.hermite_overlap:.6f} "
            f"dist={rec.hermite_distance:.3e} "
            f"arith_dev={rec.arithmetic_deviation:.3e}"
        )
        lines.append(f"    coeff_opt={np.array(rec.coeff_opt)}")
        lines.append(f"    coeff_H  ={np.array(rec.coeff_hermite)}")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    lengths = [int(part.strip()) for part in args.lengths.split(",") if part.strip()]
    points = zeta_ordinates(args.n_zeros, args.a, args.dps)
    payload = {
        "a": args.a,
        "n_zeros": args.n_zeros,
        "lengths": lengths,
        "records": {},
    }

    print(f"scan for X_a with a={args.a}, zeros={args.n_zeros}, lengths={lengths}")
    for length in lengths:
        records = scan_length(points, length)
        payload["records"][str(length)] = [asdict(rec) for rec in records[: args.top]]
        print(f"\nL={length}")
        print(summarize(records, args.top))

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"\njson written to {args.out_json}")


if __name__ == "__main__":
    main()
