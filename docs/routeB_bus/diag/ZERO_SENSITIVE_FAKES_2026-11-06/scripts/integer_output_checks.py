#!/usr/bin/env python3
"""Post-production invariants and independent small-prefix replay checks."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream))


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def close(actual: float, expected: float, tol: float = 2e-12) -> bool:
    return math.isfinite(actual) and math.isfinite(expected) and abs(actual - expected) <= tol * max(1.0, abs(expected))


def mu(n: int) -> int:
    if n == 1:
        return 1
    x = n
    sign = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            if x % p == 0:
                return 0
            sign = -sign
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        sign = -sign
    return sign


def chi4(n: int) -> int:
    return 1 if n % 4 == 1 else (-1 if n % 4 == 3 else 0)


def divisors(n: int) -> list[int]:
    out = [1]
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
        d += 1
    if n > 1:
        out.append(n)
    return sorted(out)


def direct_w10(coefficients: list[float]) -> float:
    prefix = 0.0
    values = []
    for value in coefficients:
        prefix += value
        values.append(prefix)
    numerator = math.fsum(values[k - 1] ** 2 / (k * (k + 1)) for k in range(1, 10))
    return numerator / math.log(10.0)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-directory", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.output_directory.resolve()
    checks: dict[str, object] = {}

    # Numeric table sanity across every recorded system/probe/sample.
    for name, expected_rows in (("T0", 701), ("T1", 701), ("T2", 601), ("F1", 601)):
        grid = read_csv(root / f"{name}.csv")
        assert len(grid) == expected_rows
        xs = [float(row["X"]) for row in grid]
        ms = [float(row["M"]) for row in grid]
        ws = [float(row["W"]) for row in grid]
        assert all(math.isfinite(x) and math.isfinite(m) and math.isfinite(w) and w >= 0
                   for x, m, w in zip(xs, ms, ws))
        assert all(xs[i] < xs[i + 1] for i in range(len(xs) - 1))
        probe = read_csv(root / f"{name}_probes.csv")
        assert len(probe) == expected_rows
        for row in probe:
            corr = float(row["unit_shift_sum_over_X"])
            support = float(row["adjacent_support_fraction"])
            count = int(row["adjacent_support_count"])
            pairs = int(row["adjacent_pair_count"])
            assert math.isfinite(corr) and 0.0 <= support <= 1.0
            assert 0 <= count <= pairs
            assert pairs == math.floor(float(row["X"])) - 1
        samples = read_csv(root / f"{name}_samples.csv")
        sample_n = 8000 if name in ("T0", "T1") else 7000
        assert len(samples) == sample_n
        for row in samples:
            assert all(math.isfinite(float(row[key])) for key in ("x", "M", "M_over_sqrt_x", "M_over_x"))
        checks[name] = {
            "status": "PASS",
            "grid_rows": len(grid),
            "probe_rows": len(probe),
            "sample_rows": len(samples),
            "grid_sha256": sha256(root / f"{name}.csv"),
        }

    # Reconstruct the integer P3/P2 outputs at the first grid point without the
    # production segmented stream.
    b0 = [mu(n) for n in range(1, 11)]
    b1 = [mu(n) * chi4(n) for n in range(1, 11)]
    j1 = json.loads((root / "integerjudges" / "J1.json").read_text(encoding="utf-8"))
    tau = j1["tau_values_n_1_to_30"]

    def t2_b(n: int) -> float:
        if n == 1:
            return 1.0
        x = n
        value = 1.0
        p = 2
        while x > 1:
            if x % p:
                p += 1
                continue
            exponent = 0
            while x % p == 0:
                x //= p
                exponent += 1
            if exponent == 1:
                value *= -tau[p - 1] / (p ** 5.5)
            elif exponent >= 3:
                return 0.0
        return value

    b2 = [t2_b(n) for n in range(1, 11)]
    f1_rows = read_csv(root / "integerjudges" / "F1_small_inverse.csv")
    b_f1 = [float(row["b"]) for row in f1_rows[:10]]
    for name, coeffs in (("T0", b0), ("T1", b1), ("T2", b2), ("F1", b_f1)):
        grid = read_csv(root / f"{name}.csv")[0]
        probe = read_csv(root / f"{name}_probes.csv")[0]
        prefix = []
        running = 0.0
        for value in coeffs:
            running += value
            prefix.append(running)
        corr = math.fsum(coeffs[n - 1] * coeffs[n] for n in range(1, 10)) / 10
        nonzero = [value != 0.0 for value in coeffs]
        support = sum(nonzero[n - 1] and nonzero[n] for n in range(1, 10)) / 9
        assert close(float(grid["M"]), prefix[-1])
        assert close(float(grid["W"]), direct_w10(coeffs))
        assert close(float(probe["unit_shift_sum_over_X"]), corr)
        assert close(float(probe["adjacent_support_fraction"]), support)
    checks["direct_X10"] = {"status": "PASS", "systems": ["T0", "T1", "T2", "F1"], "independent_prefix": True}

    # Recompute each P2 residue vector/scalar from its exact integer counts.
    p2 = read_csv(root / "T0_prime_p2.csv")
    grouped: dict[tuple[str, int], list[dict[str, str]]] = {}
    for row in p2:
        grouped.setdefault((row["X"], int(row["modulus"])), []).append(row)
    for (x, modulus), group in grouped.items():
        assert len(group) == modulus
        group.sort(key=lambda row: int(row["residue"]))
        counts = [int(row["count"]) for row in group]
        total = int(group[0]["total_count"])
        assert sum(counts) == total and all(int(row["total_count"]) == total for row in group)
        expected = [total / modulus] * modulus
        scalar = math.sqrt(math.fsum((count - total / modulus) ** 2 for count in counts) / total) if total else 0.0
        for residue, row in enumerate(group):
            assert int(row["residue"]) == residue
            assert close(float(row["expected_uniform"]), expected[residue])
            imbalance = (counts[residue] - total / modulus) / math.sqrt(total) if total else 0.0
            assert close(float(row["normalized_imbalance"]), imbalance)
            assert close(float(row["probe_scalar"]), scalar)
    p2_10 = [row for row in p2 if float(row["X"]) == 10.0]
    primes = [2, 3, 5, 7]
    for modulus in (3, 4, 5, 6):
        group = sorted((row for row in p2_10 if int(row["modulus"]) == modulus), key=lambda row: int(row["residue"]))
        assert [int(row["count"]) for row in group] == [sum(p % modulus == r for p in primes) for r in range(modulus)]
    max_x = max(float(x) for x, _ in grouped)
    for modulus in (3, 4, 5, 6):
        final_group = grouped[(format(max_x, ".0f"), modulus)]
        assert int(final_group[0]["total_count"]) == 5_761_455
    t1_probe = read_csv(root / "T1_probes.csv")
    assert all(float(row["unit_shift_sum_over_X"]) == 0.0 and
               float(row["adjacent_support_fraction"]) == 0.0 for row in t1_probe)
    checks["P2"] = {
        "status": "PASS",
        "X_modulus_vectors_checked": len(grouped),
        "direct_X10": True,
        "prime_count_at_1e8": 5_761_455,
        "T1_even_support_identity": True,
    }

    # P5 exact pair-count identities and a direct ordered-pair check at X=10.
    p5 = read_csv(root / "F1_p5_probes.csv")
    pair_counts = read_csv(root / "F1_p5_residue_pair_counts.csv")
    last = p5[-1]
    matrix_total = sum(int(row["ordered_coprime_pair_count"]) for row in pair_counts)
    assert matrix_total == int(last["defect_pair_count"])
    assert int(last["defect_pair_count"]) <= int(last["total_ordered_coprime_pairs"])
    kappa = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)
    for row in p5:
        denominator = int(row["total_ordered_coprime_pairs"])
        numerator = int(row["defect_pair_count"])
        density = numerator / denominator
        assert close(float(row["relative_defect_pair_density"]), density)
        assert close(float(row["mean_absolute_defect"]), (1 + kappa * kappa) * density)
    a = {0: 0.0, 1: 1.0, 2: kappa, 3: -kappa, 4: -1.0}
    brute_num = 0.0
    brute_den = 0
    for m in range(1, 11):
        for n in range(1, 11):
            if math.gcd(m, n) == 1:
                brute_den += 1
                brute_num += abs(a[(m * n) % 5] - a[m % 5] * a[n % 5])
    first = p5[0]
    assert brute_den == int(first["total_ordered_coprime_pairs"])
    assert close(brute_num / brute_den, float(first["mean_absolute_defect"]))
    checks["P5"] = {
        "status": "PASS",
        "grid_rows_checked": len(p5),
        "max_pair_matrix_sums_to_numerator": True,
        "direct_ordered_pairs_X10": {"numerator": brute_num, "denominator": brute_den},
    }

    judges = json.loads((root / "integerjudges" / "JUDGES.json").read_text(encoding="utf-8"))
    assert judges.get("status") == "PASS"
    checks["preproduction_judges"] = {"status": "PASS", "receipt_sha256": sha256(root / "integerjudges" / "JUDGES.json")}
    receipt = {
        "status": "PASS",
        "classification": "FINITE_OUTPUT_INVARIANTS_NOT_RH",
        "checks": checks,
        "output_directory": str(root),
    }
    target = root / "integerjudges" / "OUTPUT_CHECKS.json"
    target.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"OUTPUT_CHECKS_PASS receipt={target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
