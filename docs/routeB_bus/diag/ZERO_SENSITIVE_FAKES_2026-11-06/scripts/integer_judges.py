#!/usr/bin/env python3
"""Independent pre-production judges for the integer-supported systems."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import sys
import time

from integer_tau import euler_series


OEIS_A000594_URL = "https://oeis.org/A000594/b000594.txt"
OEIS_TAU_1_TO_30 = [
    1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920,
    534612, -370944, -577738, 401856, 1217160, 987136, -6905934, 2727432,
    10661420, -7109760, -4219488, -12830688, 18643272, 21288960,
    -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
]
DH_ZEROS = [
    ("0.808517182456637", "85.699348485377592"),
    ("0.650830080609737", "114.163342730756980"),
]


def write_json(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def divisors(n: int) -> list[int]:
    result = [1]
    d = 2
    while d * d <= n:
        if n % d == 0:
            result.append(d)
            if d * d != n:
                result.append(n // d)
        d += 1
    if n > 1:
        result.append(n)
    return sorted(result)


def mu_trial(n: int) -> int:
    if n == 1:
        return 1
    remaining = n
    sign = 1
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            remaining //= p
            if remaining % p == 0:
                return 0
            sign = -sign
            while remaining % p == 0:
                remaining //= p
        p += 1
    if remaining > 1:
        sign = -sign
    return sign


def chi4(n: int) -> int:
    r = n % 4
    return 1 if r == 1 else (-1 if r == 3 else 0)


def run_j1(out_dir: Path) -> dict:
    from mpmath import mp

    started = time.monotonic()
    mp.dps = 80
    sqrt5 = mp.sqrt(5)
    kappa = (mp.sqrt(10 - 2 * sqrt5) - 2) / (sqrt5 - 1)

    def dh(s):
        return mp.power(5, -s) * (
            mp.zeta(s, mp.mpf(1) / 5)
            + kappa * mp.zeta(s, mp.mpf(2) / 5)
            - kappa * mp.zeta(s, mp.mpf(3) / 5)
            - mp.zeta(s, mp.mpf(4) / 5)
        )

    roots = []
    for re0, im0 in DH_ZEROS:
        guess = mp.mpc(mp.mpf(re0), mp.mpf(im0))
        root = mp.findroot(
            dh,
            (guess, guess + mp.mpc("0.001", "0.001")),
            tol=mp.mpf("1e-65"),
            maxsteps=100,
        )
        residual = abs(dh(root))
        if residual >= mp.mpf("1e-20"):
            raise AssertionError(f"DH zero residual {mp.nstr(residual, 12)} is not below 1e-20")
        roots.append({
            "initial_guess": [re0, im0],
            "refined_zero": [mp.nstr(mp.re(root), 40), mp.nstr(mp.im(root), 40)],
            "residual_abs": mp.nstr(residual, 20),
            "passed_residual_lt_1e-20": True,
        })

    tau = euler_series(30)
    actual_tau = [int(tau[n]) for n in range(1, 31)]
    if actual_tau != OEIS_TAU_1_TO_30:
        raise AssertionError("exact tau(1..30) differs from OEIS A000594 values")
    receipt = {
        "status": "PASS",
        "judge": "J1",
        "classification": "FINITE_SOURCE_AND_SERIES_CHECK",
        "dh_function": "5^(-s)*(zeta(s,1/5)+kappa*zeta(s,2/5)-kappa*zeta(s,3/5)-zeta(s,4/5))",
        "kappa_formula": "(sqrt(10-2*sqrt(5))-2)/(sqrt(5)-1)",
        "mpmath_dps": 80,
        "dh_zeros": roots,
        "tau_values_n_1_to_30": actual_tau,
        "tau_source": OEIS_A000594_URL,
        "tau_match": True,
        "elapsed_seconds": time.monotonic() - started,
    }
    write_json(out_dir / "J1.json", receipt)
    return receipt


def run_j4(out_dir: Path, f1_small_csv: Path) -> dict:
    from mpmath import mp

    started = time.monotonic()
    mp.dps = 80
    # T1: L(s,chi_4) and its exact Mobius-character inverse.
    t1_max_residual = 0
    for n in range(1, 501):
        value = sum(chi4(d) * mu_trial(n // d) * chi4(n // d) for d in divisors(n))
        expected = 1 if n == 1 else 0
        if value != expected:
            raise AssertionError(f"T1 inversion convolution failed at n={n}: {value}")
        t1_max_residual = max(t1_max_residual, abs(value - expected))

    # T2: construct exact tau coefficients through 200 and check the normalized
    # degree-two Euler inverse by high-precision Dirichlet convolution.
    t2_n = 200
    tau = euler_series(t2_n)
    tau_int = [0] + [int(tau[n]) for n in range(1, t2_n + 1)]
    a2 = [mp.mpf(0)] * (t2_n + 1)
    for n in range(1, t2_n + 1):
        a2[n] = mp.mpf(tau_int[n]) / mp.power(n, mp.mpf(11) / 2)
    b2 = [mp.mpf(0)] * (t2_n + 1)
    b2[1] = 1
    for n in range(2, t2_n + 1):
        x = n
        local = mp.mpf(1)
        while x > 1:
            p = 2
            while p * p <= x and x % p != 0:
                p += 1
            if x % p == 0:
                exponent = 0
                while x % p == 0:
                    x //= p
                    exponent += 1
            else:
                p = x
                exponent = 1
                x = 1
            if exponent == 1:
                local *= -a2[p]
            elif exponent >= 3:
                local = mp.mpf(0)
        b2[n] = local
    t2_max_residual = mp.mpf(0)
    for n in range(1, t2_n + 1):
        conv = mp.fsum(a2[d] * b2[n // d] for d in divisors(n))
        residual = abs(conv - (1 if n == 1 else 0))
        t2_max_residual = max(t2_max_residual, residual)
    if t2_max_residual > mp.mpf("1e-65"):
        raise AssertionError(f"T2 normalized inverse convolution residual {mp.nstr(t2_max_residual, 12)}")

    # F1: compare C++ long-double recurrence to an independent mpmath recurrence,
    # then check the high-precision Dirichlet convolution through n=500.
    kappa = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)

    def a1(n: int):
        return {0: mp.mpf(0), 1: mp.mpf(1), 2: kappa, 3: -kappa, 4: mp.mpf(-1)}[n % 5]

    b1 = [mp.mpf(0)] * 501
    b1[1] = mp.mpf(1)
    for n in range(2, 501):
        b1[n] = -mp.fsum(a1(d) * b1[n // d] for d in divisors(n) if d > 1)
    max_scaled_coefficient_error = mp.mpf(0)
    with f1_small_csv.open("r", encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream))
    if len(rows) != 500:
        raise AssertionError(f"F1 small coefficient file has {len(rows)} rows, expected 500")
    for n, row in enumerate(rows, start=1):
        if int(row["n"]) != n:
            raise AssertionError("F1 small coefficients are not a complete ordered prefix")
        actual = mp.mpf(row["b"])
        scaled_error = abs(actual - b1[n]) / max(mp.mpf(1), abs(b1[n]))
        max_scaled_coefficient_error = max(max_scaled_coefficient_error, scaled_error)
    if max_scaled_coefficient_error > mp.mpf("1e-12"):
        raise AssertionError(
            f"F1 C++/mpmath small coefficient mismatch {mp.nstr(max_scaled_coefficient_error, 12)}"
        )
    f1_max_residual = mp.mpf(0)
    for n in range(1, 501):
        conv = mp.fsum(a1(d) * b1[n // d] for d in divisors(n))
        residual = abs(conv - (1 if n == 1 else 0))
        f1_max_residual = max(f1_max_residual, residual)
    if f1_max_residual > mp.mpf("1e-65"):
        raise AssertionError(f"F1 inversion convolution residual {mp.nstr(f1_max_residual, 12)}")

    receipt = {
        "status": "PASS",
        "judge": "J4_integer_inverse_convolutions",
        "classification": "FINITE_INVERSION_AND_SMALL_PRECISION_CHECK",
        "T1": {"n_max": 500, "integer_convolution_max_abs_residual": t1_max_residual},
        "T2": {
            "n_max": t2_n,
            "max_abs_convolution_residual": mp.nstr(t2_max_residual, 20),
            "tau_source": "exact fmpz_series Euler pentagonal product power 24 times q",
            "normalization": "tau(n)/n^(11/2)",
            "inverse_local_factors": "b(p)=-tau(p)/p^(11/2), b(p^2)=1, b(p^e)=0 for e>=3",
        },
        "F1": {
            "n_max": 500,
            "max_abs_convolution_residual": mp.nstr(f1_max_residual, 20),
            "cpp_vs_mpmath_max_scaled_coefficient_error": mp.nstr(max_scaled_coefficient_error, 20),
            "coefficient_precision_threshold": "1e-12 relative to max(1,abs(reference))",
            "cpp_source_sha256": file_sha256(f1_small_csv),
            "zero_support_convention": "production counts b(n) nonzero iff abs(b(n))>64*long_double_epsilon*sum_abs_recurrence_terms; zero term scale yields exact-zero cutoff",
        },
        "elapsed_seconds": time.monotonic() - started,
    }
    write_json(out_dir / "J4.json", receipt)
    return receipt


def read_rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream))


def run_j2_t1(out_dir: Path, trial_csv: Path) -> dict:
    started = time.monotonic()
    rows = read_rows(trial_csv)
    if len(rows) != 50000:
        raise AssertionError(f"T1 trial factor input has {len(rows)} rows, expected 50000")
    checked = 0
    for expected_n, row in enumerate(rows, start=1):
        if int(row["n"]) != expected_n:
            raise AssertionError("T1 trial factor input is not a complete ordered prefix")
        expected = mu_trial(expected_n) * chi4(expected_n)
        if int(row["b"]) != expected:
            raise AssertionError(f"T1 mu*chi4 differs from trial factorization at n={expected_n}")
        checked += 1
    receipt = {
        "status": "PASS",
        "judge": "J2_T1_trial_factor",
        "independent_method": "per-n trial factorization with square-factor detection, then chi_4 residue",
        "n_max": 50000,
        "rows_checked": checked,
        "input_sha256": file_sha256(trial_csv),
        "elapsed_seconds": time.monotonic() - started,
    }
    write_json(out_dir / "J2_T1.json", receipt)
    return receipt


def exact_power_row(path: Path, power: int) -> dict[str, str]:
    target = str(10**power)
    for row in read_rows(path):
        if float(row["X"]) == float(target):
            return row
    raise AssertionError(f"{path} has no exact 10^{power} row")


def run_j2_t0(out_dir: Path, t0_csv: Path, predecessor_s0_csv: Path,
              rerun_s0_csv: Path, rerun_checks_json: Path) -> dict:
    started = time.monotonic()
    if t0_csv.read_bytes() != predecessor_s0_csv.read_bytes():
        raise AssertionError("T0.csv is not a byte-for-byte reuse of predecessor S0.csv")
    checks = json.loads(rerun_checks_json.read_text(encoding="utf-8"))
    observed_powers = checks["J1"]["observed_M_10k"]
    expected_powers = checks["J1"]["expected_M_10k"]
    if checks["J1"]["status"] != "PASS" or observed_powers != expected_powers:
        raise AssertionError("predecessor runner's exact Mobius power checkpoints failed")
    compared = []
    for power in range(1, 9):
        current = exact_power_row(t0_csv, power)
        replay = exact_power_row(rerun_s0_csv, power)
        if current["M"] != replay["M"]:
            raise AssertionError(f"T0 M(10^{power}) differs at printed precision")
        item = {"power": power, "M_printed": current["M"], "M_exact_string_match": True}
        if power == 7:
            if current["W"] != replay["W"]:
                raise AssertionError("T0 W(1e7) differs at printed precision")
            item["W_printed"] = current["W"]
            item["W_exact_string_match"] = True
        compared.append(item)
    receipt = {
        "status": "PASS",
        "judge": "J2_T0_replay",
        "source_csv_reuse": True,
        "old_true_runner_output_sha256": file_sha256(rerun_s0_csv),
        "predecessor_s0_sha256": file_sha256(predecessor_s0_csv),
        "t0_csv_sha256": file_sha256(t0_csv),
        "rerun_power_checkpoints_M_10k": observed_powers,
        "rerun_checks_sha256": file_sha256(rerun_checks_json),
        "checkpoints": compared,
        "elapsed_seconds": time.monotonic() - started,
    }
    write_json(out_dir / "J2_T0.json", receipt)
    return receipt


def finalize(out_dir: Path) -> dict:
    paths = [out_dir / name for name in ("J1.json", "J2_T0.json", "J2_T1.json", "J4.json")]
    missing = [str(p) for p in paths if not p.exists()]
    if missing:
        raise RuntimeError(f"cannot finalize incomplete integer judges: {missing}")
    parts = [json.loads(path.read_text(encoding="utf-8")) for path in paths]
    failed = [part.get("judge") for part in parts if part.get("status") != "PASS"]
    if failed:
        raise RuntimeError(f"integer judge failures: {failed}")
    result = {
        "status": "PASS",
        "classification": "PRE_PRODUCTION_JUDGES_PASS",
        "judges": {part["judge"]: {"status": part["status"], "path": str(path)}
                   for part, path in zip(parts, paths)},
    }
    write_json(out_dir / "J2.json", {
        "status": "PASS",
        "judge": "J2",
        "T0": parts[1],
        "T1": parts[2],
    })
    write_json(out_dir / "JUDGES.json", result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", required=True, choices=("preproduction", "j2-t1", "j2-t0", "finalize"))
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--f1-small-csv", type=Path)
    parser.add_argument("--t1-trial-csv", type=Path)
    parser.add_argument("--t0-csv", type=Path)
    parser.add_argument("--predecessor-s0-csv", type=Path)
    parser.add_argument("--rerun-s0-csv", type=Path)
    parser.add_argument("--rerun-checks-json", type=Path)
    args = parser.parse_args()
    out_dir = args.output_directory.resolve() / "integerjudges"
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.phase == "preproduction":
        if args.f1_small_csv is None:
            parser.error("--f1-small-csv is required for preproduction")
        run_j1(out_dir)
        run_j4(out_dir, args.f1_small_csv.resolve())
    elif args.phase == "j2-t1":
        if args.t1_trial_csv is None:
            parser.error("--t1-trial-csv is required for j2-t1")
        run_j2_t1(out_dir, args.t1_trial_csv.resolve())
    elif args.phase == "j2-t0":
        required = [args.t0_csv, args.predecessor_s0_csv, args.rerun_s0_csv, args.rerun_checks_json]
        if any(value is None for value in required):
            parser.error("--t0-csv, --predecessor-s0-csv, and --rerun-s0-csv are required for j2-t0")
        run_j2_t0(
            out_dir, args.t0_csv.resolve(), args.predecessor_s0_csv.resolve(),
            args.rerun_s0_csv.resolve(), args.rerun_checks_json.resolve(),
        )
    else:
        finalize(out_dir)
    print(f"JUDGE_PHASE_PASS phase={args.phase}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
