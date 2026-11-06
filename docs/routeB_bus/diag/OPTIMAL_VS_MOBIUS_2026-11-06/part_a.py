# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5", "matplotlib==3.10.8"]
# ///
"""Part A: compare pinned full-Gram NB coefficients with the Mobius taper.

Run from anywhere with:
    uv run --no-project docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/part_a.py

The archived coefficient CSV stores x=G^{-1}b. The preregistered residual is
1 + sum c_n r_n, so the full-Gram minimizer used here is c_opt=-x.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import os
import platform
import subprocess
import tempfile
import time
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE_COMMIT = "ba5654b46adf84159702748b006699bafa0ed89b"
SOURCE_DIR = "docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06"
SOURCE_PINS = {
    "coefficients": (f"{SOURCE_DIR}/part_a_coefficients.csv",
                     "7baa38bc0f5a9437e985f739aecb823ec2dedf1a"),
    "results": (f"{SOURCE_DIR}/part_a_results.csv",
                "419143642b1a0f9c499bcfb663d3232d9cb4624e"),
}
TARGETS = [500, 1000, 2000, 5000]
PAIR_POINTS = 4096
THREAD_CAP = 16


def progress(i: int, n: int, started: float, label: str) -> None:
    frac = i / n
    elapsed = time.monotonic() - started
    eta = elapsed * (1 - frac) / max(frac, 1e-30)
    filled = int(30 * frac)
    print(f"[{'#' * filled}{'.' * (30 - filled)}] {100 * frac:5.1f}% "
          f"ETA {eta:.1f}s {label}", flush=True)


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def pinned_source(name: str) -> tuple[str, str, str]:
    path, expected_blob = SOURCE_PINS[name]
    actual_blob = git("rev-parse", f"{SOURCE_COMMIT}:{path}").decode().strip()
    if actual_blob != expected_blob:
        raise RuntimeError(f"source blob mismatch for {path}: {actual_blob}")
    content = git("show", f"{SOURCE_COMMIT}:{path}").decode("utf-8")
    digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
    return content, actual_blob, digest


def load_inputs() -> tuple[dict[int, dict[int, float]], dict[int, dict[str, float]], dict]:
    coeff_text, coeff_blob, coeff_sha = pinned_source("coefficients")
    results_text, results_blob, results_sha = pinned_source("results")
    archived: dict[int, dict[int, float]] = {}
    for row in csv.DictReader(io.StringIO(coeff_text)):
        N, n = int(row["N"]), int(row["n"])
        if N in TARGETS:
            archived.setdefault(N, {})[n] = float(row["c"])
    reference: dict[int, dict[str, float]] = {}
    for row in csv.DictReader(io.StringIO(results_text)):
        N = int(row["N"])
        if N in TARGETS:
            reference[N] = {
                "e_N": float(row["e_N"]),
                "E_V_centered": float(row["E_V_centered"]),
            }
    for N in TARGETS:
        if sorted(archived.get(N, {})) != list(range(2, N + 1)):
            raise RuntimeError(f"incomplete archived coefficient vector at N={N}")
        if N not in reference:
            raise RuntimeError(f"missing pinned full-Gram reference row at N={N}")
    source_info = {
        "commit": SOURCE_COMMIT,
        "coefficients_path": SOURCE_PINS["coefficients"][0],
        "coefficients_blob": coeff_blob,
        "coefficients_sha256": coeff_sha,
        "results_path": SOURCE_PINS["results"][0],
        "results_blob": results_blob,
        "results_sha256": results_sha,
        "archived_c_sign": "archived c is x=G^-1 b; use c_opt=-x under residual 1+sum c_n r_n",
    }
    return archived, reference, source_info


def compile_native(tmp: Path) -> Path:
    compiler = os.environ.get("CXX", "clang++")
    exe = tmp / "gram_native"
    source = HERE / "gram_native.cpp"
    cmd = [compiler, "-O3", "-std=c++17", "-pthread", str(source), "-o", str(exe)]
    print("COMPILE: " + " ".join(cmd), flush=True)
    subprocess.run(cmd, check=True)
    return exe


def native_matrix(exe: Path, N: int, path: Path) -> tuple[np.ndarray, np.ndarray, dict]:
    started = time.monotonic()
    result = subprocess.run([str(exe), str(N), str(path)], check=True, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    with path.open("rb") as f:
        raw_d = np.fromfile(f, dtype=np.uint32, count=1)
        if len(raw_d) != 1 or int(raw_d[0]) != N - 1:
            raise RuntimeError("native Gram header mismatch")
        d = int(raw_d[0])
        G = np.fromfile(f, dtype=np.float64, count=d * d).reshape(d, d)
        q1 = np.fromfile(f, dtype=np.float64, count=N + 1)
        if len(q1) != N + 1 or f.read(1):
            raise RuntimeError("native Gram output length mismatch")
    meta = {"N": N, "seconds": time.monotonic() - started,
            "bytes": path.stat().st_size}
    return G, q1, meta


def arithmetic(N: int) -> dict[str, np.ndarray]:
    mu = np.ones(N + 1, dtype=np.int8)
    mu[0] = 0
    is_prime = np.ones(N + 1, dtype=bool)
    is_prime[:2] = False
    omega = np.zeros(N + 1, dtype=np.int16)
    von_mangoldt = np.zeros(N + 1, dtype=np.float64)
    for p in range(2, N + 1):
        if not is_prime[p]:
            continue
        is_prime[p * p::p] = False
        for k in range(p, N + 1, p):
            mu[k] *= -1
            omega[k] += 1
        for k in range(p * p, N + 1, p * p):
            mu[k] = 0
        power = p
        while power <= N:
            von_mangoldt[power] = math.log(p)
            if power > N // p:
                break
            power *= p
    return {"mu": mu, "is_prime": is_prime, "omega": omega,
            "Lambda": von_mangoldt}


def write_csv(path: Path, rows: list[dict]) -> None:
    if not rows:
        raise ValueError(f"refusing to write empty CSV: {path}")
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def compute_part_a(G: np.ndarray, archived: dict[int, dict[int, float]],
                   reference: dict[int, dict[str, float]], arith: dict[str, np.ndarray]):
    coefficient_rows: list[dict] = []
    feature_rows: list[dict] = []
    energy_rows: list[dict] = []
    judge_rows: list[dict] = []
    regress_rows: list[dict] = []
    arrays: dict[int, dict[str, np.ndarray]] = {}
    started = time.monotonic()

    for index, N in enumerate(TARGETS, 1):
        n_int = np.arange(2, N + 1, dtype=np.int64)
        n = n_int.astype(np.float64)
        G_N = G[:N - 1, :N - 1]
        b = np.log(n) / n
        x_archived = np.array([archived[N][int(k)] for k in n_int], dtype=np.float64)
        c_opt = -x_archived
        mu = arith["mu"][n_int].astype(np.float64)
        a = mu * (1.0 - np.log(n) / math.log(N))
        delta = c_opt - a

        e_opt = float(1.0 + 2.0 * (b @ c_opt) + c_opt @ G_N @ c_opt)
        e_wrong_sign = float(1.0 + 2.0 * (b @ x_archived) + x_archived @ G_N @ x_archived)
        E_a = float(1.0 + 2.0 * (b @ a) + a @ G_N @ a)
        normal = G_N @ c_opt + b
        norm_inf = float(np.linalg.norm(normal, ord=np.inf))
        norm_2 = float(np.linalg.norm(normal))
        j1_diff = abs(e_opt - reference[N]["e_N"])
        j2_diff = abs(E_a - reference[N]["E_V_centered"])
        if j1_diff >= 1e-10 or j2_diff >= 1e-10:
            raise AssertionError(f"J1/J2 mismatch at N={N}: {j1_diff=} {j2_diff=}")
        if e_wrong_sign <= e_opt or norm_inf > 1e-8:
            raise AssertionError(f"sign/normal-equation sanity failed at N={N}")

        c_norm_sq = float(c_opt @ c_opt)
        delta_norm_sq = float(delta @ delta)
        cosine = float((c_opt @ a) / math.sqrt(c_norm_sq * float(a @ a)))
        mu_int = arith["mu"][n_int]
        omega = arith["omega"][n_int]
        is_prime = arith["is_prime"][n_int]
        is_squarefree = mu_int != 0
        is_nonsquarefree = ~is_squarefree
        proper_prime_power = (~is_prime) & (omega == 1)
        other = (~is_prime) & (~proper_prime_power)
        sqrt_cut = n_int <= math.isqrt(N)
        n_half = n_int > N / 2.0

        def energy(mask: np.ndarray) -> float:
            return float(np.sum(delta[mask] ** 2, dtype=np.float64))

        split = {
            "n_le_sqrtN": energy(sqrt_cut),
            "n_gt_sqrtN": energy(~sqrt_cut),
            "n_gt_N_over_2": energy(n_half),
            "squarefree": energy(is_squarefree),
            "non_squarefree_mu_zero": energy(is_nonsquarefree),
            "primes": energy(is_prime),
            "proper_prime_powers": energy(proper_prime_power),
            "other": energy(other),
        }
        row = {"N": N, "free_coefficients": len(n_int),
               "cosine_copt_a": cosine, "delta_norm_sq": delta_norm_sq,
               "copt_norm_sq": c_norm_sq,
               "delta_sq_over_copt_sq": delta_norm_sq / c_norm_sq,
               "nonsquarefree_copt_sq_fraction": float(np.sum(c_opt[is_nonsquarefree] ** 2) / c_norm_sq)}
        for key, value in split.items():
            row[f"delta_sq_{key}"] = value
            row[f"delta_sq_fraction_{key}"] = value / delta_norm_sq
        energy_rows.append(row)

        mu_log = mu * np.log(n) / math.log(N)
        lam_scaled = arith["Lambda"][n_int] / math.log(N)
        inv_n = 1.0 / n
        small = (n_int <= math.sqrt(N)).astype(np.float64)
        omega_f = omega.astype(np.float64)
        X_features = np.column_stack([mu, mu_log, lam_scaled, inv_n, small, omega_f])
        X = np.column_stack([np.ones_like(n), X_features])
        beta, _, rank, singular = np.linalg.lstsq(X, delta, rcond=None)
        fitted = X @ beta
        residual = delta - fitted
        sse = float(residual @ residual)
        sst = float(np.sum((delta - np.mean(delta)) ** 2))
        r2 = 1.0 - sse / sst
        cond = float(singular[0] / singular[-1]) if len(singular) and singular[-1] else math.inf
        feature_names = ["mu", "mu_log_n_over_logN", "Lambda_over_logN",
                         "inverse_n", "indicator_n_le_sqrtN", "omega"]
        regrow = {"N": N, "samples": len(n_int), "rank": int(rank), "R2": r2,
                  "SSE": sse, "residual_RMS": math.sqrt(sse / len(n_int)),
                  "design_condition_2": cond, "intercept": float(beta[0])}
        regrow.update({f"beta_{name}": float(value)
                       for name, value in zip(feature_names, beta[1:])})
        regress_rows.append(regrow)

        for i, ni in enumerate(n_int):
            coefficient_rows.append({"N": N, "n": int(ni), "c_opt": float(c_opt[i]),
                                     "a_mobius_taper": float(a[i]), "delta": float(delta[i])})
            feature_rows.append({"N": N, "n": int(ni), "mu": int(mu_int[i]),
                                 "mu_log_n_over_logN": float(mu_log[i]),
                                 "Lambda_over_logN": float(lam_scaled[i]),
                                 "inverse_n": float(inv_n[i]),
                                 "indicator_n_le_sqrtN": int(small[i]),
                                 "omega": int(omega[i]),
                                 "is_squarefree": int(is_squarefree[i]),
                                 "is_prime": int(is_prime[i]),
                                 "is_proper_prime_power": int(proper_prime_power[i]),
                                 "arithmetic_class": ("prime" if is_prime[i] else
                                     "proper_prime_power" if proper_prime_power[i] else "other")})

        judge_rows.append({
            "N": N,
            "source_e_N": reference[N]["e_N"],
            "recomputed_E_copt": e_opt,
            "J1_abs_difference": j1_diff,
            "J1_pass_lt_1e-10": int(j1_diff < 1e-10),
            "source_E_V_centered": reference[N]["E_V_centered"],
            "recomputed_E_a": E_a,
            "J2_abs_difference": j2_diff,
            "J2_pass_lt_1e-10": int(j2_diff < 1e-10),
            "wrong_sign_error_archived_positive": e_wrong_sign,
            "normal_residual_inf_Gc_plus_b": norm_inf,
            "normal_residual_l2_Gc_plus_b": norm_2,
        })
        arrays[N] = {"n": n, "n_int": n_int, "c_opt": c_opt, "a": a,
                     "delta": delta, "cosine": np.array([cosine]),
                     "energy": np.array([delta_norm_sq])}
        progress(index, len(TARGETS), started, f"coefficient analysis N={N}")

    return coefficient_rows, feature_rows, energy_rows, judge_rows, regress_rows, arrays


def pair_profiles(arrays: dict[int, dict[str, np.ndarray]]):
    profile_rows: list[dict] = []
    summary_rows: list[dict] = []
    started = time.monotonic()
    pairs = [(TARGETS[i], TARGETS[j]) for i in range(len(TARGETS))
             for j in range(i + 1, len(TARGETS))]
    for index, (N1, N2) in enumerate(pairs, 1):
        lo = max(2.0 / N1, 2.0 / N2)
        u = np.linspace(lo, 1.0, PAIR_POINTS)
        u1 = arrays[N1]["n_int"] / float(N1)
        u2 = arrays[N2]["n_int"] / float(N2)
        d1 = np.interp(u, u1, arrays[N1]["delta"])
        d2 = np.interp(u, u2, arrays[N2]["delta"])
        corr = float(np.corrcoef(d1, d2)[0, 1])
        summary_rows.append({"N1": N1, "N2": N2, "points": PAIR_POINTS,
                             "u_min": lo, "u_max": 1.0,
                             "pearson_delta_profile": corr,
                             "preregistered_stable_ge_0.7": int(corr >= 0.7)})
        for k in range(PAIR_POINTS):
            profile_rows.append({"N1": N1, "N2": N2, "point": k,
                                 "u_n_over_N": float(u[k]),
                                 "delta_N1_interpolated": float(d1[k]),
                                 "delta_N2_interpolated": float(d2[k])})
        progress(index, len(pairs), started, f"profile pair N={N1},{N2}")
    return profile_rows, summary_rows


def make_plots(arrays: dict[int, dict[str, np.ndarray]]) -> None:
    for N in TARGETS:
        data = arrays[N]
        u = data["n_int"] / float(N)
        fig, axes = plt.subplots(2, 1, figsize=(10, 7), sharex=True,
                                 gridspec_kw={"height_ratios": [1, 1.2]})
        axes[0].plot(u, data["c_opt"], lw=0.75, label=r"$c^{opt}$")
        axes[0].plot(u, data["a"], lw=0.75, label=r"$a_n=\mu(n)\log(N/n)/\log N$")
        axes[0].set_ylabel("coefficient")
        axes[0].set_title(f"Full-Gram optimal vs Mobius taper, N={N}")
        axes[0].grid(True, alpha=0.25)
        axes[0].legend(loc="best")
        axes[1].plot(u, data["delta"], lw=0.75, color="#6b4c9a")
        axes[1].axhline(0, color="black", lw=0.6)
        axes[1].set_xlabel("u = n/N")
        axes[1].set_ylabel(r"$\delta_n=c_n^{opt}-a_n$")
        axes[1].grid(True, alpha=0.25)
        fig.tight_layout()
        fig.savefig(HERE / f"part_a_coeff_profile_N{N}.png", dpi=170)
        plt.close(fig)


def plots_only() -> None:
    arrays: dict[int, dict[str, np.ndarray]] = {}
    with (HERE / "part_a_coefficients.csv").open(newline="", encoding="utf-8") as f:
        grouped: dict[int, list[dict]] = {}
        for row in csv.DictReader(f):
            grouped.setdefault(int(row["N"]), []).append(row)
    for N in TARGETS:
        rows = sorted(grouped.get(N, []), key=lambda row: int(row["n"]))
        if [int(row["n"]) for row in rows] != list(range(2, N + 1)):
            raise RuntimeError(f"cannot regenerate plot: incomplete coefficients at N={N}")
        arrays[N] = {
            "n_int": np.array([int(row["n"]) for row in rows], dtype=np.int64),
            "c_opt": np.array([float(row["c_opt"]) for row in rows], dtype=np.float64),
            "a": np.array([float(row["a_mobius_taper"]) for row in rows], dtype=np.float64),
            "delta": np.array([float(row["delta"]) for row in rows], dtype=np.float64),
        }
    make_plots(arrays)
    print("[##############################] 100.0% ETA 0s plots regenerated from coefficient CSV",
          flush=True)


def run() -> None:
    started = time.monotonic()
    archived, reference, source_info = load_inputs()
    arithmetic_data = arithmetic(max(TARGETS))
    cxx = os.environ.get("CXX", "clang++")
    with tempfile.TemporaryDirectory(prefix="optimal_vs_mobius_a_") as td:
        tmp = Path(td)
        exe = compile_native(tmp)
        matrix_path = tmp / "full_gram_N5000.bin"
        G, _, gram_meta = native_matrix(exe, max(TARGETS), matrix_path)
        (coeffs, features, energies, judges, regressions, arrays) = compute_part_a(
            G, archived, reference, arithmetic_data)
        profiles, profile_correlations = pair_profiles(arrays)

    write_csv(HERE / "part_a_coefficients.csv", coeffs)
    write_csv(HERE / "part_a_features.csv", features)
    write_csv(HERE / "part_a_energy_splits.csv", energies)
    write_csv(HERE / "part_a_judges.csv", judges)
    write_csv(HERE / "part_a_regression.csv", regressions)
    write_csv(HERE / "part_a_allpairprofiles.csv", profiles)
    write_csv(HERE / "part_a_profile_correlations.csv", profile_correlations)
    make_plots(arrays)

    byN = {int(row["N"]): row for row in energies}
    by_pair = {(int(row["N1"]), int(row["N2"])): row for row in profile_correlations}
    q = {
        "Q1": {"p": 0.55, "observed": float(arrays[5000]["cosine"][0]),
               "hit": bool(arrays[5000]["cosine"][0] >= 0.8)},
        "Q2": {"p": 0.60, "observed": float(by_pair[(2000, 5000)]["pearson_delta_profile"]),
               "hit": bool(by_pair[(2000, 5000)]["pearson_delta_profile"] >= 0.7)},
        "Q3": {"p": 0.50,
               "observed": float(byN[5000]["delta_sq_fraction_n_gt_sqrtN"]),
               "hit": bool(byN[5000]["delta_sq_fraction_n_gt_sqrtN"] > 0.5)},
        "Q4": {"p": 0.50,
               "observed": float(byN[5000]["nonsquarefree_copt_sq_fraction"]),
               "hit": bool(byN[5000]["nonsquarefree_copt_sq_fraction"] >= 0.1)},
    }
    partial_brier = float(np.mean([(float(v["p"]) - int(bool(v["hit"]))) ** 2
                                   for v in q.values()]))
    summary = {
        "part": "A coefficient space and J1/J2 only",
        "preregistration": "PREREGISTRATION.json was committed at 42eeaebd0 before this run",
        "source": source_info,
        "N": TARGETS,
        "convention": "free n=2..N; c_opt=-archived c; a=mu(n)*log(N/n)/logN; residual 1+sum c_n*r_n",
        "full_gram": gram_meta,
        "full_gram_platform": platform.platform(),
        "compiler": cxx,
        "j1_all_pass": all(int(row["J1_pass_lt_1e-10"]) for row in judges),
        "j2_all_pass": all(int(row["J2_pass_lt_1e-10"]) for row in judges),
        "max_j1_abs_difference": max(float(row["J1_abs_difference"]) for row in judges),
        "max_j2_abs_difference": max(float(row["J2_abs_difference"]) for row in judges),
        "max_normal_residual_inf": max(float(row["normal_residual_inf_Gc_plus_b"]) for row in judges),
        "r8_certificate_role": "R8 certificate_witness_N*.json are upper-envelope optimizer candidates; they are not substituted for these NB full-Gram optima",
        "Q1_Q4": q,
        "partial_brier_Q1_Q4_only": partial_brier,
        "elapsed_seconds_including_plots": time.monotonic() - started,
        "limitations": [
            "Full-Gram calculations use platform long double for Vasyunin moments and float64 stored Gram/linear algebra; they are diagnostics, not outward-rounded interval certificates.",
            "Part B zero-localization work, J3 continuous-integral/tail comparison, and J4 permutation nulls are outside this Part A run.",
        ],
    }
    (HERE / "part_a_results.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--plots-only", action="store_true",
                        help="regenerate coefficient/profile plots from part_a_coefficients.csv")
    args = parser.parse_args()
    plots_only() if args.plots_only else run()
