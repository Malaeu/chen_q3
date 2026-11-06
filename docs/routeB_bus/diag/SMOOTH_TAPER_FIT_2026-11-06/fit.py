# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5", "scipy==1.17.0", "matplotlib==3.10.8"]
# ///
"""Fit smooth Mobius profiles against prefixes of the pinned full Gram.

Run from any directory with:
    uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/fit.py

The archived optimum is stored in physical sign convention as c_opt=-x, with
residual 1 + sum_{n=2}^N c_n r_n. Raw coefficient n=1 is set to 1 for both
the log and selected profiles, as frozen in the preregistration.
"""
from __future__ import annotations

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
from typing import Iterable, Sequence

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.linalg import svd


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PREREG_COMMIT = "60ea7f7d3"
PREREG_PATH = "docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/PREREGISTRATION.json"
PREREG_BLOB = "712c14b9fe5d68b8e8f124326afc1e7391af2482"
GRAM_SOURCE_COMMIT = "ec1e2e961e07899824890db7f5fe39a89f2aa795"
CORE_SOURCE_COMMIT = "a180142f5b60d1424df53512b666915b7d22117e"
ARCHIVE_DIR = "docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06"
CORE_DIR = "docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06"
SOURCE_PINS = {
    "coefficients": (
        GRAM_SOURCE_COMMIT,
        f"{ARCHIVE_DIR}/part_a_coefficients.csv",
        "8f40a66e373d3626347e9d045a43230c949447b6",
    ),
    "judges": (
        GRAM_SOURCE_COMMIT,
        f"{ARCHIVE_DIR}/part_a_judges.csv",
        "e6463f68208e45eacc622850f84f082d631d5f09",
    ),
    "core_grid": (
        CORE_SOURCE_COMMIT,
        f"{CORE_DIR}/core_full_H.csv",
        "8d62edae64a79dd1eca0c6979b73b03ba7132687",
    ),
}
MAIN_N = (500, 1000, 2000, 5000)
J2_N = (50, 200, 1000)
GRID_COUNT = 92
SPLINE_X0 = (0.05, 0.1, 0.2, 0.35, 0.5)
BEST_TIE_TOL = 1e-12
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


def pinned_text(commit: str, path: str, expected_blob: str) -> tuple[str, str]:
    actual = git("rev-parse", f"{commit}:{path}").decode().strip()
    if actual != expected_blob:
        raise RuntimeError(f"source blob mismatch for {path}: {actual}")
    content = git("show", f"{commit}:{path}").decode("utf-8")
    digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
    return content, digest


def load_sources() -> tuple[dict[int, dict[int, float]], dict[int, dict[str, float]], list[int], dict]:
    prereg_blob = git("rev-parse", f"{PREREG_COMMIT}:{PREREG_PATH}").decode().strip()
    if prereg_blob != PREREG_BLOB:
        raise RuntimeError(f"preregistration blob mismatch: {prereg_blob}")
    prereg = json.loads(git("show", f"{PREREG_COMMIT}:{PREREG_PATH}").decode("utf-8"))
    if prereg.get("state", "").find("Committed before new numerical experiments") < 0:
        raise RuntimeError("preregistration state does not confirm pre-run commitment")

    contents = {}
    digests = {}
    for name, (commit, path, blob) in SOURCE_PINS.items():
        contents[name], digests[name] = pinned_text(commit, path, blob)

    archived: dict[int, dict[int, float]] = {}
    for row in csv.DictReader(io.StringIO(contents["coefficients"])):
        N = int(row["N"])
        if N in MAIN_N:
            archived.setdefault(N, {})[int(row["n"])] = float(row["c_opt"])
    for N in MAIN_N:
        if sorted(archived.get(N, {})) != list(range(2, N + 1)):
            raise RuntimeError(f"incomplete physical optimum at N={N}")

    optimum_reference: dict[int, dict[str, float]] = {}
    for row in csv.DictReader(io.StringIO(contents["judges"])):
        N = int(row["N"])
        if N in MAIN_N:
            optimum_reference[N] = {
                "E_opt": float(row["recomputed_E_copt"]),
                "E_log": float(row["source_E_V_centered"]),
            }
    if set(optimum_reference) != set(MAIN_N):
        raise RuntimeError("missing archived J1/J3 reference rows")

    core_ns = []
    for row in csv.DictReader(io.StringIO(contents["core_grid"])):
        if row["log_grid"].lower() == "true":
            core_ns.append(int(row["N"]))
    if len(core_ns) != GRID_COUNT or len(set(core_ns)) != GRID_COUNT:
        raise RuntimeError(f"expected {GRID_COUNT} unique core grid Ns, found {len(set(core_ns))}")
    geom = sorted(set(int(np.rint(float(v))) for v in np.geomspace(3, 10000, 100)))
    if core_ns != geom:
        raise RuntimeError("pinned core grid differs from preregistered rounded geomspace")

    targets = sorted(set(core_ns) | set(MAIN_N) | set(J2_N))
    source_info = {
        "preregistration": {"commit": PREREG_COMMIT, "path": PREREG_PATH,
                            "blob": prereg_blob},
        "sources": {
            name: {"commit": SOURCE_PINS[name][0], "path": SOURCE_PINS[name][1],
                  "blob": SOURCE_PINS[name][2], "sha256": digests[name]}
            for name in SOURCE_PINS
        },
        "grid_N_count": len(core_ns),
        "requested_N_count_after_union": len(targets),
        "targets": targets,
    }
    return archived, optimum_reference, targets, source_info


def compile_native(tmp: Path) -> Path:
    compiler = os.environ.get("CXX", "clang++")
    exe = tmp / "gram_native"
    source = HERE / "gram_native.cpp"
    cmd = [compiler, "-O3", "-std=c++17", "-pthread", str(source), "-o", str(exe)]
    print("COMPILE: " + " ".join(cmd), flush=True)
    subprocess.run(cmd, check=True)
    return exe


def build_gram(exe: Path, N: int, path: Path) -> tuple[np.memmap, dict]:
    started = time.monotonic()
    result = subprocess.run([str(exe), str(N), str(path)], check=True, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    expected = 4 + (N - 1) * (N - 1) * 8 + (N + 1) * 8
    if path.stat().st_size != expected:
        raise RuntimeError(f"native Gram file size mismatch: {path.stat().st_size} != {expected}")
    with path.open("rb") as f:
        header = int.from_bytes(f.read(4), byteorder="little")
    if header != N - 1:
        raise RuntimeError(f"native Gram header mismatch: {header} != {N - 1}")
    gram = np.memmap(path, mode="r", dtype=np.float64, offset=4, shape=(N - 1, N - 1))
    meta = {"N": N, "seconds": time.monotonic() - started,
            "bytes": path.stat().st_size, "format": "uint32 d, row-major float64 dxd, float64 q1[0..N]"}
    return gram, meta


def arithmetic(N: int) -> dict[str, np.ndarray]:
    mu = np.ones(N + 1, dtype=np.int8)
    mu[0] = 0
    is_prime = np.ones(N + 1, dtype=bool)
    is_prime[:2] = False
    omega = np.zeros(N + 1, dtype=np.int16)
    for p in range(2, N + 1):
        if not is_prime[p]:
            continue
        is_prime[p * p::p] = False
        for k in range(p, N + 1, p):
            mu[k] *= -1
            omega[k] += 1
        for k in range(p * p, N + 1, p * p):
            mu[k] = 0
    return {"mu": mu, "is_prime": is_prime, "omega": omega}


def basis_data(N: int, mu: np.ndarray) -> tuple[np.ndarray, list[str], dict[str, int], np.ndarray, np.ndarray]:
    n_int = np.arange(2, N + 1, dtype=np.int64)
    n = n_int.astype(np.float64)
    logN = math.log(N)
    x = np.log(N / n) / logN
    columns: list[np.ndarray] = []
    labels: list[str] = []
    for j in range(1, 5):
        labels.append("x" if j == 1 else f"x^{j}")
        columns.append(mu[n_int].astype(np.float64) * x**j)
    for x0 in SPLINE_X0:
        hinge = np.maximum(x0 - x, 0.0)
        for order in (2, 3):
            labels.append(f"spline_{x0:.2f}_h{order}")
            columns.append(mu[n_int].astype(np.float64) * (hinge**order - x0**order))
    M = np.column_stack(columns)
    b = np.log(n) / n
    return M, labels, {name: i for i, name in enumerate(labels)}, n_int, b


def specs(indices: dict[str, int]) -> list[dict]:
    out = []
    for d in range(1, 5):
        keys = ["x" if j == 1 else f"x^{j}" for j in range(1, d + 1)]
        for endpoint in ("free", "fixed1"):
            out.append({"family": f"poly_d{d}_{endpoint}", "kind": "polynomial",
                        "degree": d, "endpoint": endpoint, "x0": None,
                        "basis_keys": keys, "basis_indices": [indices[k] for k in keys]})
    for x0 in SPLINE_X0:
        keys = ["x", f"spline_{x0:.2f}_h2", f"spline_{x0:.2f}_h3"]
        out.append({"family": f"spline_x0_{x0:.2f}", "kind": "spline",
                    "degree": 3, "endpoint": "free", "x0": x0,
                    "basis_keys": keys, "basis_indices": [indices[k] for k in keys]})
    return out


def svd_solve(A: np.ndarray, rhs: np.ndarray) -> tuple[np.ndarray, int, float, float, list[float]]:
    if A.size == 0:
        return np.zeros(rhs.shape, dtype=np.float64), 0, math.inf, 0.0, []
    U, singular, Vh = svd(A, full_matrices=False, check_finite=False,
                          lapack_driver="gesdd")
    smax = float(singular[0]) if len(singular) else 0.0
    tol = max(A.shape) * np.finfo(np.float64).eps * smax
    keep = singular > tol
    rank = int(np.count_nonzero(keep))
    if rank:
        solution = Vh[keep, :].T @ ((U[:, keep].T @ rhs) / singular[keep])
        condition = float(singular[0] / singular[keep][-1])
    else:
        solution = np.zeros(A.shape[1], dtype=np.float64)
        condition = math.inf
    return solution, rank, condition, tol, [float(s) for s in singular]


def fit_one(spec: dict, M_all: np.ndarray, gram_hessian: np.ndarray,
            gram_linear: np.ndarray) -> dict:
    idx = spec["basis_indices"]
    H = np.asarray(gram_hessian[np.ix_(idx, idx)], dtype=np.float64)
    H = (H + H.T) * 0.5
    g = np.asarray(gram_linear[idx], dtype=np.float64)
    M = M_all[:, idx]
    basis_scale = np.linalg.norm(M, axis=0)
    basis_scale[basis_scale == 0.0] = 1.0
    M_scaled = M / basis_scale
    basis_s = svd(M_scaled, compute_uv=False, check_finite=False, lapack_driver="gesdd")
    basis_tol = max(M.shape) * np.finfo(np.float64).eps * (basis_s[0] if len(basis_s) else 0.0)
    basis_rank = int(np.count_nonzero(basis_s > basis_tol))
    basis_condition = (float(basis_s[0] / basis_s[basis_rank - 1])
                       if basis_rank and basis_rank == len(idx) else math.inf)

    # Normalize by the Gram norm of each basis vector before SVD. In particular,
    # this keeps the small-x0 spline hinges from appearing numerically rank zero.
    gram_scale = np.sqrt(np.maximum(np.diag(H), 0.0))
    gram_scale[gram_scale == 0.0] = 1.0
    H_scaled = H / np.outer(gram_scale, gram_scale)
    H_scaled = (H_scaled + H_scaled.T) * 0.5
    g_scaled = g / gram_scale
    if spec["endpoint"] == "fixed1":
        # P(1)=1 is solved in the SVD nullspace after basis normalization.
        constraint = np.ones(len(idx), dtype=np.float64) / gram_scale
        z0 = constraint / float(constraint @ constraint)
        _, _, Vh = svd(constraint[None, :], full_matrices=True,
                       check_finite=False, lapack_driver="gesdd")
        null = Vh[1:, :].T
        reduced_H = null.T @ H_scaled @ null
        reduced_g = null.T @ (H_scaled @ z0 + g_scaled)
        y, rank, condition, tolerance, singular_values = svd_solve(reduced_H, -reduced_g)
        z = z0 + null @ y
        theta = z / gram_scale
        effective_dimension = len(idx) - 1
        projected_gradient = null.T @ ((H @ theta + g) / gram_scale)
        gradient_inf = float(np.linalg.norm(projected_gradient, ord=np.inf)) if len(projected_gradient) else 0.0
        constraint_residual = abs(float(np.sum(theta)) - 1.0)
    else:
        z, rank, condition, tolerance, singular_values = svd_solve(H_scaled, -g_scaled)
        theta = z / gram_scale
        effective_dimension = len(idx)
        gradient_inf = float(np.linalg.norm(H @ theta + g, ord=np.inf))
        constraint_residual = 0.0

    energy = float(1.0 + 2.0 * (g @ theta) + theta @ H @ theta)
    return {"theta": theta, "E": energy, "H": H, "g": g,
            "solver_rank": rank, "effective_dimension": effective_dimension,
            "rank_deficient": rank < effective_dimension,
            "hessian_condition": condition, "svd_tolerance": tolerance,
            "scaled_hessian_singular_values": singular_values,
            "scaled_hessian_rcond": (tolerance / singular_values[0]
                                     if singular_values and singular_values[0] else 0.0),
            "basis_rank": basis_rank, "basis_condition": basis_condition,
            "normal_residual_inf": gradient_inf,
            "constraint_residual": constraint_residual}


def slope_and_endpoint(spec: dict, theta: np.ndarray) -> tuple[float, float]:
    if spec["kind"] == "polynomial":
        slope = float(theta[0])
        at_one = float(np.sum(theta))
    else:
        x0 = float(spec["x0"])
        slope = float(theta[0] - 2.0 * x0 * theta[1] - 3.0 * x0**2 * theta[2])
        at_one = float(theta[0] - x0**2 * theta[1] - x0**3 * theta[2])
    return slope, at_one


def profile_value(spec: dict, theta: np.ndarray, x: np.ndarray) -> np.ndarray:
    if spec["kind"] == "polynomial":
        result = np.zeros_like(x, dtype=np.float64)
        for j, value in enumerate(theta, start=1):
            result += value * x**j
        return result
    x0 = float(spec["x0"])
    hinge = np.maximum(x0 - x, 0.0)
    return theta[0] * x + theta[1] * (hinge**2 - x0**2) + theta[2] * (hinge**3 - x0**3)


def objective_from_vector(gram: np.ndarray, b: np.ndarray, vector: np.ndarray) -> float:
    return float(1.0 + 2.0 * (b @ vector) + vector @ (gram @ vector))


def energy_splits(N: int, delta: np.ndarray, n_int: np.ndarray,
                  arith: dict[str, np.ndarray]) -> dict[str, float]:
    mu = arith["mu"][n_int]
    omega = arith["omega"][n_int]
    prime = arith["is_prime"][n_int]
    squarefree = mu != 0
    proper_prime_power = (~prime) & (omega == 1)
    other = (~prime) & (~proper_prime_power)
    masks = {
        "n_le_sqrtN": n_int <= math.isqrt(N),
        "n_gt_sqrtN": n_int > math.isqrt(N),
        "n_gt_N_over_2": n_int > N / 2.0,
        "squarefree": squarefree,
        "non_squarefree_mu_zero": ~squarefree,
        "primes": prime,
        "proper_prime_powers": proper_prime_power,
        "other": other,
    }
    total = float(delta @ delta)
    row = {key: float(np.sum(delta[mask] ** 2, dtype=np.float64))
           for key, mask in masks.items()}
    for key, value in list(row.items()):
        row[f"fraction_{key}"] = value / total if total else 0.0
    row["delta_norm_sq"] = total
    return row


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames, lineterminator="\n",
                                extrasaction="raise")
        writer.writeheader()
        writer.writerows(rows)


def finite_or_none(value: float | None) -> float | None:
    if value is None:
        return None
    return float(value) if math.isfinite(float(value)) else None


def coefficient_names(spec: dict) -> list[str]:
    if spec["kind"] == "polynomial":
        return [f"p{j}" for j in range(1, spec["degree"] + 1)]
    return ["x", "h2", "h3"]


def best_choice(results: dict[str, dict], candidate_specs: dict[str, dict]) -> tuple[str, list[str]]:
    min_energy = min(float(row["E"]) for row in results.values())
    tolerance = BEST_TIE_TOL * max(1.0, abs(min_energy))
    tied = sorted(name for name, row in results.items()
                  if float(row["E"]) <= min_energy + tolerance)
    return tied[0], tied


def make_plots(main_data: dict[int, dict], output: Path) -> None:
    for N, data in main_data.items():
        xgrid = np.linspace(0.0, 1.0, 501)
        fig, ax = plt.subplots(figsize=(9, 5.5))
        ax.plot(xgrid, xgrid, color="#555555", lw=1.7, label="log taper P(x)=x")
        ax.plot(xgrid, profile_value(data["spec"], data["theta"], xgrid),
                color="#007c91", lw=2.1, label=f"best: {data['spec']['family']}")
        ax.set(xlabel="x = log(N/n) / log N", ylabel="P(x)",
               title=f"Best smooth Mobius taper profile, N={N}")
        ax.grid(True, alpha=0.25)
        ax.legend(loc="best")
        fig.tight_layout()
        fig.savefig(output / f"fit_profile_N{N}.png", dpi=170)
        plt.close(fig)

        u = data["n_int"] / float(N)
        delta_sq = data["delta"] ** 2
        cumulative = np.cumsum(delta_sq) / max(float(np.sum(delta_sq)), 1e-300)
        fig, axes = plt.subplots(2, 1, figsize=(9, 7), sharex=True,
                                 gridspec_kw={"height_ratios": [1, 1]})
        axes[0].plot(u, delta_sq, color="#8055a5", lw=0.8)
        axes[0].set_ylabel(r"$\delta_n^2$")
        axes[0].set_title(f"Remaining optimal-vector difference, N={N}")
        axes[1].plot(u, cumulative, color="#c05a24", lw=1.4)
        axes[1].set(xlabel="u = n/N", ylabel=r"cumulative fraction of $||\delta||_2^2$",
                    ylim=(-0.02, 1.02))
        for ax in axes:
            ax.axvline(math.sqrt(N) / N, color="#333333", ls="--", lw=0.8,
                       label=r"$n=\sqrt{N}$")
            ax.axvline(0.5, color="#888888", ls=":", lw=0.8, label="n=N/2")
            ax.grid(True, alpha=0.25)
        axes[0].legend(loc="best")
        fig.tight_layout()
        fig.savefig(output / f"fit_delta_energy_N{N}.png", dpi=170)
        plt.close(fig)


def selected_profiles_document(selected: dict[int, dict], path: Path) -> None:
    out = {}
    for N, data in sorted(selected.items()):
        spec, theta = data["spec"], data["theta"]
        if spec["kind"] == "polynomial":
            names = coefficient_names(spec)
            basiscoeffs = {f"x^{j}": float(value)
                           for j, value in enumerate(theta, start=1)}
            monomialcoeffs = [float(v) for v in theta]
        else:
            basiscoeffs = {
                "x": float(theta[0]),
                "(x0-x)_+^2-x0^2": float(theta[1]),
                "(x0-x)_+^3-x0^3": float(theta[2]),
            }
            monomialcoeffs = None
        profile = {
            "family": spec["family"],
            "kind": spec["kind"],
            "basis": "monomial" if spec["kind"] == "polynomial" else "linear_plus_edge_hinges",
            "basiscoeffs": basiscoeffs,
            "monomialcoeffs": monomialcoeffs,
            "degree": spec["degree"],
            "x0": spec["x0"],
            "E": data["E"],
            "E_log": data["E_log"],
            "E_log_times_logN": data["E_log_times_logN"],
            "gap_closure": finite_or_none(data["gap_closure"]),
            "E_opt": finite_or_none(data["E_opt"]),
            "P_at_1": data["P_at_1"],
            "Pprime_0": data["Pprime_0"],
            "Pprime_0_over_log_slope": data["Pprime_0"],
            "solver_rank": data["solver_rank"],
            "effective_dimension": data["effective_dimension"],
            "rank_deficient": data["rank_deficient"],
            "condition_number_hessian": finite_or_none(data["hessian_condition"]),
            "condition_number_basis": finite_or_none(data["basis_condition"]),
            "scaled_hessian_singular_values": data["scaled_hessian_singular_values"],
            "scaled_hessian_rcond": data["scaled_hessian_rcond"],
            "constraint_residual": data["constraint_residual"],
            "best_tie_families": data["tie_families"],
            "vector_contract": "raw a_1=1; for n=2..N, a_n=mu(n)*P(log(N/n)/logN)",
        }
        out[str(N)] = {"bestprofile": profile}
    path.write_text(json.dumps(out, indent=2, allow_nan=False) + "\n", encoding="utf-8")


def write_selected_vectors(selected: dict[int, dict], arith: dict[str, np.ndarray], path: Path) -> None:
    def rows():
        for N, data in sorted(selected.items()):
            yield {"N": N, "n": 1, "log": "1", "best": "1"}
            n_int = np.arange(2, N + 1, dtype=np.int64)
            logN = math.log(N)
            x = np.log(N / n_int.astype(np.float64)) / logN
            mu = arith["mu"][n_int].astype(np.float64)
            a_log = mu * x
            a_best = mu * profile_value(data["spec"], data["theta"], x)
            for i, n in enumerate(n_int):
                yield {"N": N, "n": int(n),
                       "log": format(float(a_log[i]), ".17g"),
                       "best": format(float(a_best[i]), ".17g")}
    write_csv(path, ("N", "n", "log", "best"), rows())


def write_report(path: Path, main_rows: list[dict], judges: list[dict],
                 predictions: dict, selected: dict[int, dict], source_info: dict,
                 gram_meta: dict, all_rows: list[dict]) -> None:
    byN = {int(row["N"]): row for row in main_rows}
    judge_j1 = [r for r in judges if r["judge"] == "J1"]
    judge_j3 = [r for r in judges if r["judge"] == "J3"]
    lines = [
        "# Part A — smooth Mobius taper fit",
        "",
        "## Contract and inputs",
        "",
        f"- Frozen preregistration: commit `{source_info['preregistration']['commit']}`; blob `{source_info['preregistration']['blob']}`.",
        f"- One native full Vasyunin Gram was built at N={gram_meta['N']} ({gram_meta['bytes']:,} bytes; {gram_meta['seconds']:.3f}s measured for the native build/read step). All smaller targets use its leading principal prefixes.",
        "- Free variables are n=2..N with physical optimum read directly from ec1 `c_opt` (the negative of the older projection coefficients); the residual convention is `1 + sum c_n r_n`.",
        "- For both exported vectors, raw coefficient n=1 is 1. For n>=2, `log=mu(n)*x` and `best=mu(n)*P(x)`, x=log(N/n)/logN.",
        "- Polynomial fits use P(0)=0, degree 1..4, both free P(1) and fixed P(1)=1; splines use the frozen three basis functions and five x0 values. No positivity or monotonicity constraints were imposed.",
        "- Best Part A/Part B profile is selected per N from degree<=3 polynomial variants and all five splines. Degree 4 is reported but excluded. Energy ties within 1e-12*max(1,|E_min|) use ascending family name.",
        "- SVD least-squares solves are used for singular and rank-deficient systems. CSVs report basis/Hessian rank and condition numbers; these floating-point computations are not interval certificates.",
        "",
        "## J1 and J3 validation",
        "",
        f"- J1: {'PASS' if all(int(r['pass']) for r in judge_j1) else 'FAIL'}; max absolute E(log)-archived E(a) difference = {max(float(r['difference']) for r in judge_j1):.6g}.",
        f"- J3: {'PASS' if all(int(r['pass']) for r in judge_j3) else 'FAIL'}; minimum E(fit)-E(opt) = {min(float(r['difference']) for r in judge_j3):.6g} across every fitted family at the four main N.",
        "",
        "| N | best family | E(best) | E(best) log N | closure | cosine(c_opt,best) | P'(0) | P(1) | rank / dimension |",
        "|---:|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for N in MAIN_N:
        r = byN[N]
        lines.append(
            f"| {N} | {r['family']} | {float(r['E']):.12g} | {float(r['E_logN']):.12g} | "
            f"{float(r['gap_closure']):.6f} | {float(r['cosine_copt_best']):.9f} | "
            f"{float(r['Pprime_0']):.9g} | {float(r['P_at_1']):.9g} | "
            f"{r['solver_rank']}/{r['effective_dimension']} |"
        )
    lines.extend(["", "## Prediction checks available in Part A", ""])
    for key in ("R1", "R2", "R3"):
        pred = predictions[key]
        lines.append(f"- {key}: **{'HIT' if pred['hit'] else 'MISS'}** (p={pred['p']}); {pred['rule']}")
        if key == "R2":
            lines.append(f"  - N=2000 winner `{pred['winner_2000']}`; N=5000 winner `{pred['winner_5000']}`; coefficient relative changes `{pred['relative_changes']}`.")
    lines.extend([
        "",
        "J2/J4, boundary scalars, head arithmetic, and the core calculation are handled separately. The literal/corrected head identity prediction R4 is not scored here.",
        "",
        "## Artifacts",
        "",
        "- `fit_all.csv`: E and numerical conditioning for every fitted family at every requested N, including log taper.",
        "- `fit_coefficients.csv`: all fitted polynomial/spline coefficients.",
        "- `fit_selected.csv`, `selected_profiles.json`, `selected_vectors.csv`: per-N Part B interface. The latter has exactly `N,n,log,best` columns and raw n=1 entries.",
        "- `fit_energy_splits.csv`: the same eight delta-energy masks as the prior Gram comparison; threshold masks can overlap arithmetic masks.",
        "- `fit_profile_N*.png` and `fit_delta_energy_N*.png`: main-N profile and remaining-delta plots.",
        "",
    ])
    path.write_text("\n".join(lines), encoding="utf-8", newline="\n")


def run() -> None:
    started = time.monotonic()
    archived, optimum_reference, targets, source_info = load_sources()
    arith = arithmetic(max(targets))
    specs_by_N: dict[int, dict[str, dict]] = {}
    all_rows: list[dict] = []
    coefficient_rows: list[dict] = []
    selected: dict[int, dict] = {}
    main_data: dict[int, dict] = {}
    main_rows: list[dict] = []
    split_rows: list[dict] = []
    judge_rows: list[dict] = []
    best_spec_list = None

    with tempfile.TemporaryDirectory(prefix="smooth_taper_fit_") as td:
        tmp = Path(td)
        exe = compile_native(tmp)
        gram_path = tmp / "full_gram_N10000.bin"
        gram, gram_meta = build_gram(exe, 10000, gram_path)
        fit_started = time.monotonic()
        for idxN, N in enumerate(targets, start=1):
            M_all, labels, label_to_i, n_int, b = basis_data(N, arith["mu"])
            G_N = gram[:N - 1, :N - 1]
            G_times_M = G_N @ M_all
            H_all = M_all.T @ G_times_M
            H_all = (H_all + H_all.T) * 0.5
            g_all = M_all.T @ b
            fam_specs = specs(label_to_i)
            best_spec_list = fam_specs
            spec_by_name = {spec["family"]: spec for spec in fam_specs}
            raw_results: dict[str, dict] = {}
            x = np.log(N / n_int.astype(np.float64)) / math.log(N)
            log_vector = arith["mu"][n_int].astype(np.float64) * x
            E_log = objective_from_vector(G_N, b, log_vector)

            for spec in fam_specs:
                fit = fit_one(spec, M_all, H_all, g_all)
                slope, at_one = slope_and_endpoint(spec, fit["theta"])
                raw_results[spec["family"]] = {**fit, "spec": spec,
                                                 "Pprime_0": slope, "P_at_1": at_one}
                names = coefficient_names(spec)
                for param, value in zip(names, fit["theta"]):
                    coefficient_rows.append({"N": N, "family": spec["family"],
                                             "kind": spec["kind"], "degree": spec["degree"],
                                             "endpoint": spec["endpoint"], "x0": spec["x0"],
                                             "parameter": param, "coefficient": float(value)})

            eligible = {name: fit for name, fit in raw_results.items()
                        if not (fit["spec"]["kind"] == "polynomial" and fit["spec"]["degree"] == 4)}
            best_name, tied = best_choice(eligible, spec_by_name)
            best = eligible[best_name]
            best_spec = best["spec"]
            best_idx = best_spec["basis_indices"]
            best_vector = M_all[:, best_idx] @ best["theta"]
            log_vs_best = []
            if N in MAIN_N:
                c_opt = np.array([archived[N][n] for n in range(2, N + 1)], dtype=np.float64)
                E_opt = objective_from_vector(G_N, b, c_opt)
                opt_reference_diff = abs(E_opt - optimum_reference[N]["E_opt"])
                if opt_reference_diff >= 1e-10:
                    raise AssertionError(f"archived optimum mismatch at N={N}: {opt_reference_diff}")
                closure_denom = E_log - E_opt
                closure = (E_log - float(best["E"])) / closure_denom if closure_denom else math.nan
                cosine = float((c_opt @ best_vector) /
                               math.sqrt(float(c_opt @ c_opt) * float(best_vector @ best_vector)))
                delta = c_opt - best_vector
                split = energy_splits(N, delta, n_int, arith)
                split_rows.append({"N": N, "best_family": best_name, **split})
                main_row = {
                    "N": N, "family": best_name, "E": best["E"], "E_log": E_log,
                    "E_logN": float(best["E"]) * math.log(N),
                    "E_log_times_logN": E_log * math.log(N), "E_opt": E_opt,
                    "gap_closure": closure, "cosine_copt_best": cosine,
                    "Pprime_0": best["Pprime_0"], "P_at_1": best["P_at_1"],
                    "solver_rank": best["solver_rank"],
                    "effective_dimension": best["effective_dimension"],
                    "rank_deficient": int(best["rank_deficient"]),
                    "hessian_condition": best["hessian_condition"],
                    "basis_condition": best["basis_condition"],
                    "scaled_hessian_singular_values": json.dumps(best["scaled_hessian_singular_values"]),
                    "scaled_hessian_rcond": best["scaled_hessian_rcond"],
                    "constraint_residual": best["constraint_residual"],
                    "best_tie_count": len(tied), "best_tie_families": ";".join(tied),
                }
                main_rows.append(main_row)
                main_data[N] = {"spec": best_spec, "theta": best["theta"],
                                "n_int": n_int, "delta": delta,
                                "c_opt": c_opt, "a_best": best_vector}
            else:
                E_opt = math.nan
                closure = math.nan
                cosine = math.nan
                opt_reference_diff = math.nan

            for name, fit in raw_results.items():
                spec = fit["spec"]
                # The log taper is the common P=x reference, not a separate candidate family.
                fit_E_log = E_log
                row = {
                    "N": N, "family": name, "kind": spec["kind"], "degree": spec["degree"],
                    "endpoint": spec["endpoint"], "x0": spec["x0"], "E": fit["E"],
                    "E_log": E_log, "E_times_logN": float(fit["E"]) * math.log(N),
                    "E_log_times_logN": E_log * math.log(N),
                    "gap_closure": ((E_log - float(fit["E"])) / (E_log - E_opt)
                                    if N in MAIN_N else math.nan),
                    "cosine_copt_profile": math.nan,
                    "P_at_1": fit["P_at_1"], "Pprime_0": fit["Pprime_0"],
                    "Pprime_0_over_log_slope": fit["Pprime_0"],
                    "solver_rank": fit["solver_rank"],
                    "effective_dimension": fit["effective_dimension"],
                    "rank_deficient": int(fit["rank_deficient"]),
                    "condition_number_hessian": fit["hessian_condition"],
                    "condition_number_basis": fit["basis_condition"],
                    "scaled_hessian_singular_values": json.dumps(fit["scaled_hessian_singular_values"]),
                    "scaled_hessian_rcond": fit["scaled_hessian_rcond"],
                    "constraint_residual": fit["constraint_residual"],
                    "normal_residual_inf": fit["normal_residual_inf"],
                }
                all_rows.append(row)

            # Include the exact log taper as a named reference record.
            all_rows.append({
                "N": N, "family": "log_taper", "kind": "reference", "degree": 1,
                "endpoint": "fixed1", "x0": "", "E": E_log, "E_log": E_log,
                "E_times_logN": E_log * math.log(N), "E_log_times_logN": E_log * math.log(N),
                "gap_closure": 0.0, "cosine_copt_profile": math.nan,
                "P_at_1": 1.0, "Pprime_0": 1.0, "Pprime_0_over_log_slope": 1.0,
                "solver_rank": 1, "effective_dimension": 1, "rank_deficient": 0,
                "condition_number_hessian": 1.0, "condition_number_basis": 1.0,
                "normal_residual_inf": 0.0,
            })
            selected[N] = {
                "spec": best_spec, "theta": best["theta"], "E": float(best["E"]),
                "E_log": E_log, "E_log_times_logN": E_log * math.log(N),
                "gap_closure": closure, "E_opt": E_opt,
                "P_at_1": best["P_at_1"], "Pprime_0": best["Pprime_0"],
                "solver_rank": best["solver_rank"],
                "effective_dimension": best["effective_dimension"],
                "rank_deficient": bool(best["rank_deficient"]),
                "hessian_condition": best["hessian_condition"],
                "basis_condition": best["basis_condition"],
                "scaled_hessian_singular_values": best["scaled_hessian_singular_values"],
                "scaled_hessian_rcond": best["scaled_hessian_rcond"],
                "constraint_residual": best["constraint_residual"],
                "tie_families": tied,
            }

            # J1 and J3 are deliberately resolved before any prediction scoring/reporting.
            if N in MAIN_N:
                j1_diff = abs(E_log - optimum_reference[N]["E_log"])
                judge_rows.append({"judge": "J1", "N": N, "observed": E_log,
                                   "reference": optimum_reference[N]["E_log"],
                                   "difference": j1_diff, "tolerance": 1e-10,
                                   "pass": int(j1_diff < 1e-10)})
                if j1_diff >= 1e-10:
                    raise AssertionError(f"J1 failed at N={N}: {j1_diff}")
                for family, fit in raw_results.items():
                    j3_diff = float(fit["E"]) - E_opt
                    judge_rows.append({"judge": "J3", "N": N, "family": family,
                                       "observed": float(fit["E"]), "reference": E_opt,
                                       "difference": j3_diff, "tolerance": -1e-10,
                                       "pass": int(j3_diff >= -1e-10)})
                    if j3_diff < -1e-10:
                        raise AssertionError(f"J3 failed for {family} at N={N}: {j3_diff}")
            progress(idxN, len(targets), fit_started, f"prefix fits N={N}")

        if not all(int(row["pass"]) for row in judge_rows):
            raise AssertionError("J1/J3 failed before report generation")

        # The N=5000 prefix is kept mapped through all calculations, then released by tempdir cleanup.
        del gram

    by_family = {(int(row["N"]), row["family"]): row for row in all_rows}
    by_main = {int(row["N"]): row for row in main_rows}
    poly_candidates_5000 = [row for row in all_rows
                             if int(row["N"]) == 5000 and row["kind"] == "polynomial"
                             and int(row["degree"]) <= 3]
    best_poly_5000 = min(poly_candidates_5000, key=lambda r: (float(r["E"]), r["family"]))
    r1_hit = float(best_poly_5000["gap_closure"]) >= 0.5

    d3_winners = {}
    for N in (2000, 5000):
        rows = [r for r in all_rows if int(r["N"]) == N and r["kind"] == "polynomial"
                and int(r["degree"]) == 3]
        d3_winners[N] = min(rows, key=lambda r: (float(r["E"]), r["family"]))
    # Extract d=3 coefficients from the coefficient table with exact named parameter order.
    def params(N: int, family: str) -> list[float]:
        values = {row["parameter"]: float(row["coefficient"]) for row in coefficient_rows
                  if int(row["N"]) == N and row["family"] == family}
        return [values[f"p{j}"] for j in (1, 2, 3)]

    d3_old = params(2000, d3_winners[2000]["family"])
    d3_new = params(5000, d3_winners[5000]["family"])
    rel_changes = []
    near_zero = []
    for j, old, new in zip((1, 2, 3), d3_old, d3_new):
        den = max(abs(old), 1e-12)
        rel = abs(new - old) / den
        rel_changes.append(rel)
        if abs(old) < 1e-12:
            near_zero.append(f"p{j}")
    r2_hit = all(value < 0.2 for value in rel_changes)
    r3_slope = float(selected[5000]["Pprime_0"])
    r3_hit = r3_slope < 0.8 or r3_slope > 1.25
    predictions = {
        "R1": {"p": 0.55, "hit": r1_hit,
               "rule": "best degree<=3 polynomial gap closure >= 0.5 at N=5000",
               "family": best_poly_5000["family"],
               "gap_closure": float(best_poly_5000["gap_closure"])},
        "R2": {"p": 0.5, "hit": r2_hit,
               "rule": "each degree-3 winner coefficient changes by <20% from N=2000 to N=5000",
               "winner_2000": d3_winners[2000]["family"],
               "winner_5000": d3_winners[5000]["family"],
               "coefficients_2000": d3_old, "coefficients_5000": d3_new,
               "relative_changes": rel_changes, "near_zero_old_coefficients": near_zero},
        "R3": {"p": 0.6, "hit": r3_hit,
               "rule": "selected best Pprime(0) outside [0.8,1.25] at N=5000",
               "selected_family": selected[5000]["spec"]["family"],
               "Pprime_0": r3_slope},
    }

    fit_all_fields = ("N", "family", "kind", "degree", "endpoint", "x0", "E", "E_log",
                      "E_times_logN", "E_log_times_logN", "gap_closure", "cosine_copt_profile",
                      "P_at_1", "Pprime_0", "Pprime_0_over_log_slope", "solver_rank",
                      "effective_dimension", "rank_deficient", "condition_number_hessian",
                      "condition_number_basis", "scaled_hessian_singular_values",
                      "scaled_hessian_rcond", "constraint_residual", "normal_residual_inf")
    fit_coeff_fields = ("N", "family", "kind", "degree", "endpoint", "x0", "parameter", "coefficient")
    write_csv(HERE / "fit_all.csv", fit_all_fields, all_rows)
    write_csv(HERE / "fit_coefficients.csv", fit_coeff_fields, coefficient_rows)
    wide_rows = []
    for row in all_rows:
        if row["family"] == "log_taper":
            wide_rows.append({"N": row["N"], "family": "log_taper", "kind": "reference",
                              "degree": 1, "P1_constraint": "fixed1", "x0": "",
                              "p1": 1.0, "p2": "", "p3": "", "p4": "",
                              "x": "", "h2": "", "h3": "", "E": row["E"],
                              "P_at_1": 1.0, "Pprime_0": 1.0})
            continue
        cr = {r["parameter"]: float(r["coefficient"]) for r in coefficient_rows
              if int(r["N"]) == int(row["N"]) and r["family"] == row["family"]}
        family_kind = row["kind"]
        wide_rows.append({
            "N": row["N"], "family": row["family"], "kind": family_kind,
            "degree": row["degree"], "P1_constraint": row["endpoint"], "x0": row["x0"],
            "p1": cr.get("p1", ""), "p2": cr.get("p2", ""),
            "p3": cr.get("p3", ""), "p4": cr.get("p4", ""),
            "x": cr.get("x", ""), "h2": cr.get("h2", ""), "h3": cr.get("h3", ""),
            "E": row["E"], "P_at_1": row["P_at_1"], "Pprime_0": row["Pprime_0"],
        })
    write_csv(HERE / "fit_results.csv",
              ("N", "family", "kind", "degree", "P1_constraint", "x0", "p1", "p2",
               "p3", "p4", "x", "h2", "h3", "E", "P_at_1", "Pprime_0"), wide_rows)
    write_csv(HERE / "fit_baselines.csv",
              ("N", "E_log", "E_log_times_logN"),
              ({"N": row["N"], "E_log": row["E_log"],
                "E_log_times_logN": row["E_log_times_logN"]}
               for row in all_rows if row["family"] == "log_taper"))
    write_csv(HERE / "fit_selected.csv",
              ("N", "family", "E", "E_log", "E_logN", "E_log_times_logN", "E_opt", "gap_closure",
               "cosine_copt_best", "Pprime_0", "P_at_1", "solver_rank",
               "effective_dimension", "rank_deficient", "hessian_condition",
               "basis_condition", "scaled_hessian_singular_values", "scaled_hessian_rcond",
               "constraint_residual", "best_tie_count", "best_tie_families"), main_rows)
    split_fields = ("N", "best_family", "n_le_sqrtN", "n_gt_sqrtN", "n_gt_N_over_2",
                    "squarefree", "non_squarefree_mu_zero", "primes", "proper_prime_powers",
                    "other", "fraction_n_le_sqrtN", "fraction_n_gt_sqrtN",
                    "fraction_n_gt_N_over_2", "fraction_squarefree",
                    "fraction_non_squarefree_mu_zero", "fraction_primes",
                    "fraction_proper_prime_powers", "fraction_other", "delta_norm_sq")
    write_csv(HERE / "fit_energy_splits.csv", split_fields, split_rows)
    write_csv(HERE / "fit_judges.csv",
              ("judge", "N", "family", "observed", "reference", "difference", "tolerance", "pass"),
              judge_rows)

    selected_profiles_document(selected, HERE / "selected_profiles.json")
    write_selected_vectors(selected, arith, HERE / "selected_vectors.csv")
    make_plots(main_data, HERE)

    predictions_path = HERE / "fit_predictions.json"
    predictions_path.write_text(json.dumps(predictions, indent=2, allow_nan=False) + "\n",
                                encoding="utf-8")
    run_meta = {
        "task": "SMOOTH_TAPER_FIT_2026-11-06 Part A and J1/J3",
        "source_info": source_info,
        "convention": {
            "free_coefficients": "n=2..N",
            "optimum_sign": "archived physical c_opt=-stored c; validated against pinned full-Gram E_opt",
            "raw_n1": 1,
            "profile": "a_n=mu(n)*P(log(N/n)/logN), n>=2",
            "selected_family": "minimum E among degree<=3 polynomials and five splines, independently for each N",
            "tie_tolerance": BEST_TIE_TOL,
        },
        "gram": {**gram_meta, "compiler": os.environ.get("CXX", "clang++"),
                 "platform": platform.platform(),
                 "method": "single N=10000 full-Gram build; all requested Ns use leading principal prefixes"},
        "judge_pass": {judge: all(int(row["pass"]) for row in judge_rows if row["judge"] == judge)
                       for judge in ("J1", "J3")},
        "max_J1_abs_difference": max(float(r["difference"]) for r in judge_rows if r["judge"] == "J1"),
        "min_J3_Ebest_minus_Eopt": min(float(r["difference"]) for r in judge_rows if r["judge"] == "J3"),
        "predictions": predictions,
        "elapsed_seconds_including_outputs": time.monotonic() - started,
        "limitations": [
            "Float64 stored Gram and SVD least-squares are diagnostics, not interval certificates.",
            "J3 is checked at the four main N against the pinned archived full-Gram optimum.",
            "Selected vectors intentionally export raw n=1=1; the free Gram coordinates are n=2..N.",
        ],
    }
    (HERE / "fit_run.json").write_text(json.dumps(run_meta, indent=2, allow_nan=False) + "\n",
                                        encoding="utf-8")
    write_report(HERE / "PART_A.md", main_rows, judge_rows, predictions, selected,
                 source_info, gram_meta, all_rows)
    print(json.dumps({"judge_pass": run_meta["judge_pass"],
                      "max_J1_abs_difference": run_meta["max_J1_abs_difference"],
                      "min_J3_Ebest_minus_Eopt": run_meta["min_J3_Ebest_minus_Eopt"],
                      "predictions": predictions,
                      "elapsed_seconds": run_meta["elapsed_seconds_including_outputs"]},
                     indent=2), flush=True)


if __name__ == "__main__":
    run()
