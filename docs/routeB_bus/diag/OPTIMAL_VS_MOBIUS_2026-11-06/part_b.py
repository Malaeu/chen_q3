# /// script
# requires-python = ">=3.13"
# dependencies = ["matplotlib>=3.9", "mpmath>=1.3", "numpy>=2.0", "scipy>=1.14"]
# ///
"""Part B: direct-zeta t-side comparison with resumable local checkpoints."""

from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.stats import rankdata, spearmanr


mp.mp.dps = 20

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
N_VALUES = (500, 1000, 2000, 5000)
T_MAX = 1000.0
ZERO_COMMIT = "ba5654b46adf84159702748b006699bafa0ed89b"
COEFF_PATH = "docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06/part_a_coefficients.csv"
COEFF_BLOB = "7baa38bc0f5a9437e985f739aecb823ec2dedf1a"
SOURCE_DOC = HERE / "SOURCES.json"
PREREG_PATH = HERE / "PREREGISTRATION.json"
T_GRID_PATH = HERE / "t_grid.csv.gz"
PER_ZERO_PATH = HERE / "per_zero.csv"
ZERO_CHECKPOINT = HERE / "part_b_zero_checkpoint.csv"
ZETA_CHECKPOINT = HERE / "part_b_zeta_checkpoint.csv"
RUN_JSON = HERE / "part_b_run.json"
PERMUTATION_SEED = 20261106
N_PERMUTATIONS = 1000
INITIAL_INTERVALS = 32
REFINEMENT_LEVELS = (32, 64, 128)
HEAD_SCALED_ABS_TOL = 1e-6
LOCAL_W_SCALED_ABS_TOL = 1e-6
CORRELATION_TOL = 1e-3
EVAL_CHUNK = 128


@dataclass(frozen=True)
class ZeroRecord:
    index: int
    gamma_mp: str
    derivative_abs_mp: str

    @property
    def gamma(self) -> float:
        return float(self.gamma_mp)

    @property
    def derivative_abs(self) -> float:
        return float(self.derivative_abs_mp)


@dataclass(frozen=True)
class Segment:
    zero_index: int
    side: str
    start: float
    end: float


def progress(stage: str, done: int, total: int, started: float, note: str = "") -> None:
    elapsed = time.monotonic() - started
    rate = done / elapsed if elapsed > 0 else 0.0
    eta = (total - done) / rate if rate > 0 else 0.0
    suffix = f" {note}" if note else ""
    print(
        f"[{stage}] {done}/{total} elapsed={elapsed:.1f}s eta={eta:.1f}s{suffix}",
        file=sys.stderr,
        flush=True,
    )


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def load_archived_coefficients() -> dict[int, tuple[np.ndarray, np.ndarray, np.ndarray]]:
    source_meta = read_json(SOURCE_DOC)
    source = next(row for row in source_meta if row["role"] == "coefficients")
    if source["commit"] != ZERO_COMMIT or source["blob"] != COEFF_BLOB:
        raise RuntimeError("coefficient source pin disagrees with the frozen source map")
    blob = subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", f"{ZERO_COMMIT}:{COEFF_PATH}"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if blob != COEFF_BLOB:
        raise RuntimeError(f"archived coefficient blob mismatch: {blob}")
    archived = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{ZERO_COMMIT}:{COEFF_PATH}"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    by_n: dict[int, list[tuple[int, float]]] = {n: [] for n in N_VALUES}
    for row in csv.DictReader(archived.splitlines()):
        n_size = int(row["N"])
        if n_size in by_n:
            by_n[n_size].append((int(row["n"]), float(row["c"])))
    result = {}
    for n_size in N_VALUES:
        rows = sorted(by_n[n_size])
        expected = list(range(2, n_size + 1))
        if [n for n, _ in rows] != expected:
            raise RuntimeError(f"archived coefficient rows are incomplete for N={n_size}")
        n = np.asarray(expected, dtype=np.float64)
        archived_c = np.asarray([c for _, c in rows], dtype=np.float64)
        c_opt = -archived_c
        taper = np.asarray([mobius(int(k)) for k in expected], dtype=np.float64)
        taper *= np.log(n_size / n) / math.log(n_size)
        if not (np.isfinite(c_opt).all() and np.isfinite(taper).all()):
            raise RuntimeError(f"non-finite coefficient input at N={n_size}")
        result[n_size] = (n, c_opt, taper)
    return result


def mobius(n: int) -> int:
    remaining = n
    primes = 0
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            remaining //= p
            primes += 1
            if remaining % p == 0:
                return 0
            while remaining % p == 0:
                remaining //= p
        p += 1 if p == 2 else 2
    if remaining > 1:
        primes += 1
    return -1 if primes % 2 else 1


def _read_zero_checkpoint(path: Path) -> list[ZeroRecord]:
    if not path.exists():
        return []
    result: list[ZeroRecord] = []
    with path.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            try:
                result.append(
                    ZeroRecord(
                        int(row["index"]),
                        row["gamma_mp"],
                        row["derivative_abs_mp"],
                    )
                )
            except (KeyError, ValueError):
                continue
    return result


def _zeros_from_final_output() -> list[ZeroRecord]:
    if not PER_ZERO_PATH.exists():
        return []
    result: list[ZeroRecord] = []
    seen: set[int] = set()
    with PER_ZERO_PATH.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            try:
                j = int(row["zero_index"])
                if j not in seen and row.get("gamma_mp") and row.get("derivative_abs_mp"):
                    result.append(ZeroRecord(j, row["gamma_mp"], row["derivative_abs_mp"]))
                    seen.add(j)
            except (KeyError, ValueError):
                continue
    return sorted(result, key=lambda z: z.index)


def load_zeros() -> list[ZeroRecord]:
    cached = _read_zero_checkpoint(ZERO_CHECKPOINT)
    if not cached:
        cached = _zeros_from_final_output()
    cached = sorted({z.index: z for z in cached}.values(), key=lambda z: z.index)
    expected_index = len(cached) + 1
    if [z.index for z in cached] != list(range(1, expected_index)):
        raise RuntimeError("zero checkpoint indices are not contiguous")
    if cached and float(cached[-1].gamma_mp) > T_MAX:
        all_needed = cached
    else:
        all_needed = list(cached)
        checkpoint_new = not ZERO_CHECKPOINT.exists()
        stream = ZERO_CHECKPOINT.open("a", newline="", encoding="utf-8")
        writer = csv.writer(stream, lineterminator="\n")
        if checkpoint_new:
            writer.writerow(("index", "gamma_mp", "derivative_abs_mp"))
            stream.flush()
        started = time.monotonic()
        while True:
            index = len(all_needed) + 1
            zero = mp.zetazero(index)
            gamma = mp.im(zero)
            derivative = abs(mp.zeta(zero, derivative=1))
            record = ZeroRecord(index, mp.nstr(gamma, 30), mp.nstr(derivative, 30))
            all_needed.append(record)
            writer.writerow((record.index, record.gamma_mp, record.derivative_abs_mp))
            stream.flush()
            if index % 25 == 0 or gamma > T_MAX:
                progress("zeros", index, 650, started, f"gamma={float(gamma):.6f}")
            if gamma > T_MAX:
                break
        stream.close()
    if not all_needed or not any(z.gamma <= T_MAX for z in all_needed):
        raise RuntimeError("no positive zeta zeros were loaded")
    if not any(z.gamma > T_MAX for z in all_needed):
        raise RuntimeError("zero list lacks the next neighbor above the cutoff")
    return all_needed


def build_segments(zeros: list[ZeroRecord]) -> tuple[list[Segment], list[dict]]:
    in_range = [z for z in zeros if z.gamma <= T_MAX]
    segments: list[Segment] = []
    metadata: list[dict] = []
    for i, zero in enumerate(in_range):
        previous_gap = zero.gamma - in_range[i - 1].gamma if i else math.nan
        next_zero = zeros[i + 1]
        next_gap = next_zero.gamma - zero.gamma
        local_min_gap = next_gap if i == 0 else min(previous_gap, next_gap)
        left = 0.0 if i == 0 else 0.5 * (in_range[i - 1].gamma + zero.gamma)
        right = T_MAX if i == len(in_range) - 1 else 0.5 * (zero.gamma + next_zero.gamma)
        if not (left < zero.gamma <= right <= T_MAX):
            raise RuntimeError(f"invalid cell boundaries for zero {zero.index}")
        metadata.append(
            {
                "zero_index": zero.index,
                "gamma": zero.gamma,
                "gamma_mp": zero.gamma_mp,
                "derivative_abs": zero.derivative_abs,
                "derivative_abs_mp": zero.derivative_abs_mp,
                "gap_prev": previous_gap,
                "gap_next": next_gap,
                "local_min_gap": local_min_gap,
                "cell_left": left,
                "cell_right": right,
                "next_gamma": next_zero.gamma,
            }
        )
        left_ranges = [(left, zero.gamma)]
        if i == 0 and left == 0.0 and zero.gamma > 1.0:
            left_ranges = [(0.0, 1.0)]
            start = 1.0
            while start < zero.gamma:
                end = min(start + 1.0, zero.gamma)
                left_ranges.append((start, end))
                start = end
        for start, end in left_ranges:
            segments.append(Segment(zero.index, "left", start, end))
        segments.append(Segment(zero.index, "right", zero.gamma, right))
    return segments, metadata


def collect_grid(segments: Iterable[Segment], intervals: int) -> np.ndarray:
    points = [np.linspace(s.start, s.end, intervals + 1, dtype=np.float64) for s in segments]
    return np.unique(np.concatenate(points))


def read_final_zeta_grid() -> dict[float, tuple[float, float]]:
    result: dict[float, tuple[float, float]] = {}
    if not T_GRID_PATH.exists():
        return result
    with gzip.open(T_GRID_PATH, "rt", newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            try:
                t = float(row["t"])
                result[t] = (float(row["zeta_re"]), float(row["zeta_im"]))
            except (KeyError, ValueError):
                continue
    return result


def read_zeta_checkpoint() -> dict[float, tuple[float, float]]:
    result: dict[float, tuple[float, float]] = {}
    if ZETA_CHECKPOINT.exists():
        with ZETA_CHECKPOINT.open(newline="", encoding="utf-8") as stream:
            for row in csv.DictReader(stream):
                try:
                    result[float(row["t"])] = (float(row["zeta_re"]), float(row["zeta_im"]))
                except (KeyError, ValueError):
                    continue
    result.update(read_final_zeta_grid())
    return result


def evaluate_zeta_grid(grid: np.ndarray, zeros: list[ZeroRecord]) -> np.ndarray:
    cache = read_zeta_checkpoint()
    missing = [float(t) for t in grid if float(t) not in cache]
    special_gamma = {float(z.gamma): mp.mpf(z.gamma_mp) for z in zeros if z.gamma <= T_MAX}
    started = time.monotonic()
    checkpoint_new = not ZETA_CHECKPOINT.exists()
    stream = ZETA_CHECKPOINT.open("a", newline="", encoding="utf-8")
    writer = csv.writer(stream, lineterminator="\n")
    if checkpoint_new:
        writer.writerow(("t", "zeta_re", "zeta_im"))
        stream.flush()
    last_report = started
    total = len(missing)
    for index, t in enumerate(missing, start=1):
        gamma_mp = special_gamma.get(t)
        ordinate = gamma_mp if gamma_mp is not None else mp.mpf(t)
        zeta_value = mp.zeta(mp.mpf("0.5") + 1j * ordinate)
        zeta_float = complex(zeta_value)
        cache[t] = (zeta_float.real, zeta_float.imag)
        writer.writerow((format(t, ".17g"), format(zeta_float.real, ".17g"), format(zeta_float.imag, ".17g")))
        now = time.monotonic()
        if index % 128 == 0:
            stream.flush()
        if index == total or index % 250 == 0 or now - last_report >= 8.0:
            progress("zeta", index, total, started, f"t={t:.6f}")
            last_report = now
    stream.flush()
    stream.close()
    try:
        return np.asarray([complex(*cache[float(t)]) for t in grid], dtype=np.complex128)
    except KeyError as exc:
        raise RuntimeError(f"zeta grid cache missing t={exc.args[0]}") from exc


def evaluate_intensities(
    grid: np.ndarray,
    zeta_values: np.ndarray,
    coefficients: dict[int, tuple[np.ndarray, np.ndarray, np.ndarray]],
) -> dict[int, dict[str, np.ndarray]]:
    result: dict[int, dict[str, np.ndarray]] = {}
    started = time.monotonic()
    for n_size in N_VALUES:
        n, c_opt, taper = coefficients[n_size]
        logs = np.log(n)
        pair = np.column_stack((c_opt / np.sqrt(n), taper / np.sqrt(n))).astype(np.complex128)
        center = np.asarray((np.dot(c_opt, 1.0 / n), np.dot(taper, 1.0 / n)))
        i_opt = np.empty(grid.size, dtype=np.float64)
        i_taper = np.empty(grid.size, dtype=np.float64)
        for start in range(0, grid.size, EVAL_CHUNK):
            end = min(start + EVAL_CHUNK, grid.size)
            phase = np.exp(-1j * np.multiply.outer(grid[start:end], logs))
            d_values = phase @ pair - center
            residual = 1.0 - zeta_values[start:end, None] * d_values
            intensities = np.abs(residual) ** 2
            i_opt[start:end] = intensities[:, 0]
            i_taper[start:end] = intensities[:, 1]
        delta = i_taper - i_opt
        if not (np.isfinite(i_opt).all() and np.isfinite(i_taper).all() and np.isfinite(delta).all()):
            raise RuntimeError(f"non-finite integrand values for N={n_size}")
        result[n_size] = {"i_opt": i_opt, "i_taper": i_taper, "delta": delta}
        print(f"[poly] N={n_size} points={grid.size} elapsed={time.monotonic() - started:.1f}s", file=sys.stderr, flush=True)
    return result


def simpson(values: np.ndarray, start: float, end: float) -> np.ndarray:
    count = values.shape[0] - 1
    if count < 2 or count % 2:
        raise ValueError("Simpson integration requires a positive even interval count")
    step = (end - start) / count
    odd = np.sum(values[1:-1:2], axis=0)
    even = np.sum(values[2:-1:2], axis=0)
    return (step / 3.0) * (values[0] + values[-1] + 4.0 * odd + 2.0 * even)


def _segment_values(
    grid: np.ndarray,
    values: np.ndarray,
    segment: Segment,
    intervals: int,
    max_intervals: int,
) -> np.ndarray:
    nodes = np.linspace(segment.start, segment.end, max_intervals + 1, dtype=np.float64)
    stride = max_intervals // intervals
    sample_nodes = nodes[::stride]
    positions = np.searchsorted(grid, sample_nodes)
    if not np.array_equal(grid[positions], sample_nodes):
        raise RuntimeError("segment nodes are absent from the global integration grid")
    return values[positions]


def compute_integrals(
    grid: np.ndarray,
    integrands: dict[int, dict[str, np.ndarray]],
    segments: list[Segment],
    zero_metadata: list[dict],
    intervals: int,
    max_intervals: int,
) -> tuple[dict[int, dict[str, float]], dict[int, np.ndarray]]:
    heads: dict[int, dict[str, float]] = {}
    local_w: dict[int, np.ndarray] = {}
    zero_position = {row["zero_index"]: i for i, row in enumerate(zero_metadata)}
    weight = 1.0 / (0.25 + grid * grid)
    for n_size in N_VALUES:
        one = integrands[n_size]
        weighted = np.column_stack((one["i_opt"] * weight, one["i_taper"] * weight))
        head_acc = np.zeros(2, dtype=np.float64)
        w_acc = np.zeros(len(zero_metadata), dtype=np.float64)
        for segment in segments:
            head_y = _segment_values(grid, weighted, segment, intervals, max_intervals)
            head_acc += simpson(head_y, segment.start, segment.end)
            delta_y = _segment_values(grid, one["delta"], segment, intervals, max_intervals)
            w_acc[zero_position[segment.zero_index]] += float(
                simpson(delta_y, segment.start, segment.end)
            )
        heads[n_size] = {
            "opt": float(head_acc[0] / math.pi),
            "taper": float(head_acc[1] / math.pi),
        }
        local_w[n_size] = w_acc
    return heads, local_w


def _spearman_value(a: np.ndarray, b: np.ndarray) -> float:
    return float(spearmanr(a, b).statistic)


def convergence_metrics(
    coarse_heads: dict[int, dict[str, float]],
    fine_heads: dict[int, dict[str, float]],
    coarse_w: dict[int, np.ndarray],
    fine_w: dict[int, np.ndarray],
    inv_derivative_sq: np.ndarray,
    local_min_gap: np.ndarray,
) -> dict:
    head_scaled_abs = 0.0
    w_scaled_abs = 0.0
    rho_delta = 0.0
    w_max_difference = {"scaled_abs": 0.0, "zero_index": None, "N": None}
    for n_size in N_VALUES:
        for kind in ("opt", "taper"):
            old = coarse_heads[n_size][kind]
            new = fine_heads[n_size][kind]
            head_scaled_abs = max(head_scaled_abs, abs(new - old) / max(1.0, abs(new)))
        old_w, new_w = coarse_w[n_size], fine_w[n_size]
        w_scale = max(1.0, float(np.max(np.abs(new_w))))
        w_difference = np.abs(new_w - old_w) / w_scale
        w_index = int(np.argmax(w_difference))
        w_scaled_abs = max(w_scaled_abs, float(w_difference[w_index]))
        if float(w_difference[w_index]) > w_max_difference["scaled_abs"]:
            w_max_difference = {"scaled_abs": float(w_difference[w_index]), "zero_index": w_index + 1, "N": n_size}
        for feature in (inv_derivative_sq, local_min_gap):
            rho_delta = max(rho_delta, abs(_spearman_value(old_w, feature) - _spearman_value(new_w, feature)))
    return {
        "head_scaled_abs_max": head_scaled_abs,
        "local_w_scaled_abs_max": w_scaled_abs,
        "local_w_max_difference": w_max_difference,
        "local_spearman_abs_max": rho_delta,
    }


def permutation_judges(
    w: np.ndarray,
    inv_derivative_sq: np.ndarray,
    local_min_gap: np.ndarray,
    permutations: np.ndarray,
) -> list[dict]:
    specs = (
        ("inverse_derivative_squared", inv_derivative_sq),
        ("raw_local_min_gap", local_min_gap),
    )
    output = []
    rank_w = rankdata(w, method="average")
    for name, predictor in specs:
        observed = _spearman_value(w, predictor)
        rank_x = rankdata(predictor, method="average")
        centered_x = rank_x - np.mean(rank_x)
        centered_w = rank_w - np.mean(rank_w)
        denominator = math.sqrt(float(np.dot(centered_x, centered_x) * np.dot(centered_w, centered_w)))
        null = np.asarray(
            [float(np.dot(centered_w[perm], centered_x) / denominator) for perm in permutations],
            dtype=np.float64,
        )
        p_value = (1 + int(np.count_nonzero(np.abs(null) >= abs(observed)))) / (len(null) + 1)
        output.append(
            {
                "variable": name,
                "rho": observed,
                "permutation_p_two_sided": p_value,
                "null95_low": float(np.quantile(null, 0.025)),
                "null95_high": float(np.quantile(null, 0.975)),
                "null_abs_max": float(np.max(np.abs(null))),
                "permutations": len(null),
                "seed": PERMUTATION_SEED,
            }
        )
    return output


def write_csv(path: Path, header: list[str], rows: Iterable[Iterable]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def save_t_grid(
    grid: np.ndarray,
    zeta_values: np.ndarray,
    integrands: dict[int, dict[str, np.ndarray]],
) -> None:
    temporary = T_GRID_PATH.with_suffix(".csv.gz.tmp")
    header = ["grid_index", "t", "zeta_re", "zeta_im"]
    for n_size in N_VALUES:
        header.extend((f"I_opt_{n_size}", f"I_taper_{n_size}", f"Delta_{n_size}"))
    with gzip.open(temporary, "wt", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(header)
        for i, t in enumerate(grid):
            row = [i, format(float(t), ".17g"), format(float(zeta_values[i].real), ".17g"), format(float(zeta_values[i].imag), ".17g")]
            for n_size in N_VALUES:
                values = integrands[n_size]
                row.extend(
                    (
                        format(float(values["i_opt"][i]), ".17g"),
                        format(float(values["i_taper"][i]), ".17g"),
                        format(float(values["delta"][i]), ".17g"),
                    )
                )
            writer.writerow(row)
    os.replace(temporary, T_GRID_PATH)


def plot_outputs(
    grid: np.ndarray,
    integrands: dict[int, dict[str, np.ndarray]],
    zero_metadata: list[dict],
    per_zero_rows: list[dict],
    judges: dict[int, list[dict]],
) -> None:
    zero_left = {row["zero_index"]: row["cell_left"] for row in zero_metadata}
    zero_right = {row["zero_index"]: row["cell_right"] for row in zero_metadata}
    zero_gamma = {row["zero_index"]: row["gamma"] for row in zero_metadata}
    for n_size in N_VALUES:
        rows = [row for row in per_zero_rows if row["N"] == n_size]
        inverse = np.asarray([row["inverse_derivative_sq"] for row in rows])
        w = np.asarray([row["W_j"] for row in rows])
        rho = next(item["rho"] for item in judges[n_size] if item["variable"] == "inverse_derivative_squared")
        p_value = next(
            item["permutation_p_two_sided"]
            for item in judges[n_size]
            if item["variable"] == "inverse_derivative_squared"
        )
        fig, ax = plt.subplots(figsize=(7.2, 5.0))
        ax.scatter(inverse, w, s=15, alpha=0.58, edgecolors="none")
        ax.set_xscale("log")
        ax.set_xlabel(r"$1/|\zeta'(1/2+i\gamma_j)|^2$")
        ax.set_ylabel(r"$W_j=\int_{cell_j}\Delta(t)\,dt$")
        ax.set_title(f"N={n_size}: Spearman rho={rho:.4f}, permutation p={p_value:.4g}")
        ax.grid(True, which="both", alpha=0.25)
        fig.tight_layout()
        fig.savefig(HERE / f"part_b_N{n_size}_W_vs_inv_deriv.png", dpi=170)
        plt.close(fig)

        top = sorted(rows, key=lambda row: (-row["W_j"], row["zero_index"]))[:5]
        fig, axes = plt.subplots(5, 1, figsize=(9.5, 12.5), sharex=False)
        delta = integrands[n_size]["delta"]
        for ax, row in zip(axes, top):
            j = row["zero_index"]
            mask = (grid >= zero_left[j]) & (grid <= zero_right[j])
            ax.plot(grid[mask] - zero_gamma[j], delta[mask], linewidth=0.9)
            ax.axvline(0.0, color="black", linewidth=0.8, alpha=0.6)
            ax.axhline(0.0, color="gray", linewidth=0.6, alpha=0.5)
            ax.set_ylabel("Delta(t)")
            ax.set_title(f"zero {j}, gamma={zero_gamma[j]:.6f}, W={row['W_j']:.6g}", fontsize=9)
            ax.grid(True, alpha=0.2)
        axes[-1].set_xlabel("t - gamma_j")
        fig.suptitle(f"N={n_size}: Delta around five largest local improvements", y=0.995)
        fig.tight_layout()
        fig.savefig(HERE / f"part_b_N{n_size}_top5_delta.png", dpi=170)
        plt.close(fig)


def write_results(
    grid: np.ndarray,
    zeta_values: np.ndarray,
    integrands: dict[int, dict[str, np.ndarray]],
    zero_metadata: list[dict],
    heads_by_level: dict[int, dict[int, dict[str, float]]],
    w_by_level: dict[int, dict[int, np.ndarray]],
    convergence: dict,
    source_sha256: str,
    coefficients: dict[int, tuple[np.ndarray, np.ndarray, np.ndarray]],
) -> tuple[dict[int, list[dict]], list[dict], float, float]:
    inv_derivative = np.asarray([1.0 / row["derivative_abs"] for row in zero_metadata])
    inv_derivative_sq = inv_derivative**2
    local_min_gap = np.asarray([row["local_min_gap"] for row in zero_metadata])
    rng = np.random.default_rng(PERMUTATION_SEED)
    permutations = np.asarray([rng.permutation(len(zero_metadata)) for _ in range(N_PERMUTATIONS)])

    per_zero_rows: list[dict] = []
    judges_by_n: dict[int, list[dict]] = {}
    for n_size in N_VALUES:
        w = w_by_level[max(w_by_level)][n_size]
        inv_rank = rankdata(-inv_derivative, method="average")
        w_rank = rankdata(-w, method="average")
        for i, zero in enumerate(zero_metadata):
            row = {
                "N": n_size,
                "zero_index": zero["zero_index"],
                "gamma": zero["gamma"],
                "gamma_mp": zero["gamma_mp"],
                "zeta_prime_abs": zero["derivative_abs"],
                "derivative_abs_mp": zero["derivative_abs_mp"],
                "gap_prev": zero["gap_prev"],
                "gap_next": zero["gap_next"],
                "local_min_gap": zero["local_min_gap"],
                "inverse_gap_secondary": 1.0 / zero["local_min_gap"],
                "inverse_derivative": inv_derivative[i],
                "inverse_derivative_sq": inv_derivative_sq[i],
                "inverse_derivative_rank": inv_rank[i],
                "cell_left": zero["cell_left"],
                "cell_right": zero["cell_right"],
                "W_j": float(w[i]),
                "W_rank": w_rank[i],
            }
            per_zero_rows.append(row)
        judges_by_n[n_size] = permutation_judges(w, inv_derivative_sq, local_min_gap, permutations)

    per_zero_header = [
        "N",
        "zero_index",
        "gamma",
        "gamma_mp",
        "zeta_prime_abs",
        "derivative_abs_mp",
        "gap_prev",
        "gap_next",
        "local_min_gap",
        "inverse_gap_secondary",
        "inverse_derivative",
        "inverse_derivative_sq",
        "inverse_derivative_rank",
        "cell_left",
        "cell_right",
        "W_j",
        "W_rank",
    ]
    write_csv(
        PER_ZERO_PATH,
        per_zero_header,
        ([row[k] for k in per_zero_header] for row in per_zero_rows),
    )

    j4_rows = []
    for n_size, tests in judges_by_n.items():
        for test in tests:
            j4_rows.append({"N": n_size, **test})
    j4_header = [
        "N",
        "variable",
        "rho",
        "permutation_p_two_sided",
        "null95_low",
        "null95_high",
        "null_abs_max",
        "permutations",
        "seed",
    ]
    write_csv(HERE / "part_b_j4.csv", j4_header, ([r[k] for k in j4_header] for r in j4_rows))

    secondary_rows = []
    for n_size, tests in judges_by_n.items():
        raw_gap_rho = next(row["rho"] for row in tests if row["variable"] == "raw_local_min_gap")
        secondary_rows.append(
            {
                "N": n_size,
                "variable": "inverse_local_min_gap_secondary",
                "rho": -raw_gap_rho,
                "interpretation": "strictly decreasing transform of positive raw gap; descriptive only",
            }
        )
    secondary_header = ["N", "variable", "rho", "interpretation"]
    write_csv(
        HERE / "part_b_secondary.csv",
        secondary_header,
        ([row[k] for k in secondary_header] for row in secondary_rows),
    )

    head_rows = []
    for n_size in N_VALUES:
        row = {"N": n_size}
        for level in sorted(heads_by_level):
            row[f"Iopt_head_{level}"] = heads_by_level[level][n_size]["opt"]
            row[f"Ia_head_{level}"] = heads_by_level[level][n_size]["taper"]
        head_rows.append(row)
    head_header = ["N"] + [f"{kind}_head_{level}" for level in sorted(heads_by_level) for kind in ("Iopt", "Ia")]
    write_csv(
        HERE / "part_b_weighted_head.csv",
        head_header,
        ([row.get(k, "") for k in head_header] for row in head_rows),
    )

    top_rows = []
    for n_size in N_VALUES:
        rows = [r for r in per_zero_rows if r["N"] == n_size]
        for row in sorted(rows, key=lambda r: (-r["W_j"], r["zero_index"]))[:20]:
            top_rows.append({"N": n_size, **{k: row[k] for k in per_zero_header if k != "N"}})
    top_header = ["N"] + [k for k in per_zero_header if k != "N"]
    write_csv(HERE / "part_b_top20.csv", top_header, ([r.get(k, "") for k in top_header] for r in top_rows))

    save_t_grid(grid, zeta_values, integrands)
    plot_outputs(grid, integrands, zero_metadata, per_zero_rows, judges_by_n)

    zero_t_mask = np.zeros(grid.size, dtype=bool)
    for row in zero_metadata:
        pos = int(np.searchsorted(grid, row["gamma"]))
        if pos < grid.size and grid[pos] == row["gamma"]:
            zero_t_mask[pos] = True
    zero_delta_max = max(
        float(np.max(np.abs(integrands[n_size]["delta"][zero_t_mask]))) for n_size in N_VALUES
    )
    d_one_max = max(
        float(
            np.max(
                np.abs(
                    coefficients[n_size][1]
                    * (1.0 / coefficients[n_size][0] - 1.0 / coefficients[n_size][0])
                )
            )
        )
        for n_size in N_VALUES
    )
    if zero_delta_max > 1e-10:
        raise RuntimeError(f"deltaI at zero ordinates failed sanity check: {zero_delta_max:.3e}")
    if d_one_max != 0.0:
        raise RuntimeError(f"centered polynomial D(1) failed exact sanity check: {d_one_max:.3e}")

    prereg = read_json(PREREG_PATH)
    run_result = {
        "method": "direct mpmath zeta on an adaptive zero-cell grid; complex128 coefficient polynomial; nested Simpson",
        "mpmath_dps": 20,
        "archived_coefficients_commit": ZERO_COMMIT,
        "archived_coefficients_path": COEFF_PATH,
        "archived_coefficients_blob": COEFF_BLOB,
        "archived_coefficients_sha256": source_sha256,
        "physical_c_opt": "negative of archived stored c, for n=2..N",
        "mobius_taper": "mu(n)*log(N/n)/log(N), for n=2..N",
        "centering": "D(s)=sum_{n=2}^N c_n*(n**(-s)-1/n); D(1)=0",
        "zero_count_le_1000": len(zero_metadata),
        "next_neighbor_gamma": zero_metadata[-1]["next_gamma"],
        "grid_unique_points": int(grid.size),
        "initial_simpson_subdivisions_per_half_cell": 16,
        "base_fine_simpson_subdivisions_per_half_cell": 32,
        "final_simpson_subdivisions_per_segment": max(w_by_level),
        "convergence_thresholds": {
            "weighted_head_scaled_abs_max": HEAD_SCALED_ABS_TOL,
            "local_W_scaled_abs_max": LOCAL_W_SCALED_ABS_TOL,
            "local_spearman_abs_max": CORRELATION_TOL,
        },
        "convergence_observed": convergence,
        "t_zero_split": "first left half-cell split at t=1 and thereafter into pieces of width <=1 to resolve the broad first cell and weight",
        "cell_convention": prereg["zeros"],
        "weight": "one-sided full-line head = (1/pi)*integral_0^1000 I_D(t)/(1/4+t^2) dt",
        "j4_permutations": N_PERMUTATIONS,
        "j4_seed": PERMUTATION_SEED,
        "j4_p_value": "(1 + count(abs(null)>=abs(observed)))/(1001), two-sided",
        "secondary_inverse_gap": "descriptive Spearman rho only; no additional permutation claim test",
        "D1_max_termwise_centering_residual": d_one_max,
        "deltaI_max_abs_at_zero_ordinates": zero_delta_max,
        "j3_tail_bound": "not computed by part_b.py; report remains truncated at T=1000",
        "rigor": "numerical quadrature only; not interval-certified",
    }
    RUN_JSON.write_text(json.dumps(run_result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return judges_by_n, per_zero_rows, d_one_max, zero_delta_max


def write_report(
    zero_metadata: list[dict],
    heads_by_level: dict[int, dict[int, dict[str, float]]],
    w_by_level: dict[int, dict[int, np.ndarray]],
    convergence: dict,
    judges_by_n: dict[int, list[dict]],
    per_zero_rows: list[dict],
    grid_size: int,
    zero_delta_max: float,
) -> None:
    final_level = max(w_by_level)
    lines = [
        "# Part B — t-side zero localization",
        "",
        "## Definitions and source convention",
        "",
        "For each N in {500, 1000, 2000, 5000}, coefficients were loaded directly from the pinned archived `part_a_coefficients.csv` Git object (commit `ba5654b46adf84159702748b006699bafa0ed89b`, blob `7baa38bc0f5a9437e985f739aecb823ec2dedf1a`). The physical free coefficients are `c_opt = -stored_c` for n=2..N. The comparator is `a_n = mu(n) log(N/n)/log N`, also for n=2..N.",
        "",
        "Both polynomials use the preregistered centering `D(s) = sum c_n (n^(-s) - 1/n)`, which gives `D(1)=0`. The intensity is `I_D(t)=|1-zeta(1/2+it)D(1/2+it)|^2`, and `Delta(t)=I_a(t)-I_opt(t)`. Positive W_j therefore means the taper has larger local squared error than the optimum.",
        "",
        "## Zero cells, grid, and quadrature",
        "",
        f"mpmath was run at 20 decimal digits. The script found {len(zero_metadata)} positive zero ordinates at or below 1000 and computed one following zero for the last local gap. The unique sorted grid has {grid_size} points at the final refinement. Each zero cell uses midpoint boundaries, with the first cell starting at 0 and the final included cell ending at 1000; the first left half-cell is additionally split at t=1. The first minimum gap uses only its next gap. The local minimum gap for later zeros is the minimum of the preceding and following gaps.",
        "",
        f"Each half-cell initially used nested composite Simpson rules with 16 and 32 subdivisions. To resolve the unusually wide first left half-cell, t=0..1 is split explicitly and the rest of that half-cell is split into segments of width at most 1 before Simpson integration. Material discrepancy was pre-defined as a scaled absolute difference above {HEAD_SCALED_ABS_TOL:g} for a weighted head (difference divided by max(1, |fine head|)), a scaled absolute difference above {LOCAL_W_SCALED_ABS_TOL:g} for a W_j (difference divided by max(1, max|W|)), or an absolute Spearman change above {CORRELATION_TOL:g}; the segmented grid is refined uniformly to 64 and, if needed, 128 subdivisions. The final measured convergence summary is `{json.dumps(convergence, sort_keys=True)}`.",
        "",
        "Zeta values were evaluated directly with `mpmath.zeta` at every unique grid point; the finite Dirichlet polynomials were evaluated in complex128. The quadrature and double-precision polynomial values are numerical diagnostics, not interval-certified enclosures.",
        "",
        "## J3 — continuous head",
        "",
        "R7 B §2 gives the exact Mellin–Parseval identity for the full-line norm of the centered residual. By conjugation symmetry, the computed one-sided head is `(1/pi) integral_0^1000 I_D(t)/(1/4+t^2) dt`. Values below are truncated heads only. The exact identity is not a claim that the finite head equals the complete norm; a separately derived tail bound is required, and the difference between a discrete norm and this head was not used as a tail estimate.",
        "",
        "| N | D | Simpson 16 | Simpson 32 | final refinement |",
        "|---:|:---|---:|---:|---:|",
    ]
    for n_size in N_VALUES:
        for kind, label in (("opt", "optimal"), ("taper", "Mobius taper")):
            vals = [heads_by_level[level][n_size][kind] for level in sorted(heads_by_level)]
            first = vals[0]
            second = vals[1] if len(vals) > 1 else vals[0]
            last = vals[-1]
            lines.append(f"| {n_size} | {label} | {first:.12g} | {second:.12g} | {last:.12g} |")
    lines.extend(
        [
            "",
            "The independently derived J3 tail bound is tracked outside this Part B computation and must be merged before treating these as full-line norm enclosures. No RH conclusion follows from this finite numerical head.",
            "",
            f"Sanity checks: `D(1)=0` by the centering identity (the code's maximum termwise residual is {0.0:.1e}); measured `max |Delta(gamma_j)| = {zero_delta_max:.3e}` on the zero-ordinate grid.",
            "",
            "## J4 — zero-label permutation null",
            "",
            "For each N, the observed Spearman correlations use W_j against `1/|zeta'(rho_j)|^2` and against the raw local minimum gap. The two-sided empirical permutation p-value is `(1 + count(|rho_perm| >= |rho_obs|))/1001`. The 1000 permutations use NumPy `default_rng(20261106)` and the same label permutations for both predictors and all N. A correlation within the central 95% null band is not evidence.",
            "",
            "| N | variable | rho | null 95% | p |",
            "|---:|:---|---:|:---:|---:|",
        ]
    )
    for n_size in N_VALUES:
        for row in judges_by_n[n_size]:
            lines.append(
                f"| {n_size} | {row['variable']} | {row['rho']:.6f} | [{row['null95_low']:.6f}, {row['null95_high']:.6f}] | {row['permutation_p_two_sided']:.4g} |"
            )
    lines.extend(
        [
            "",
            "The preregistered inverse-gap correlation is reported separately as descriptive secondary output. Since every local gap is positive and the reciprocal is a strictly decreasing transform, its Spearman rho is the negative of the raw-gap rho; no additional hypothesis test or p-value is attached.",
            "",
            "| N | secondary variable | rho |",
            "|---:|:---|---:|",
        ]
    )
    for n_size in N_VALUES:
        raw_gap_rho = next(row["rho"] for row in judges_by_n[n_size] if row["variable"] == "raw_local_min_gap")
        lines.append(f"| {n_size} | inverse local minimum gap | {-raw_gap_rho:.6f} |")
    q5_derivative = next(row for row in judges_by_n[5000] if row["variable"] == "inverse_derivative_squared")
    q6_raw_gap = next(row for row in judges_by_n[5000] if row["variable"] == "raw_local_min_gap")
    q5_hit = q5_derivative["rho"] >= 0.3 and q5_derivative["permutation_p_two_sided"] < 0.01
    q6_hit = (
        q6_raw_gap["rho"] != 0
        and q5_derivative["rho"] != 0
        and math.copysign(1, q6_raw_gap["rho"]) == math.copysign(1, q5_derivative["rho"])
        and q6_raw_gap["permutation_p_two_sided"] < 0.01
    )
    lines.extend(
        [
            "",
            "## Preregistered Part B prediction scores",
            "",
            f"- Q5: {'HIT' if q5_hit else 'MISS'} — at N=5000, rho(W, 1/|zeta prime|^2)={q5_derivative['rho']:.6f}, p={q5_derivative['permutation_p_two_sided']:.4g}; the preregistered thresholds were rho>=0.3 and p<0.01.",
            f"- Q6: {'HIT' if q6_hit else 'MISS'} — at N=5000, raw-gap rho={q6_raw_gap['rho']:.6f} versus Q5 rho={q5_derivative['rho']:.6f}, p={q6_raw_gap['permutation_p_two_sided']:.4g}; same nonzero sign and p<0.01 were required.",
        ]
    )
    lines.extend(["", "## Largest local improvements", ""])
    for n_size in N_VALUES:
        rows = [row for row in per_zero_rows if row["N"] == n_size]
        top = sorted(rows, key=lambda row: (-row["W_j"], row["zero_index"]))[:20]
        lines.extend(
            [
                f"### N={n_size}",
                "",
                "| rank W | zero j | gamma | W_j | abs zeta prime | previous gap | next gap | local min gap | rank inverse abs zeta prime |",
                "|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
            ]
        )
        for row in top:
            prev = "—" if not math.isfinite(row["gap_prev"]) else f"{row['gap_prev']:.8g}"
            lines.append(
                f"| {int(row['W_rank'])} | {row['zero_index']} | {row['gamma']:.9f} | {row['W_j']:.10g} | {row['zeta_prime_abs']:.9g} | {prev} | {row['gap_next']:.8g} | {row['local_min_gap']:.8g} | {int(row['inverse_derivative_rank'])} |"
            )
        lines.append("")
    lines.extend(
        [
            "## Output files and truncations",
            "",
            "- `per_zero.csv`: one row per N and zero gamma_j <= 1000, including |zeta'|, adjacent gaps, W_j, and both ranks.",
            "- `t_grid.csv.gz`: every unique direct-zeta grid point, all four Delta profiles, and the two intensities per N.",
            "- `part_b_j4.csv`: observed correlations, permutation p-values, and 95% null bands.",
            "- `part_b_secondary.csv`: preregistered descriptive inverse-gap Spearman values, without extra p-value claims.",
            "- `part_b_weighted_head.csv`: nested Simpson head values.",
            "- `part_b_top20.csv`: top twenty W_j rows for each N.",
            "- Eight PNG plots: W versus inverse derivative squared and Delta around the five largest W_j zeros, separately for each N.",
            "",
            "Truncations: t is restricted to [0,1000]; zero ordinates are restricted to gamma<=1000 with one next neighbor for gap metadata; coefficient vectors contain only n=2..N; no uncomputed tail is inferred from discrete-minus-head. Q5/Q6 are localization diagnostics, not causal claims or RH evidence.",
            "",
        ]
    )
    (HERE / "PART_B.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preflight", action="store_true", help="verify preregistered pins and coefficient inputs only")
    args = parser.parse_args()

    source_text = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{ZERO_COMMIT}:{COEFF_PATH}"],
        check=True,
        capture_output=True,
    ).stdout
    import hashlib

    source_sha256 = hashlib.sha256(source_text).hexdigest()
    coefficients = load_archived_coefficients()
    d_one_max = max(
        float(
            np.max(
                np.abs(
                    coefficients[n_size][1]
                    * (1.0 / coefficients[n_size][0] - 1.0 / coefficients[n_size][0])
                )
            )
        )
        for n_size in N_VALUES
    )
    print(
        f"[preflight] archived_blob={COEFF_BLOB} sha256={source_sha256} Ns={','.join(map(str, N_VALUES))} D1_max={d_one_max:.1e}",
        file=sys.stderr,
        flush=True,
    )
    if args.preflight:
        return

    zeros = load_zeros()
    segments, zero_metadata = build_segments(zeros)
    deriv = np.asarray([row["derivative_abs"] for row in zero_metadata])
    inv_d2 = 1.0 / (deriv * deriv)
    gaps = np.asarray([row["local_min_gap"] for row in zero_metadata])

    converged = False
    convergence = {}
    previous_heads = None
    previous_w = None
    final_grid = None
    final_zeta = None
    final_integrands = None
    heads_by_level: dict[int, dict[int, dict[str, float]]] = {}
    w_by_level: dict[int, dict[int, np.ndarray]] = {}
    for level in REFINEMENT_LEVELS:
        grid = collect_grid(segments, level)
        zeta_values = evaluate_zeta_grid(grid, zeros)
        integrands = evaluate_intensities(grid, zeta_values, coefficients)
        heads, local_w = compute_integrals(grid, integrands, segments, zero_metadata, level, level)
        if level == INITIAL_INTERVALS:
            coarse_heads, coarse_w = compute_integrals(
                grid, integrands, segments, zero_metadata, 16, level
            )
            heads_by_level[16] = coarse_heads
            w_by_level[16] = coarse_w
            heads_by_level[level] = heads
            w_by_level[level] = local_w
            convergence = convergence_metrics(coarse_heads, heads, coarse_w, local_w, inv_d2, gaps)
            print(f"[convergence] intervals=16->32 metrics={json.dumps(convergence, sort_keys=True)}", file=sys.stderr, flush=True)
            if (
                convergence["head_scaled_abs_max"] <= HEAD_SCALED_ABS_TOL
                and convergence["local_w_scaled_abs_max"] <= LOCAL_W_SCALED_ABS_TOL
                and convergence["local_spearman_abs_max"] <= CORRELATION_TOL
            ):
                converged = True
                final_grid, final_zeta, final_integrands = grid, zeta_values, integrands
                break
        else:
            heads_by_level[level] = heads
            w_by_level[level] = local_w
        final_grid, final_zeta, final_integrands = grid, zeta_values, integrands
        if previous_heads is not None and previous_w is not None:
            convergence = convergence_metrics(previous_heads, heads, previous_w, local_w, inv_d2, gaps)
            print(f"[convergence] intervals={level} metrics={json.dumps(convergence, sort_keys=True)}", file=sys.stderr, flush=True)
            if (
                convergence["head_scaled_abs_max"] <= HEAD_SCALED_ABS_TOL
                and convergence["local_w_scaled_abs_max"] <= LOCAL_W_SCALED_ABS_TOL
                and convergence["local_spearman_abs_max"] <= CORRELATION_TOL
            ):
                converged = True
                break
        previous_heads, previous_w = heads, local_w
    if final_grid is None or final_zeta is None or final_integrands is None:
        raise RuntimeError("no integration grid was evaluated")
    # Ensure the reported convergence compares the last two evaluated nested levels.
    level_numbers = sorted(heads_by_level)
    if len(level_numbers) >= 2:
        convergence = convergence_metrics(
            heads_by_level[level_numbers[-2]],
            heads_by_level[level_numbers[-1]],
            w_by_level[level_numbers[-2]],
            w_by_level[level_numbers[-1]],
            inv_d2,
            gaps,
        ) | {"compared_intervals": level_numbers[-2:]}
    elif not convergence:
        convergence = {"compared_intervals": [], "note": "only one level was needed to establish available grid"}
    convergence["converged"] = converged
    convergence["max_refinement_reached"] = not converged and max(w_by_level) >= REFINEMENT_LEVELS[-1]

    judges_by_n, per_zero_rows, _d_one_max, zero_delta_max = write_results(
        final_grid,
        final_zeta,
        final_integrands,
        zero_metadata,
        heads_by_level,
        w_by_level,
        convergence,
        source_sha256,
        coefficients,
    )
    write_report(
        zero_metadata,
        heads_by_level,
        w_by_level,
        convergence,
        judges_by_n,
        per_zero_rows,
        final_grid.size,
        zero_delta_max,
    )
    for checkpoint in (ZERO_CHECKPOINT, ZETA_CHECKPOINT):
        if checkpoint.exists():
            checkpoint.unlink()
    print(
        f"[done] zeros={len(zero_metadata)} points={final_grid.size} final_intervals={max(w_by_level)} convergence={json.dumps(convergence, sort_keys=True)}",
        file=sys.stderr,
        flush=True,
    )


if __name__ == "__main__":
    main()
