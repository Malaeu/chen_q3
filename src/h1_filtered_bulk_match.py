#!/usr/bin/env python3
r"""
Numerical filtered-bulk diagnostics for the direct H1^f bridge.

We compare the filtered Suzuki blocks

    M_{mn}^{σ τ}(a)
      = w_{eps_σ m, eps_τ n}(a)
      + w_{eps_σ (m+1), eps_τ n}(a)
      + w_{eps_σ m, eps_τ (n+1)}(a)
      + w_{eps_σ (m+1), eps_τ (n+1)}(a)

against the filtered Q3 blocks

    \tilde q_{mn}^{σ τ}
      = q_{eps_σ m, eps_τ n}
      + q_{eps_σ (m+1), eps_τ n}
      + q_{eps_σ m, eps_τ (n+1)}
      + q_{eps_σ (m+1), eps_τ (n+1)}.

The live H1^f target is the direct filtered bulk match on the two primary
families:

    (++): M_{mn}^{++}(a) = kappa(a) \tilde q_{mn}^{++}
    (+-): M_{mn}^{+-}(a) = kappa(a) \tilde q_{mn}^{+-}

The remaining filtered blocks are formal Hermitian consequences.

This script now has two diagnostic layers:

1. entrywise mismatch maps and low-rank / low-mode summaries;
2. cap-defect classifier:
   compare the leading defect subspaces between `++` and `+-`,
   and across runs in `(a,M,zeros)`, to see whether the residual behaves like
   a common finite-dimensional cap-space or only like a family-dependent
   structured correction.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

import mpmath as mp
import numpy as np

from h1_raw_bulk_match import (
    QConvention,
    WConvention,
    fit_kappa,
    q_conventions,
    q_rs,
    residual_metrics,
    w_conventions,
    w_rs,
)
from h1_raw_operator_sanity import active_prime_nodes, arch_coefficients


EPSILON = {"+": +1, "-": -1}
DEFAULT_SWEEP_A = (0.75, 1.0, 1.25)
DEFAULT_SWEEP_M = (2, 3, 4)
DEFAULT_SWEEP_ZEROS = (10, 20)
TOP_K = 5
LOW_MODE_CUTOFF = 1
DEFAULT_DEFECT_RANK = 2


@dataclass(frozen=True)
class FilteredSample:
    family: str
    m: int
    n: int
    q: complex
    w: complex


@dataclass(frozen=True)
class BucketStats:
    count: int
    avg_abs: float
    max_abs: float
    share_total_abs: float


@dataclass(frozen=True)
class LowRankStats:
    size: int
    fro_norm: float
    rank1_relative_residual: float
    rank2_relative_residual: float
    sv1_energy_share: float
    sv12_energy_share: float
    top_left_1_share: float
    top_left_2_share: float


@dataclass(frozen=True)
class LowModeStats:
    size: int
    fro_norm: float
    low_union_1_relative_residual: float
    low_union_2_relative_residual: float
    low_union_3_relative_residual: float
    low_union_1_share: float
    low_union_2_share: float
    low_union_3_share: float


@dataclass
class DefectBasis:
    family: str
    size: int
    rank: int
    singular_values: np.ndarray
    left_basis: np.ndarray
    right_basis: np.ndarray
    matrix: np.ndarray


@dataclass(frozen=True)
class DefectSubspaceStats:
    source_family: str
    target_family: str
    defect_rank: int
    column_alignment: float
    row_alignment: float
    transfer_relative_residual: float


@dataclass(frozen=True)
class RunResult:
    run_id: str
    q_convention: str
    w_convention: str
    samples: list[FilteredSample]
    family_kappa: dict[str, complex]
    family_metrics: dict[str, dict[str, float]]
    family_low_rank: dict[str, LowRankStats]
    family_low_mode: dict[str, LowModeStats]
    family_defect_basis: dict[str, DefectBasis]
    cross_family_stats: list[DefectSubspaceStats]
    joint_kappa: complex
    joint_metrics: dict[str, float]


def filtered_block_q(
    m: int,
    n: int,
    sigma: str,
    tau: str,
    A: dict[int, complex],
    nodes,
    q_convention: QConvention,
) -> complex:
    eps_sigma = EPSILON[sigma]
    eps_tau = EPSILON[tau]
    return (
        q_rs(eps_sigma * m, eps_tau * n, A, nodes, q_convention)
        + q_rs(eps_sigma * (m + 1), eps_tau * n, A, nodes, q_convention)
        + q_rs(eps_sigma * m, eps_tau * (n + 1), A, nodes, q_convention)
        + q_rs(eps_sigma * (m + 1), eps_tau * (n + 1), A, nodes, q_convention)
    )


def filtered_block_w(
    a: float,
    m: int,
    n: int,
    sigma: str,
    tau: str,
    zeros: int,
    w_convention: WConvention,
) -> complex:
    eps_sigma = EPSILON[sigma]
    eps_tau = EPSILON[tau]
    return (
        w_rs(a, eps_sigma * m, eps_tau * n, zeros, w_convention)
        + w_rs(a, eps_sigma * (m + 1), eps_tau * n, zeros, w_convention)
        + w_rs(a, eps_sigma * m, eps_tau * (n + 1), zeros, w_convention)
        + w_rs(a, eps_sigma * (m + 1), eps_tau * (n + 1), zeros, w_convention)
    )


def collect_filtered_samples(
    M: int,
    a: float,
    A: dict[int, complex],
    nodes,
    zeros: int,
    q_convention: QConvention,
    w_convention: WConvention,
) -> list[FilteredSample]:
    samples: list[FilteredSample] = []
    for m in range(1, M + 1):
        for n in range(1, M + 1):
            samples.append(
                FilteredSample(
                    "++",
                    m,
                    n,
                    filtered_block_q(m, n, "+", "+", A, nodes, q_convention),
                    filtered_block_w(a, m, n, "+", "+", zeros, w_convention),
                )
            )
            samples.append(
                FilteredSample(
                    "+-",
                    m,
                    n,
                    filtered_block_q(m, n, "+", "-", A, nodes, q_convention),
                    filtered_block_w(a, m, n, "+", "-", zeros, w_convention),
                )
            )
    return samples


def sample_abs_residual(sample: FilteredSample, kappa: complex) -> float:
    return abs(sample.w - kappa * sample.q)


def sample_relative_residual(sample: FilteredSample, kappa: complex) -> float:
    scale = max(abs(sample.q), abs(sample.w), 1.0)
    return sample_abs_residual(sample, kappa) / scale


def bucket_stats(
    samples: list[FilteredSample],
    kappa: complex,
    predicate,
) -> BucketStats:
    total_abs = sum(sample_abs_residual(sample, kappa) for sample in samples)
    bucket = [sample for sample in samples if predicate(sample)]
    if not bucket:
        return BucketStats(0, 0.0, 0.0, 0.0)
    bucket_residuals = [sample_abs_residual(sample, kappa) for sample in bucket]
    return BucketStats(
        count=len(bucket),
        avg_abs=float(sum(bucket_residuals) / len(bucket_residuals)),
        max_abs=float(max(bucket_residuals)),
        share_total_abs=float(sum(bucket_residuals) / total_abs) if total_abs else 0.0,
    )


def top_offenders(
    samples: list[FilteredSample],
    kappa: complex,
    top_k: int = TOP_K,
) -> list[tuple[FilteredSample, float, float]]:
    ranked = [
        (sample, sample_abs_residual(sample, kappa), sample_relative_residual(sample, kappa))
        for sample in samples
    ]
    ranked.sort(key=lambda item: item[2], reverse=True)
    return ranked[:top_k]


def format_complex(z: complex) -> str:
    return f"{z.real:.12e}  + {z.imag:.12e}i"


def family_residual_matrix(samples: list[FilteredSample], family: str, kappa: complex) -> np.ndarray:
    family_samples = [sample for sample in samples if sample.family == family]
    size = max(sample.m for sample in family_samples)
    matrix = np.zeros((size, size), dtype=np.complex128)
    for sample in family_samples:
        matrix[sample.m - 1, sample.n - 1] = sample.w - kappa * sample.q
    return matrix


def safe_ratio(num: float, den: float) -> float:
    return num / den if den else 0.0


def low_rank_stats(samples: list[FilteredSample], family: str, kappa: complex) -> LowRankStats:
    matrix = family_residual_matrix(samples, family, kappa)
    size = matrix.shape[0]
    fro_sq = float(np.linalg.norm(matrix, ord="fro") ** 2)
    if fro_sq == 0.0:
        return LowRankStats(size, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
    singular_values = np.linalg.svd(matrix, compute_uv=False)
    sv_sq = np.abs(singular_values) ** 2
    rank1_sq = float(sv_sq[0]) if len(sv_sq) >= 1 else 0.0
    rank2_sq = float(np.sum(sv_sq[:2])) if len(sv_sq) >= 2 else rank1_sq
    top_left_1_sq = float(np.linalg.norm(matrix[:1, :1], ord="fro") ** 2)
    block2 = min(2, size)
    top_left_2_sq = float(np.linalg.norm(matrix[:block2, :block2], ord="fro") ** 2)
    return LowRankStats(
        size=size,
        fro_norm=math.sqrt(fro_sq),
        rank1_relative_residual=math.sqrt(max(fro_sq - rank1_sq, 0.0) / fro_sq),
        rank2_relative_residual=math.sqrt(max(fro_sq - rank2_sq, 0.0) / fro_sq),
        sv1_energy_share=safe_ratio(rank1_sq, fro_sq),
        sv12_energy_share=safe_ratio(rank2_sq, fro_sq),
        top_left_1_share=safe_ratio(top_left_1_sq, fro_sq),
        top_left_2_share=safe_ratio(top_left_2_sq, fro_sq),
    )


def low_mode_stats(samples: list[FilteredSample], family: str, kappa: complex) -> LowModeStats:
    matrix = family_residual_matrix(samples, family, kappa)
    size = matrix.shape[0]
    fro_sq = float(np.linalg.norm(matrix, ord="fro") ** 2)
    if fro_sq == 0.0:
        return LowModeStats(size, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)

    def union_share(k: int) -> float:
        cutoff = min(k, size)
        mask = np.zeros((size, size), dtype=bool)
        mask[:cutoff, :] = True
        mask[:, :cutoff] = True
        masked_sq = float(np.linalg.norm(matrix * mask, ord="fro") ** 2)
        return safe_ratio(masked_sq, fro_sq)

    share1 = union_share(1)
    share2 = union_share(2)
    share3 = union_share(3)
    return LowModeStats(
        size=size,
        fro_norm=math.sqrt(fro_sq),
        low_union_1_relative_residual=math.sqrt(max(1.0 - share1, 0.0)),
        low_union_2_relative_residual=math.sqrt(max(1.0 - share2, 0.0)),
        low_union_3_relative_residual=math.sqrt(max(1.0 - share3, 0.0)),
        low_union_1_share=share1,
        low_union_2_share=share2,
        low_union_3_share=share3,
    )


def defect_basis(
    samples: list[FilteredSample],
    family: str,
    kappa: complex,
    defect_rank: int,
) -> DefectBasis:
    matrix = family_residual_matrix(samples, family, kappa)
    U, singular_values, Vh = np.linalg.svd(matrix, full_matrices=False)
    rank = min(defect_rank, len(singular_values))
    return DefectBasis(
        family=family,
        size=matrix.shape[0],
        rank=rank,
        singular_values=singular_values,
        left_basis=U[:, :rank],
        right_basis=Vh.conj().T[:, :rank],
        matrix=matrix,
    )


def resize_basis(basis: np.ndarray, target_size: int) -> np.ndarray:
    rows, cols = basis.shape
    if rows == target_size:
        return basis
    if rows < target_size:
        pad = np.zeros((target_size - rows, cols), dtype=basis.dtype)
        return np.vstack([basis, pad])
    truncated = basis[:target_size, :]
    if truncated.size == 0:
        return truncated
    q, r = np.linalg.qr(truncated)
    diag = np.abs(np.diag(r))
    keep = diag > 1e-12
    if not np.any(keep):
        return np.zeros((target_size, 0), dtype=basis.dtype)
    return q[:, keep]


def subspace_alignment_score(source: np.ndarray, target: np.ndarray) -> float:
    common = min(source.shape[1], target.shape[1])
    if common == 0:
        return 0.0
    gram = source.conj().T @ target
    singular_values = np.linalg.svd(gram, compute_uv=False)
    return float(np.sum(np.abs(singular_values[:common]) ** 2) / common)


def transfer_relative_residual(
    source_left: np.ndarray,
    source_right: np.ndarray,
    target_matrix: np.ndarray,
) -> float:
    if source_left.shape[1] == 0 or source_right.shape[1] == 0:
        return 1.0
    approx = source_left @ (source_left.conj().T @ target_matrix @ source_right) @ source_right.conj().T
    target_norm = float(np.linalg.norm(target_matrix, ord="fro"))
    if target_norm == 0.0:
        return 0.0
    residual_norm = float(np.linalg.norm(target_matrix - approx, ord="fro"))
    return residual_norm / target_norm


def compare_defect_bases(source: DefectBasis, target: DefectBasis) -> DefectSubspaceStats:
    left = resize_basis(source.left_basis, target.size)
    right = resize_basis(source.right_basis, target.size)
    return DefectSubspaceStats(
        source_family=source.family,
        target_family=target.family,
        defect_rank=min(source.rank, target.rank),
        column_alignment=subspace_alignment_score(left, target.left_basis),
        row_alignment=subspace_alignment_score(right, target.right_basis),
        transfer_relative_residual=transfer_relative_residual(left, right, target.matrix),
    )


def print_bucket_report(label: str, stats: BucketStats) -> None:
    print(
        f"  {label:<18s} count={stats.count:3d}  "
        f"avg={stats.avg_abs:.3e}  max={stats.max_abs:.3e}  share={stats.share_total_abs:.3f}"
    )


def print_family_report(
    samples: list[FilteredSample],
    family: str,
    kappa: complex,
    low_rank: LowRankStats,
    low_mode: LowModeStats,
) -> None:
    family_samples = [sample for sample in samples if sample.family == family]
    metrics = residual_metrics(family_samples, kappa)
    print(f"[{family}]")
    print(f"  fitted kappa:           {format_complex(kappa)}")
    print(f"  max |residual|:         {metrics['max_abs_residual']:.3e}")
    print(f"  RMS residual:           {metrics['rms_residual']:.3e}")
    print(f"  relative max residual:  {metrics['relative_max_residual']:.3e}")
    print("  low-rank residual fit:")
    print(
        f"    rank-1 rel residual:  {low_rank.rank1_relative_residual:.3e}  "
        f"(sv1 share={low_rank.sv1_energy_share:.3f})"
    )
    print(
        f"    rank-2 rel residual:  {low_rank.rank2_relative_residual:.3e}  "
        f"(sv1+sv2 share={low_rank.sv12_energy_share:.3f})"
    )
    print(
        f"    top-left 1x1 share:   {low_rank.top_left_1_share:.3f}  "
        f"top-left 2x2 share: {low_rank.top_left_2_share:.3f}"
    )
    print("  low-mode support fit:")
    print(
        f"    union<=1 rel resid:  {low_mode.low_union_1_relative_residual:.3e}  "
        f"(share={low_mode.low_union_1_share:.3f})"
    )
    print(
        f"    union<=2 rel resid:  {low_mode.low_union_2_relative_residual:.3e}  "
        f"(share={low_mode.low_union_2_share:.3f})"
    )
    print(
        f"    union<=3 rel resid:  {low_mode.low_union_3_relative_residual:.3e}  "
        f"(share={low_mode.low_union_3_share:.3f})"
    )
    print("  buckets:")
    print_bucket_report("diagonal", bucket_stats(family_samples, kappa, lambda s: s.m == s.n))
    print_bucket_report("off-diagonal", bucket_stats(family_samples, kappa, lambda s: s.m != s.n))
    print_bucket_report("near-diagonal", bucket_stats(family_samples, kappa, lambda s: abs(s.m - s.n) <= 1))
    print_bucket_report("far", bucket_stats(family_samples, kappa, lambda s: abs(s.m - s.n) >= 2))
    print_bucket_report(
        f"low-strip<= {LOW_MODE_CUTOFF}",
        bucket_stats(family_samples, kappa, lambda s: s.m <= LOW_MODE_CUTOFF or s.n <= LOW_MODE_CUTOFF),
    )
    print("  top offenders:")
    for sample, abs_res, rel_res in top_offenders(family_samples, kappa):
        print(
            f"    (m={sample.m}, n={sample.n})  "
            f"abs={abs_res:.3e}  rel={rel_res:.3e}"
        )


def print_cross_family_report(stats: list[DefectSubspaceStats]) -> None:
    print("[cross-family defect basis]")
    for stat in stats:
        print(
            f"  {stat.source_family} -> {stat.target_family}: "
            f"col_align={stat.column_alignment:.3f}  "
            f"row_align={stat.row_alignment:.3f}  "
            f"transfer_rel_resid={stat.transfer_relative_residual:.3e}"
        )


def search_conventions(
    M: int,
    a: float,
    A: dict[int, complex],
    nodes,
    zeros: int,
) -> list[tuple[float, str, str, complex, dict[str, float]]]:
    results = []
    for q_conv in q_conventions():
        for w_conv in w_conventions():
            samples = collect_filtered_samples(M, a, A, nodes, zeros, q_conv, w_conv)
            kappa = fit_kappa(samples)
            metrics = residual_metrics(samples, kappa)
            results.append((metrics["relative_max_residual"], q_conv.name, w_conv.name, kappa, metrics))
    results.sort(key=lambda item: item[0])
    return results


def default_csv_path() -> Path:
    timestamp = datetime.now().strftime("%Y_%m_%d_%H%M%S_%f")
    return Path("/Users/emalam/Documents/GitHub/rh_lean_01_2026/tmp") / f"h1_filtered_mismatch_map_{timestamp}.csv"


def default_subspace_csv_path(csv_path: Path) -> Path:
    return csv_path.with_name(f"{csv_path.stem}_subspace{csv_path.suffix}")


def build_rows(run: RunResult) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for sample in run.samples:
        family_kappa = run.family_kappa[sample.family]
        rows.append(
            {
                "run_id": run.run_id,
                "q_convention": run.q_convention,
                "w_convention": run.w_convention,
                "family": sample.family,
                "m": sample.m,
                "n": sample.n,
                "q_real": sample.q.real,
                "q_imag": sample.q.imag,
                "w_real": sample.w.real,
                "w_imag": sample.w.imag,
                "kappa_family_real": family_kappa.real,
                "kappa_family_imag": family_kappa.imag,
                "kappa_joint_real": run.joint_kappa.real,
                "kappa_joint_imag": run.joint_kappa.imag,
                "residual_family_abs": sample_abs_residual(sample, family_kappa),
                "residual_joint_abs": sample_abs_residual(sample, run.joint_kappa),
                "relative_residual_family": sample_relative_residual(sample, family_kappa),
                "relative_residual_joint": sample_relative_residual(sample, run.joint_kappa),
                "is_diagonal": int(sample.m == sample.n),
                "distance_from_diagonal": abs(sample.m - sample.n),
                "is_near_diagonal": int(abs(sample.m - sample.n) <= 1),
                "is_low_strip": int(sample.m <= LOW_MODE_CUTOFF or sample.n <= LOW_MODE_CUTOFF),
            }
        )
    return rows


def build_subspace_rows(
    runs: list[RunResult],
    anchor_by_family: dict[str, str] | None = None,
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    if not runs:
        return rows

    if anchor_by_family is None:
        anchor_by_family = {}
        for family in ("++", "+-"):
            best = min(runs, key=lambda run: run.family_low_rank[family].rank2_relative_residual)
            anchor_by_family[family] = best.run_id

    run_map = {run.run_id: run for run in runs}
    for run in runs:
        for family in ("++", "+-"):
            anchor_run = run_map[anchor_by_family[family]]
            anchor_basis = anchor_run.family_defect_basis[family]
            current_basis = run.family_defect_basis[family]
            stats = compare_defect_bases(anchor_basis, current_basis)
            rows.append(
                {
                    "kind": "anchor_stability",
                    "run_id": run.run_id,
                    "family": family,
                    "anchor_run_id": anchor_run.run_id,
                    "defect_rank": stats.defect_rank,
                    "column_alignment": stats.column_alignment,
                    "row_alignment": stats.row_alignment,
                    "transfer_relative_residual": stats.transfer_relative_residual,
                    "rank1_relative_residual": run.family_low_rank[family].rank1_relative_residual,
                    "rank2_relative_residual": run.family_low_rank[family].rank2_relative_residual,
                    "low_union_1_relative_residual": run.family_low_mode[family].low_union_1_relative_residual,
                    "low_union_2_relative_residual": run.family_low_mode[family].low_union_2_relative_residual,
                    "low_union_3_relative_residual": run.family_low_mode[family].low_union_3_relative_residual,
                }
            )
        for stat in run.cross_family_stats:
            rows.append(
                {
                    "kind": "cross_family",
                    "run_id": run.run_id,
                    "family": f"{stat.source_family}->{stat.target_family}",
                    "anchor_run_id": "",
                    "defect_rank": stat.defect_rank,
                    "column_alignment": stat.column_alignment,
                    "row_alignment": stat.row_alignment,
                    "transfer_relative_residual": stat.transfer_relative_residual,
                    "rank1_relative_residual": "",
                    "rank2_relative_residual": "",
                    "low_union_1_relative_residual": "",
                    "low_union_2_relative_residual": "",
                    "low_union_3_relative_residual": "",
                }
            )
    return rows


def write_rows_csv(path: Path, rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        raise ValueError("No rows to write.")
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def run_check(
    *,
    run_id: str,
    a: float,
    M: int,
    B: float,
    t: float,
    zeros: int,
    dps: int,
    grid_size: int,
    defect_rank: int,
    q_convention: QConvention,
    w_convention: WConvention,
) -> RunResult:
    mp.mp.dps = dps
    nodes = active_prime_nodes(B, t)
    A = arch_coefficients(B, t, max_k=2 * M + 2, grid_size=grid_size)
    samples = collect_filtered_samples(M, a, A, nodes, zeros, q_convention, w_convention)
    family_kappa = {
        family: fit_kappa([sample for sample in samples if sample.family == family])
        for family in ("++", "+-")
    }
    family_metrics = {
        family: residual_metrics([sample for sample in samples if sample.family == family], family_kappa[family])
        for family in ("++", "+-")
    }
    family_low_rank = {
        family: low_rank_stats(samples, family, family_kappa[family])
        for family in ("++", "+-")
    }
    family_low_mode = {
        family: low_mode_stats(samples, family, family_kappa[family])
        for family in ("++", "+-")
    }
    family_defect_basis = {
        family: defect_basis(samples, family, family_kappa[family], defect_rank)
        for family in ("++", "+-")
    }
    cross_family_stats = [
        compare_defect_bases(family_defect_basis["++"], family_defect_basis["+-"]),
        compare_defect_bases(family_defect_basis["+-"], family_defect_basis["++"]),
    ]
    joint_kappa = fit_kappa(samples)
    joint_metrics = residual_metrics(samples, joint_kappa)
    return RunResult(
        run_id=run_id,
        q_convention=q_convention.name,
        w_convention=w_convention.name,
        samples=samples,
        family_kappa=family_kappa,
        family_metrics=family_metrics,
        family_low_rank=family_low_rank,
        family_low_mode=family_low_mode,
        family_defect_basis=family_defect_basis,
        cross_family_stats=cross_family_stats,
        joint_kappa=joint_kappa,
        joint_metrics=joint_metrics,
    )


def print_run_report(
    result: RunResult,
    *,
    a: float,
    M: int,
    B: float,
    t: float,
    zeros: int,
    dps: int,
    defect_rank: int,
) -> None:
    print(f"\n[run {result.run_id}]")
    print("=" * (6 + len(result.run_id)))
    print(f"a={a}  M={M}  B={B}  t={t}  zeros={zeros}  dps={dps}  defect-rank={defect_rank}")
    print(f"baseline conventions: {result.q_convention} vs {result.w_convention}")
    print_family_report(
        result.samples,
        "++",
        result.family_kappa["++"],
        result.family_low_rank["++"],
        result.family_low_mode["++"],
    )
    print_family_report(
        result.samples,
        "+-",
        result.family_kappa["+-"],
        result.family_low_rank["+-"],
        result.family_low_mode["+-"],
    )
    print("[joint]")
    print(f"  fitted kappa:           {format_complex(result.joint_kappa)}")
    print(f"  max |residual|:         {result.joint_metrics['max_abs_residual']:.3e}")
    print(f"  RMS residual:           {result.joint_metrics['rms_residual']:.3e}")
    print(f"  relative max residual:  {result.joint_metrics['relative_max_residual']:.3e}")
    print_cross_family_report(result.cross_family_stats)


def print_anchor_stability_report(runs: list[RunResult]) -> None:
    if not runs:
        return
    print("\n[anchor stability]")
    print("==================")
    for family in ("++", "+-"):
        anchor = min(runs, key=lambda run: run.family_low_rank[family].rank2_relative_residual)
        print(
            f"  family {family}: anchor={anchor.run_id}  "
            f"rank2_rel={anchor.family_low_rank[family].rank2_relative_residual:.3e}"
        )
        anchor_basis = anchor.family_defect_basis[family]
        for run in runs:
            stats = compare_defect_bases(anchor_basis, run.family_defect_basis[family])
            print(
                f"    {run.run_id:<24s} "
                f"col_align={stats.column_alignment:.3f}  "
                f"row_align={stats.row_alignment:.3f}  "
                f"transfer_rel_resid={stats.transfer_relative_residual:.3e}"
            )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Numerically test the filtered H1^f bulk identities.")
    parser.add_argument("--a", type=float, default=1.0, help="Suzuki interval parameter a > 0.")
    parser.add_argument("--M", type=int, default=3, help="Use filtered indices m,n in {1,...,M}.")
    parser.add_argument("--B", type=float, default=0.2, help="Compact prime window parameter B.")
    parser.add_argument("--t", type=float, default=0.15, help="Heat parameter t.")
    parser.add_argument("--zeros", type=int, default=50, help="Number of positive zeta zeros to use.")
    parser.add_argument("--grid-size", type=int, default=20001, help="Integration grid size for A_k.")
    parser.add_argument("--dps", type=int, default=80, help="mpmath precision in decimal digits.")
    parser.add_argument(
        "--defect-rank",
        type=int,
        default=DEFAULT_DEFECT_RANK,
        help="Rank used for the defect-subspace classifier.",
    )
    parser.add_argument(
        "--search-conventions",
        action="store_true",
        help="Search the lightweight sign/index/conjugation conventions after filtering (single-run only).",
    )
    parser.add_argument(
        "--sweep",
        action="store_true",
        help="Run the built-in small grid sweep over a, M, and zeros.",
    )
    parser.add_argument(
        "--csv-out",
        type=Path,
        default=None,
        help="Write the entrywise mismatch map to this CSV path (defaults to tmp/ with timestamp).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.a <= 0 or args.M <= 0 or args.B <= 0 or args.t <= 0 or args.zeros <= 0:
        raise SystemExit("Need a, M, B, t, and zeros to be positive.")
    if args.sweep and args.search_conventions:
        raise SystemExit("--search-conventions is only supported in single-run mode.")

    csv_path = args.csv_out or default_csv_path()
    subspace_csv_path = default_subspace_csv_path(csv_path)
    baseline_q = q_conventions()[0]
    baseline_w = w_conventions()[0]

    if args.sweep:
        print("H1 filtered-bulk mismatch map (small grid sweep)")
        print("===============================================")
        sweep_runs: list[RunResult] = []
        all_rows: list[dict[str, object]] = []
        for a in DEFAULT_SWEEP_A:
            for M in DEFAULT_SWEEP_M:
                for zeros in DEFAULT_SWEEP_ZEROS:
                    run_id = f"a={a:.2f}|M={M}|zeros={zeros}"
                    result = run_check(
                        run_id=run_id,
                        a=a,
                        M=M,
                        B=args.B,
                        t=args.t,
                        zeros=zeros,
                        dps=args.dps,
                        grid_size=args.grid_size,
                        defect_rank=args.defect_rank,
                        q_convention=baseline_q,
                        w_convention=baseline_w,
                    )
                    sweep_runs.append(result)
                    print_run_report(
                        result,
                        a=a,
                        M=M,
                        B=args.B,
                        t=args.t,
                        zeros=zeros,
                        dps=args.dps,
                        defect_rank=args.defect_rank,
                    )
                    all_rows.extend(build_rows(result))
        print_anchor_stability_report(sweep_runs)
        write_rows_csv(csv_path, all_rows)
        write_rows_csv(subspace_csv_path, build_subspace_rows(sweep_runs))
        print(f"\nCSV written to: {csv_path}")
        print(f"Subspace CSV written to: {subspace_csv_path}")
        return 0

    print("H1 filtered-bulk match check")
    print("============================")
    result = run_check(
        run_id=f"a={args.a:.2f}|M={args.M}|zeros={args.zeros}",
        a=args.a,
        M=args.M,
        B=args.B,
        t=args.t,
        zeros=args.zeros,
        dps=args.dps,
        grid_size=args.grid_size,
        defect_rank=args.defect_rank,
        q_convention=baseline_q,
        w_convention=baseline_w,
    )
    print_run_report(
        result,
        a=args.a,
        M=args.M,
        B=args.B,
        t=args.t,
        zeros=args.zeros,
        dps=args.dps,
        defect_rank=args.defect_rank,
    )
    rows = build_rows(result)
    write_rows_csv(csv_path, rows)
    write_rows_csv(subspace_csv_path, build_subspace_rows([result]))
    print(f"\nCSV written to: {csv_path}")
    print(f"Subspace CSV written to: {subspace_csv_path}")

    if args.search_conventions:
        print("\nconvention search")
        print("-----------------")
        nodes = active_prime_nodes(args.B, args.t)
        A = arch_coefficients(args.B, args.t, max_k=2 * args.M + 2, grid_size=args.grid_size)
        for rel_res, q_name, w_name, kappa, metrics in search_conventions(args.M, args.a, A, nodes, args.zeros)[:8]:
            print(
                f"{q_name:18s} vs {w_name:14s}  "
                f"rel={rel_res:.3e}  "
                f"max={metrics['max_abs_residual']:.3e}  "
                f"kappa={kappa.real:.6e}+{kappa.imag:.6e}i"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
