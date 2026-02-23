#!/usr/bin/env python3
"""
Generate prime-power interval proofs for grid i19 pointwise upper bounds.

Input data: BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_AllBuckets.lean
Output: chunked Lean modules + aggregator theorem for a chosen n-range.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import math
import os
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp


@dataclass(frozen=True)
class PPEntry:
    n: int
    ub_num: int


@dataclass(frozen=True)
class Bounds:
    l: Fraction
    u: Fraction
    r: Fraction
    b_low: Fraction
    k_low: int
    split: int
    k_high: int
    k_exp: int
    bound: Fraction
    exp_sum: Fraction
    exp_ub: Fraction
    fejer_ub: Fraction


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--data", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--min-n", type=int, default=0)
    p.add_argument("--max-n", type=int, required=True)
    p.add_argument("--digits", type=int, default=20)
    p.add_argument("--split", type=int, default=10)
    p.add_argument("--k-low", type=int, default=30)
    p.add_argument("--k-exp-start", type=int, default=12)
    p.add_argument("--k-exp-step", type=int, default=2)
    p.add_argument("--chunk-size", type=int, default=5000)
    p.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 1)))
    p.add_argument("--progress-step", type=int, default=1000)
    p.add_argument("--name-suffix", type=str, default="")
    return p.parse_args()


def parse_entries(path: Path, min_n: int, max_n: int) -> Tuple[int, str, List[PPEntry]]:
    text = path.read_text(encoding="utf-8")
    m = re.search(r"def\s+([A-Za-z0-9_]+)_den\s*:\s*ℚ\s*:=\s*(\d+)", text)
    if not m:
        raise SystemExit("Could not find <prefix>_den")
    prefix = m.group(1)
    den = int(m.group(2))

    bucket_block = re.compile(
        rf"def\s+{re.escape(prefix)}_bucket_\d+\s*:\s*Array\s*\(Nat\s*×\s*Nat\)\s*:=\s*#\[(.*?)\n\]",
        re.DOTALL,
    )
    tuple_pat = re.compile(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)")

    entries: List[PPEntry] = []
    for block in bucket_block.findall(text):
        for n_s, num_s in tuple_pat.findall(block):
            n = int(n_s)
            if min_n <= n <= max_n:
                entries.append(PPEntry(n=n, ub_num=int(num_s)))

    entries.sort(key=lambda e: e.n)
    if not entries:
        raise SystemExit("No entries parsed in requested range")
    return den, prefix, entries


def prime_power_base_exp(n: int) -> Tuple[int, int]:
    if n < 2:
        raise ValueError(f"n must be >=2, got {n}")
    for p in range(2, int(math.isqrt(n)) + 1):
        if n % p == 0:
            k = 0
            m = n
            while m % p == 0:
                m //= p
                k += 1
            if m == 1:
                return p, k
            raise ValueError(f"Not a prime power: {n}")
    return n, 1


def factorial(n: int) -> int:
    return math.factorial(n)


def taylor_upper(x: Fraction, k: int) -> Fraction:
    s = Fraction(0, 1)
    for m in range(k):
        s += x**m / factorial(m)
    rem = x**k * Fraction(k + 1, factorial(k) * k)
    return s + rem


def taylor_sum(x: Fraction, k: int) -> Fraction:
    s = Fraction(0, 1)
    for m in range(k):
        s += x**m / factorial(m)
    return s


def ceil_log_bound(n: int, u: Fraction) -> int:
    s = Fraction(0, 1)
    k = 0
    while s < n:
        s += u**k / factorial(k)
        k += 1
        if k > 200:
            raise RuntimeError(f"k_high too large for n={n}")
    return k


def bound_for_n(
    n: int,
    ub: Fraction,
    k: int,
    digits: int,
    split: int,
    k_low: int,
    k_exp_start: int,
    k_exp_step: int,
    pi_ub: Fraction,
    b_i19: Fraction,
) -> Bounds:
    scale = 10**digits
    mp.mp.dps = digits + 50
    logn = mp.log(n)
    sqrt_n = mp.sqrt(n)

    l_num = int(mp.floor(logn * scale))
    u_num = int(mp.ceil(logn * scale))
    r_num = int(mp.floor(sqrt_n * scale))

    l = Fraction(l_num, scale)
    u = Fraction(u_num, scale)
    r = Fraction(r_num, scale)

    x = l / split
    b_low = taylor_upper(x, k_low)

    k_high = ceil_log_bound(n, u)

    t_critical = Fraction(3, 20)
    c = t_critical * l * l

    k_exp = k_exp_start
    bound = None
    exp_sum = None
    exp_ub = None
    fejer_ub = None

    while True:
        s = taylor_sum(c, k_exp)
        exp_sum = s
        exp_ub = Fraction(1, 1) / s
        fejer_raw = Fraction(1, 1) - l / (Fraction(2, 1) * pi_ub * b_i19)
        fejer_ub = max(Fraction(0, 1), fejer_raw)
        bound = (Fraction(2, 1) * (u / k) / r) * exp_ub * fejer_ub
        if bound <= ub:
            break
        k_exp += k_exp_step
        if k_exp > 220:
            raise RuntimeError(f"k_exp too large for n={n}")

    if b_low**split > n:
        raise RuntimeError(f"exp(l) bound failed for n={n}")

    return Bounds(
        l=l,
        u=u,
        r=r,
        b_low=b_low,
        k_low=k_low,
        split=split,
        k_high=k_high,
        k_exp=k_exp,
        bound=bound,
        exp_sum=exp_sum,
        exp_ub=exp_ub,
        fejer_ub=fejer_ub,
    )


def format_frac(fr: Fraction) -> Tuple[int, int]:
    return fr.numerator, fr.denominator


def list_literal(nums: List[int]) -> str:
    if not nums:
        return "([] : List ℕ)"
    return "([" + ", ".join(str(n) for n in nums) + "] : List ℕ)"


def compute_entry(
    task: Tuple[int, int, int, int, int, int, int, int, int, Fraction, Fraction],
) -> Tuple[int, int, int, Bounds]:
    (
        n,
        ub_num,
        den,
        digits,
        split,
        k_low,
        k_exp_start,
        k_exp_step,
        _unused_jobs,
        pi_ub,
        b_i19,
    ) = task
    p, k = prime_power_base_exp(n)
    ub = Fraction(ub_num, den)
    bounds = bound_for_n(
        n,
        ub,
        k,
        digits,
        split,
        k_low,
        k_exp_start,
        k_exp_step,
        pi_ub,
        b_i19,
    )
    if bounds.bound > ub:
        raise RuntimeError(f"bound still above ub for n={n}")
    return (n, p, k, bounds)


def main() -> None:
    args = parse_args()
    if args.min_n < 0:
        raise SystemExit("min-n must be nonnegative")
    if args.max_n < args.min_n:
        raise SystemExit("max-n must be >= min-n")

    data_path = Path(args.data)
    out_path = Path(args.out)

    den, prefix, entries = parse_entries(data_path, args.min_n, args.max_n)
    ub_map: Dict[int, int] = {e.n: e.ub_num for e in entries}

    digits = args.digits
    scale = 10**digits

    if args.name_suffix and not re.fullmatch(r"[_A-Za-z0-9]+", args.name_suffix):
        raise SystemExit("name-suffix must match [_A-Za-z0-9]+")
    suffix = args.name_suffix
    pi_name = f"pi_ub{suffix}"
    pi_le_name = f"pi_le_pi_ub{suffix}"
    pi_pos_name = f"pi_ub{suffix}_pos"

    pi_ub_num = 314159265358979323847
    pi_ub_den = 10**20
    pi_ub = Fraction(pi_ub_num, pi_ub_den)
    b_i19 = Fraction(49, 10)

    tasks = [
        (
            e.n,
            e.ub_num,
            den,
            digits,
            args.split,
            args.k_low,
            args.k_exp_start,
            args.k_exp_step,
            args.jobs,
            pi_ub,
            b_i19,
        )
        for e in entries
    ]

    bucket: List[Tuple[int, int, int, Bounds]] = []
    if args.jobs <= 1:
        for i, task in enumerate(tasks, 1):
            bucket.append(compute_entry(task))
            if args.progress_step > 0 and i % args.progress_step == 0:
                print(f"[progress] computed {i}/{len(tasks)} bounds", flush=True)
    else:
        with concurrent.futures.ProcessPoolExecutor(max_workers=args.jobs) as ex:
            done = 0
            for res in ex.map(compute_entry, tasks, chunksize=256):
                bucket.append(res)
                done += 1
                if args.progress_step > 0 and done % args.progress_step == 0:
                    print(f"[progress] computed {done}/{len(tasks)} bounds", flush=True)

    bucket.sort(key=lambda t: t[0])
    per_n = {n: (p, k, b) for n, p, k, b in bucket}

    def write_file(path: Path, lines: List[str]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    mod_prefix = "Q3.Proofs.PrimeCert."
    base_name = f"{out_path.stem}Base"
    base_mod = mod_prefix + base_name
    base_path = out_path.with_name(base_name + ".lean")

    base_lines: List[str] = []
    base_lines.append("import Mathlib")
    base_lines.append("import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_PointwiseCore")
    base_lines.append("set_option maxRecDepth 200000")
    base_lines.append("set_option maxHeartbeats 0")
    base_lines.append("set_option linter.unnecessarySimpa false")
    base_lines.append("set_option linter.unusedSimpArgs false")
    base_lines.append("")
    base_lines.append("/-!")
    base_lines.append("Auto-generated i19 prime-power pointwise bounds (base).")
    base_lines.append("")
    base_lines.append(f"Source: {data_path}")
    base_lines.append(f"Generated by: scripts/{Path(__file__).name}")
    base_lines.append(f"Range: [{args.min_n}, {args.max_n}]")
    base_lines.append("-/")
    base_lines.append("")
    base_lines.append("noncomputable section")
    base_lines.append("")
    base_lines.append("namespace Q3.Proofs.PrimeCert")
    base_lines.append("")
    base_lines.append(f"def {pi_name} : ℝ := ({pi_ub_num} : ℝ) / ({pi_ub_den} : ℝ)")
    base_lines.append(f"lemma {pi_le_name} : Real.pi ≤ {pi_name} := by")
    base_lines.append(f"  have h' : ({pi_name} : ℝ) = (3.14159265358979323847 : ℝ) := by")
    base_lines.append(f"    norm_num [{pi_name}]")
    base_lines.append(f"  have h : (Real.pi : ℝ) < ({pi_name} : ℝ) := by")
    base_lines.append("    simpa [h'] using Real.pi_lt_d20")
    base_lines.append("  exact le_of_lt h")
    base_lines.append(f"lemma {pi_pos_name} : 0 < {pi_name} := by")
    base_lines.append(f"  norm_num [{pi_name}]")
    base_lines.append("")
    base_lines.append("end Q3.Proofs.PrimeCert")
    write_file(base_path, base_lines)

    def emit_chunk(lo: int, hi: int) -> Path:
        chunk_name = f"{out_path.stem}_{lo}_{hi}"
        chunk_mod = mod_prefix + chunk_name
        chunk_path = out_path.with_name(chunk_name + ".lean")
        chunk_entries = [n for n in sorted(per_n) if lo <= n <= hi]

        lines: List[str] = []
        lines.append(f"import {base_mod}")
        lines.append("set_option maxRecDepth 200000")
        lines.append("set_option maxHeartbeats 0")
        lines.append("set_option linter.unnecessarySimpa false")
        lines.append("set_option linter.unusedSimpArgs false")
        lines.append("")
        lines.append("/-!")
        lines.append(f"Auto-generated i19 prime-power pointwise bounds for [{lo}, {hi}].")
        lines.append("")
        lines.append(f"Source: {data_path}")
        lines.append(f"Generated by: scripts/{Path(__file__).name}")
        lines.append("-/")
        lines.append("")
        lines.append("noncomputable section")
        lines.append("")
        lines.append("namespace Q3.Proofs.PrimeCert")
        lines.append("")

        for n in chunk_entries:
            p, k, b = per_n[n]
            l_num, l_den = format_frac(b.l)
            u_num, u_den = format_frac(b.u)
            r_num, r_den = format_frac(b.r)
            b_num, b_den = format_frac(b.b_low)
            sum_num, sum_den = format_frac(b.exp_sum)
            bound_num, bound_den = format_frac(b.bound)
            fejer_num, fejer_den = format_frac(b.fejer_ub)
            ub_num = ub_map[n]

            lines.append(f"def l_{n} : ℝ := ({l_num} : ℝ) / ({l_den} : ℝ)")
            lines.append(f"def u_{n} : ℝ := ({u_num} : ℝ) / ({u_den} : ℝ)")
            lines.append(f"def r_{n} : ℝ := ({r_num} : ℝ) / ({r_den} : ℝ)")
            lines.append(f"def b_{n} : ℝ := ({b_num} : ℝ) / ({b_den} : ℝ)")
            lines.append("")

            lines.append(f"lemma exp_l_{n}_div_le_b : Real.exp (l_{n} / {b.split}) ≤ b_{n} := by")
            lines.append(f"  have hx0 : 0 ≤ l_{n} / {b.split} := by")
            lines.append(f"    dsimp [l_{n}]")
            lines.append(f"    positivity")
            lines.append(f"  have hx1 : l_{n} / {b.split} ≤ 1 := by norm_num [l_{n}]")
            lines.append("  have h' :")
            lines.append(
                f"      (∑ m ∈ Finset.range {b.k_low}, (l_{n} / {b.split}) ^ m / (Nat.factorial m)) +"
            )
            lines.append(
                f"          (l_{n} / {b.split}) ^ {b.k_low} * ({b.k_low} + 1) / (Nat.factorial {b.k_low} * {b.k_low}) ≤"
            )
            lines.append(f"        b_{n} := by")
            lines.append(f"    norm_num [l_{n}, b_{n}]")
            lines.append(
                f"  exact exp_le_of_taylor_bound (x := l_{n} / {b.split}) (b := b_{n}) hx0 hx1"
                f" (n := {b.k_low}) (by decide) h'"
            )
            lines.append("")

            lines.append(f"lemma exp_l_{n}_le_n : Real.exp l_{n} ≤ ({n} : ℝ) := by")
            lines.append(f"  have hpow : Real.exp l_{n} ≤ b_{n} ^ {b.split} := by")
            lines.append(
                f"    exact exp_le_pow_of_div_le (x := l_{n}) (b := b_{n}) (n := {b.split})"
                f" (by decide) (by simpa using exp_l_{n}_div_le_b)"
            )
            lines.append(f"  have hpow' : b_{n} ^ {b.split} ≤ ({n} : ℝ) := by")
            lines.append(f"    norm_num [b_{n}]")
            lines.append("  exact hpow.trans hpow'")
            lines.append("")

            lines.append(f"lemma n_le_exp_u_{n} : ({n} : ℝ) ≤ Real.exp u_{n} := by")
            lines.append(f"  have hx0 : 0 ≤ u_{n} := by norm_num [u_{n}]")
            lines.append("  have hsum :")
            lines.append(
                f"      ({n} : ℝ) ≤ ∑ m ∈ Finset.range {b.k_high}, u_{n} ^ m / (Nat.factorial m) := by"
            )
            lines.append(f"    norm_num [u_{n}]")
            lines.append("  have hle :")
            lines.append(
                f"      ∑ m ∈ Finset.range {b.k_high}, u_{n} ^ m / (Nat.factorial m) ≤ Real.exp u_{n} := by"
            )
            lines.append(f"    simpa using (Real.sum_le_exp_of_nonneg hx0 {b.k_high})")
            lines.append("  exact le_trans hsum hle")
            lines.append("")

            lines.append(f"lemma log_bounds_{n} :")
            lines.append(f"    l_{n} ≤ Real.log ({n} : ℝ) ∧ Real.log ({n} : ℝ) ≤ u_{n} := by")
            lines.append(f"  have hn : 0 < ({n} : ℕ) := by norm_num")
            lines.append(
                f"  exact log_nat_bounds_of_exp_bounds (n := {n}) (hn := hn)"
                f" (a := l_{n}) (b := u_{n}) (ha := exp_l_{n}_le_n) (hb := n_le_exp_u_{n})"
            )
            lines.append("")
            lines.append(f"lemma l_{n}_le_log : l_{n} ≤ Real.log ({n} : ℝ) := by")
            lines.append(f"  exact (log_bounds_{n}).1")
            lines.append("")
            lines.append(f"lemma log_le_u_{n} : Real.log ({n} : ℝ) ≤ u_{n} := by")
            lines.append(f"  exact (log_bounds_{n}).2")
            lines.append("")

            lines.append(f"lemma r_{n}_pos : 0 < r_{n} := by")
            lines.append(f"  norm_num [r_{n}]")
            lines.append(f"lemma r_{n}_sq_le : r_{n} ^ 2 ≤ ({n} : ℝ) := by")
            lines.append(f"  norm_num [r_{n}]")
            lines.append("")

            lines.append(f"def sum_num_{n} : ℚ := {sum_num}")
            lines.append(f"def sum_den_{n} : ℚ := {sum_den}")
            lines.append(f"def exp_ub_{n} : ℝ := (sum_den_{n} : ℝ) / (sum_num_{n} : ℝ)")
            lines.append(
                f"lemma exp_bound_{n} : Real.exp (-t_critical * l_{n} ^ 2) ≤ exp_ub_{n} := by"
            )
            lines.append(f"  have hc : 0 ≤ t_critical * l_{n} ^ 2 := by")
            lines.append("    have ht : 0 ≤ t_critical := by norm_num [t_critical]")
            lines.append(f"    have hl : 0 ≤ l_{n} ^ 2 := by nlinarith")
            lines.append("    nlinarith")
            lines.append("  have hsum :")
            lines.append(
                f"      Real.exp (-t_critical * l_{n} ^ 2) ≤"
                f"        1 / (∑ m ∈ Finset.range {b.k_exp}, (t_critical * l_{n} ^ 2) ^ m / (Nat.factorial m)) := by"
            )
            lines.append(
                f"    simpa using (exp_neg_le_inv_sum (c := t_critical * l_{n} ^ 2) hc"
                f" (n := {b.k_exp}) (by decide))"
            )
            lines.append("  have hsum_eval :")
            lines.append(
                f"      (∑ m ∈ Finset.range {b.k_exp}, (t_critical * l_{n} ^ 2) ^ m / (Nat.factorial m)) ="
            )
            lines.append(f"        ((sum_num_{n} : ℝ) / (sum_den_{n} : ℝ)) := by")
            lines.append(f"    norm_num [t_critical, l_{n}, sum_num_{n}, sum_den_{n}]")
            lines.append(f"  have hnum_pos : (0 : ℝ) < (sum_num_{n} : ℝ) := by")
            lines.append(f"    norm_num [sum_num_{n}]")
            lines.append(f"  have hden_pos : (0 : ℝ) < (sum_den_{n} : ℝ) := by")
            lines.append(f"    norm_num [sum_den_{n}]")
            lines.append("  have hsum' :")
            lines.append(
                f"      1 / (∑ m ∈ Finset.range {b.k_exp}, (t_critical * l_{n} ^ 2) ^ m / (Nat.factorial m)) ="
            )
            lines.append(f"        (sum_den_{n} : ℝ) / (sum_num_{n} : ℝ) := by")
            lines.append("    calc")
            lines.append(
                f"      1 / (∑ m ∈ Finset.range {b.k_exp}, (t_critical * l_{n} ^ 2) ^ m / (Nat.factorial m))"
            )
            lines.append(f"          = 1 / ((sum_num_{n} : ℝ) / (sum_den_{n} : ℝ)) := by")
            lines.append("            simpa [hsum_eval]")
            lines.append(f"      _ = (sum_den_{n} : ℝ) / (sum_num_{n} : ℝ) := by")
            lines.append("        field_simp [hnum_pos.ne', hden_pos.ne']")
            lines.append("  have hsum'' :")
            lines.append(
                f"      1 / (∑ m ∈ Finset.range {b.k_exp}, (t_critical * l_{n} ^ 2) ^ m / (Nat.factorial m)) ≤ exp_ub_{n} := by"
            )
            lines.append(f"    simpa [exp_ub_{n}, hsum']")
            lines.append("  exact hsum.trans hsum''")
            lines.append("")

            lines.append(f"def fejer_num_{n} : ℚ := {fejer_num}")
            lines.append(f"def fejer_den_{n} : ℚ := {fejer_den}")
            lines.append(f"def fejer_ub_{n} : ℝ := (fejer_num_{n} : ℝ) / (fejer_den_{n} : ℝ)")
            lines.append(f"lemma fejer_bound_{n} :")
            lines.append(
                f"    max (0 : ℝ) (1 - l_{n} / (2 * {pi_name} * prime_b_grid_i19_B)) ≤ fejer_ub_{n} := by"
            )
            lines.append(
                f"  norm_num [l_{n}, {pi_name}, prime_b_grid_i19_B, fejer_num_{n}, fejer_den_{n}, fejer_ub_{n}]"
            )
            lines.append("")

            lines.append(f"def bound_num_{n} : ℚ := {bound_num}")
            lines.append(f"def bound_den_{n} : ℚ := {bound_den}")
            lines.append("")

            lines.append(f"lemma hub_{n} :")
            lines.append(
                f"    prime_b_grid_pp_envelope_ub u_{n} r_{n} exp_ub_{n} fejer_ub_{n} {k} ≤"
            )
            lines.append(f"      {prefix}_ub {n} := by")
            lines.append("  have hval :")
            lines.append(
                f"      prime_b_grid_pp_envelope_ub u_{n} r_{n} exp_ub_{n} fejer_ub_{n} {k} ="
            )
            lines.append(f"        ((bound_num_{n} : ℝ) / (bound_den_{n} : ℝ)) := by")
            lines.append(
                f"    norm_num [prime_b_grid_pp_envelope_ub, u_{n}, r_{n}, exp_ub_{n}, fejer_ub_{n},"
                f" sum_num_{n}, sum_den_{n}, bound_num_{n}, bound_den_{n},"
                f" fejer_num_{n}, fejer_den_{n}]"
            )
            lines.append(
                f"  have hrat : (bound_num_{n} / bound_den_{n}) ≤ ({ub_num} : ℚ) / {prefix}_den := by"
            )
            lines.append("    native_decide")
            lines.append(
                f"  have hrat' : ((bound_num_{n} : ℝ) / (bound_den_{n} : ℝ)) ≤ (({ub_num} : ℚ) / {prefix}_den : ℝ) := by"
            )
            lines.append("    exact_mod_cast hrat")
            lines.append(
                f"  have hrat'' : ((bound_num_{n} : ℝ) / (bound_den_{n} : ℝ)) ≤ {prefix}_ub {n} := by"
            )
            lines.append(
                f"    have hq : {prefix}_ub_q_get {n} = ({ub_num} : ℚ) / {prefix}_den := by"
            )
            lines.append("      native_decide")
            lines.append(f"    simpa [{prefix}_ub, hq] using hrat'")
            lines.append("  exact hval.le.trans hrat''")
            lines.append("")

            lines.append(f"lemma prime_b_grid_weight_term_i19_le_pp_ub_{n} :")
            lines.append(
                f"    prime_b_grid_weight_term prime_b_grid_i19 {n} ≤ {prefix}_ub {n} := by"
            )
            lines.append(f"  have hp : ({p} : ℕ).Prime := by native_decide")
            lines.append(f"  have hk : 0 < {k} := by decide")
            lines.append(f"  have hpk : ({p} ^ {k} : ℕ) = {n} := by norm_num")
            lines.append(
                f"  have h := (prime_b_grid_weight_term_i19_le_pp_ub_of_prime_pow_bounds"
                f" (p := {p}) (k := {k}) hp hk"
            )
            lines.append(f"    (l := l_{n}) (u := u_{n}) (r := r_{n})")
            lines.append(f"    (exp_ub := exp_ub_{n}) (pi_ub := {pi_name}) (fejer_ub := fejer_ub_{n})")
            lines.append(f"    (hl0 := by norm_num [l_{n}]) (hu0 := by norm_num [u_{n}])")
            lines.append(
                f"    (hlog_l := by simpa using l_{n}_le_log)"
                f" (hlog_u := by simpa using log_le_u_{n})"
            )
            lines.append(f"    (hr0 := r_{n}_pos) (hsqrt := by simpa using r_{n}_sq_le)")
            lines.append(f"    (hexp := by simpa using exp_bound_{n})")
            lines.append(f"    (hpi_pos := {pi_pos_name}) (hpi := {pi_le_name})")
            lines.append(f"    (hfejer := by simpa using fejer_bound_{n})")
            lines.append(f"    (hub := by simpa using hub_{n}))")
            lines.append(f"  simpa [hpk] using h")
            lines.append("")

        list_name = f"prime_b_grid_pp_i19_auto_list_{lo}_{hi}"
        mem_lemma_name = f"prime_b_grid_weight_term_i19_le_pp_ub_of_{lo}_{hi}_primepow_mem"
        core_lemma_name = f"prime_b_grid_weight_term_i19_le_pp_ub_of_{lo}_{hi}_primepow"

        lines.append(f"def {list_name} : Finset ℕ := ({list_literal(chunk_entries)}).toFinset")
        lines.append("")
        lines.append(f"lemma {list_name}_spec :")
        lines.append(f"    {list_name} = ((Finset.Icc {lo} {hi}).filter IsPrimePow) := by")
        lines.append("  native_decide")
        lines.append("")

        lines.append(f"lemma {mem_lemma_name} {{n : ℕ}}")
        lines.append(f"    (hmem : n ∈ {list_name}) :")
        lines.append(f"    prime_b_grid_weight_term prime_b_grid_i19 n ≤ {prefix}_ub n := by")
        if not chunk_entries:
            lines.append("  simpa using (False.elim (by simpa [" + list_name + "] using hmem))")
        elif len(chunk_entries) == 1:
            n0 = chunk_entries[0]
            lines.append(f"  have h0 : n = {n0} := by")
            lines.append(f"    simpa [{list_name}] using hmem")
            lines.append(f"  simpa [h0] using prime_b_grid_weight_term_i19_le_pp_ub_{n0}")
        else:
            disj = " ∨ ".join(f"n = {n}" for n in chunk_entries)
            lines.append(f"  have hcases : {disj} := by")
            lines.append(f"    simpa [{list_name}] using hmem")
            rcases_vars = " | ".join(f"h{i}" for i in range(len(chunk_entries)))
            lines.append(f"  rcases hcases with {rcases_vars}")
            for i, n in enumerate(chunk_entries):
                lines.append(f"  · simpa [h{i}] using prime_b_grid_weight_term_i19_le_pp_ub_{n}")
        lines.append("")

        lines.append(f"lemma {core_lemma_name} {{n : ℕ}}")
        lines.append(f"    (hn : IsPrimePow n) (hlo : {lo} ≤ n) (hhi : n ≤ {hi}) :")
        lines.append(f"    prime_b_grid_weight_term prime_b_grid_i19 n ≤ {prefix}_ub n := by")
        lines.append(f"  have hmemRange : n ∈ ((Finset.Icc {lo} {hi}).filter IsPrimePow) := by")
        lines.append("    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hn⟩")
        lines.append(f"  have hmem : n ∈ {list_name} := by")
        lines.append(f"    simpa [{list_name}_spec] using hmemRange")
        lines.append(f"  exact {mem_lemma_name} hmem")
        lines.append("")

        lines.append("end Q3.Proofs.PrimeCert")
        write_file(chunk_path, lines)
        return chunk_path

    chunk_size = args.chunk_size
    if chunk_size <= 0:
        raise SystemExit("chunk-size must be positive")

    chunks: List[Tuple[int, int]] = []
    lo = args.min_n
    while lo <= args.max_n:
        hi = min(lo + chunk_size - 1, args.max_n)
        chunks.append((lo, hi))
        lo = hi + 1

    chunk_paths = [emit_chunk(lo, hi) for lo, hi in chunks]
    if not chunk_paths:
        raise SystemExit("No chunk files generated")

    agg_lines: List[str] = []
    agg_lines.append(f"import {base_mod}")
    for lo, hi in chunks:
        agg_lines.append(f"import {mod_prefix}{out_path.stem}_{lo}_{hi}")
    agg_lines.append("set_option maxRecDepth 200000")
    agg_lines.append("set_option maxHeartbeats 0")
    agg_lines.append("set_option linter.unnecessarySimpa false")
    agg_lines.append("set_option linter.unusedSimpArgs false")
    agg_lines.append("")
    agg_lines.append("/-!")
    agg_lines.append("Auto-generated i19 prime-power pointwise bounds (aggregator).")
    agg_lines.append("")
    agg_lines.append(f"Source: {data_path}")
    agg_lines.append(f"Generated by: scripts/{Path(__file__).name}")
    agg_lines.append(f"Range: [{args.min_n}, {args.max_n}]")
    agg_lines.append("-/")
    agg_lines.append("")
    agg_lines.append("noncomputable section")
    agg_lines.append("")
    agg_lines.append("namespace Q3.Proofs.PrimeCert")
    agg_lines.append("")

    agg_name = f"prime_b_grid_weight_term_i19_le_pp_ub_of_{args.min_n}_{args.max_n}_primepow_all"
    agg_lines.append(f"lemma {agg_name} {{n : ℕ}}")
    agg_lines.append(f"    (hn : IsPrimePow n) (hlo : {args.min_n} ≤ n) (hhi : n ≤ {args.max_n}) :")
    agg_lines.append(f"    prime_b_grid_weight_term prime_b_grid_i19 n ≤ {prefix}_ub n := by")

    if len(chunks) == 1:
        lo0, hi0 = chunks[0]
        agg_lines.append(
            f"  exact prime_b_grid_weight_term_i19_le_pp_ub_of_{lo0}_{hi0}_primepow hn hlo hhi"
        )
    else:
        lo0, hi0 = chunks[0]
        agg_lines.append(f"  by_cases h0 : n ≤ {hi0}")
        agg_lines.append(
            f"  · exact prime_b_grid_weight_term_i19_le_pp_ub_of_{lo0}_{hi0}_primepow hn hlo h0"
        )
        for i in range(1, len(chunks)):
            lo_i, hi_i = chunks[i]
            prev_hi = chunks[i - 1][1]
            if lo_i != prev_hi + 1:
                raise SystemExit("Chunks must be contiguous")
            agg_lines.append(f"  have h{i - 1}' : {lo_i} ≤ n := by")
            agg_lines.append(f"    exact (Nat.succ_le_iff).2 (Nat.lt_of_not_ge h{i - 1})")
            if i < len(chunks) - 1:
                agg_lines.append(f"  by_cases h{i} : n ≤ {hi_i}")
                agg_lines.append(
                    f"  · exact prime_b_grid_weight_term_i19_le_pp_ub_of_{lo_i}_{hi_i}_primepow hn h{i - 1}' h{i}"
                )
            else:
                agg_lines.append(
                    f"  exact prime_b_grid_weight_term_i19_le_pp_ub_of_{lo_i}_{hi_i}_primepow hn h{i - 1}' hhi"
                )

    agg_lines.append("")
    agg_lines.append("end Q3.Proofs.PrimeCert")
    write_file(out_path, agg_lines)


if __name__ == "__main__":
    main()
