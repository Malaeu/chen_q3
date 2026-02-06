#!/usr/bin/env python3
"""
Generate bucket-0 prime-power interval proofs for prime-heat bounds.

This script reads the prime-power upper-bound table from
`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowData.lean`,
then builds rational interval bounds (l,u,r,exp_ub) and emits a Lean file
with per-n proofs using the `prime_heat_weight_term_le_pp_ub_of_prime_pow_bounds`
lemma (interval envelope with 1/k factor).
"""

from __future__ import annotations

import argparse
import math
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

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


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--data", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--digits", type=int, default=20)
    p.add_argument("--split", type=int, default=10)
    p.add_argument("--k-low", type=int, default=30)
    p.add_argument("--k-exp-start", type=int, default=12)
    p.add_argument("--k-exp-step", type=int, default=2)
    p.add_argument("--limit", type=int, default=10000)
    p.add_argument("--chunk-size", type=int, default=1000)
    return p.parse_args()


def parse_bucket0(path: Path, limit: int) -> Tuple[int, List[PPEntry]]:
    text = path.read_text(encoding="utf-8")
    m = re.search(r"def prime_heat_pp_term_ub_den : ℚ := (\d+)", text)
    if not m:
        raise SystemExit("Could not find prime_heat_pp_term_ub_den")
    den = int(m.group(1))

    start = text.find("def prime_heat_pp_term_ub_q_get_bucket_0")
    if start < 0:
        raise SystemExit("Could not find bucket_0 def")
    end = text.find("def prime_heat_pp_term_ub_q_get_bucket_1", start)
    if end < 0:
        raise SystemExit("Could not find bucket_1 def")
    segment = text[start:end]

    entries: List[PPEntry] = []
    pattern = re.compile(r"\|\s+(\d+)\s+=>\s+\((\d+)\s+:\s+ℚ\)\s+/\s+prime_heat_pp_term_ub_den")
    for n_s, num_s in pattern.findall(segment):
        n = int(n_s)
        if n <= limit:
            entries.append(PPEntry(n=n, ub_num=int(num_s)))
    entries.sort(key=lambda e: e.n)
    if not entries:
        raise SystemExit("No entries parsed for bucket_0")
    return den, entries


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
    pi_lb: Fraction,
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
    while True:
        s = taylor_sum(c, k_exp)
        exp_sum = s
        exp_ub = Fraction(1, 1) / s
        # base bound (without the 1/k factor)
        bound = (Fraction(2, 1) * u / r) * exp_ub * (u / (Fraction(2, 1) * pi_lb))
        if bound / k <= ub:
            break
        k_exp += k_exp_step
        if k_exp > 200:
            raise RuntimeError(f"k_exp too large for n={n}")

    # sanity: exp(l) <= n using the Taylor split
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
    )


def format_frac(fr: Fraction) -> Tuple[int, int]:
    return fr.numerator, fr.denominator


def main() -> None:
    args = parse_args()
    data_path = Path(args.data)
    out_path = Path(args.out)

    den, entries = parse_bucket0(data_path, args.limit)
    ub_map: Dict[int, int] = {e.n: e.ub_num for e in entries}

    digits = args.digits
    scale = 10**digits
    pi_lb_num = 314159265358979323846
    pi_lb = Fraction(pi_lb_num, scale)

    bucket: List[Tuple[int, int, int, Bounds]] = []
    for e in entries:
        p, k = prime_power_base_exp(e.n)
        ub = Fraction(ub_map[e.n], den)
        bounds = bound_for_n(
            e.n,
            ub,
            k,
            digits,
            args.split,
            args.k_low,
            args.k_exp_start,
            args.k_exp_step,
            pi_lb,
        )
        # apply 1/k factor in final bound
        bound_with_k = bounds.bound / k
        if bound_with_k > ub:
            raise RuntimeError(f"bound still above ub for n={e.n}")
        bucket.append((e.n, p, k, bounds))

    def write_file(path: Path, lines: List[str]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    mod_prefix = "Q3.Proofs.PrimeCert."
    base_name = f"{out_path.stem}Base"
    base_mod = mod_prefix + base_name
    base_path = out_path.with_name(base_name + ".lean")

    # Base file with shared definitions
    base_lines: List[str] = []
    base_lines.append("import Mathlib")
    base_lines.append("import Q3.Proofs.PrimeCert.IntervalPilot")
    base_lines.append("import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFull")
    base_lines.append("set_option maxHeartbeats 0")
    base_lines.append("")
    base_lines.append("/-!")
    base_lines.append("Auto-generated bucket-0 prime-power interval bounds (base).")
    base_lines.append("")
    base_lines.append(f"Source: {data_path}")
    base_lines.append(f"Generated by: scripts/prime_brange_heat_pp_bucket0_auto.py")
    base_lines.append("-/")
    base_lines.append("")
    base_lines.append("noncomputable section")
    base_lines.append("")
    base_lines.append("namespace Q3.Proofs.PrimeCert")
    base_lines.append("")
    base_lines.append(f"def pi_lb : ℝ := ({pi_lb_num} : ℝ) / ({scale} : ℝ)")
    base_lines.append("lemma pi_lb_le_pi : pi_lb ≤ Real.pi := by")
    base_lines.append("  have h' : (pi_lb : ℝ) = (3.14159265358979323846 : ℝ) := by")
    base_lines.append("    norm_num [pi_lb]")
    base_lines.append("  have h : (pi_lb : ℝ) < Real.pi := by")
    base_lines.append("    simpa [h'] using Real.pi_gt_d20")
    base_lines.append("  exact le_of_lt h")
    base_lines.append("lemma pi_lb_pos : 0 < pi_lb := by")
    base_lines.append("  norm_num [pi_lb]")
    base_lines.append("")
    base_lines.append("end Q3.Proofs.PrimeCert")
    write_file(base_path, base_lines)

    prime_power_set = {e.n for e in entries}

    def emit_chunk(lo: int, hi: int) -> Path:
        chunk_name = f"{out_path.stem}_{lo}_{hi}"
        chunk_mod = mod_prefix + chunk_name
        chunk_path = out_path.with_name(chunk_name + ".lean")
        lines: List[str] = []
        lines.append(f"import {base_mod}")
        lines.append("set_option maxHeartbeats 0")
        lines.append("")
        lines.append("/-!")
        lines.append(f"Auto-generated bucket-0 prime-power interval bounds for [{lo}, {hi}].")
        lines.append("")
        lines.append(f"Source: {data_path}")
        lines.append(f"Generated by: scripts/prime_brange_heat_pp_bucket0_auto.py")
        lines.append("-/")
        lines.append("")
        lines.append("noncomputable section")
        lines.append("")
        lines.append("namespace Q3.Proofs.PrimeCert")
        lines.append("")

        for n, p, k, b in bucket:
            if n < lo or n > hi:
                continue
            l_num, l_den = format_frac(b.l)
            u_num, u_den = format_frac(b.u)
            r_num, r_den = format_frac(b.r)
            b_num, b_den = format_frac(b.b_low)
            bound_num, bound_den = format_frac(b.bound / k)
            ub_num = ub_map[n]

            lines.append(f"def l_{n} : ℝ := ({l_num} : ℝ) / ({l_den} : ℝ)")
            lines.append(f"def u_{n} : ℝ := ({u_num} : ℝ) / ({u_den} : ℝ)")
            lines.append(f"def r_{n} : ℝ := ({r_num} : ℝ) / ({r_den} : ℝ)")
            lines.append(f"def b_{n} : ℝ := ({b_num} : ℝ) / ({b_den} : ℝ)")
            lines.append("")

            lines.append(f"lemma exp_l_{n}_div_le_b : Real.exp (l_{n} / {b.split}) ≤ b_{n} := by")
            lines.append(f"  have hx0 : 0 ≤ l_{n} / {b.split} := by norm_num [l_{n}]")
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
            lines.append(f"  exact hpow.trans hpow'")
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
            lines.append(f"  exact le_trans hsum hle")
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

            sum_num, sum_den = format_frac(b.exp_sum)
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

            lines.append(f"def bound_num_{n} : ℚ := {bound_num}")
            lines.append(f"def bound_den_{n} : ℚ := {bound_den}")
            lines.append("")

            lines.append(f"lemma hub_{n} :")
            lines.append(f"    prime_heat_pp_envelope_ub u_{n} r_{n} exp_ub_{n} pi_lb {k} ≤")
            lines.append(f"      Full.prime_heat_pp_term_ub {n} := by")
            lines.append("  have hval :")
            lines.append(f"      prime_heat_pp_envelope_ub u_{n} r_{n} exp_ub_{n} pi_lb {k} =")
            lines.append(f"        ((bound_num_{n} : ℝ) / (bound_den_{n} : ℝ)) := by")
            lines.append(
                f"    norm_num [prime_heat_pp_envelope_ub, t_critical, u_{n}, r_{n}, exp_ub_{n}, pi_lb,"
                f" sum_num_{n}, sum_den_{n}, bound_num_{n}, bound_den_{n}]"
            )
            lines.append(
                f"  have hrat : (bound_num_{n} / bound_den_{n}) ≤ ({ub_num} : ℚ) / Full.prime_heat_pp_term_ub_den := by"
            )
            lines.append("    native_decide")
            lines.append(
                f"  have hrat' : ((bound_num_{n} : ℝ) / (bound_den_{n} : ℝ)) ≤ (({ub_num} : ℚ) / Full.prime_heat_pp_term_ub_den : ℝ) := by"
            )
            lines.append("    exact_mod_cast hrat")
            lines.append(
                f"  have hrat'' : ((bound_num_{n} : ℝ) / (bound_den_{n} : ℝ)) ≤ Full.prime_heat_pp_term_ub {n} := by"
            )
            lines.append(
                f"    have hq : Full.prime_heat_pp_term_ub_q_get {n} ="
                f" ({ub_num} : ℚ) / Full.prime_heat_pp_term_ub_den := by"
            )
            lines.append("      native_decide")
            lines.append(f"    simpa [Full.prime_heat_pp_term_ub, hq] using hrat'")
            lines.append("  exact hval.le.trans hrat''")
            lines.append("")

            lines.append(f"lemma prime_heat_weight_term_le_pp_ub_{n} :")
            lines.append(f"    prime_heat_weight_term {n} ≤ Full.prime_heat_pp_term_ub {n} := by")
            lines.append(f"  have hp : ({p} : ℕ).Prime := by native_decide")
            lines.append(f"  have hk : 0 < {k} := by decide")
            lines.append(f"  have hpk : ({p} ^ {k} : ℕ) = {n} := by norm_num")
            lines.append(
                f"  have h := (prime_heat_weight_term_le_pp_ub_of_prime_pow_bounds"
                f" (p := {p}) (k := {k}) (l := l_{n}) (u := u_{n}) (r := r_{n})"
                f" (exp_ub := exp_ub_{n}) (pi_lb := pi_lb) hp hk"
            )
            lines.append(f"    (hl0 := by norm_num [l_{n}]) (hu0 := by norm_num [u_{n}])")
            lines.append(
                f"    (hlog_l := by simpa using l_{n}_le_log) (hlog_u := by simpa using log_le_u_{n})"
            )
            lines.append(f"    (hr0 := r_{n}_pos) (hsqrt := by simpa using r_{n}_sq_le)")
            lines.append(f"    (hpi_pos := pi_lb_pos) (hpi := pi_lb_le_pi)")
            lines.append(
                f"    (hexp := by simpa using exp_bound_{n}) (hub := by simpa using hub_{n}))"
            )
            lines.append(f"  simpa [hpk] using h")
            lines.append("")

        # chunk dispatcher
        if lo == 0:
            lines.append(
                f"lemma prime_heat_weight_term_le_pp_ub_of_le_{hi} {{n : ℕ}} (hN : n ≤ {hi}) :"
            )
            lines.append("    prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n := by")
        else:
            lines.append(
                f"lemma prime_heat_weight_term_le_pp_ub_of_{lo}_{hi} {{n : ℕ}} (hlo : {lo} ≤ n) (hhi : n ≤ {hi}) :"
            )
            lines.append("    prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n := by")
        lines.append("  interval_cases n")
        for n in range(lo, hi + 1):
            if n in prime_power_set:
                lines.append(f"  · simpa using prime_heat_weight_term_le_pp_ub_{n}")
            else:
                lines.append(f"  · have hnp : ¬ IsPrimePow {n} := by native_decide")
                lines.append(
                    "    have h0 : prime_heat_weight_term "
                    f"{n} = 0 := prime_heat_weight_term_eq_zero_of_not_prime_pow hnp"
                )
                lines.append(
                    "    have hq : (0 : ℚ) ≤ Full.prime_heat_pp_term_ub_q_get "
                    f"{n} := by native_decide"
                )
                lines.append(
                    "    have hq' : (0 : ℝ) ≤ (Full.prime_heat_pp_term_ub_q_get "
                    f"{n} : ℝ) := by exact_mod_cast hq"
                )
                lines.append("    simpa [Full.prime_heat_pp_term_ub, h0] using hq'")
        lines.append("")
        lines.append("end Q3.Proofs.PrimeCert")
        write_file(chunk_path, lines)
        return chunk_path

    chunk_size = args.chunk_size
    if chunk_size <= 0:
        raise SystemExit("chunk-size must be positive")
    chunks: List[Tuple[int, int]] = []
    lo = 0
    while lo <= args.limit:
        hi = min(lo + chunk_size - 1, args.limit)
        chunks.append((lo, hi))
        lo = hi + 1
    chunk_paths = [emit_chunk(lo, hi) for lo, hi in chunks]

    # Aggregator file
    agg_lines: List[str] = []
    agg_lines.append(f"import {base_mod}")
    for lo, hi in chunks:
        agg_lines.append(f"import {mod_prefix}{out_path.stem}_{lo}_{hi}")
    agg_lines.append("set_option maxHeartbeats 0")
    agg_lines.append("")
    agg_lines.append("/-!")
    agg_lines.append("Auto-generated bucket-0 prime-power interval bounds (aggregator).")
    agg_lines.append("")
    agg_lines.append(f"Source: {data_path}")
    agg_lines.append(f"Generated by: scripts/prime_brange_heat_pp_bucket0_auto.py")
    agg_lines.append("-/")
    agg_lines.append("")
    agg_lines.append("noncomputable section")
    agg_lines.append("")
    agg_lines.append("namespace Q3.Proofs.PrimeCert")
    agg_lines.append("")
    limit = args.limit
    agg_lines.append(
        f"lemma prime_heat_weight_term_le_pp_ub_of_le_{limit} {{n : ℕ}} (hN : n ≤ {limit}) :"
    )
    agg_lines.append("    prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n := by")
    if not chunks:
        agg_lines.append("  simpa using (by cases hN)")
    else:
        lo0, hi0 = chunks[0]
        if lo0 != 0:
            raise SystemExit("First chunk must start at 0")
        if len(chunks) == 1:
            agg_lines.append(f"  exact prime_heat_weight_term_le_pp_ub_of_le_{hi0} hN")
        else:
            agg_lines.append(f"  by_cases h0 : n ≤ {hi0}")
            agg_lines.append(f"  · exact prime_heat_weight_term_le_pp_ub_of_le_{hi0} h0")
            for i in range(1, len(chunks)):
                lo, hi = chunks[i]
                prev_hi = chunks[i - 1][1]
                if lo != prev_hi + 1:
                    raise SystemExit("Chunks must be contiguous")
                agg_lines.append(f"  have h{i - 1}' : {lo} ≤ n := by")
                agg_lines.append(f"    exact (Nat.succ_le_iff).2 (Nat.lt_of_not_ge h{i - 1})")
                if i < len(chunks) - 1:
                    agg_lines.append(f"  by_cases h{i} : n ≤ {hi}")
                    agg_lines.append(
                        f"  · exact prime_heat_weight_term_le_pp_ub_of_{lo}_{hi} h{i - 1}' h{i}"
                    )
                else:
                    agg_lines.append(
                        f"  exact prime_heat_weight_term_le_pp_ub_of_{lo}_{hi} h{i - 1}' hN"
                    )
    agg_lines.append("")
    agg_lines.append("end Q3.Proofs.PrimeCert")
    write_file(out_path, agg_lines)


if __name__ == "__main__":
    main()
