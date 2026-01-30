#!/usr/bin/env python3
"""Convert prime_cert_brange output into a Lean grid table.

Usage:
  scripts/prime_brange_to_lean.py \
    --input output/prime_cert_brange_tcritical_2026-01-25_2046.txt \
    --output full/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_2046.lean \
    --digits 12
"""

from __future__ import annotations

import argparse
import datetime as dt
from decimal import ROUND_CEILING, ROUND_FLOOR, Decimal, getcontext
from pathlib import Path


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--input", required=True)
    p.add_argument("--output", required=True)
    p.add_argument("--digits", type=int, default=12)
    return p.parse_args()


def main() -> None:
    args = parse_args()
    inp = Path(args.input)
    outp = Path(args.output)

    getcontext().prec = max(50, args.digits + 10)
    quant = Decimal("1e-{}".format(args.digits))

    lines = inp.read_text().splitlines()
    margins = []
    prime_ubs = []
    prime_sums = []
    arch_terms = []
    tail_bound = None
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if "tail_bound" in line:
            parts = line.split("=", 1)
            if len(parts) == 2:
                tail_bound = Decimal(parts[1].strip())
        if line.startswith("B,"):
            continue
        if line[0].isdigit():
            parts = [p.strip() for p in line.split(",")]
            if len(parts) < 5:
                continue
            # B, prime_sum, prime_ub, arch_term, margin
            prime_sum = Decimal(parts[1])
            prime_ub = Decimal(parts[2])
            arch_term = Decimal(parts[3])
            margin = Decimal(parts[4])
            prime_ub_q = prime_ub.quantize(quant, rounding=ROUND_CEILING)
            arch_term_q = arch_term.quantize(quant, rounding=ROUND_FLOOR)
            prime_sum_q = prime_sum.quantize(quant, rounding=ROUND_CEILING)
            margin_q = margin.quantize(quant, rounding=ROUND_FLOOR)
            prime_sums.append(prime_sum_q)
            prime_ubs.append(prime_ub_q)
            arch_terms.append(arch_term_q)
            margins.append(margin_q)

    if not margins:
        raise SystemExit("No data rows parsed.")

    def fmt(d: Decimal) -> str:
        return format(d, "f")

    def render_fin_table(name: str, values: list[Decimal]) -> str:
        lines = [f"def {name} : Fin prime_b_grid_size -> ℚ"]
        for idx, val in enumerate(values):
            lines.append(f"| ⟨{idx}, _⟩ => {fmt(val)}")
        # fallback should be unreachable for Fin prime_b_grid_size
        lines.append(f"| _ => {fmt(values[-1])}")
        return "\n".join(lines)

    table_margin = render_fin_table("prime_b_grid_val_q", margins)
    table_prime_ub = render_fin_table("prime_b_grid_prime_ub_q_get", prime_ubs)
    table_prime_sum = render_fin_table("prime_b_grid_prime_sum_q_get", prime_sums)
    table_arch = render_fin_table("prime_b_grid_arch_term_q_get", arch_terms)
    ts = dt.datetime.now().strftime("%Y-%m-%d %H:%M")

    lean = f"""import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.A3_Floor_Bounds

/-! Prime B-range margin grid values for t_critical.
Source: {inp}
Generated: {ts}
Values are rounded to {args.digits} decimal places.
- margin and arch_term: rounded down (lower bounds)
- prime_ub: rounded up (upper bounds)
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Size of the B-grid certificate table. -/
abbrev prime_b_grid_size : Nat := 20

def prime_b_grid (i : Fin prime_b_grid_size) : ℝ :=
  B_min + (i.1 : ℝ) * prime_cert_B_h

/-- Grid margins for B in [B_min, prime_cert_B_max] with step prime_cert_B_h. -/
{table_margin}

/-- Grid prime upper bounds (same B grid). -/
{table_prime_ub}

/-- Grid prime partial sums (same B grid). -/
{table_prime_sum}

/-- Grid arch term lower bounds (same B grid). -/
{table_arch}

def prime_b_grid_val (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_val_q i : ℝ)

def prime_b_grid_prime_ub (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_prime_ub_q_get i : ℝ)

def prime_b_grid_prime_sum (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_prime_sum_q_get i : ℝ)

def prime_b_grid_arch_term (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_arch_term_q_get i : ℝ)

def prime_b_grid_tail_bound_q : ℚ := {tail_bound if tail_bound is not None else Decimal("0")}

def prime_b_grid_tail_bound : ℝ :=
  (prime_b_grid_tail_bound_q : ℝ)

def prime_cert_margin_lb_q : ℚ := (12 / 25)

lemma prime_cert_margin_lb_eq_q : (prime_cert_margin_lb : ℝ) = prime_cert_margin_lb_q := by
  norm_num [prime_cert_margin_lb, prime_cert_margin_lb_q]

/-- Table min bound in ℚ: every grid margin is ≥ prime_cert_margin_lb_q. -/
lemma prime_b_grid_val_ge_lb_q :
    ∀ i : Fin prime_b_grid_size,
      prime_cert_margin_lb_q ≤ prime_b_grid_val_q i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val_q, prime_cert_margin_lb_q] <;> norm_num

/-- Table min bound: every grid margin is ≥ prime_cert_margin_lb. -/
lemma prime_b_grid_val_ge_lb :
    ∀ i : Fin prime_b_grid_size,
      prime_cert_margin_lb ≤ prime_b_grid_val i := by
  intro i
  have hq : prime_cert_margin_lb_q ≤ prime_b_grid_val_q i := prime_b_grid_val_ge_lb_q i
  have hq' : (prime_cert_margin_lb_q : ℝ) ≤ (prime_b_grid_val_q i : ℝ) := by
    exact_mod_cast hq
  simpa [prime_cert_margin_lb_eq_q, prime_b_grid_val] using hq'

/-- Table min bound with Lipschitz slack in ℚ: every grid margin is ≥ lb + L*h/2. -/
lemma prime_b_grid_val_ge_lb_with_slack_q :
    ∀ i : Fin prime_b_grid_size,
      (prime_cert_margin_lb_q + (3/5) * (1/10) / (2:ℚ)) ≤ prime_b_grid_val_q i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val_q, prime_cert_margin_lb_q] <;> norm_num

/-- Table min bound with Lipschitz slack: every grid margin is ≥ margin_lb + L*h/2. -/
lemma prime_b_grid_val_ge_lb_with_slack :
    ∀ i : Fin prime_b_grid_size,
      prime_cert_margin_lb + prime_cert_L_ub * prime_cert_B_h / 2 ≤ prime_b_grid_val i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val, prime_b_grid_val_q, prime_cert_margin_lb,
          prime_cert_L_ub, prime_cert_B_h] <;> norm_num

/-! Table arithmetic: margin lower bound from arch/prime bounds. -/

lemma prime_b_grid_val_le_arch_sub_prime_ub_q :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_val_q i ≤
        prime_b_grid_arch_term_q_get i - prime_b_grid_prime_ub_q_get i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val_q,
          prime_b_grid_arch_term_q_get,
          prime_b_grid_prime_ub_q_get] <;> norm_num

lemma prime_b_grid_val_le_arch_sub_prime_ub :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_val i ≤
        prime_b_grid_arch_term i - prime_b_grid_prime_ub i := by
  intro i
  have hq :
      prime_b_grid_val_q i ≤
        prime_b_grid_arch_term_q_get i - prime_b_grid_prime_ub_q_get i :=
    prime_b_grid_val_le_arch_sub_prime_ub_q i
  have hq' :
      (prime_b_grid_val_q i : ℝ) ≤
        (prime_b_grid_arch_term_q_get i - prime_b_grid_prime_ub_q_get i : ℝ) := by
    exact_mod_cast hq
  simpa [prime_b_grid_val, prime_b_grid_arch_term, prime_b_grid_prime_ub] using hq'

/-! Table arithmetic: prime partial sum + tail bound ≤ prime_ub. -/

lemma prime_b_grid_prime_sum_add_tail_le_prime_ub_q :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_prime_sum_q_get i + prime_b_grid_tail_bound_q ≤
        prime_b_grid_prime_ub_q_get i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_prime_sum_q_get,
          prime_b_grid_prime_ub_q_get,
          prime_b_grid_tail_bound_q] <;> norm_num

lemma prime_b_grid_prime_sum_add_tail_le_prime_ub :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_prime_sum i + prime_b_grid_tail_bound ≤
        prime_b_grid_prime_ub i := by
  intro i
  have hq :
      prime_b_grid_prime_sum_q_get i + prime_b_grid_tail_bound_q ≤
        prime_b_grid_prime_ub_q_get i := prime_b_grid_prime_sum_add_tail_le_prime_ub_q i
  have hq' :
      (prime_b_grid_prime_sum_q_get i + prime_b_grid_tail_bound_q : ℝ) ≤
        (prime_b_grid_prime_ub_q_get i : ℝ) := by
    exact_mod_cast hq
  simpa [prime_b_grid_prime_sum, prime_b_grid_tail_bound, prime_b_grid_prime_ub] using hq'

end Q3.Proofs.PrimeCert
"""

    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(lean)


if __name__ == "__main__":
    main()
