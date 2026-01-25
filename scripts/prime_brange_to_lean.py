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
from decimal import ROUND_FLOOR, Decimal, getcontext
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
    data = []
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.startswith("B,"):
            continue
        if line[0].isdigit():
            parts = [p.strip() for p in line.split(",")]
            if len(parts) < 5:
                continue
            # B, prime_sum, prime_ub, arch_term, margin
            margin = Decimal(parts[4])
            margin_q = margin.quantize(quant, rounding=ROUND_FLOOR)
            data.append(margin_q)

    if not data:
        raise SystemExit("No data rows parsed.")

    def fmt(d: Decimal) -> str:
        return format(d, "f")

    arr_items = ", ".join(fmt(d) for d in data)
    ts = dt.datetime.now().strftime("%Y-%m-%d %H:%M")

    lean = f"""import Mathlib
import Q3.Proofs.PrimeCert.Defs

/-! Prime B-range margin grid values for t_critical.
Source: {inp}
Generated: {ts}
Values are rounded *down* to {args.digits} decimal places.
-/-

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Grid margins for B in [B_min, prime_cert_B_max] with step prime_cert_B_h. -/
def prime_b_grid_vals_q : Array ℚ := #[{arr_items}]

def prime_b_grid_val_q (i : Fin (prime_b_grid_vals_q.size)) : ℚ :=
  prime_b_grid_vals_q.get! i.1

def prime_b_grid_val (i : Fin (prime_b_grid_vals_q.size)) : ℝ :=
  (prime_b_grid_val_q i : ℝ)

def prime_cert_margin_lb_q : ℚ := (1 / 2)

lemma prime_cert_margin_lb_eq_q : (prime_cert_margin_lb : ℝ) = prime_cert_margin_lb_q := by
  norm_num [prime_cert_margin_lb, prime_cert_margin_lb_q]

/-- Table min bound: every grid margin is ≥ prime_cert_margin_lb. -/
lemma prime_b_grid_val_ge_lb :
    ∀ i : Fin (prime_b_grid_vals_q.size),
      prime_cert_margin_lb ≤ prime_b_grid_val i := by
  intro i
  have hq : prime_cert_margin_lb_q ≤ prime_b_grid_val_q i := by
    decide
  have hq' : (prime_cert_margin_lb_q : ℝ) ≤ (prime_b_grid_val_q i : ℝ) := by
    exact_mod_cast hq
  simpa [prime_cert_margin_lb_eq_q, prime_b_grid_val] using hq'

end Q3.Proofs.PrimeCert
"""

    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(lean)


if __name__ == "__main__":
    main()
