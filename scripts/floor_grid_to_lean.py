#!/usr/bin/env python3
"""Convert floor_grid_tcritical output into a Lean grid table.

Usage:
  scripts/floor_grid_to_lean.py \
    --input full/q3.lean.aristotle/output/floor_grid_tcritical_2026-01-25_2219.txt \
    --output full/q3.lean.aristotle/Q3/Proofs/FloorCert/Grid_2219.lean \
    --digits 18
"""

from __future__ import annotations

import argparse
import datetime as dt
from decimal import Decimal, getcontext, ROUND_FLOOR
from pathlib import Path


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--input", required=True)
    p.add_argument("--output", required=True)
    p.add_argument("--digits", type=int, default=18)
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
        if not line.strip():
            continue
        if line.startswith("i\t"):
            continue
        if line[0].isdigit() or (line[0] == '-' and len(line) > 1 and line[1].isdigit()):
            parts = line.split("\t")
            if len(parts) < 3:
                continue
            # idx = int(parts[0])
            val = Decimal(parts[2])
            # lower bound: floor to given decimals
            val_q = val.quantize(quant, rounding=ROUND_FLOOR)
            data.append(val_q)

    if not data:
        raise SystemExit("No data rows parsed.")

    # Build Lean array literal
    def fmt(d: Decimal) -> str:
        s = format(d, f"f")
        return s

    arr_items = ", ".join(fmt(d) for d in data)
    ts = dt.datetime.now().strftime("%Y-%m-%d %H:%M")

    lean = f"""import Mathlib
import Q3.Proofs.FloorCert.Defs
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

/-! Grid certificate values for t_critical.
Source: {inp}
Generated: {ts}
Values are rounded *down* to {args.digits} decimal places.
-/-

noncomputable section

namespace Q3.Proofs.FloorCert

def floor_grid_vals : Array ℝ := #[{arr_items}]

def floor_grid_val (i : Fin (floor_cert_N + 1)) : ℝ :=
  floor_grid_vals.get! i.1

/-- Table-to-function bridge: values are below the true P_A at grid points. -/
axiom floor_grid_val_le_P_A :
    ∀ i : Fin (floor_cert_N + 1),
      floor_grid_val i ≤ P_A B_min t_critical (floor_grid i)

/-- Table min bound: every grid value is ≥ floor_cert_min_lb. -/
axiom floor_grid_val_ge_min_lb :
    ∀ i : Fin (floor_cert_N + 1),
      floor_cert_min_lb ≤ floor_grid_val i

/-- Grid certificate: min bound holds at every grid point. -/
lemma P_A_floor_cert_on_grid_cert :
    ∀ i : Fin (floor_cert_N + 1),
      floor_cert_min_lb ≤ P_A B_min t_critical (floor_grid i) := by
  intro i
  exact le_trans (floor_grid_val_ge_min_lb i) (floor_grid_val_le_P_A i)

end Q3.Proofs.FloorCert
"""

    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(lean)


if __name__ == "__main__":
    main()
