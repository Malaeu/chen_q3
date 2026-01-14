# Sandbox Test: Pure Mathlib

## What to Prove

Three theorems using ONLY Mathlib facts:

1. `two_plus_two`: 2 + 2 = 4 (trivial arithmetic)
2. `add_self_gt`: For x > 0, x + x > x
3. `inv_tendsto_zero`: lim(1/n) = 0 as n → ∞

## Proof Hints

### two_plus_two
Just `rfl` or `norm_num` should work.

### add_self_gt
Use: `lt_add_of_pos_right` or `add_pos`
Key: x + x = x + x, and x > 0, so x + x > x + 0 = x

### inv_tendsto_zero
Use: `tendsto_const_div_atTop_nhds_zero_nat` or similar from Mathlib.Analysis.SpecificLimits

## Important

The formal_input_context file has NO custom axioms — only `import Mathlib`.
This tests whether Aristotle accepts pure Mathlib sandbox.
