# NODE BRIEF - Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin

## Location
- File: `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`
- Declaration: `Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin`

## Goal (informal)
Replace axiom with theorem; no new axioms, no new imports.

## Fixed assumptions / invariants
- Single-scale mainline (t_critical).
- Avoid two-scale bridges.
- Use only already-imported lemmas.

## Preferred finish
- simp / linarith / nlinarith
- Avoid heavy `aesop` unless non-terminal
