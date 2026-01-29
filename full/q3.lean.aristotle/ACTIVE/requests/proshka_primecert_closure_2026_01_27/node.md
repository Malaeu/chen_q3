# Node: proshka_primecert_closure_2026_01_27

## Status
- state: in_progress
- updated: 2026-01-27

## Source
- request: `../../input/proshka_primecert_closure_2026_01_27.md`

## Why we are here
- Main chain depends on two PrimeCert axioms (`prime_b_grid_val_le_margin`, `prime_margin_Lipschitz_on_Brange`).
- Need an audit-resistant plan to remove these axioms (numerical certificate closure).

## Evidence / checks
- Axioms declared in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`.
- Symbolic Lipschitz skeleton exists in `Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean`.
- Grid table and slack lemma exist in `Q3/Proofs/PrimeCert/BrangeGrid_2046.lean`.

## Decision
- Ask Proshka for the minimal closure architecture (Lean-side verifier vs keep certificate-backed axioms).
