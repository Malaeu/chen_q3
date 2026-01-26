# Node: proshka_primecert_lipschitz_2026_01_26

## Status
- state: in_progress
- updated: 2026-01-26 15:47

## Source
- request: `../../input/proshka_primecert_lipschitz_2026_01_26.md`

## Why we are here
- PrimeCert B-range axioms are certificate-backed; long‑term goal is analytic closure.
- Need a Lipschitz‑in‑B bound for the margin and a way to eliminate grid‑point axioms.

## Evidence / checks
- `prime_margin_Lipschitz_on_Brange` is used in `Q3/Proofs/PrimeCert/Brange_2046.lean`.
- `prime_b_grid_val_le_margin` links grid values to the true margin at grid points.

## Decision
- Ask Proshka for a Lean‑ready lemma chain (or monotonicity reduction) to close these axioms.
