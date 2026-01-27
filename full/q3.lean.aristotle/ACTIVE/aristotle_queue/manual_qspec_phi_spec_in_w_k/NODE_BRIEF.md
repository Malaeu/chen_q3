# NODE BRIEF — Φ_spec_in_W_K

## Location
- File: `Q3/Proofs/QSpec.lean`
- Declaration: `Φ_spec_in_W_K`

## Goal (informal)
Show `Φ_spec spec ∈ W_K spec.K` using continuity + support + even + nonneg.
Only continuity/support subgoals are unfinished (two sorries).

## Fixed assumptions / invariants
- Single-scale; no two-scale bridges.
- No new imports or defs.
- Use already-imported lemmas.

## Available lemmas (already imported)
- `Q3.Proofs.ShiftedWindows.continuous_phi_shift`
- `Q3.Proofs.ShiftedWindows.phi_shift_support` / `phi_shift_support_of_margin`
- `Q3.fejer_heat_window_nonneg`

## Preferred finish
- `simp`, `linarith`, `nlinarith`.
- Avoid heavy `aesop` unless non-terminal.
