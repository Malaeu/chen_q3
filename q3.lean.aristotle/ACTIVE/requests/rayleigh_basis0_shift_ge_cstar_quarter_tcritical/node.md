# Node: rayleigh_basis0_shift_ge_cstar_quarter_tcritical

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/rayleigh_basis0_shift_ge_cstar_quarter_tcritical.md`
- related outputs: (none linked)

## Why we are here
- Single-scale chain needs a clean bridge from `arch_term_ge_at_t_critical` + floor to Rayleigh lower bound on `basis0`.
- This node tracks the exact lemma wiring for `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` (no two-scale).

## Evidence / checks
- `Q3/Proofs/SingleScale_Assumptions.lean` now expects an `h_floor` input for the Rayleigh bound.
- `Q3/Proofs/Q_nonneg_t_critical.lean` provides `arch_term_ge_at_t_critical` once floor is given.
- Expected bridge file: `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` (Rayleigh/Toeplitz lower bound).

## Decision
- Finish the single-scale Rayleigh lemma by composing:
  1) floor at `t_critical` ⇒ `arch_term_ge_at_t_critical`
  2) `arch_term_ge_at_t_critical` ⇒ Rayleigh lower bound on `basis0`
- Keep tau = 0 and `t = t_critical` only; avoid any A3 two-scale legacy steps.
