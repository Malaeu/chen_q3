# Node: Rayleigh_integral_P_A_eq_arch_term

## Status
- state: verified
- updated: 2026-01-25

## Source
- request: `../../input/Rayleigh_integral_P_A_eq_arch_term.md`
- related outputs: (none linked)

## Why we are here
- This is the analytic bridge: identify the arch term with the integral of the symbol used in Rayleigh/Toeplitz.
- Needed for clean wiring between `arch_term_ge_at_t_critical` and the Rayleigh lower bound.

## Evidence / checks
- Lemma exists in `Q3/Proofs/ShiftedWindows.lean`: `integral_P_A_shift_eq_arch_term`.
- Non-shifted version also exists in `Q3/Proofs/Rayleigh_Q_identification.lean`: `integral_P_A_eq_arch_term`.
- This is a short rewrite/periodization identity (no heavy analysis in Lean).

## Decision
- Treat as available; reuse `integral_P_A_shift_eq_arch_term` with `tau = 0` in single-scale proofs.
- No new lemma needed unless a typeclass/performance wrapper is required.
