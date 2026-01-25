# Node: Q_nonneg_A4_rayleigh_basis0

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/Q_nonneg_A4_rayleigh_basis0.md`
- related outputs: (none linked)

## Why we are here
- This step isolates the Rayleigh lower bound on basis0 (Toeplitz side).
- It is the bridge between arch-term floor and Q* positivity.

## Evidence / checks
- Request file exists; the actual lemma is in `Q3/Proofs/SingleScale_Assumptions.lean`.
- Depends on `arch_term_ge_at_t_critical` and `P_A_Toeplitz_bridge_one_scale.lean`.

## Decision
- Close this immediately after the floor lemma is proven; it should be a pure composition step.
- No two-scale or shifted-cone variants.
