# Node: proshka_floor_tcritical_request_2026_01_24

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/proshka_floor_tcritical_request_2026_01_24.md`
- related outputs:
  - `../../output/proshka_context_floor_tcritical.md`
  - `../../output/proshka_floor_tcritical_bundle_2026_01_24.md`

## Why we are here
- Single-scale chain blocks on a missing floor bound at t_critical; this is the last analytic input needed for `rayleigh_basis0_shift_ge_cstar_quarter`.
- We need a Proshka-grade synthesis that either produces a Lean-friendly lemma or isolates the exact missing sub-lemmas (no extra branches).

## Evidence / checks
- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` now takes a `h_floor` hypothesis; the missing piece is the floor itself at `t_critical`.
- `Q3/Proofs/Q_nonneg_t_critical.lean` already rewrites `arch_term_ge_at_t_critical` to assume the floor bound.
- Outputs bundled in:
  - `../../output/proshka_context_floor_tcritical.md`
  - `../../output/proshka_floor_tcritical_bundle_2026_01_24.md`

## Decision
- Ask Proshka to produce a minimal, Lean-ready lemma for the floor at `t_critical` (or a decomposition into 2-3 micro-lemmas with file/lemma names).
- Keep scope single-scale and tau = 0; no two-scale detours.
