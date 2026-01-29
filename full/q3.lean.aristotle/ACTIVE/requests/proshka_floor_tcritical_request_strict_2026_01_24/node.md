# Node: proshka_floor_tcritical_request_strict_2026_01_24

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/proshka_floor_tcritical_request_strict_2026_01_24.md`
- related outputs:
  - `../../output/proshka_context_floor_tcritical.md`
  - `../../output/proshka_floor_tcritical_bundle_2026_01_24.md`

## Why we are here
- Same floor-at-t_critical blocker as the non-strict request, but we want a strict, no-detour Proshka response.
- The goal is a Lean-ready lemma (or explicit micro-lemmas) with file/lemma pointers only.

## Evidence / checks
- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` depends on `h_floor` at `t_critical`.
- `arch_term_ge_at_t_critical` already uses this floor as input, so the gap is isolated and well-posed.
- Bundled context outputs:
  - `../../output/proshka_context_floor_tcritical.md`
  - `../../output/proshka_floor_tcritical_bundle_2026_01_24.md`

## Decision
- Keep single-scale only, tau = 0. No two-scale bridges, no alternative parameter regimes.
- Request the minimal lemma statement(s) that can be pasted into `Q3/Proofs/A3_Floor_Critical_Goal.lean` or nearby.
