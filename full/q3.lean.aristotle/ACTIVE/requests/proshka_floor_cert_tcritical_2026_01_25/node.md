# Node: proshka_floor_cert_tcritical_2026_01_25

## Status
- state: in_progress
- updated: 2026-01-25 15:22

## Source
- request: `../../input/proshka_floor_cert_tcritical_2026_01_25.md`
- related outputs:
  - `../../output/proshka_floor_cert_tcritical_bundle_2026_01_25.md`

## Why we are here
- FloorGoal at t_critical depends on a certified lower bound for P_A on Icc(-1/2, 1/2).
- This is the remaining `sorry` in `P_A_ge_c_star_at_t_critical`.

## Evidence / checks
- Wrapper proof in `Q3/Proofs/A3_Floor_Critical_Proof.lean` compiles and reduces FloorGoal to this lemma.
- The proof in `Q3/Proofs/Q_nonneg_t_critical.lean` is still `sorry`.

## Decision
- Ask Proshka for a Lean-ready certificate or minimal lemma decomposition.
- Single-scale only, tau = 0; no two-scale variants.
