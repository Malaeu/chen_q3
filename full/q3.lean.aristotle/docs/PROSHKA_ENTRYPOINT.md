# PROSHKA ENTRYPOINT (READ THIS FIRST)

Purpose: Provide the minimal, current context for Q3 formalization.
All other files are optional and linked below.

## 1) Contract (must match RH_Q3)
- docs/PROJECT_SPECS.md
- docs/insights/rh_q3_invariants_contract_2026_01_16.md

## 2) Current status and next step
- PROJECT_ORCHESTRATOR.md (Active Next Step)
- PROJECT_WORKFLOW.md

## 3) Drift checklist (red flags)
- A3 symbol must be P_A (period-1); do not use a_star as A3 symbol.
- Toeplitz in A3 must be Fourier/Rayleigh, not sampling P(π(i-j)/M).
- Prime operator must be compression/rank-one sum with w_Q.
- Keep t_sym and t_rkhs distinct; do not mix w_Q and w_RKHS.

## 4) If stuck
- docs/INSIGHTS.md + docs/insights/INDEX.md
- docs/ERRORS_DESTROYER.md

## 5) Current Proshka request
- PROSHKA_REQUEST_4.md (single-scale closure pack; 3 open axioms)

## 6) Packed context (one file)
- PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md
 - Build script: scripts/build_proshka_brief.py

## 7) Policy (canonical set)
- docs/PROSHKA_POLICY.md

## 8) Legacy
- PROSHKA_REQUEST_3.md (archive only)
