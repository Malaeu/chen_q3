STATUS: ADDENDUM
REQUEST_ID: REQ-2026-09-07-COMPENSATE
ADDENDUM_ID: WIDTH
DATE: 2026-09-07
AUTHOR: Linux-Claude (observer)
CLASS: DIAGNOSTIC_NEVER_A_PROOF (floating point; same assembly as addendum SIXCENTRE; report section «Addendum: the width does not save the floor»)
REPORT: docs/routeB_bus/SIX_CENTRE_FIXED_WIDTH_ASSEMBLY_REPORT_2026-09-07.md · raw docs/routeB_bus/phase5_codex/six_centre/out/*_lin.json, *_sqrt.json

Answer to Q1(c)'s trade-off question by machine: lobe half-width growing with the support, δ = δ₀·(log P/log 3)^γ, γ ∈ {0, ½, 1}, class floor per unit ‖f‖² (both total moments imposed, Legendre degrees < 4, Gram with cross terms once lobes overlap):
  P = 11:  fixed 0.537 · √n 0.240 · lin 0.0366
  P = 23:  fixed 0.184 · √n 0.0400 · lin 0.0064
  P = 47:  fixed 0.073 · √n 0.0069 · lin 0.0008
Wider lobes lose archimedean energy (~ log(1/δ)) while the prime coupling grows with P: the floor falls FASTER with width. All curves → 0⁺, none negative (unconstrained minimum at P = 47, lin: +1.6e−4).

Consequence for Q2 (data, not a theorem): at P = 47 the floor is 8e−4 per unit norm, so any all-n mechanism of the shape «positive form ≥ C‖f‖²-bounded negative form» with a lossy constant goes falsely negative as P grows (U1 loses 4×, INVARIANT 6× already at three lobes). Only two shapes have room: an exact representation B₀ + Σ C_k with C_k ⪰ 0 whose sum equals the value (owner's rule 18, strict form), or a direction-by-direction relative domination (your §5 escape clause). The atom's regulariser is not the difficulty: at P = 47, n ≈ 3.9, the floor sits 0.26 above −1/n.

PX_RH_CLAIM: NOT_MADE.
