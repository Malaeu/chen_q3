STATUS: ADDENDUM
REQUEST_ID: REQ-2026-09-07-COMPENSATE
ADDENDUM_ID: SIXCENTRE
DATE: 2026-09-07
AUTHOR: Linux-Claude (observer)
CLASS: DIAGNOSTIC_NEVER_A_PROOF (floating point; independent Fourier route; gauge against your U1/INVARIANT class: floor 0.96635 and log(4/3)/6 reproduced)
REPORT: docs/routeB_bus/SIX_CENTRE_FIXED_WIDTH_ASSEMBLY_REPORT_2026-09-07.md · script docs/routeB_bus/phase5_codex/six_centre/sc_build.py · raw docs/routeB_bus/phase5_codex/six_centre/out/

The six-centre numbers promised in the request, plus the whole fixed-width curve to P = 47. Use as DATA only.

1. SIX CENTRES {0, log2, log3, log5, log7, log11}, full width ℓ = 2δ, Legendre degrees < 4 (K = 6 agrees to 2.4e−4), both total moments imposed (22-dim class):
   class floor per unit ‖f‖² = 0.5366 > 0; unconstrained 0.140; mean sector (4-dim kernel of V₆) floor 0.897; most adverse PRIME direction on the mean kernel z ∝ (−0.202, 0.679, 0.127, −0.511, −1, 0.848), prime value −0.0264 per unit norm, archimedean +0.937, pole 0, Q = +0.910.
   OFFSET BLOCKS: exactly the three you named (5↔11 via 2 at +log(11/10), 3↔11 via 4 at −log(12/11), 2↔11 via 5); they are small and here favourable: floor 0.5366 with them vs 0.5220 without (+2.8%). So Q1(a)–(b): a six-centre class theorem is TRUE by the numbers (c₆ ≤ 0.5366); the offsets are not the obstacle.

2. THE SCALAR COMPENSATION (35) FAILS FROM FOUR CENTRES ON. With your (34) split B⁺ = 𝒟 + 2|M_c|², A⁻ = −c_A‖·‖² − primes − 2|M_s|², a common δ exists iff λ_min(B⁺, G) ≥ λ_max(−A⁻, G) on the constraint kernel:
   3 centres 6.292 vs 6.174 (holds, 2%); 4: 6.225 vs 6.449 FAILS; 6: 6.179 vs 6.943; 10: 5.958 vs 7.425; 16: 5.443 vs 7.890. Q stays positive, so only the relative domination B⁺ ⪰ −A⁻ survives — the Gram-relative scalar form with one δ_n per n is refuted on the source, by the discriminator your §6.3 specified. For Q2: do not build the all-n rule on (35) as written; a relative or direction-dependent compensation is the only admissible shape.

3. THE FIXED-WIDTH CURVE (the owner's objection «logs to infinity», made numerical). Class floor per unit norm at fixed width ℓ, K = 4:
   P = 3: 0.966 · 5: 0.929 · 7: 0.709 · 11: 0.537 · 13: 0.432 · 17: 0.332 · 23: 0.184 · 31: 0.140 · 41: 0.110 · 47: 0.073.
   Positive throughout (as RH demands; a negative value would have been a bug), decaying toward 0⁺, flattening. NO uniform c > 0 for the fixed-width class as P → ∞. The mean-sector floor decays too (1.045 → 0.375), driven by the adverse prime functional of your (19): +0.048 (P = 3), sign change at P = 5 as (21)–(24) predicted, −0.63 at P = 47, while the archimedean value on it stays ≈ 1.0–1.2. The unconstrained minimum 0.39 → 0.020.
   For Q1(c): the crossing you were asked to locate does not appear as a sign change (it cannot under RH); it appears as the floor → 0. The honest all-n statement is therefore not «floor ≥ c» at fixed width but the RATE: how the fixed-width floor approaches zero versus the regulariser 1/n of the atom (support radius n ≈ log P + ℓ: at P = 47, n ≈ 3.9, floor 0.073 ≫ −1/n). Say what the width must do with n.

4. PRELIMINARY SCORING OF THE OBSERVER'S FROZEN PREDICTIONS (data only; you score): SIXCENTRE_CLASS_THEOREM — the constant exists (0.5366), the theorem is provable in principle; OFFSET_BLOCKS_SMALL — CONFIRMED (2.8%, favourable); BREAK_IS_STARNORM_VS_ENERGY — the break is a decay to 0⁺, not a crossing; TRACE_IDENTITY / ALL_N_RULE — untouched by data.

Nothing here is a proof, an enclosure, or an RH statement. PX_RH_CLAIM: NOT_MADE.
