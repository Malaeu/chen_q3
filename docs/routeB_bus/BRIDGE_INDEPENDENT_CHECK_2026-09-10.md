# BRIDGE independent check — 2026-09-10

Verdict: ACCEPTED as a paper derivation at the stated scope. FIRST_INCORRECT_ASSERTION: NONE_FOUND. RH remains unproved; production HOLD and PX_RH_CLAIM: NOT_MADE remain unchanged.

## Provenance

One fresh native read-only checker, bridge_verdict_check (gpt-5.6-terra/xhigh), read the full request and verdict and all five pinned shelf files. No descendants. Target: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_BRIDGE_2026-09-09.md at 4ae462655affe4e3511a765a54a04a6510338f72; SHA256 0d2117118585b58acc6f765f3692b5d536e3fb832039c29d9680e12ebbaf0550; blob24c934f63e3e28a448f3989014bbadca154a94bc; 47350 bytes,605 lines,final LF. Parent verified bytes, request ancestry and one-path commit independently. Request b968f9443d5491778ab5e65c75c4ad7d64ba0b14; shelf952bb52113fe3ff6881c905e7c8557846cfe96df.

## Display audit

| Display | Verdict lines | Classification |
|---|---:|---|
| B0 |41–45|VERIFIED|
| B1 |101–107|VERIFIED|
| B2 |126–140|VERIFIED|
| B3 |144–156|VERIFIED|
| B4 |157–162|VERIFIED|
| B5 |164–177|VERIFIED|
| B6 |181–191|VERIFIED|
| B7 |207–211|VERIFIED|
| B8 |217–229|VERIFIED|
| B9 |233–242|VERIFIED|
| B10 |265–270|VERIFIED|
| B11 |274–286|VERIFIED|
| B12 |287–293|VERIFIED|
| B13 |297–303|VERIFIED|
| B14 |305–313|VERIFIED|
| B15 |346–355|VERIFIED|
| B16 |357–361|VERIFIED|
| ATOM |372–381|PLAUSIBLE, explicitly unproved target|
| B17 |383–389|VERIFIED|
| B18 |391–398|VERIFIED conditional on ATOM|
| B19 |402–405|VERIFIED on bounded blocks|
| B20 |407–417|VERIFIED on positive-block chains|
| B21 |419–425|VERIFIED when limiting recovery is finite|
| B22 |477–483|VERIFIED arithmetic of published rounded data|
| B23 |485–490|VERIFIED with upper endpoint of signed interval|
| TEST |507–519|VERIFIED finite discriminator definition; not executed in verdict|

## Mathematical checks

B10–B16: L=IT and N²=I(1−T). The jump estimate and pointwise tail envelope imply D[t]=L log(e^(2a))+O(L). B13 includes two same-side overlaps and the opposite-side overlap only for u>=2a. The entire prime-power lattice is bounded using Lambda(n)<=log(n), with no prime-number theorem or finite prime truncation. Both pole moments contribute O(e^(−a)L). Thus Q[t]=(2a+O(1))L holds for this source. The resulting obstruction excludes c=0 only; it does not exclude the derivative shells.

B2–B9: antilinear-first pairings, N factors, cut/tail energy identities and distinct coefficient-choice and positive-majorant losses are consistent. Negative, coupled-null and decoupled-null cases are preserved. Abstract examples prove only nonreversal from finite algebra, not theta-source strictness.

B17–B18: unrestricted degree permits least-degree selection after assuming ATOM. Factor-two slack avoids assuming attainment of the limiting infimum. This is a conditional existence equivalence, not proof of ATOM or an effective degree-growth law. B20 does not lower-bound recovery merely from small positive pivots. B21 retains the full uniform precision requirement.

## Independent parent arithmetic

16420.4321288621 − 1.069376844 = 16419.3627520181.

For B22, subtraction of the signed interval gives [99602.7920418505,99602.7920418525]. The displayed midpoint99602.7920418515 lies inside it. Parent initially compared B23 to the signed midpoint, but the verdict correctly uses the upper endpoint for a lower bound; no verdict correction is needed.

## Source limits

Checker verified local Suzuki v1 PDF (docs/routeB_bus/litreview/pdfs/2606.09096.pdf), its June8/June9 dates and page13 formula(3.1), and live v1 HTML with August24 body date. DLMF25.4.4 and20.7.32 supply the stated normalization and theta inversion. These external-source observations are checker evidence; parent did not independently repeat them. Suzuki v2 remains UNVERIFIED; no cofinal result is imported from it. Historical numerical certificates remain pinned report evidence, not fresh reruns by the checker.

## Next finite test

The reviewed plan evaluates reference-minimizer signed energy against(107/100)T² at a=.7,m=6. Input coefficient intervals must come from a rigorous interval solve, not merely residual containment. Parent independently reconstructed saved H and ell, ran512-bit interval LU and confirmed all eight coefficient enclosures and Z overlap the saved preconditioned solve. Cached basis majorants and full coefficient errors propagate through Lobatto synthesis and S41. The new computation is separate from this accepted paper audit and remains provisional until its implementation/results are reviewed. No finite outcome establishes ATOM, lower sign or RH.

## BRIDGE finite TEST accepted — 2026-09-10

The separate implementation review has converged: one MEDIUM provenance finding fixed by pre-run dependency hash assertions; two subsequent clean confirmations, no open findings. Post-patch background recheck exit0 reproduced the result. At a=7/10,m=6, the exact positive-reference minimizer has Q[f_B]/T²=[2.268595464 +/-1.90e-10], and (107/100)T²−Q[f_B]=[-7.89858308e-13 +/-4.40e-22]. The serialized margin itself passes tenfold error separation; parent independently recomputed subtraction and sign. Full E-transfer uncertainty is about1.16809846e-22. This is ACCEPTED_FINITE_ELSE_B only: the reference coefficient fails a finite budget met by the prior signed row, so coefficient choice matters. No positivity of C is inferred, and no cofinal target is settled.

Reproduction and complete intervals: docs/routeB_bus/phase5_codex/six_centre/out/bridge_reference_test_20260910.json. Source container remains unchanged. Next justified analytic question: uniform accumulated full-source recovery B20–B21 in the exact derivative family; do not refine this already resolved scalar again. Lower sign remains a separate unpaid supplier.
