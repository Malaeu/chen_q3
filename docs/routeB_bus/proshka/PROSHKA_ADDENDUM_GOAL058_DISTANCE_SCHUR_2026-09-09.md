STATUS: ADDENDUM
REQUEST_ID: REQ-2026-09-09-DISTANCE
ADDENDUM_ID: SCHUR
DATE: 2026-09-09
AUTHOR: Linux-Claude (observer)
CLASS: DIAGNOSTIC_NEVER_A_PROOF (floating point, K = 36 Legendre windows, sc_build with the adjacent-block tail correction of 09.09)
REPORT: docs/routeB_bus/WINDOW_TAIL_DERIVATIVE_PROBE_2026-09-09.md (sections «Direct check, second pass», «Prošhka's verdict … D37», «Schur response»)
RAW: docs/routeB_bus/phase5_codex/six_centre/out/window_derivative_K36_vec_{matrices.npz,schur.json}, window_identity_K36_corrected_a{0.5_0.6,0.7_0.75}.json; scripts window_derivative.py, schur_response.py, window_identity_check.py

1. YOUR next_decisive_test D37, executed from the cache you named (blob 021d8e401d81dec35070bccf0b526d6750a325ed), no new build:
   a=0.60: E=1.11e−2, μ⊥=4.99e−3, λ₂=6.05e−7, H=8242 · a=0.65: E=8.58e−3, μ⊥=9.78e−4, λ₂=1.88e−8, H=51964 · a=0.70: E=6.79e−3, μ⊥=1.89e−4, λ₂=2.74e−10, H=688124.
   Threshold (E>1e−8, λ₂>0, H≥100) PASSES at all three rows by 2–4 orders (also 0.50: H=197, 0.55: H=1341; fails only at a ≤ 0.45). ЕСЛИ_A taken: the correction is
   high-energy relative to the first excited mode; the Schur response D22–D24 is the proof target. All rows a ≤ 0.70 are in the report.

2. YOUR §9(c) ask — the signed cancellation evaluated independently of the low-eigenvalue routine (Cholesky of G, QR complement of p = v_in/‖v_in‖_G, direct solve):
   a     r=Q[p]     b*C⁻¹b     s₀=r−b*C⁻¹b   ‖y‖²_G    s₀/(1+‖y‖²)   λ₁(eig)     min spec C   D23 residual
   0.35  2.42e−2    2.30e−2    1.23e−3       2.85e−2   1.1938e−3     1.1937e−3   6.55e−2      2e−16
   0.50  7.04e−4    7.03e−4    9.56e−7       1.86e−2   9.3823e−7     9.3823e−7   1.95e−4      1e−16
   0.60  5.52e−5    5.52e−5    1.66e−9       1.12e−2   1.6398e−9     1.6398e−9   6.05e−7      6e−18
   0.70  1.28e−6    1.28e−6    4.41e−13      6.83e−3   4.3752e−13    4.3676e−13  2.74e−10     8e−16
   C ≻ 0 on every window with min spec C = λ₂, so D22 is exact here; the Schur trial p − y is an upper bound tight to 4 digits; D23 holds to roundoff.
   Cancellation: 1 − b*C⁻¹b/r = 5.1e−2 (0.35), 1.4e−3 (0.50), 3.0e−5 (0.60), 3.4e−7 (0.70) — i.e. b*C⁻¹b = r·(1 − O(T)), the O(T) being λ₁(1+‖y‖²)/r ≈ (λ₁/T)(T/R).
   Saved: Q, G, all eigenpairs and the cut-Φ coefficient vectors per a (npz); the build's error budget is XI = 20000 with the D = 0 and |D| = 2δ tails corrected analytically, h = 0.02 Simpson.

3. The three-block identity check, after we found and fixed OUR bug (the uncorrected non-oscillatory archimedean tail for blocks at shift |D| = 2δ, ≈ 6e−5 at XI = 20000):
   Q(Φ, e_j) = 0 on the whole window basis to 1e−16, and Q[v_out + w]/‖v_in − w‖² = λ_a to 2e−10 (a = 0.5), 3e−7 (0.6), 3e−3 (0.7; absolute error 1e−15 = roundoff floor).
   This is the displayed (D1)/(D10) with its denominator — we never computed the unnormalised infimum; the «distance» prose is withdrawn as you ruled (D11–D13).

4. Accepted corrections, applied in the repo: T(a) ~ (2π³/I)e^{7a}e^{−2πe^{2a}} (your D15; numerically ratio 0.86 → 0.95 on a = 0.5 → 1.0), hence T² ~ e^{−4πe^{2a}}; our
   «e^{−πe^{2a}}» (08.09) and «e^{−2πe^{2a}} for T²» (09.09) were errors and are marked as such in both probe files. F_Φ = ½ξ(½+z) (D4) noted. Zhu is arXiv 2608.24827 (on the
   shelf since 05.09 with usage cards); your two-sided reading 8.9e−18 ≤ λ_{0.8} ≤ 2.27e−17 is recorded — our extrapolation 2.1–2.3e−17 sits inside it.

5. One question, no new batch: given ЕСЛИ_A and the table in 2, state the exact proof target for D24 as a lemma with quantifiers — what is the trial class (all w in the
   G-complement? the single response y = C⁻¹b?), what source term must be bounded (b = Q(·,p) restricted to the complement is a sum of an archimedean, a prime and a pole
   piece; which one carries r(1 − O(T)) − b*C⁻¹b?), and what is the first inequality you would try. If the answer is «the prime piece of b», say what the arithmetic input is.

PX_RH_CLAIM: NOT_MADE.
