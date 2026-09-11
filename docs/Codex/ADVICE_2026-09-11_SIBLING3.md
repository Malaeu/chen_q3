TO: MAT

# ADVICE SIBLING3 — dictionary Connes–Consani Thm 1 ↔ Castelnuovo on span{Δ, Γ_F} (observer, 2026-09-11 22:00; HYPOTHESIS, verify)

Your caution is correct: «only two fibres left» is not justified as stated, because CC-WEILPOS-2020 (arXiv:2006.13771, p.3)
has the defect term c·|ĝ(0)|², 13 < c < 17, between the Sonin trace and the Weil form:
    (4)  W_∞(g∗g*) ≥ Tr(ϑ(g) S ϑ(g)*)      for supp g ⊂ [2^{-1/2}, 2^{1/2}], ĝ(i/2) = ĝ(0) = 0,
    (6)  c|ĝ(0)|² + Σ_{s∈S} ĝ(s)ĝ(s̄)‾ ≥ Tr(ϑ(g) S ϑ(g)*).
Read through the finite sibling (SIBLING2: V = Aᵀ T_μ A, T_μ = normalized Castelnuovo form 2d1d2 − D²), the page gives a dictionary:

| CC Thm 1 / (6)                                        | function field (SIBLING2)                          |
|-------------------------------------------------------|----------------------------------------------------|
| ĝ(0) = 0 and ĝ(i/2) = 0                               | D·H1 = 0 and D·H2 = 0 (primitive part)             |
| defect c·|ĝ(0)|²                                       | the fibre term 2·d1·d2                              |
| «Schwartz kernel δ(λx−y) of the scaling action corresponds geometrically to the divisor of the Frobenius correspondence» (their Fact, p.3) | Γ_F |
| supp g ⊂ [2^{-1/2}, 2^{1/2}]  (g∗g* sees only the prime 2 and ∞) | span{Δ, Γ_F}: one Frobenius power, our genus-1 block |
| positivity proved only on that support                 | Castelnuovo for k ≤ 1                              |

Claim to test (PAPER): CC Theorem 1 is the number-field analogue of Hodge index on span{Δ, Γ_F} restricted to primitive classes.
The wall is then growth of the support to [1/N, N] (the form sees all primes ≤ N) ⟷ span{Γ_{F^k}, k ≤ log N}; RH ⟺ all k.
Checks, cheapest first:
  (a) In the sibling, write the primitive-part condition and the fibre term explicitly for span{Δ,Γ_F}: C = 2d1d2 − D², with
      d1 = D·H1, d2 = D·H2; confirm that on d1 = d2 = 0 the form is −D² and that this is the genus-1 block [[2,−a/√q],[−a/√q,2]]
      after the q^{-(i+j)/2} normalization (the observer verified the block, not the H-decomposition).
  (b) Match ĝ(0), ĝ(i/2) with the two pole contributions of ζ (s = 1, 0) exactly as (1−T)(1−qT) in Z(T) = P/((1−T)(1−qT)):
      the fibre classes H1, H2 ARE the poles. If this holds, c|ĝ(0)|² is the number-field shadow of 2d1d2, not a nuisance.
  (c) Identify what in CC replaces «k = 1»: the support length log 2 (only p = 2). State what breaks for support [1/N, N] in their
      Toeplitz control (Thm 6.11): is c(N) bounded, or does the defect grow with N?
Victory for SIBLING3 = (a)+(b) proved and (c) answered with an exact locator in CC. IF_A: dictionary exact → the next Proshka request
is «Castelnuovo for k ≤ K via Sonin compression with K primes», the wall named as K → ∞. IF_B: (b) fails → record the exact
mismatch between poles and fibres; that mismatch is the wall as an object. No new grid, no re-derivation of SL1–SL24.
