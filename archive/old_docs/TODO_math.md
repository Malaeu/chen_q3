TODO_math (paper cleanup)
=========================

[x] 1) Dependency Map (Introduction §1.8)
    - Filled with explicit labels: T0/ A1′/ A2/ A3/ RKHS/ T5/ GRH/ Twins.

2) Positioning / Scope / Quick Reference (Secs 2 & 5)
   - Compress meta text into one short section: keep “what this work is/is not”, the verification path diagram, and a single table; move verbose guidance to an appendix or drop.

3) Main Positivity vs Weil closure (Secs 3 and 20)
   - State Theorem 3.1 as a restatement of Theorem 20.4; avoid duplicated proofs—cross‑reference instead.
   - Synchronize remarks on “analytic vs numerical” between §3 and §20.

4) Notation duplication (Sec 4 vs Appendix A)
   - Keep intuitive definitions + Q(Φ) in §4; keep only the table in Appendix A. Ensure ξ_n, w(n), w_max match Sec 11 formulas.

5) Core analytic chain (Secs 7–13)
   - Ensure labels match usage:
     * Lemma 7.2 = A1′ Cone density.
     * Lemma 8.2 = A2 Lipschitz.
     * Theorem 10.10 (A3 unified floor) assumptions align with parameters M*(K), t*(K) used later.
     * RKHS cap result referenced uniformly as `thm:rkhs-contraction`.
     * T5 transfer (`thm:T5-transfer`) formulas match Theorem 3.1/20.4 constants.

6) GRH block (Sec 16)
   - Check T_P^χ uses χ(p)·w_RKHS(p) (no extra factor 2) in the text.
   - If Lemma 16.10 (V_twins ≥ 0) is duplicated in §18, keep one and cross‑reference.

[x] 7) Twin coherence (Sec 17)
    - `thm:scaling` renamed to numerical scaling law with empirical disclaimer and updated exponents; remark added about weight/window dependence.
    - δ/phase formulas unchanged (match code); keep for future verification if needed.

[x] 8) Coherence→Counting (Sec 18)
    - Theorem now states explicit |Z| ≥ C X^ε, W₂ ≤ polylog; proof updated accordingly; remark retains “conditional”.

9) Numerical results & appendices (Sec 19, App B/C)
   - Tables B.1–B.3 must match current scripts; cite tables directly in §19 text.
   - Appendix C: file names must match repository paths.

[ ] 10) Global cautions (Secs 20–22)
    - Reiterate explicitly: RH/GRH not proven; TPC not proven; only Cauchy–Schwarz bridge + algebraic facts are unconditional. (still to polish)
