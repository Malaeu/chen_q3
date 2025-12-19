Proof Tasks (actionable checklist)
==================================

Step 1 — Archimedean barrier (A3) with explicit constants
---------------------------------------------------------
1.1 Digamma bounds (real axis surrogate for complex).
    - Prove for all ξ∈ℝ: Re ψ(1/4 + iπξ) ≤ log(√((1/4)^2 + π^2 ξ^2)) − 1/(2·(1/4))·1/(1+4π^2 ξ^2).
    - Source candidates: Batir (2008) inequalities for ψ on ℂ; Abramowitz–Stegun §6.3 with explicit remainder.
1.2 Lower bound for a*(ξ) = 2π(log π − Re ψ(1/4 + iπξ)).
    - Derive explicit c_arch(K) := inf_{|ξ|≤K} a*(ξ) ≥ f(K) with closed form (no numerics).
1.3 Modulus of continuity of P_A.
    - Express P_A as convolution of a* with Fejér×heat kernel. Use |P_A'| ≤ ∥a*∥_{BV} * kernel to bound ω_{P_A}(δ) ≤ C_arch·K·δ.
    - Produce an explicit C_arch via the bound on a*'.
1.4 Discretization floor.
    - Using Szegő/Böttcher remainder: prove λ_min(T_M[P_A]) ≥ c_arch(K) − C_T ω_{P_A}(π/M) with explicit C_T (classical Toeplitz norm bound).
1.5 Choose M*(K).
    - Solve C_T ω_{P_A}(π/M*) ≤ c_arch(K)/2 to get a closed form M*(K).

Step 2 — Prime cap in RKHS (analytic)
-------------------------------------
2.1 Node gap δ_K.
    - Prove δ_K ≥ 1/(2π(e^{2πK}+1)) (already elementary).
2.2 Tail sum S_K(t).
    - Derive S_K(t) ≤ 2 e^{-δ_K^2/(4t)}/(1−e^{-δ_K^2/(4t)}) without heuristic η_K.
2.3 Choose t_min(K).
    - Solve S_K(t_min) ≤ (c_arch(K)/4 − w_max)/√w_max with explicit w_max=2/e to get t_min(K) in closed form.
2.4 Tail of Λ(n) with Gaussian weight.
    - Bound ∑_{n>N} Λ(n)/√n · e^{-4π^2 t (log n)^2} ≤ C_tail e^{-4π^2 t (log N)^2}/t using partial summation and the standard ψ(x) bound |ψ(x)−x| ≤ A x exp(−B√log x) (explicit A,B from literature).

Step 3 — Global schedules and T5
--------------------------------
3.1 Define monotone schedules K↦(t_min(K), M*(K)) from Steps 1–2.
3.2 Prove A3+RKHS conditions hold for all K with these schedules.
3.3 Reprove T5 transfer using these schedules; no finite-K certificates.

Step 4 — GRH twist
------------------
4.1 Repeat Steps 1–3 with χ-weights: replace Λ(n) by χ(n)Λ(n); adjust w_max (still 2/e).
4.2 Show class operators H_± inherit the same bounds.

Step 5 — Twin block (decision)
------------------------------
5.1 If keeping: provide analytic lower bounds for |Z(X)|; otherwise move Scoh/Sinc/Gain to a clearly conditional appendix.

Step 6 — Editorial cleanup
--------------------------
6.1 Main theorems depend only on proved analytic constants; numerical tables demoted to non-essential appendix.
6.2 State final global theorem: λ_min(T_M[P_A]−T_P) ≥ ½ c_arch(K) ∀K ⇒ Q(Φ)≥0 ⇒ RH (and GRH for χ).
