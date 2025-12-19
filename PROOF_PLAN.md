Proof Conversion Plan (full analytic closure)
=============================================

Goal: eliminate all numerical/empirical dependencies and produce a fully analytic proof of the positivity chain (T0–A1′–A2–A3–RKHS–T5) and its GRH/twin extensions.

Milestones (ordered by dependency)
----------------------------------
1) Archimedean barrier (A3) — analytic constants only
   - [ ] Derive explicit lower bound c0(K) for all K>0 from the digamma/Gamma terms (no fitted numbers).
   - [ ] Prove modulus of continuity ω_{P_A}(π/M) with explicit constant C_SB.
   - [ ] Choose M*(K) s.t. λ_min(T_M[P_A]) ≥ c0(K)/2 via explicit formula; record closed-form M*(K).

2) Prime cap in RKHS — analytic
   - [ ] Bound S_K(t) analytically using spacing δ_K and Gaussian kernel; no empirical η_K.
   - [ ] Choose t_min(K) explicitly so that ∥T_P∥ ≤ c0(K)/4 for all K; derive closed form in terms of K.
   - [ ] Control tails ∑ Λ(n)/√n e^{-4π^2 t (log n)^2} with explicit constants (use known ψ(x) bounds).

3) Monotone schedules + T5
   - [ ] Define monotone K ↦ t_min(K), M_min(K) satisfying A3+RKHS conditions globally.
   - [ ] Reprove T5 transfer with these schedules (no finite-K certificates).

4) Toeplitz discretization remainder
   - [ ] Give explicit Szegő/Böttcher-type remainder ensuring |λ_min(T_M[P_A]) − λ_min(T[P_A])| ≤ ω_{P_A}(π/M) with proved constant C_T.
   - [ ] Combine with (1) to maintain λ_min(T_M[P_A]) ≥ c0(K)/2.

5) GRH twist (χ)
   - [ ] Repeat (1)–(4) with χ-weights: show ∥T_P^χ∥ bound and λ_min(T_M[P_A]−T_P^χ) ≥ c0^χ(K)/2 for all K.
   - [ ] Class operators H_±: same constants; ensure no numerical inputs.

6) Twin section — make strictly conditional or prove new bounds
   - [ ] Option A: move Scoh/Sinc/Gain scaling to “conditional/numerical appendix”.
   - [ ] Option B: supply analytic lower bounds for |Z(X)| sufficient for Theorem 18.5; otherwise label results explicitly as conditional.

7) Remove numerical tables from core proof
   - [ ] Replace B.1–B.3 by theorems with analytic constants; move numeric tables to an appendix labeled “computational check (non-essential)”.
   - [ ] Eliminate any dependence of main theorems on scripts/logs.

8) Final logical closure
   - [ ] State and prove global theorem: for all K>0, with explicit M*(K), t*(K), λ_min(T_M[P_A]−T_P) ≥ ½ c0*(K) >0 ⇒ Q(Φ)≥0 ∀Φ∈W ⇒ RH (and GRH for covered χ).
   - [ ] Cite all external analytic estimates (ψ bounds, zero-free regions not needed) with explicit constants.

Work split
----------
- Analytic bounds (1,2,4): requires derivations from explicit formula; likely senior analytic effort.
- Schedule + T5 (3): after constants from 1–2 are fixed.
- GRH twist (5): parallel once 1–2 constants framework set.
- Twins (6): decision whether to keep as conditional appendix.
- Editorial (7,8): after analytic constants are locked.

Definition of done
------------------
- Main body contains only proved statements with explicit constants; all numerical content isolated as non-essential appendix.
- No reliance on scripts/tables for logical implications.
- Single final theorem delivering RH/GRH equivalence via proved operator inequalities.
