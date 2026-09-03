# Appendix NEW — literature scout report, period 2020–2026 (agent A, 2026-09-03)

Verbatim report of the research subagent (general-purpose, web tools). Legend:
VERIFIED = the agent opened the arXiv abstract/HTML/PDF text itself;
RELAY_UNVERIFIED = only seen via search snippets or third-party pages.
Observer's synthesis lives in `SURVEY_WALLS_A_B_DELTA_2026-09-03.md`.

## Task 1 — Weil form on finite windows / compressions, inertia index, bottom of spectrum

1. [VERIFIED] Lamzouri, Y. — "A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line", 2026, arXiv:2609.02882. Prop. 2.1: for a finite conjugation-invariant multiset 𝒵 ⊂ ℂ and K = (η̂)² with η ∈ L²(ℝ) real, even, supp η ⊂ (−λ,λ), η̂(0)² = 1: #{z ∈ 𝒵∩ℝ, m_z = 1} ≥ 2·#𝒵 − Σ_{z,s∈𝒵} K(z−s)², and #distinct(𝒵) ≥ (3/2)#𝒵 − (1/2)Σ K(z−s)². Applied to 𝒵_T = {i(ρ−1/2)·log T/(2π)} with unconditional pair correlation (Lemma 3.1, Q_δ ∈ C_c^∞((−1,1))) gives ≥ 0.6725 simple-on-line and ≥ 0.8362 distinct. Remark 3.4: "C_MT is the optimal constant that one can obtain using our method." Gives: cleanest abstract inequality; inputs are only the second moment and conjugation invariance. Does not give: anything about a finite matrix, an eigenvector, or a gap.

2. [VERIFIED] Alpöge, L.; Furman, R. — "More than two thirds of the zeta zeros are simple and on the critical line", 2026, arXiv:2608.13637. Theorem A: N₀ˢ(T,2T) ≥ (2/3 − o(1))N(T,2T), N_d(T,2T) ≥ (5/6 − o(1))N(T,2T). Machinery: even window ψ ∈ C²([−1/2,1/2]), ψ>0; basis of d ~ N(T,2T) modulated copies at α_k = T + 2πk/L, L = log(T/2π), supp(φ*φ) ⊂ [−L,L]. Prop. 4.1: compressed form = P + Q with P ⪰ 0, rank P ≤ N₀*(I′), tr P ≤ N₀(I′), n₊(Q) ≤ ½·#off, because each off-line pair contributes m_ρ(v_ρv_ρᵀ + v_ρ̄v_ρ̄ᵀ) = 2m_ρ(aaᵀ − bbᵀ) (Sylvester, Lemma 3.1). Lemma 3.2 (rank–trace): for Hermitian P ⪰ 0, Q with n₊(Q) ≤ b: rank P ≥ 2 tr P + 4 tr Q − 4b − ‖P+Q‖²_HS. Window length L = log(T/2π) in the dual variable — same as CCM's [0,L], L = log m. Does not give: lower bound on the smallest eigenvalue, nothing about the ground eigenvector. §7.2(a): bandwidth constraint (Fourier support 1) caps the method.

3. [VERIFIED] Suzuki, M. — "Weil's quadratic form via the screw function", 2026, arXiv:2606.09096 (v2 Aug 17 2026). Q_W^a(v) = ⟨A_a v, v⟩ on L²(−a,a), A_a Friedrichs extension of B_a = D*G_aD, G_a integral operator with kernel g(x−y). Thm 1.3: λ_a continuous in a (no RH). Thm 1.4: for small a, λ_a positive, simple, even eigenfunction, λ_a = log(1/a) + μ₁ − log 2π + ψ(2) − 1 + O(a). Thm 1.5: W(a,θ;z) entire with all zeros real. Cor. 1.6: uniform-on-compacta convergence of e^{φ(a,z)}W(a,θ;z) to ξ(1/2−iz)/(ξ(1/2−iz)+ξ′(1/2−iz)) as a → ∞ implies RH. Failure of RH ⇔ ∃a with λ_a < 0. No second eigenvalue, no gap. Closest independent twin of the CCM roof: W(a,θ;·) ↔ our F_m; Cor. 1.6 ↔ roof theorem; (A),(B) left open. Thm 1.4 is "Δ>0 and bottom positive" only as a→0, the opposite limit from ours.

4. [VERIFIED] Connes, Consani, Moscovici — "Zeta Spectral Triples", 2025, arXiv:2511.22755. Lemma 5.1 matrix τ_{i,i} = a_i, τ_{i,j} = (b_i−b_j)/(i−j). Cor. 5.6: δ_N := L^{−1/2}Σ V_n. Prop. 5.9: ξ̂(z) = 2L^{−1/2} sin(zL/2) Σ_j ξ_j/(z−2πj/L). Thm 5.10: simple smallest eigenvalue with even eigenvector, δ_N(ξ)=1 ⇒ det_reg(D−z) = −iλ^{−iz}ξ̂(z), ξ̂ entire, all zeros real. Cor. 3.8: lim_{λ→∞} μ_λ = 0 ⇒ RH. §7: "Establishing this convergence rigorously would amount to a proof of the Riemann Hypothesis … the main remaining obstacle." No gap lemma.

5. [VERIFIED] Connes, A.; van Suijlekom, W. D. — "Quadratic Forms, Real Zeros and Echoes of the Spectral Action", 2025, arXiv:2511.23257. Cor. 1.1 (Carathéodory–Fejér); Thm 3.1: h even continuous on [−L,L], kernel h(x−y) on L²([0,L]), largest eigenvalue simple ⇒ all zeros of ξ̂ real. Thm 5.6: q_{i,i}=a_i, q_{i,j}=(b_i−b_j)/(i−j), Q ≥ 0 with one-dimensional even kernel ξ ⇒ all roots of P(s) = Σ_k ξ_k Π_{j≠k}(j−s) real. Thm 6.1: Q lower-bounded essentially self-adjoint, minimum of spectrum a simple isolated eigenvalue with even eigenfunction ⇒ all zeros of ξ̂ real; proof: finite-rank ξ_N → ξ in norm, ξ̂_N → ξ̂ uniformly on compacta at FIXED L, Hurwitz. Remark 2.3: non-simple eigenvalue controls only common zeros. Explicit: "No explicit bounds on |ξ̂(z)| in the complex plane are provided."

6. [VERIFIED] Connes, A. — CIRM slides "Extremal Eigenvectors, Spectral Action, and the Zeta Spectral Triple", 2026, https://www.cirm-math.fr/RepOrga/3196/Slides/1-Connes.pdf. Slides 32–33: log of smallest eigenvalue of QW_λ⁺ for λ² = μ ∈ {2,…,17}; "Assuming RH one knows that the smallest eigenvalue of QW_λ⁺ is strictly positive … |φ(z)| ≤ c λ^{|z|/2} for some constant c < ∞, so that n(r) = O(r)." Only growth bound in the CCM corpus; c not uniform in λ.

7. [VERIFIED] Groskin, A. — "A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form", 2026, arXiv:2607.02828 (v2 Aug 14 2026). Thm 1: closed-form band-limited test function reproducing the truncated form exactly. Thm 3.2: for T₂>T₁>max(ρN,7) the archimedean increment is positive definite and strictly totally positive. Cor. 3.3: B_T = (2N+1)ρ/(π²T)·(log(T/2π)+1)(1+o(1)); λ_j(Q_T^tot) ≥ 0 certifies λ_j(Q_∞) > 0; λ_j < −B_T certifies λ_j(Q_∞) < 0; eigenvalues increase strictly to λ_j(Q_∞). Verified to the first 512 zeros; no RH claims. Gives: monotonicity — truncating the archimedean part only lowers eigenvalues.

8. [VERIFIED abstract] Groskin, A. — "High-Precision Approximation of Riemann Zeros via the Truncated Weil Form", 2026, arXiv:2605.20224. 16 cutoffs c = 13…67, 100; at c=100, N=250 smallest positive even-sector eigenvalue ≈ 10^{−334}, first ten zeros to 307–329 digits; negative blocks at finite archimedean cutoff T=800 disappear as T grows; Aitken-accelerated "spectral gap" converges monotonically in N. Numerical only.

9. [VERIFIED abstract] Kim, T. et al. — "A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator…", 2026, arXiv:2607.24830. FEM of Suzuki's A_a; λ_k(a) = log(1/a) + log(k−2) + B₀ + O(a) (30 digits). Numerical only; small-a regime.

10. [VERIFIED abstract] Connes, Consani — "Weil positivity and Trace formula, the archimedean place", 2020, arXiv:2006.13771 (Selecta 2021). Thm 1: supp g ⊂ [2^{−1/2}, 2^{1/2}], ĝ(0)=ĝ(i/2)=0 ⇒ W_∞(g*g*) ≥ Tr(ϑ(g) 𝐒 ϑ(g)*), 𝐒 projection onto Sonin's space. Thm 11: 13 < c < 17 with W_∞(g*g*) ≥ Tr(…) − c|ĝ(0)|². Proved via Toeplitz matrices K_q on q^ℤ, q→1⁺. Only unconditional "bottom ≥ 0" on a window, L = log 2.

11. [VERIFIED abstract] Connes, Consani — "Spectral Triples and Zeta-Cycles", 2021, arXiv:2106.01715. Very small eigenvalues of the Weil form on a fixed interval; eigenvectors finite sums of prolate spheroidal wave functions; perturbed Dirac operator on a circle of length L reproduces first 31 zeros numerically.

12. [VERIFIED abstract] Connes, Moscovici — "Prolate spheroidal operator and Zeta", 2021, arXiv:2112.05500 (PNAS 2022); Connes, Consani, Moscovici — "Zeta zeros and prolate wave operators", arXiv:2310.18423. Conceptual prolate ↔ zeta link; no ground-state bounds, no gap, no strip estimates.

13. [VERIFIED abstract, EUDML] Bombieri, E. — "Remarks on Weil's quadratic functional in the theory of prime numbers, I", Rend. Lincei Mat. Appl. 11 (2000) 183–233, https://eudml.org/doc/252338. Positive semidefinite iff RH; minimum on the unit ball of L² supported in [−t,t] attained; Yoshida's small-t positivity re-proved; "if RH is false but only with finitely many zeros off the line, the number of negative eigenvalues is precisely one-half of the number of zeros failing RH, provided the truncation is big enough."

14. [VERIFIED abstract] Suzuki, M. — arXiv:2301.00421 (Hilbert space from the Weil distribution; under RH isometric to a de Branges space); arXiv:2209.04658 (screw line); Li, X.-J. — arXiv:2404.13427 (Hilbert–Schmidt operator and Weil distribution). All RH-conditional; nothing quantitative for (B), (Δ).

## Task 2 — Normality / uniform bounds in a strip

15. [NEGATIVE FINDING] No 2020–2026 theorem gives uniform boundedness on a strip (or exponentially weighted edge-moment bounds) for Fourier transforms of eigenvectors of truncated convolution/Toeplitz/Weil operators along a growing window.

16. [VERIFIED] Bonami–Karoui, C. R. Math. 352 (2014) 229–234; Bonami–Karoui, Constr. Approx. 2016, arXiv:1405.3676; [VERIFIED PDF] Osipov, arXiv:1206.4056; [VERIFIED abstract] Bonami–Jaming–Karoui, arXiv:1804.01257; [RELAY] Bonami–Jaming–Karoui ACHA 2021. Bounds on ψ_{n,c}(0), ψ′_{n,c}(0), ψ_{n,c}(1) uniform in n and c; Osipov Thm 24: χ_n > c² ⇒ |ψ_n(1)| > 1/√2; Thm 25: |ψ_n(x)| < |ψ_n(1)| when χ_n > c²; Thm 26: n even, χ_n > c² ⇒ 1/|ψ_n(0)| ≤ 4 n^{1/2}(χ_n/c²)^{1/2}. Interval bounds only.

## Task 3 — Sampling at critical density

17. [VERIFIED PDF] Olevskii, Ulanovskii — "On Beurling's sampling theorem in ℝⁿ", arXiv:1106.0576. Beurling: Λ sampling for B_S, S=[a,b], iff D⁻(Λ) > |S|/2π strictly. Our lattice 2πℤ/L for type L/2 has D⁻ = L/2π exactly ⇒ not a sampling set; witness sin(zL/2).

18. [VERIFIED PDF] Pogány, arXiv:1307.3332 (Plancherel–Pólya inequality restated). Agent's computation: F_m is the cardinal series of its lattice values, so ‖F_m‖²_{L²(ℝ)} = (2π/L)Σ|F_m(2πk/L)|² = 2π uniformly in m (unit ξ); Paley–Wiener then gives only |F_m(x+iy)| = O(√L·m^{|y|/2}).

19. [VERIFIED] Gerosa, Eriksson — "Stability Analysis for Autoregressive Sampling Sets", 2026, arXiv:2606.03942. AR(1)-jittered lattice has Nyquist density a.s. yet is a.s. not a stable sampling set.

## Task 4 — Unconditional results toward "all zeros real" via real-zero families

20. [VERIFIED abstract] Dobner — "A proof of Newman's conjecture for the extended Selberg class", 2020, arXiv:2005.05142: Λ ≥ 0.
21. Polymath 2019 arXiv:1904.12438: Λ ≤ 0.22; [RELAY] Gomila blog (Aug 2026) Λ ≤ 0.1787854, no arXiv id; [VERIFIED abstract] Michalowski arXiv:2602.20313: de Bruijn–Newman kernel not PF₅; [flag] Yang arXiv:2211.17269 (math.GM) unreviewed.
22. [VERIFIED abstract] Griffin, Ono, Rolen, Thorner, Tripp, Wagner — Adv. Math. 397 (2022), arXiv:1910.01227; [VERIFIED] Holland — arXiv:2608.08682: n³log²(n+2) ≥ K d⁵ ⇒ J^{d,n} hyperbolic; semicircle limit; [VERIFIED abstract] O'Sullivan arXiv:2007.13582; Romik arXiv:1902.06330. Hyperbolicity known only in a wedge; RH needs all (d,n).
23. [NEGATIVE] No 2020–2026 paper proves convergence of a real-zero approximant family to Ξ with strip uniformity.

## Task 5 — Ceiling statements

24. [VERIFIED] Alpöge–Furman §7.2(a): 2/3 sharp with Fourier support 1; form factor on all supports would certify 100%. Lamzouri Rem. 3.4. [VERIFIED abstract] Goldston, Lee, Schettler, Suriajaya arXiv:2503.15449 (PCC ⇒ 100%), arXiv:2507.06823 (AH form). Baluyot et al. arXiv:2501.14545 (v. Sep 1 2026); Goldston–Suriajaya arXiv:2603.28104, arXiv:2511.20059. Carneiro, Chandee, Littmann, Milinovich arXiv:1406.5462 (Crelle 725, 2017); Carneiro, Milinovich, Ramos arXiv:2310.01913.

## Agent synthesis

1. Wall (B): no existing theorem; closest tools are Connes' type bound (non-uniform c), PSWF edge bounds (if ξ is provably a finite prolate sum), Groskin's total-positivity monotonicity. Beurling proves lattice data at exact Nyquist never controls sup-norms; free L² identity yields only O(√L·m^{1/4}) on |Im z|<1/2. (B) is intrinsically the edge-moment bound on q_m.
2. Wall (A): stated as the open step by CCM, Connes–van Suijlekom, Suzuki, Groskin; Jensen route has the same missing uniformity.
3. Wall (Δ): no gap theorem anywhere; positive-bottom results only for small windows; under RH the bottom tends to 0 monotonically; simplicity essential; inertia results count, never bound.
4. Ceiling unchanged by 2024–2026.
5. The finite-Weil-matrix literature has converged on exactly our three walls and written none of them down as theorems.
