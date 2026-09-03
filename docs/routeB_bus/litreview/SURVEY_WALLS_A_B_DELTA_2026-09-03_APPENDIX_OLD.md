# Appendix OLD — literature scout report, classical results under other names (agent B, 2026-09-03)

Verbatim report of the research subagent. VERIFIED = opened by the agent (extracted
texts copied to `pdfs/survey_2026-09-03_sources/`); RELAY_UNVERIFIED = secondary
source or snippet only. OCR of 1950s AMS scans garbles Greek letters; reconstructed
constants are flagged. Observer's synthesis: `SURVEY_WALLS_A_B_DELTA_2026-09-03.md`.

## 1. Exponential type controlled by lattice samples (walls B, A)

1.1 [VERIFIED via Blank–Ulanovskii 2016, arXiv:1603.09585 "On Cartwright's theorem"; original bibliographic] M. L. Cartwright, "On certain integral functions of order one", Quart. J. Math. Oxford 7 (1936) 46–55. Theorem 1: f ∈ E_{<π} bounded on ℤ ⇒ bounded on ℝ. Critical case: f(z) = z·sin(πz) — type exactly π, zero on ℤ, unbounded on ℝ. Theorem 2: Λ is a Cartwright set for E_{<σ} iff it contains a uniformly discrete subset with D⁻ ≥ σ/π; Beurling's Theorem 3: Λ is a sampling set for B_σ iff D⁻ > σ/π (strict). Strip bound (eq. (3), Levin Lect. 6 Thm 3): |f(x+iy)| ≤ ‖f‖_∞ e^{σ|y|}. Same mathematics as wall (B): type L/2 sampled at 2π/L is density σ/π exactly.

1.2 [VERIFIED, primary PDF] R. J. Duffin, A. C. Schaeffer, "A class of nonharmonic Fourier series", Trans. AMS 72 (1952) 341–366. Uniform density d: |λ_n − n/d| ≤ L, |λ_n − λ_m| ≥ δ. Theorem I: {e^{iλ_n t}} is a frame over (−γ,γ) for 0 < γ < πd. Theorem I′: f of type γ < πd, f ∈ L² ⇒ A ≤ Σ|f(λ_n)|²/∫|f|² ≤ B. Lemma IV (citing their 1945 paper): type γ, uniform density d > γ/π ⇒ bounded on the real axis and in every strip in terms of sup_n|f(λ_n)|. Critical case: "If γ = π and λ_n = n then A = B = 1 is Parseval's relation." Half-sequence complete but not a frame. Theorem II: bounded imaginary perturbations keep the frame. Same mathematics as (A)/(B): at our critical density ℓ² of samples is an isometry with L²(ℝ) of F_m.

1.3 [VERIFIED statement via Carneiro et al. arXiv:1311.4862 Lemma 2.6(b); original bibliographic] Plancherel, Pólya, Comment. Math. Helv. 10 (1937/38) 110–163: f of type ≤ τ, f ∈ L^p ⇒ ∫|f(x+iy)|^p dx ≤ e^{pτ|y|}∫|f(x)|^p dx; f = o(1) on strips.

1.4 [VERIFIED, Encyclopedia of Mathematics] Bernstein 1923: sup_ℝ|f^{(r)}| ≤ Mσ^r for type ≤ σ.

1.5 [RELAY_UNVERIFIED] Boas, Entire Functions, 1954 (not opened); Boas 1940 Duke 6; Boas–Schaeffer 1942.

## 2. Edge behaviour of eigenvectors of truncated convolution operators (walls B, Δ)

2.1 [VERIFIED, archive.org] Slepian, Pollak, BSTJ 40 (1961) 43–63: λ_0 > λ_1 > … > 0, ψ_i bandlimited, orthonormal and complete in 𝔅; ∫_{−T/2}^{T/2} ψ_iψ_j = λ_iδ_ij; λ_iψ_i(t) = ∫ [sin Ω(t−s)/(π(t−s))]ψ_i(s)ds for all complex t; commuting differential operator; nondegeneracy and ordering.

2.2 [VERIFIED, archive.org] Landau, Pollak, BSTJ 40 (1961) 65–84 and BSTJ 41 (1962) 1295–1336. Theorem 3 (1962): f bandlimited to W, unit energy, energy 1−ε_T² in [−T/2,T/2] ⇒ ‖f − Σ_{n≤[2WT]} a_nψ_n‖² ≤ 12ε_T²; Theorem 5: for ε_T < 0.915 about 2WT functions do not suffice for C₁ near 1; sampling functions sin t/t do worse.

2.3 [VERIFIED via Bonami–Karoui arXiv:1509.02646 eq. (39); original blocked] W. H. J. Fuchs, JMAA 9 (1964) 317–330: ∂_c ln λ_n(c) = 2|ψ_{n,c}(1)|²/c. Consequences: λ_n(c) = ½ exp(−2∫_c^{c*_n} ψ_{n,τ}(1)²/τ dτ), (π/2)(n−1) ≤ c*_n ≤ (π/2)(n+1); |ψ_{n,τ}(1)| ≤ 2χ_n(τ)^{1/4}. Same mathematics as (B): Hadamard/Hellmann–Feynman for window variation; edge mass = rate of change of the extreme eigenvalue. Only for the sinc kernel. Slepian 1965 asymptotic 1−λ_0(c) ~ 4√(πc)e^{−2c}: RELAY_UNVERIFIED.

2.4 [VERIFIED via Bonami–Karoui (5) and Osipov arXiv:1206.4541 Thm 2; originals blocked] Widom, Arch. Rational Mech. Anal. 17 (1964): λ_n(c) ~ (ec/(4(n+½)))^{2n+1}. Landau–Widom, JMAA 77 (1980): N(c,α) = 2c/π + (1/π²) log((1−α)/α) log c + o(log c) (also via Karnik–Romberg–Davenport arXiv:2006.00427). Same mathematics as (Δ): plunge region of width ~log c — gaps collapsing.

2.5 [VERIFIED primary PDF] Widom, "On the eigenvalues of certain Hermitian operators", Trans. AMS 88 (1958) 491–522, quoting Kac–Murdock–Szegő (J. Rational Mech. Anal. 2 (1953) 767–800): for T_n(f), f continuous even with unique maximum M = f(0), σ² = −f″(0) ≠ 0: λ_{ν,n} = M − σ²ν²π²/(2n²) + o(n⁻²); Widom Thm 2.1 sharpens to O(n⁻³); continuous analogue Thm 3.1: λ_{ν,A} = M − σ²ν²π²/(8A²) + o(A⁻²) (Greek letters reconstructed from OCR; n⁻², A⁻² unambiguous). Parter, Trans. AMS 99 (1961) 153–192: degenerate extrema. Same mathematics as (Δ): smooth symbol ⇒ gap between two extreme eigenvalues → 0; a uniform gap can only come from a non-smooth (atomic) symbol. Grenander–Szegő 1958: RELAY (distribution only, never a gap).

2.6 [VERIFIED as quoted in Andrews–Clutterbuck and Ashbaugh 2006] Brascamp, Lieb, J. Funct. Anal. 22 (1976) 366–389: first Dirichlet eigenfunction of −Δ+V on a convex domain with convex V is log-concave. No classical analogue for truncated convolution operators.

## 3. The spectral gap as "the" inequality (wall Δ)

3.1 [VERIFIED primary] Ashbaugh, Benguria, Proc. AMS 105 (1989) 419–424: −d²/dx²+V, Dirichlet, V symmetric single-well ⇒ λ₂ − λ₁ ≥ 3π²/d², equality iff V constant; Prop. 1: V₁ − V₀ single-well ⇒ λ₂−λ₁ ≥ μ₂−μ₁. Mechanism: trial u = (v₁/v₂)u₂; sign of cross term from monotonicity of u₂/u₁.

3.2 [VERIFIED primary] Lavine, Proc. AMS 121 (1994) 815–821: V convex on [0,R] ⇒ E₂−E₁ ≥ Γ₀ (Dirichlet 3π²/R², Neumann π²/R²). Mechanism: (i) Hellmann–Feynman Γ′(τ) = ∫ ∂_τV·(u₂² − u₁²)dx, u₂/u₁ monotone; (ii) Lemma 3.2 deformation to linear potentials with Γ′ < 0; (iii) minimizer for linear V = ax, stationarity ∫x(u₂²−u₁²) = 0, virial identity (Lemma 3.3, g(x)=x) forces a = 0.

3.3 [VERIFIED primary, arXiv:1006.1686] Andrews, Clutterbuck, "Proof of the fundamental gap conjecture", J. AMS 24 (2011) 899–916. Cor. 1.4: Ω convex, diameter D, V weakly convex ⇒ λ₁ − λ₀ ≥ 3π²/D². History (their intro; Ashbaugh 2006 AIM note opened): van den Berg 1983; Singer–Wong–Yau–Yau 1985 π²/(4D²); Yu–Zhong 1986 π²/D²; Ashbaugh–Benguria 1989; Lavine 1994. Mechanism: (a) Thm 2.1 modulus-of-continuity estimate for v_t = Δv + X·∇v via two-point function Z_ε(y,x,t) = v(y,t) − v(x,t) − 2φ(|y−x|/2,t) − εe^t; (b) v = u₁/u₀ with drift X = 2∇log φ₀; modulus of concavity of log φ₀ = modulus of contraction for X; (c) Thm 1.5: modulus of convexity of V ⇒ (log φ̃₀)′ modulus of concavity for log φ₀; for convex V, φ̃₀ = cos(πx/D), modulus −(π/D)tan(π|y−x|/D); plain log-concavity only gives π²/D²; (d) 1-D comparison decays at 3π²/D², osc(u₁/u₀)(t) ≤ Ce^{−3π²t/D²}. No maximum principle for integral operators.

3.4 Discrete/matrix analogues. [VERIFIED, arXiv:1403.1473] Jarret, Jordan 2014: L(P_N)+W, W convex on the path graph ⇒ Γ ≥ 2(1 − cos(π/N)), proof modeled on Lavine (Hellmann–Feynman + Cauchy interlacing + node tracking). [VERIFIED, arXiv:2508.16353] Hofmann–Kerner–Pechmann 2026: on growing paths the gap → 0, compactly supported potential makes it go faster. Hopf 1963, Alon–Milman 1985: RELAY. All classical gap theorems for growing truncations give a decaying gap.

## 4. RH as one inequality (classical criteria)

4.1 Weil 1952 [VERIFIED via Bombieri's Clay description §V and Suzuki arXiv:2206.03682 §3.2]: explicit formula and criterion RH ⇔ W(ψ ∗ ψ̃) ≥ 0 for all ψ ∈ C_c^∞(ℝ) (compact-support form due to Yoshida). Unconditional partials: Yoshida 1992 (small windows); Connes–Consani arXiv:2006.13771 Thm 1 and 6.11 (window (1/2,2), Sonin compression, 13 < c < 17).

4.2 Bombieri 2000 [VERIFIED abstract, EUDML] Rend. Lincei (9) 11 (2000) 183–233: psd iff RH; minimum on unit ball supported in [−t,t] attained; Yoshida re-proved; finitely many off-line zeros ⇒ number of negative eigenvalues of a big truncation = half their number. Sign count, not gap.

4.3 Nyman–Beurling–Báez-Duarte [VERIFIED via Burnol arXiv:math/0103058 Thm 1.1 and Báez-Duarte arXiv:math/0202141]: RH ⇔ χ_(0,1] ∈ closure span{ρ_a : a ∈ ℕ} in L²(0,∞) (Báez-Duarte 2003). Lower bound (Báez-Duarte–Balazard–Landreau–Saias): ‖F − χ‖ ≥ C/√(log N); Burnol 2002 Thm 1.3: liminf D(λ)√(log 1/λ) ≥ √(Σ_ρ m_ρ²/|ρ|²). Conjecture d_N² ~ (2+γ−log 4π)/log N: RELAY.

4.4 Li 1997 / Bombieri–Lagarias 1999 [VERIFIED via MathWorld and Maślanka arXiv:math/0402168]: λ_n = Σ_ρ[1 − (1 − 1/ρ)ⁿ]; RH ⇔ λ_n ≥ 0 ∀n. Maślanka 2004: positive for n ≤ 3300 (verified). Johansson n = 10⁵: RELAY.

4.5 Yoshida 1992 [VERIFIED via Suzuki arXiv:2206.03682 §4.2]: Lemma 2: ⟨·,·⟩_W positive definite on K(a) for a small, unconditionally; Lemma 3: for a₀, μ > 0 there is N with ⟨φ,φ⟩_W ≥ μ‖φ‖² on K_N(a), 0 < a ≤ a₀. Suzuki Thm 1.4/1.3: RH ⇔ no zero eigenvalue of G_g[a] for every a. Closest classical statement to "gap above the ground state on a window", small windows only.

4.6 de Branges positivity [VERIFIED primary, arXiv:math/9812166] Conrey, Li 1998/2000: Theorem 1 (de Branges) correct; the positivity condition fails for the natural spaces from ζ(s) and L(s,χ₄).

## 5. Montgomery 1973 and Gallagher–Mueller 1978

[VERIFIED via Goldston's notes arXiv:math/0412313 §3–4, §7; originals bibliographic] Montgomery's explicit formula (Prop. 1, RH "notational"); squaring the zero-sum and integrating over 0≤t≤T gives the positive form Σ_{γ,γ′} x^{i(γ−γ′)}w(γ−γ′), w(u) = 4/(4+u²); Dirichlet polynomial mean square via Montgomery–Vaughan. Theorem 1 (RH): F(α) real, even, ≥ 0, F(α) = α + o(1) + (1+o(1))T^{−2α}log T for 0 ≤ α ≤ 1−ε. RH needed so that |Σ|² is a genuine square with a positive diagonal. Gallagher–Mueller 1978: pair correlation density ⇒ simple-zero conjecture (framework unconditional), ψ(x) = x + o(x^{1/2}(log x)²) under (7.1)+RH.

## Agent synthesis

1. Oldest theorem closest to (B): Cartwright 1936 / Duffin–Schaeffer 1945 — only for type strictly below Nyquist; at exact critical density only Parseval survives plus Plancherel–Pólya with the fatal factor e^{L|y|/2}.
2. (B) is an edge-mass statement on the coefficient side; oldest theorem about that: Fuchs 1964, ∂_c ln λ_n(c) = 2|ψ_{n,c}(1)|²/c.
3. Closest to (A): Paley–Wiener/Duffin–Schaeffer isometry at critical density (ℓ² of samples ⇔ L²(ℝ) of F_m); Landau–Pollak 1962 Thm 3.
4. Closest to (Δ): Kac–Murdock–Szegő 1953 / Widom 1958 — smooth symbol ⇒ gap O(n⁻²); uniform gap must come from the atomic arithmetic symbol.
5. Classical gap proofs estimate the shape of the ground eigenvector, never eigenvalues directly; Bombieri fixes inertia only; Yoshida Lemma 3 gives a uniform lower bound on small windows.
6. Most worth transplanting: the Fuchs/Hadamard window-variation identity — dλ_min(L)/dL as a positive multiple of the squared edge coefficient; monotonicity plus boundedness ⇒ ∫(edge mass)² dL < ∞.
7. Second: Lavine's first variation Γ′ = ∫∂V·(u₂² − u₁²) with the window length as deformation parameter; Jarret–Jordan ran it on a matrix.
8. Nothing classical gives (Δ) as stated.
9. RELAY items: Slepian 1965, Boas 1954, Grenander–Szegő 1958, Hopf 1963, Alon–Milman 1985, Bombieri–Lagarias content, the d_N² conjecture, Johansson's n = 10⁵.
10. Extracted full texts saved alongside.
