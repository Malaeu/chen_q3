# SWEEP C — fresh foreign tools for (8) on the semilocal two-lobe class (2026-09-06)

Reduction as given: L_S = N_S − E_S; (8) `n₀ − ν_a ≤ A₀ + J_a + w`, w = (log 2)/√2, on
𝒞₋^{00} = A₋{h ∈ C_c^∞(−δ₀,δ₀) : A₊(h)=A₋(h)=0}, δ₀ = (log3−log2)/8 ≈ 0.05068.
Support of v = A₋h: half-width a/2 + δ₀ = 0.34657 + 0.05068 = **0.39725**; autocorrelation
half-width 0.7945. Classical Yoshida window half-width = a/2 = 0.34657 → **our class sits just
outside the classical window**. Remember this number; it decides card C1.

Reading level per card: `abs` = abstract page opened; `html` = theorem text opened; `api` = arXiv
API entry (title+abstract summary) only. Nothing below is cited from memory.
## C1 — Zhu, *Weil positivity in compact windows* — **PARTIAL_MECHANISM (top)**
arXiv:**2608.24827v2**, submitted 25 Aug 2026, revised 2 Sep 2026. Single author (Xuefeng Zhu).
Read: `abs` (abstract verbatim).
> "We prove by certified computation that Q(f) >= 8.9e-18 ||f||^2 for all supp f in [-0.8,0.8],
> i.e. autocorrelation support 1.6, 2.3 times the classical range. […] The odd parity sector shows
> that the certified positivity holds for arbitrary complex test functions of support 1.6, and that
> the window ground state is simple and even […]. Upper bounds (unconditional): variational bounds
> are evaluated on the geometric side in interval arithmetic, with no appeal to zeros or RH, down to
> 3.2e-283 at L=2. They follow the empirical law -ln lambda_min(L) ~ 2 pi^2 N(T*)/ln N(T*),
> T* = 2 pi e^{2L} […]; 2 pi^2 matches the Landau-Widom eigenvalue-plunge rate. […] any one-stroke
> certificate must resolve frequencies up to 2 pi e^{A_L}, A_L ~ 4e^L, a doubly exponential threshold
> that no pointwise bound on the prime comb lowers, while the spectral margin collapses at the
> Landau-Widom rate."

Bounds: λ_min(L) = inf Q(f)/‖f‖² over supp f ⊂ [−L,L], two-sided, unconditional, complex tests
included in the odd sector. No RH input (explicitly stated).
For (8): our class has L = 0.39725 < 0.8, and λ_min is nonincreasing in L, so **Q(v) ≥ 8.9·10⁻¹⁸‖v‖²
holds on all of 𝒞₋^{00} as a corollary** — not (8), which is Q ≥ n, but it converts (8) into a
single finite comparison: is n(v₋) ≤ λ_min(0.39725)‖v‖²? It also certifies the "simple and even
ground state" hypothesis the class construction leans on, and its doubly-exponential resolution
obstruction is a direct warning about the packet matrix (10): a one-stroke finite certificate on
a window needs frequencies to 2πe^{A_L} — δ_eval cannot be waved through.
**TRANSFER: PARTIAL_MECHANISM.**
## C2 — Suzuki, *Weil's quadratic form via the screw function* — **DIRECT_TOOL (for A₀ only)**
arXiv:**2606.09096v2**, v1 8 Jun 2026, v2 17 Aug 2026. Read: `abs` (verbatim) + `html` intro.
> "We establish a unified operator-theoretic framework for understanding the results on the Weil
> quadratic form obtained by Yoshida (1992), Bombieri (2001, 2003), Connes--Consani (2023), and
> Connes--Consani--Moscovici (2025+) from the perspective of the screw function […] it provides a
> method to study the Weil quadratic form, which is originally defined in terms of distributions, by
> means of continuous functions and brings the theory of de Branges spaces into the analysis […]
> All these results are obtained without assuming the Riemann Hypothesis."

From the introduction (quoted in the HTML):
> Theorem 1.3: "The lowest eigenvalue λ_a is continuous in a."
> Theorem 1.4: "For sufficiently small a>0, the lowest eigenvalue λ_a is positive, simple, and
> satisfies λ_a = log(1/a) + μ₁ − log(2π) + ψ(2) − 1 + O(a)." The eigenfunction is even.

Bounds λ_a = inf of the Weil form on supp ⊂ (−a,a) with an **exact constant** (ψ(2) = 1−γ, log 2π),
the same c_A family our A₀ carries; no RH input. For (8): supplies A₀ = (𝒟(h) − c_A H)/H as a
continuous-function (screw) object rather than a distribution, with a closed asymptotic on narrow h —
the regime of δ₀ ≈ 0.05 — and is the cleanest published bridge from our objects to
Yoshida/Bombieri/CC/CCM. It does **not** touch n₀ − ν_a (no Sonin trace anywhere).
Caveat, load-bearing: same author as 2301.00421, whose printed Theorem 1.4 the project already
found inconsistent with its own printed definitions (verdict SECONDEXPR-B). Re-derive, do not cite.
**TRANSFER: DIRECT_TOOL for the archimedean term; NONE for the Sonin cross term.**
## C3 — Connes–Consani–Moscovici, *q-series and the moment problem for local factors* — **DIRECT_TOOL (computation)**
arXiv:**2403.01247v1**, 2 Mar 2024, 37 pp. Read `abs` (fetcher paraphrase, not verbatim — re-open
before quoting): the moment problem and Jacobi matrix attached by the semilocal-trace-formula
framework to a finite set S of places, worked out for S = {∞, p}; moments, orthogonal polynomials and
Jacobi coefficients are power series in q = 1/p, moment series are Lambert series, **all coefficients
lie in ℤ[1/√2]**, explained via Catalan numbers. That is our own G = P₀B*BP₀ and its inverse (9) at
p = 2, r = 1/√2 — the same ring. Offers an exact-arithmetic route to n₀ and ν_a (Jacobi recursion)
instead of the truncated Neumann series R_d + ε_d with a numerical enclosure, killing the
"carrier model error" failure mode that TA/TB disagreed on. Nothing about the sign.
**TRANSFER: DIRECT_TOOL for evaluating the left side of (8) exactly.** Read in full first.
## C4 — Marceca–Romero–Speckbacher, *Eigenvalue estimates for Fourier concentration operators on two domains* — **PARTIAL_MECHANISM**
arXiv:**2301.11685**, ARMA 248 (2024), no. 35. Read: `html` (Theorem 1.1 quoted).
Operator: "Sf = χ_F ℱ^(-1) χ_E ℱ χ_F f, f ∈ L²(ℝ^d)".
> Theorem 1.1 (E, F compact, maximally Ahlfors-regular boundaries, |∂E||∂F| ≥ 1; α ∈ (0,1/2)):
> "#{λ_n ∈ (ε, 1-ε)} ≤ A_α,d · |∂E|/κ_∂E · |∂F|/κ_∂F · log(|∂E||∂F|/(κ_∂E ε))^(2d(1+α)+1)"

Bounds the plunge count of a two-domain Fourier concentration operator **non-asymptotically, with
explicit constants, for non-convex and non-symmetric domains** (first such). Kernel (18) writes
A_{p,λ} as Σ_j c_j (dilated archimedean block on (0,λ)×(0,p^jλ)); Thm 1.1 bounds each block's plunge
count by C·p^jλ²·log^{…}(1/ε) — a constant-explicit replacement for the ad-hoc HS count (25), whose
Σ_j divergence is the geometric shadow of Theorem 3's non-HS conclusion. Certifies (24) on A^(J).
No RH input. Nothing for the sign of (8).
**TRANSFER: PARTIAL_MECHANISM (angle spectrum only).**
## C5 — Hughes–Israel–Mayeli, *Trace bounds for limiting operators on rough domains* — **PARTIAL_MECHANISM**
arXiv:**2607.02996v1**, 3 Jul 2026. Read: `abs` (verbatim).
> "This work concerns a quantitative form of Landau's eigenvalue theorem for spatio-spectral limiting
> operators. We isolate a simple mechanism that converts the problem of estimating the distribution of
> eigenvalues of a limiting operator into the problem of bounding the trace of the difference between
> the operator and its square. This mechanism allows us to analyze limiting operators for domains with
> fractal boundaries. When the boundaries have finite perimeter, we recover the expected optimal
> dependence on the scaling parameter."

(A PDF fetch returned a paraphrase of Thms 1.1/1.2, not verbatim — treat those as unread.)
With T = P Q P, Tr(T − T²) = ‖(I−Q)QP‖²_HS is exactly the Halmos angle energy Theorem 3 proves
**infinite** for the one-prime pair — so this is the right currency, and the rough-boundary version is
the one that can survive the lacunary geometry. Use: bound the count for A^(J) (finite perimeter),
read the J → ∞ blow-up as the quantitative form of non-HS. **TRANSFER: PARTIAL_MECHANISM.**
## C6 — Azimifard, sine-kernel/prolate eigenvalue counts — **PARTIAL (archimedean side)**
arXiv:**2608.15808v2** (16/20 Aug 2026), read `abs` verbatim; companion **2608.17338v1** (18 Aug 2026,
"Entropy-type traces and moment expansions for the sine-kernel time-band limiting operator"), read
`api` entry only. For S_c = P_(0,c) Q P_(0,c), N_a(c) = #{n : λ_n(c) > a}, L̄ = log((1−δ)/δ):
> "N_δ(c)=c+π^{-2} L̄ log(4π²c/L̄)+O_A(log c+L̄) for 6 ≤ L̄ ≤ A log c", plus a signed
> growing-parameter determinant asymptotic "log det(I+(e^{2ω}−1)K_s) = 4ωs/π + 2π^{-2}ω² log(4s)
> + 2 log|G(1+iω/π)|² + O_A((1+ω)⁴ log²s/s)" (Barnes G; negative-coupling counterpart of
> Bothner–Deift–Its–Krasovsky).
The archimedean pair P_λ F_∞ P_λ is the even sine/cosine-kernel concentration operator, so these give
uniform quantile-level control of the archimedean Sonin tail — of n_∞(Bv) in the sandwich (12), the
only upper bound the project has for n(v). Single-author, unrefereed, two weeks old.
**TRANSFER: PARTIAL_MECHANISM.**
## C7 — Kulikov, exponential lower bound before the plunge — **PARTIAL (small, clean)**
arXiv:**2306.12430v1**, 3 Jun 2023. Read `abs` verbatim: "the eigenvalues λₙ(c) of the time-frequency
localization operator satisfy λₙ(c) > 1 − δᶜ for n = ⌊(1−ε)c⌋, where δ = δ(ε) < 1 and ε > 0 is
arbitrary, improving on the result of Bonami, Jaming and Karoui, who proved it for ε ≥ 0.42."
So 1 − λ_n is exponentially small before the plunge: the complementary (Sonin-side) archimedean
energy is exponentially small there. Archimedean only. Zero RH input.
**TRANSFER: PARTIAL_MECHANISM (upper bound for n_∞).**
## C8 — Groskin, finite Guinand–Weil dictionary — **PARTIAL_MECHANISM (for δ_eval)**
arXiv:**2607.02828v3**, v1 2 Jul 2026, v3 14 Aug 2026, single author. Read `abs` verbatim.
> "every real even Galerkin coefficient vector v determines, in closed form, a band-limited
> Guinand-Weil test function g_v whose zero sum over the nontrivial zeros of zeta equals the quadratic
> value <v, Q v> exactly […] beyond the Galerkin band the omitted archimedean tail is a totally
> positive Cauchy-Stieltjes increment. This yields a two-sided certification rule with an explicit
> budget B_T ~ (2N+1) rho log(T)/(pi^2 T) […] finite-cutoff positivity certifies cutoff-free
> positivity, a finite-cutoff eigenvalue below -B_T certifies a cutoff-free negative, and a negative
> eigenvalue in the band [-B_T, 0) certifies nothing."
The "totally positive Cauchy–Stieltjes increment" is a sign-definite bound for the omitted archimedean
tail — the structure needed to make δ_eval one-sided in (10)/(10b) instead of a two-sided fudge.
Different truncation (CvS/CCM Galerkin, not Sonin): the transfer is the tail-sign mechanism, not the
theorem. Unrefereed. **TRANSFER: PARTIAL_MECHANISM.**
## C9 — Connes–van Suijlekom 2511.23257 / CCM 2511.22755 — **COORDINATE**
**2511.23257v1** (28 Nov 2025, Commun. Math. Phys. 2025): quadratic form with kernel 𝒟̃(x−y) on
L²([−L/2,L/2]); if the lowest spectral value λ is a simple isolated eigenvalue with even
eigenfunction ξ, then all zeros of ξ̂ are real. Proof via a C*-algebraic Carathéodory–Fejér corollary
and Hurwitz. **2511.22755v1** (27 Nov 2025, CCM, *Zeta Spectral Triples*): rank-one perturbations of
the scaling spectral triple on [λ⁻¹,λ] using only Euler products over p ≤ x = λ²; "A rigorous proof
of this convergence would establish the Riemann Hypothesis." Read: `abs` verbatim, both.
Neither treats the semilocal Sonin split or the sign of ε(ρ); 22755's premise is a numerically
observed convergence, the same wall in new coordinates. 23257 is however where the "simple, isolated,
even ground state" hypothesis comes from — the one C1 certifies. Dictionary entry, not supplier.
**TRANSFER: COORDINATE.**
## C10 — Fractal uncertainty branch — **NONE (with one coordinate)**
- Cohen, *Fractal uncertainty in higher dimensions*, arXiv:**2305.05022v2** (v1 8 May 2023,
  v2 5 Oct 2024), **to appear in Annals of Mathematics**. Read `abs` verbatim: "if a fractal set in
  ℝ^d avoids lines in a certain quantitative sense, which we call line porosity, then it has a
  fractal uncertainty principle. The main ingredient is a new higher dimensional Beurling-Malliavin
  multiplier theorem."
- Badalucco–Franchi, *Fractal uncertainty principle over ℚ_p*, arXiv:**2607.11534v2** (v1 13 Jul
  2026). Read `abs` + `html`. Theorem 1.2: X ⊂ B₁ ν-porous from scales h to 1, Y ⊂ B_{h^{-1}}
  ν-porous from scales 1 to h⁻¹, h = p^{−n}: "for every f ∈ L²(ℚ_p) such that supp f̂ ⊆ Y, one has
  ‖𝟙_X f‖ ≤ C h^β ‖f‖", C = C(p,ν), β = β(p,ν) > 0. Finite form (Thm 1.4): X,Y ⊂ ℤ/p^nℤ L-porous ⇒
  "‖𝟙_Y ℱ_n 𝟙_X‖ ≤ C p^{−βn}". ν-porous: "for every ball B of diameter R ∈ (α₀,α₁), there exists
  x ∈ B such that B(x,νR) ∩ E = ∅".
**Blunt: FUP does not apply to our pair.** P_λ (a ball |x| ≤ λ) and the semilocal Fourier cutoff Q_λ
are *balls* — maximally non-porous; FUP is vacuous for them and gives no decay. The lacunary structure
in (18) is a *lattice* {j log p} in log-scale, again the opposite of Cantor-like. The p-adic result is
on the right group (ℚ_2) and is the freshest thing in the area, so: one line in CHAT_DIGESTS. It would
become a supplier only if the semilocal cutoff were replaced by a digit-restricted (porous) cutoff —
a different object. **TRANSFER: NONE (2305.05022), COORDINATE (2607.11534).**
## C11 — lacunary Schatten dictionary — **COORDINATE (not fresh)**
Aleksandrov–Peller, *Hankel and Toeplitz–Schur Multipliers*, arXiv:**math/0101264v1** (31 Jan 2001);
read `api` entry only: Schatten–von Neumann characterisation of Hankel/Toeplitz–Schur multipliers
"with special attention to lacunary power series symbols". This is the classical mechanism behind the
project's own Theorem 3 (lacunary symbol ⇒ S_q decided by ℓ^q of the coefficients, threshold q = 2)
and the place to look for an exact singular-value asymptotic instead of the two-sided (22). Listed so
the sweep is honest about where Theorem 3 already sits. **TRANSFER: COORDINATE.**
## Negative findings (searched, nothing there)
1. **No new Sonin-space paper by anyone, 2020–2026.** arXiv full-text search on "Sonin space" returns
   only CCM 2310.18423, CM 2112.05500, CC 2008.10974 and Burnol's 2001–2004 papers. Burnol's entire
   2024–2026 output (2402.08525, 2402.09083, 2402.14761, 2403.01957, 2403.03912, 2404.13763,
   2405.03625, 2601.23158, 2602.05511, 2602.19727, 2603.29998, 2604.24754) is Kempner/Irwin sums and
   missing-digit Dirichlet series — the Sonin line is dormant at its source.
2. **Nobody treats the sign of the prolate remainder ε(ρ)** in CC 2006.13771 Thm 4.7 (83)–(84).
   No follow-up, 2020–2026.
3. **No singular-value asymptotic for Σ_j c_j cos(2π p^j uv)** exists. Searches on lacunary + Schatten
   / singular values / trace class return only the 2001–2017 Hankel-multiplier line (C11).
4. Nothing puts the semilocal split (N_S − E_S) in print; the SEMILOCAL verdict's own claim that this
   is "written by nobody" survives this sweep.
## Blunt summary (five lines)
1. Nothing in 2021–2026 bounds the Sonin cross term ν_a. (8) has no supplier in the literature.
2. The one item that moves today is **C1 (Zhu 2608.24827)**: it certifies Q ≥ 8.9·10⁻¹⁸‖v‖² on a
   support window strictly containing our class, and it reduces (8) to one finite comparison.
3. The angle-spectrum question (22)/(24)/(25) has three genuine fresh tools — C4, C5, C6 — that
   replace the project's ad-hoc HS count with explicit-constant, non-asymptotic bounds.
4. Fractal uncertainty is a dead end for this reduction: our cutoffs are balls and the lacunary set is
   a lattice; FUP needs porosity on *both* sides. Record it as a coordinate and stop probing.
5. Two suppliers deserve real reading time, both by the Connes school and both unread here in full:
   **CCM 2403.01247** (exact ℤ[1/√2] arithmetic for our Gram G at p = 2) and **Suzuki 2606.09096**
   (screw-function form of A₀ with the exact constants), with Suzuki carrying a source-defect history.
## Single most promising item — exact locator
**arXiv:2608.24827v2 — Xuefeng Zhu, "Weil positivity in compact windows: a finite reduction, certified
two-sided bounds, and a Landau–Widom decay law", submitted 25 Aug 2026, revised 2 Sep 2026.**
`https://arxiv.org/abs/2608.24827`
Use: (a) λ_min(L) is nonincreasing in L and our class has L = a/2 + δ₀ = 0.39725 < 0.8, so his
certified bound gives **Q(v) ≥ 8.9·10⁻¹⁸‖v‖² unconditionally for every v ∈ 𝒞₋^{00}** — the whole
class, complex tests included (his odd-parity sector). (b) (8) then holds on the class iff
n(v₋) ≤ λ_min(0.39725)‖v₋‖², one finite number against one certified number: the cheapest decisive
probe available, and it runs on the existing packet machinery (9)+(12). (c) his doubly-exponential
resolution threshold 2πe^{A_L}, A_L ≈ 4e^L, is a direct cost estimate for the packet matrix (10) —
read it before authorising that run.
Before it is used as a premise: re-verify the interval-arithmetic certificate independently
(unrefereed single-author preprint), and confirm his normalisation of Q and of "support" against
c_A = γ + log 8π + π/2.
