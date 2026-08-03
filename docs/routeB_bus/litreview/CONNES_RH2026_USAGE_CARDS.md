# Connes, The Riemann Hypothesis 2026 (arXiv:2602.04022) — verified usage cards

Source PDF: pdfs/2602.04022.pdf

Title: "The Riemann Hypothesis: Past, Present and a Letter Through Time", [Alain Connes], February 5, 2026 (v1, 3 Feb 2026). 34 pages.

Scope of this extraction: the survey body (Sec. 1–4) is standard historical recap and is NOT mined here. All cards below come from the paper's ORIGINAL contribution: Sec. 5 ("A Letter to Professor Bernhard Riemann", pp. 23–25), Sec. 6 ("The strategy and the next small steps", pp. 26–30), and Sec. 7 ("Geometric Perspectives", pp. 30–34). Quotes are verbatim; mathematical symbols transcribed as faithfully as the PDF text layer allows.

---

## 1. Unique even-sector ground state for the truncated Weil form (→ H2a) — Letter, p. 24 + §6.6, p. 30

VERBATIM (Letter, p. 24): "Next, I know how to prove that there is a function η(u) realizing the minimum of the quadratic form Q(φ) while ∫ φ(u)²du/u = 1. The proof of existence is entirely similar to the proof given by Hilbert in 1900, in his paper "Über das Dirichletsche Prinzip" for the Dirichlet principle. I then take the Mellin transform of the function η(u). I also know how to prove that the zeros of this Mellin transform are on the critical line. This is proved modulo a condition of uniqueness of the minimum"

VERBATIM (footnote 12 to the words "uniqueness of the minimum", p. 24): "The proof uses a generalization of a Theorem of Caratheodory-Fejer on Toeplitz matrices, obtained in 1911, one needs to assume that the lowest eigenvalue of the quadratic form is simple and even"

VERBATIM (§6.6 "Remaining steps", p. 30): "In order to apply Theorem 6.1 one needs to show that the smallest eigenvalue of the Weil quadratic form QW_λ is simple with even eigenvector. The analogue of this property is known for the prolate wave operator."

K7-TAG: OPEN-QUESTION (the simple-even property of QW_λ is explicitly listed as a REMAINING step / assumed hypothesis, not proved here)
MAPS TO Q3 WALL: H2a SIMPLE_EVEN
PROVED-OR-OPEN: OPEN for the Weil form QW_λ. It is an *assumed hypothesis* ("one needs to assume that the lowest eigenvalue ... is simple and even") and is listed under "Remaining steps" as something that "one needs to show". Existence of the minimizer η is proved (à la Hilbert/Dirichlet). Simplicity + evenness is NOT proved for QW_λ in this paper. The *analogue* is stated to be "known for the prolate wave operator".

---

## 2. Fourier–Mellin zeros lie on the critical line (→ H2b) — Letter p. 24–25 + Theorem 6.1, p. 26

VERBATIM (Letter, p. 24): "I also know how to prove that the zeros of this Mellin transform are on the critical line. This is proved modulo a condition of uniqueness of the minimum" [footnote 11 to "critical line": "Which is normalized here as the imaginary line"]

VERBATIM (Letter, p. 25): "What this is saying is that we have a firm grasp on your zeros, without at any point involving the infinity of the collection of all primes. And moreover we know a priori that all zeros of the Mellin transform of η(u) are on the critical line."

VERBATIM — the rigorous theorem behind the claim (Theorem 6.1, §6.1, p. 26): "Let L > 0, D be a real distribution on the interval [0, L] and D̃ the associated even distribution on [−L, L]. Assume that the quadratic form with Schwartz kernel D̃(x − y) defines a lower-bounded selfadjoint operator on L²([−L/2, L/2]), and that the minimum of its spectrum is a simple, isolated eigenvalue, with even eigenfunction η. Then all the zeros of the entire function η̂(z), z ∈ ℂ, Fourier transform of η lie on the real line."

VERBATIM (attribution of Theorem 6.1, p. 26): "The proof of this result follows from a theorem shown in a joint paper [32] with Walter van Suijlekom, entitled "Quadratic Forms, Real Zeros and Echoes of the Spectral Action"."

K7-TAG: THEOREM (conditional) — the critical-line statement IS a proved theorem, but CONDITIONAL on the simple+even hypothesis of card 1.
MAPS TO Q3 WALL: H2b real-zero bridge (Theorem-5.10-type)
PROVED-OR-OPEN: PROVED HERE as a theorem (Theorem 6.1), cited from joint paper [32] with W. van Suijlekom, "Quadratic Forms, Real Zeros and Echoes of the Spectral Action". CRUCIAL: the "provably on the critical line" is genuine — but it is an IMPLICATION whose HYPOTHESIS (smallest eigenvalue simple + even eigenfunction) is itself unproven for QW_λ (card 1). So "provably" is real math, gated on H2a. The letter's proof route uses "a generalization of a Theorem of Caratheodory-Fejer on Toeplitz matrices". Theorem 6.1's proof "is based on the special form of the matrix of the quadratic form in the trigonometric orthonormal basis, the construction for finite matrices of that special form of a selfadjoint operator and the above mentioned Hurwitz theorem to pass to the limit when the size of the matrices tends to infinity."

---

## 3. The c → ∞ convergence to actual Riemann zeros (→ C3-B) — Letter p. 25 + §6.6 + Fact 6.4

VERBATIM (Letter, p. 25): "What we do not know is that, when we increase the upper limit, which was x = 13 here, the corresponding set of zeros will converge towards the zeros of zeta. This is something which at this point is not proved. On the other hand, it seems that the abstract reason why your conjecture is true is now within reach since we know that the zeros of the Mellin transforms of the minimal eigenvectors η_x are purely imaginary, and we expect that the η_x converge to the function whose Mellin transform is your function Ξ(it). The result would then follow from Hurwitz's theorem, which implies that all the zeros of the limit of a convergent sequence of holomorphic functions whose zeros are on a fixed line are still on that line."

VERBATIM (§6.6 "Remaining steps", p. 30): "Moreover it still remains to show that k_λ is a sufficiently good approximation of θ_x, λ = √x."

VERBATIM (Fact 6.4, p. 30): "The Fourier transform of k_λ converges, when λ → ∞, towards the Ξ-function of Riemann uniformly on closed substrips of the open strip ℑ(z) < 1/2."

VERBATIM (§7.4, p. 32): "The remaining difficulty in proving that the eigenvectors θ_x converge to the function k = E(h) of Fact 6.2 is to effectively compare θ_x with k_λ for λ = √x. The numerical evidence was shown in [25]..."

K7-TAG: OPEN-QUESTION (explicitly "not proved"; the convergence of finite/truncated zeros to Riemann zeros is THE stated open wall)
MAPS TO Q3 WALL: C3-B ground→trial (k_λ ≈ ξ_λ and finite-zeros → Riemann-zeros as cutoff → ∞)
PROVED-OR-OPEN: OPEN. Connes states flatly "This is something which at this point is not proved." What IS proved (Fact 6.4) is only that the Fourier transform of the *trial* function k_λ (an educated-guess approximation, NOT the true minimal eigenvector) converges to Ξ uniformly on closed substrips. The gap is exactly: (a) does the *actual* minimal eigenvector θ_x converge to k = E(h)? — "remaining difficulty" (§7.4); and (b) is k_λ a good enough approximation of θ_x? — "still remains to show" (§6.6). Convergence would then close via Hurwitz's theorem. NOTE: the paper's own abstract/conclusion frame this as "a potential proof strategy based on establishing convergence of zeros from finite to infinite Euler products", i.e. explicitly a strategy, not a result.

---

## 4. Simple-even for QW_λ vs the prolate PW_λ (which is proved, which is open) — §6.6 p.30, Fact 6.3 p.28, §7.6 p.33

VERBATIM (§6.6, p. 30): "The analogue of this property [smallest eigenvalue simple with even eigenvector] is known for the prolate wave operator."

VERBATIM (Fact 6.3, §6.3, p. 28): "The eigenvalues of the operator P_λ P̂_λ P_λ in L²([−λ, λ])^ev are simple and form a decreasing sequence ν_n(λ), n ≥ 0, ν_n(λ) → 0 for n → ∞, such that 1 > ν_0(λ) > ν_1(λ) > ... > 0. The corresponding eigenfunctions are the prolate spheroidal wave functions of even index h_{2n,λ} where h_{m,λ} is the m + 1-th eigenfunction of the prolate wave operator (15) in L²([−λ, λ])."

VERBATIM (§7.6, p. 33): "in our joint work [27]: a careful study of the natural selfadjoint extension of PW_λ extended to L²(ℝ) shows that it still has discrete spectrum and that its negative eigenvalues reproduce the ultraviolet behavior of the squares of zeros of the Riemann zeta function."

K7-TAG: THEOREM (prolate side, simplicity via Fact 6.3) vs OPEN-QUESTION (QW_λ side)
MAPS TO Q3 WALL: H2a SIMPLE_EVEN
PROVED-OR-OPEN: SPLIT. For the PROLATE operator PW_λ / the compression P_λ P̂_λ P_λ: simplicity of the eigenvalues is a stated FACT (Fact 6.3, non-degenerate strictly decreasing sequence), and evenness of the ground state h_{0,λ} is built in (even-index prolate functions). For the WEIL form QW_λ: the simple-even property is NOT proved — only "the analogue ... is known for the prolate wave operator". So the prolate model has the property; transferring it to QW_λ is the open H2a step.

---

## 5. NEW results in THIS paper bearing on H2a/H2b/C3-B (vs earlier CCM "Zeta Spectral Triples" 2511.22755)

VERBATIM (Theorem 6.1 attribution, p. 26): "The proof of this result follows from a theorem shown in a joint paper [32] with Walter van Suijlekom, entitled "Quadratic Forms, Real Zeros and Echoes of the Spectral Action"." — a general real-zeros theorem (any lower-bounded quadratic form on [0,L] with simple even ground state ⇒ Fourier transform of ground state has only real zeros). This is the engine for H2b.

VERBATIM (the explicit trial construction, §6.4, p. 29, eq. (17)): "k_λ(u) := E(h_λ)(u), ∀u ∈ [λ⁻¹, λ]" ... "where h_λ is, up to a multiplicative scalar, the only linear combination of h_{0,λ}, h_{4,λ} with vanishing integral." — the concrete prolate-based educated guess for the minimal eigenvector, with proved Fourier-transform convergence (Fact 6.4).

VERBATIM (the letter's numerical result, Abstract, p. 1): "Using only primes less than 13, this optimization procedure yields approximations to the first 50 zeros with accuracies ranging from 2.6 × 10⁻⁵⁵ to 10⁻³. Moreover we prove a general result that these approximating values lie exactly on the critical line ℜ(z) = 1/2."

VERBATIM (§7.5, p. 32, IR construction): "For the infrared regime we construct in [30] self-adjoint operators D_log^{(λ,N)} obtained as rank-one perturbations of the spectral triple associated with the scaling operator on the interval [λ⁻¹, λ] and whose spectrum coincides with the stunning approximation of the low lying zeta zeros as described in the letter to Riemann."

K7-TAG: THEOREM (Theorem 6.1 / [32]) + SURVEY-CLAIM (numerical accuracies, plots) + THEOREM (Fact 6.4 convergence of trial)
MAPS TO Q3 WALL: H2b (Theorem 6.1), C3-B (k_λ construction + Fact 6.4)
PROVED-OR-OPEN: The genuinely NEW proved item flagged in THIS survey is Theorem 6.1 (via joint paper [32] with van Suijlekom — the "Quadratic Forms, Real Zeros and Echoes of the Spectral Action" real-zeros theorem) plus the k_λ construction and its Fourier-transform convergence (Fact 6.4). CAVEAT / VERIFICATION LIMIT: I did NOT read arXiv 2511.22755 in this session, so I cannot certify which items are strictly absent from the earlier CCM (Connes–Consani–Moscovici) work versus merely restated. The paper cross-references its own companion works [24], [25], [27] (joint with H. Moscovici), [30], [32] (with van Suijlekom). Treat "[32] real-zeros theorem" and the "primes ≤ 13 → 50 zeros, errors down to 2.6×10⁻⁵⁵" numerical table as the headline new material presented here. The 10⁻⁵⁵ accuracy is NUMERICAL evidence, not a proof of convergence (see card 3).

---

## 6. Exact definition of the truncated Weil quadratic form — §6.4 p.28 + Letter p.24 + §4.1 p.20–21

VERBATIM (primary definition, §6.4, p. 28): "Let λ > 1, and QW_λ be the restriction of the Weil quadratic form to test functions whose support is within the interval [λ⁻¹, λ]. By the result of André Weil discussed in §4.1, the positivity of QW_λ for all λ > 1 is equivalent to RH."

VERBATIM (associated operator, §6.4, p. 28, eq. (16)): "There is (see [25],[31]) for each λ > 1 a canonical lower bounded, unbounded selfadjoint operator A_λ with compact resolvent, in the Hilbert space L²([λ⁻¹, λ], du/u) such that QW_λ(f, f) = ⟨A_λ f | f⟩"

VERBATIM (the elementary form used in the Letter, p. 24): "Out of these primes, 2, 3, etc., up to 13, one fabricates a quadratic form. ... It is a quadratic form on the infinite dimensional space of functions φ(u) of a positive real variable which vanish outside the interval [1, 13]. The value Q(φ) of the quadratic form is obtained by applying the explicit formula to the function ψ(v) = ∫ φ(u)φ(uv)du/u. Thus because the function φ vanish outside the interval [1, 13], the function ψ vanishes outside the interval [1/13, 13] and one does not need to use any prime power than 2, 3, 4, 5, 7, 8, 9, 11, 13 to compute Q(φ)."

VERBATIM (underlying Weil form / explicit formula, §4.1, p. 20–21, eqs. (9)–(10)): "the quadratic form QW defined using the Riemann-Weil explicit formulas applied to test functions with support in a compact symmetric interval." Explicit formula (p. 21): "f̂(i/2) − Σ_{1/2+is∈Z} f̂(s) + f̂(−i/2) = Σ_v W_v(f)", with "f̂(s) := ∫₀^∞ f(x)x^{−is} d*x, d*x = dx/x", non-archimedean "W_p(f) := (log p) Σ_{m=1}^∞ p^{−m/2}(f(p^m) + f(p^{−m}))" (eq. 9), archimedean "W_ℝ(f) := (log 4π + γ)f(1) + ∫₁^∞ (f(x) + f(x⁻¹) − 2x^{−1/2}f(1)) x^{1/2}/(x − x⁻¹) d*x" (eq. 10). Weil's equivalence (p. 21): "RH ⟺ Σ_v W_v(g * g*) ≤ 0, ∀g, ĝ(±i/2) = 0".

K7-TAG: CONVENTION / DEFINITION
MAPS TO Q3 WALL: STEP34 / Weil positivity (prime W_p vs archimedean W_ℝ sign structure); underpins H2a/H2b/C3-B
PROVED-OR-OPEN: DEFINITION (not a theorem). QW_λ = restriction of the Riemann–Weil explicit-formula quadratic form to test functions supported in the symmetric compact interval [λ⁻¹, λ] (⇔ φ supported in [1, x] with x = λ² in the letter's coordinates; letter uses x = 13). Truncating support to [λ⁻¹, λ] means only primes p with p^m ≤ x = λ² enter (finitely many primes). Weil positivity of QW_λ for all λ > 1 ⇔ RH (Weil's criterion, §4.1). The prime-vs-archimedean split is exactly eqs. (9) [W_p] vs (10) [W_ℝ].

---

## Summary of verification

- Items found VERBATIM: all 6 requested cards located with exact quotes and locations. No "NOT FOUND".
- The task's paraphrased open question is CONFIRMED and matches §6.6 + Letter p. 25 + §7.4 nearly word-for-word in substance.

### CRUCIAL bottom line — PROVED vs OPEN

- Even-sector ground state (simple + even) for the truncated Weil form QW_λ: **OPEN / ASSUMED.** Explicitly a "Remaining step" (§6.6) and an assumed hypothesis (footnote 12, p. 24). The analogue is proved only for the PROLATE operator (Fact 6.3), not for QW_λ.
- "Fourier–Mellin zeros provably lie on the critical line": **PROVED as a CONDITIONAL theorem** (Theorem 6.1, from joint paper [32] with van Suijlekom). The word "provably" is honest math — but it is an implication whose hypothesis is exactly the unproven simple-even property above. So H2b is closed *modulo* H2a.
- c → ∞ convergence of finite/truncated zeros to actual Riemann zeros: **OPEN — "not proved" (Connes' own words, p. 25).** Only the *trial* function k_λ has proved Fourier-convergence to Ξ (Fact 6.4); convergence of the true minimal eigenvector θ_x and the θ_x ↔ k_λ comparison remain open (§6.6, §7.4). The 2.6×10⁻⁵⁵-accuracy agreement is NUMERICAL evidence only.

Net: This paper does NOT close H2a or C3-B. It supplies a conditional H2b engine (Theorem 6.1) and strong numerics. Do NOT read any of this as Q3 closure.
