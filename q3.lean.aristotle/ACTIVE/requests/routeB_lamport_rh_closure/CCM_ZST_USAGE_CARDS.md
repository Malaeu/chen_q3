# CCM Zeta Spectral Triples (arXiv:2511.22755) — verified theorem-usage cards
Source PDF: pdfs/2511.22755.pdf

Note on locations: page numbers below are the printed page numbers of the article
(header/footer numbering), which match the PDF page count 1:1 for this file.

---

## Theorem 5.10 (regularized determinant / real zeros of the Fourier transform) — p. 23, §5.6 "Spectrum and regularized determinant of D_log^{(λ,N)}"
VERBATIM:
"Theorem 5.10. Let ε_N be the smallest eigenvalue of QW_λ^N assumed simple and ξ the corresponding
eigenvector assumed even, normalized by δ_N(ξ) = 1.
(i) The operator D_log^{(λ,N)} is selfadjoint in the direct sum E'_N ⊕ E_N^⊥ where on the subspace E'_N = E_N/ℂξ
the inner product is given by the restriction of the quadratic form QW_λ^N − ε_N⟨·|·⟩.
(ii) The regularized determinant of D_log^{(λ,N)} is given by
    det_reg(D_log^{(λ,N)} − z) = −i λ^{−iz} ξ̂(z)
where ξ̂ is the Fourier transform of ξ for the duality ⟨ℝ*_+ | ℝ⟩.
(iii) The Fourier transform ξ̂(z) is an entire function, all its zeros are on the real line and coincide
with the spectrum of D_log^{(λ,N)}."
K7-TAG: THEOREM (proven in the paper; note the two standing hypotheses inside its own statement — see CAVEAT)
USED IN Q3 FOR: H2b real-zero bridge — this is the exact result that turns the regularized determinant
(hence the Fourier transform ξ̂) of the perturbed scaling operator into an entire function whose zeros are
ALL real and equal to the operator spectrum. It is the finite-N (truncated) analogue of the "zeros on the
critical line" mechanism Route B relies on for the real-zero bridge.
CAVEAT: The theorem is CONDITIONAL on its own hypotheses, stated in the theorem head: "ε_N ... assumed
simple" and "ξ the corresponding eigenvector assumed even". These are exactly the two properties §8 flags
as unproven for QW_λ (the simple-even condition). The determinant identity and reality-of-zeros conclusion
hold once simple+even is granted; the paper does not prove simple+even for QW_λ itself.

---

## Theorem 3.6 (discrete lower-bounded spectrum of A_λ) — p. 9, §3.2 "Discrete spectrum of the semilocal Weil quadratic form QW_λ"
VERBATIM:
"Theorem 3.6. The selfadjoint operator A_λ has discrete lower bounded spectrum."
(Surrounding context, same page: "Thus, for each λ > 1, there is a canonical lower bounded unbounded
selfadjoint operator A_λ in the Hilbert space L²([λ^{-1}, λ], d*u) such that QW_λ(f,f) = ⟨A_λ f | f⟩."
(3.23). Proof sketch given: reduces via Prop. 3.5 to compactness of an embedding map, handled through the
archimedean multiplier ∂_t θ(t) = (1/2)(log|t| − log 2 − log π) − 1/(48 t²) + O(t^{-4}) (3.24).)
K7-TAG: THEOREM (proven in the paper, building on Prop. 3.3, 3.4, 3.5 and Schmüdgen [12] representation
theorem for semibounded forms)
USED IN Q3 FOR: H2a SIMPLE_EVEN(QW_λ) — this theorem is what GUARANTEES the existence of a genuine
smallest eigenvalue of A_λ (equivalently of QW_λ): a discrete, lower-bounded spectrum means the infimum is
an attained eigenvalue. It underwrites the "existence of ξ_λ" half of the H2a gap. It does NOT by itself
give simplicity or evenness of that eigenvalue.
CAVEAT: Gives discreteness + lower boundedness only. Simplicity and evenness of the smallest eigenvalue are
NOT part of this theorem; §8 explicitly lists proving "simple and ... even" as still missing. A_λ is defined
via the representation theorem for semibounded closed forms (needs QW_λ densely defined, lower semicontinuous
— established in Prop. 3.3/3.4).

---

## Lemma 7.2 (λ^{-2} uniform estimates for h_{n,λ}, n = 0,4) — p. 29, §7 "Outlook"
VERBATIM:
"Lemma 7.2. (i) The eigenfunctions h_{n,λ} of PW_λ, suitably normalized, fulfill for n = 0,4 an
estimate of the form (with c < ∞)
    max_{x∈[−λ,λ]} |h_{n,λ}(x) − h_n(x)| ≤ c λ^{−2}          (7.7)
(ii) Let h_λ be the suitably normalized linear combination of h_{0,λ}, h_{4,λ} with vanishing integral. One
has an estimate of the form (with c < ∞)
    max_{x∈[−λ,λ]} |h_λ(x) − h(x)| ≤ c λ^{−2}                (7.8)"
K7-TAG: LEMMA (proven; proof rests on Meixner–Schäfke [9] Satz 9 spheroidal-function asymptotics and
Fuchs [8] Theorem 1 for the 1−χ(λ) decay)
USED IN Q3 FOR: C3-B ground→trial (and feeds C3-A) — this is the quantitative control that the prolate
eigenfunctions h_{n,λ} converge (rate λ^{-2}) to the fixed Hermite functions h_n, and that the trial
combination h_λ converges to Riemann's h. It is the analytic backbone for bounding how close the educated
guess trial function is to the true ground/trial object as λ → ∞.
CAVEAT: Controls h_λ vs h (the FIXED prolate/Hermite side), NOT h_λ vs ξ_λ (the Weil-form eigenvector). The
gap "k_λ ≈ ξ_λ" is separate and is exactly what §8 calls unproven. Constant c is non-explicit ("c < ∞").
Depends on [9] Satz 9 and [8] Thm 1 as external inputs.

---

## Lemma 7.3 (convergence of the transform of k_λ to Ξ on closed substrips) — p. 31, §7 "Outlook"
VERBATIM:
"Lemma 7.3. The Fourier transform of k_λ converges, when λ → ∞, towards the Ξ-function of
Riemann uniformly on closed substrips of the open strip |ℑ(z)| < 1/2."
(Proof spans pp. 31–32, using the map ℰ, the estimate δ(λ) ≤ c λ^{-2} from (7.8), a Mellin-transform bound
|ℳ(k_λ)(s) − ∫_{λ^{-1}}^{λ} k(u) u^{s-1} du| = O(λ^{-1/2-α}) for α = ℜ(s) ∈ (−1/2, 1/2), and Poisson
symmetry k(u) = k(u^{-1}) to kill the tail ∫_λ^∞ k(u) u^{s-1} du → 0.)
K7-TAG: LEMMA (proven in the paper)
USED IN Q3 FOR: C3-A trial→Ξ — this is precisely the "transform of the trial function converges to the
Riemann Ξ-function" statement, on closed substrips of the critical strip. It is the analytic target of the
Route B trial→Ξ leg: once k_λ is the transform of the educated-guess trial h_λ, its transform limit is Ξ.
CAVEAT: This is about k_λ = transform of the EXPLICIT trial function h_λ (the prolate/Hermite educated
guess), NOT about the transform of the true Weil eigenvector ξ_λ. Convergence to Ξ is established for k_λ;
linking k_λ to ξ_λ (so that the OPERATOR determinant converges to Ξ) remains the unproven "k_λ ≈ ξ_λ" step
of §8. Convergence is uniform only on CLOSED substrips strictly inside |ℑ(z)| < 1/2.

---

## §8 "The missing steps" (two essential unproven hypotheses) — p. 32, §8 "The missing steps"
VERBATIM:
"There are two essential steps still missing to justify our tentative proof of the Riemann Hypothesis. The
first is that, in order to apply Theorem 5.10 to the Weil quadratic form QW_λ, one must prove that its
smallest eigenvalue—whose existence is ensured by Theorem 3.6—is simple and that its corresponding
eigenvector ξ_λ is even. The second step is to establish that k_λ provides a sufficiently accurate
approximation to (a scalar multiple of) ξ_λ, in order to justify the convergence of the zeros of ξ̂_λ
towards the non-trivial zeros of ζ(1/2 + is).
There are, however, three indications supporting the feasibility of these steps.
(1) The 'simple-even' condition holds for all values of λ for the prolate-wave operator PW_λ.
(2) The extremely small numbers ε_λ that occur as eigenvalues of the Weil quadratic form QW_λ also appear—
see Figure 4—when evaluating the discrepancy for h_λ to belong simultaneously to P_λ and P̂_λ.
(3) The numerical evidence for the proximity between k_λ and ξ_λ extends to the higher eigenfunctions of the
Weil quadratic form."
K7-TAG: CONJECTURE (authors explicitly call these the two "missing steps" / unproven hypotheses; the three
"indications" are numerical/heuristic support, not proofs — item (2) rests on Figure 4, a plot)
USED IN Q3 FOR: H2a SIMPLE_EVEN(QW_λ) + C3-B ground→trial — this text is the authors' own statement of the
two gaps that Route B is trying to close: (a) smallest eigenvalue of QW_λ is simple with even eigenvector,
and (b) the trial k_λ approximates ξ_λ well enough. These map directly onto the Q3 H2a and C3 gaps.
CAVEAT: Authors call both steps UNPROVEN ("essential steps still missing"). The supporting "indications"
(1)-(3) are explicitly heuristic: (1) is proven only for PW_λ (prolate operator), NOT for QW_λ; (2) and (3)
are numerical evidence (Figure 4). Do NOT treat the simple-even condition or k_λ ≈ ξ_λ as established for the
Weil form.

---

## Definition of the prolate operator W_λ (= PW_λ) and the trial function h_λ — pp. 27–28, §7 "Outlook" (eqns 7.1–7.6)
VERBATIM (prolate wave operator):
"It is based on the deformation of the harmonic oscillator called the prolate wave operator
    PW_λ := −∂_x ((λ² − x²)∂_x) + (2πλx)².          (7.5)
The eigenfunctions h_{n,λ}(u) of PW_λ have the same labelling as the Hermite functions h_n, they are even
for n even and invariant under the Fourier transform for n multiple of 4."
VERBATIM (trial function / educated guess):
"In agreement with Lemma 7.1, the educated guess k_λ is
    k_λ(u) := ℰ(h_λ)(u),   ∀u ∈ [λ^{-1}, λ]          (7.6)
where h_λ is, up to a multiplicative scalar, the only linear combination of h_{0,λ}, h_{4,λ} with vanishing
integral."
Supporting (Riemann's h and the map ℰ, eqns 7.1–7.3):
"k(u) = ℰ(h)(u),   h(u) = (π/2) u² (2π u² − 3) e^{−π u²}.     (7.1)"
"ℰ(f)(u) := u^{1/2} Σ_{1}^{∞} f(nu).     (7.2)"
"**H** f(u) := −f''(u) + 4π² u² f(u)     (7.3)"  [Hermite/harmonic-oscillator operator; h_n its normalized
eigenfunction for eigenvalue 2π(1+2n)]
K7-TAG: CONVENTION (definitions/notation introduced by the paper)
USED IN Q3 FOR: prolate operator definition — supplies the exact operator PW_λ (7.5) and the exact trial
function h_λ / k_λ (7.6) that Route B's C3 legs and the "world of prolate wave functions" bridge rely on.
h_λ is the vanishing-integral combination of h_{0,λ} and h_{4,λ}; k_λ = ℰ(h_λ).
CAVEAT: PW_λ is the PROLATE operator, distinct from the Weil-form operator A_λ / QW_λ. The paper proves
simple-even for PW_λ (§8 indication 1) but NOT for QW_λ. h_λ is an "educated guess"/trial (their words),
constructed to approximate a scalar multiple of ξ_λ; the adequacy of that approximation is one of the
unproven §8 steps. Construction of k_λ is attributed to [4] (Connes–Consani, Spectral triples and ζ-cycles).

---

### Coverage summary
All 6 requested results were found VERBATIM in this PDF:
1. Theorem 5.10 — p. 23 — FOUND
2. Theorem 3.6 — p. 9 — FOUND
3. Lemma 7.2 — p. 29 — FOUND
4. Lemma 7.3 — p. 31 — FOUND
5. §8 missing steps text — p. 32 — FOUND
6. Prolate operator PW_λ (7.5) + trial h_λ/k_λ (7.6) — pp. 27–28 — FOUND
