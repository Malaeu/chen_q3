# IMPORT SUPPLEMENT — §8, Theorem 3.6, δ_N normalization (for the simple+even card)

Acquired: 2026-07-31 by conductor-CLI (Mythos packet-4 item 3).
Source: arXiv 2511.22755, Connes–Consani–Moscovici, *Zeta Spectral Triples*
(PDF on the bus: `imports/2511.22755.pdf`; pdftotext extraction, PDF authoritative).
Companion to: `imports/THM510_ZETA_SPECTRAL_TRIPLES_2026-07-31.md`.

## §8 "The missing steps" (verbatim modulo OCR)

There are two essential steps still missing to justify our tentative proof of the
Riemann Hypothesis. The first is that, in order to apply Theorem 5.10 to the Weil
quadratic form QW_λ, one must prove that its smallest eigenvalue—whose existence is
ensured by Theorem 3.6—is simple and that its corresponding eigenvector ξ_λ is even.
The second step is to establish that k_λ provides a sufficiently accurate
approximation to (a scalar multiple of) ξ_λ, in order to justify the convergence of
the zeros of ξ̂_λ towards the non-trivial zeros of ζ(1/2 + is).

There are, however, three indications supporting the feasibility of these steps.
(1) The "simple-even" condition holds for all values of λ for the prolate-wave
operator PW_λ.
(2) The extremely small numbers ε_λ that occur as eigenvalues of the Weil quadratic
form QW_λ also appear—see Figure 4—when evaluating the discrepancy for h_λ to belong
simultaneously to P_λ and P̂_λ.
(3) The numerical evidence for the proximity between k_λ and ξ_λ extends to the
higher eigenfunctions of the Weil quadratic form.

## Theorem 3.6 + supporting Proposition 3.5 (verbatim modulo OCR)

Proposition 3.5 (from [12], Proposition 10.6). Suppose that A ≥ m_A is a lower
semibounded self-adjoint operator and m < m_A. Then the following are equivalent:
1. The embedding map I_t^A : (D[A], ‖·‖_t^A) → (H, ‖·‖) is compact.
2. The resolvent R_λ(A) is compact for one, hence for all, λ ∈ ρ(A).
3. (A − mI)^{−1/2} is compact.
4. A has a purely discrete spectrum.

Theorem 3.6. The selfadjoint operator A_λ has discrete lower bounded spectrum.

Proof (head, verbatim): By the proof of the lower boundedness in [4], the
contribution of the non-archimedean primes to the operator A_λ is bounded as well
as the contribution of the evaluation of the Fourier transform at the poles. Thus
it is enough to deal, for any λ > 1, with the contribution of the archimedean place
to A_λ in the Hilbert space L²(λ^{−1}, λ), d*u. It is given, after Fourier
transform, by the multiplication by
  ∂_t θ(t) = (1/2)(log|t| − log 2 − log π) − 1/2 + O(t^{−4})   (3.24)
[continues in PDF]

## δ_N — Dirichlet kernel and the normalization δ_N(ξ) = 1

§5.3 "The Dirichlet Kernel δ_N as an approximation of the Dirac Delta":

  D_N(x) = Σ_{n=−N}^{N} exp(2πinx/L), x ∈ [0, L]                (5.8)
         = sin(π(2N+1)x/L) / sin(πx/L)

Context line (paper p. ~5): "We let δ_N ∈ E_N be the vector representing the
Dirichlet [kernel functional]". Theorem 5.10 normalizes the eigenvector by
δ_N(ξ) = 1 — i.e. the Dirichlet-kernel evaluation functional applied to ξ equals 1
(finite-N substitute for point evaluation ξ(0) = 1; the λ→∞ Outlook normalization
is ξ(λ) = 1).

## Card hook (Mythos promotion/wall card)

Candidate named lemma for the S2·H2b wall:
  SIMPLE_EVEN(QW_λ): the smallest eigenvalue of QW_λ (exists by Thm 3.6) is simple,
  and its eigenvector ξ_λ is even.
Their feasibility anchor: simple-even holds for the prolate operator PW_λ for ALL λ
— and the prolate layer already lives on this bus (goals 016/019/020,
ProlateLayer.lean). K7: SIMPLE_EVEN is CONJECTURE-level for QW_λ (their own missing
step), THEOREM for PW_λ per their citation.
