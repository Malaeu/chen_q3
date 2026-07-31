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

## ADDENDUM (2026-07-31, PW simple-even citation audit — Proshka UNVERIFIED_IMPORT)

The §8 claim "(1) The 'simple-even' condition holds for all values of λ for the
prolate-wave operator PW_λ" carries NO inline citation marker in the paper text.
Nearest candidate sources from the bibliography:
  [5] A. Connes, C. Consani, H. Moscovici, "Zeta zeros and prolate wave
      operators", arXiv:2310.18423 — the dedicated prolate companion paper;
  [9] J. Meixner, F. W. Schäfke, "Mathieusche Funktionen und Sphäroidfunktionen",
      Springer 1954 — classical prolate spectral theory (Sturm–Liouville
      simplicity);
  [6] A. Connes, H. Moscovici, PNAS 119 (2022) — UV prolate spectrum.
K7 status UNCHANGED: UNVERIFIED_IMPORT until the exact theorem statement is
extracted from [5] or [9]. Next acquisition step: fetch arXiv:2310.18423 and
locate the simple-even theorem verbatim.

## ADDENDUM 2 (2026-07-31, PW simple-even acquisition — fetch of arXiv:2310.18423)

Fetched: [5] Connes–Consani–Moscovici, "Zeta Zeros and Prolate Wave Operators —
Semilocal Adelic Operators", arXiv:2310.18423v2 (PDF on the bus:
imports/2310.18423.pdf). RESULT OF THE SEARCH:

1. arXiv:2310.18423 does NOT contain an explicit "simple-even for PW_λ" theorem
   (the phrase "admits a simple expression" at its p.3 is about the formula
   Wλ = −S² + 2πλ²(4N+1) − 1/4, not the spectrum). Candidate [5] ELIMINATED as
   the direct source.
2. The actual source trail runs through [9] Meixner–Schäfke 1954: the main paper
   (2511.22755, §7) cites "[9], Satz 9, page 243, Section 3.2 ('Die
   Sphäroidfunktionen')" for uniform eigenfunction estimates; simplicity of the
   m=0 prolate eigenvalues and the parity of eigenfunctions (ps_n has parity
   (−1)^n, so the ground state ps_0 is EVEN) is classical Sturm–Liouville theory
   in that book. K7 status: source CLASS located (M–S 1954, §3.2 around Satz 9);
   exact Satz with the simplicity statement still needs the book itself (not
   freely fetchable) → import remains UNVERIFIED at theorem-statement level,
   but the acquisition target is now precise: Meixner–Schäfke, §3.2.

## CROSS-LINK FIND (same fetch, bigger than the citation)

2511.22755 §7 (p.29, around Lemma 7.2) states verbatim: "h_λ is, up to a
multiplicative scalar, the ONLY linear combination of h_{0,λ}, h_{4,λ} with
vanishing integral", with uniform estimates (Satz-9-based)
  max_{[−λ,λ]} |h_{n,λ} − h_n| ≤ c λ^{−2}   (n = 0, 4)
  max_{[−λ,λ]} |h_λ − h| ≤ c λ^{−2}
and: "Justifying rigorously this step is the main remaining obstacle to our
approach to RH."

This h_λ is EXACTLY the object class of our source-locked hTrial_m (normalized
combination of prolate modes h0,λ/h4,λ, zero mass — cf. 011 source-lock). I.e.
the CCM paper's k_λ ≈ ξ_λ obstacle and our bridge Hfam ↔ G_m (Gate C3) touch
THE SAME concrete function family, with published λ^{−2} approximation rates
for it. Candidate import for the bridge card: Lemma 7.2 (i)/(ii)
[ABSTRACT][PAPER, proof via M–S Satz 9].
