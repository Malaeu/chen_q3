# IMPORT ACQUISITION — Theorem 5.10, "Zeta Spectral Triples"

Acquired: 2026-07-31 by conductor-CLI (owner task from Mythos routing table, item 3).
Source: arXiv 2511.22755 — Alain Connes, Caterina Consani, Henri Moscovici,
*Zeta Spectral Triples*. PDF stored alongside: `imports/2511.22755.pdf` (668 KB).
Extraction: pdftotext; formulas may carry OCR artifacts — the PDF is authoritative.
K7 classification: Theorem 5.10 itself = THEOREM (proved in the paper).
The RH strategy built on it = CONDITIONAL (the paper's own §8 "The missing steps").

## Theorem 5.10 (verbatim modulo OCR)

Let ε_N be the smallest eigenvalue of QW_λ^N assumed simple and ξ the corresponding
eigenvector assumed even, normalized by δ_N(ξ) = 1.

(i) The operator D_log^(λ,N) is selfadjoint in the direct sum E_N ⊕ E_N^⊥ where on
    the subspace E'_N = E_N / Cξ the inner product is given by the restriction of
    the quadratic form QW_λ − ε_N⟨|⟩.

(ii) The regularized determinant of D_log^(λ,N) is given by

    det_reg(D_log^(λ,N) − z) = −i λ^{−iz} ξ̂(z)

    where ξ̂ is the Fourier transform of ξ for the duality ⟨R*₊ | R⟩.

(iii) The Fourier transform ξ̂(z) is an entire function, ALL ITS ZEROS ARE ON THE
    REAL LINE and coincide with the spectrum of D_log^(λ,N).

## Why this is the mainline entry (map: импорт Thm 5.10 → S2 cluster · H2b)

Clause (iii) is an H2-machine: an explicit finite-dimensional construction whose
associated entire function has provably REAL zeros (selfadjoint spectrum ⇒ real).
The paper's Outlook then states the two-limit strategy:

- fixed λ, N → ∞: det_reg(D_log^(λ,N) − s) → −i λ^{−iz} ξ̂_λ(z);
- λ → ∞: ξ̂_λ (suitably normalized) → Riemann's Ξ uniformly on closed substrips of
  |Im z| < 1/2; convergence would entail RH via Hurwitz.

This is structurally OUR H1–H4 ladder (entire approximants, real zeros, strip
tracking, decay) built from the Weil quadratic form + prolate spheroidal side —
the same objects as the Q3 mainline (Weil positivity, prolate layer on this bus:
ProlateLayer.lean, goals 016/019/020).

## The paper's own missing steps (§8, verbatim summary)

1. To apply Theorem 5.10 to QW_λ one must PROVE that its smallest eigenvalue
   (existence by their Theorem 3.6) is SIMPLE and its eigenvector ξ_λ is EVEN.
2. Establish that k_λ approximates (a scalar multiple of) ξ_λ accurately enough to
   justify convergence of the zeros of ξ̂_λ to the nontrivial zeros of ζ(1/2 + is).

Supporting indications named by the authors: simple-even holds for the prolate-wave
operator PW_λ for all λ; the tiny eigenvalues ε_λ match the P_λ/P̂_λ discrepancy;
numerical proximity k_λ ≈ ξ_λ extends to higher eigenfunctions.

## Cross-links for the promotion card (Mythos)

- Their QW_λ = Weil quadratic form ↔ Q3 Weil positivity core (Weil_criterion_tau0).
- Their prolate approximation ↔ bus prolate layer (goals 016/019/020, ProlateLayer.lean).
- Their "simple + even smallest eigenvalue" gap ↔ candidate NEW named lemma for the
  S2 cluster / H2b wall — this is the exact statement the mainline import needs.
- Numerical spectra ≈ zeta zeros = evidence, not proof (their own wording); no
  status promotion follows from this import.
