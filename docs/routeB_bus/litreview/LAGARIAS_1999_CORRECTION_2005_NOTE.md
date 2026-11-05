# Lagarias, positivity of Re ξ′/ξ — the 2005 Correction and its relevance to Route B (Mythos, 2026-11-05)

## Sources

**Main paper.** J. C. Lagarias, "On a positivity property of the Riemann ξ-function", Acta Arith. 89 (1999) 217–234, DOI 10.4064/aa-89-3-217-234.
- Preprint, Oct. 5, 1998 revision, in this repo: `docs/routeB_bus/litreview/pdfs/lagarias_1998_positivity_xi.pdf`, blob d85b26c0.
- **WARNING:** this file is a Git LFS pointer of 131 bytes. Agents reading it through the raw or contents API get only the pointer, not the PDF. The real PDF (235970 bytes) is here:
  https://media.githubusercontent.com/media/Malaeu/chen_q3/rh_clean/docs/routeB_bus/litreview/pdfs/lagarias_1998_positivity_xi.pdf
- The PDF uses Type-3 fonts, so pdftotext returns garbage. Read the pages as images.

**Correction.** J. C. Lagarias, "Correction to: 'On a positivity property of the Riemann ξ-function' (Acta Arith. 89 (1999), 217–234)", Acta Arith. 116 (2005) 293–294, DOI 10.4064/aa116-3-5.
- EuDML: https://eudml.org/doc/278481
- The PDF is behind IMPAN and is NOT in this repo; this environment could not fetch it.
- Public abstract (academia.edu listing): the correction addresses an error in **Lemma 3.1**, restates it, and discusses the consequences for the subsequent lemmas.

## What is wrong in Lemma 3.1 (Mythos derivation, sympy-checked; the Correction text itself was not read)

The preprint states, for t ≠ 0:

  1/(σ0²+(t+γ)²) + 1/(σ0²+(t−γ)²) ≥ 2/(σ0²+t²)  ⇔  3γ² ≥ σ0² + t²   (preprint (3.3)–(3.4))

Clearing denominators exactly gives

  LHS − RHS = −2γ²(γ² + σ0² − 3t²) / [(σ0²+t²)(σ0²+(t−γ)²)(σ0²+(t+γ)²)],

so the correct condition is

  **3t² ≥ σ0² + γ²**

The roles of t and γ are swapped in the preprint.

Check at σ0 = 0.5, γ = 14.13:
- t = 0.1: the inequality is FALSE; the preprint condition predicts TRUE.
- t = 30: TRUE; the preprint condition predicts FALSE.

**Consequence.** The preprint's proof of Lemma 3.2 (RH ⇒ Re ξ′/ξ(σ+it) > ξ′/ξ(σ) for 0 < |t| ≤ 21) applies Lemma 3.1 to conjugate zero pairs, using |γ| > 14.13 and |t| ≤ 21. With the corrected condition this fails for small |t|, below roughly γ₁/√3 ≈ 8.2. So the near-axis part of Theorem 1.3 (RH ⇒ the infimum on vertical lines is attained at t = 0 for all σ > 1/2) needs the repair given in the Correction.

**Not affected** (they do not use Lemma 3.1):
- Theorem 1.1: Re f′/f > 0 on Re s > θ ⇔ all zeros have Re ρ ≤ θ. This gives RH ⇔ Re ξ′/ξ > 0 on Re s > 1/2 (also in Hinkkanen).
- Theorem 1.2: for σ ≥ 10 (number fields: σ ≥ 1 + 9/n_K^{1/3}) the infimum is attained at t = 0, unconditionally.

Later literature extends Theorem 1.2: Garunkštis (Lith. Math. J. 42, 2002) to σ ≥ 1; Broughan (2005) to near the critical strip.

## Why Proshka needs it, and the synergies with Route B (Mythos assessment)

1. **The pole is the only obstruction in Lagarias's proof (preprint §2, (2.13)–(2.22)).** For σ > 1:
   - The prime part −Σ Λ(n) n^{−σ} cos(t log n) is minimised at t = 0, because Λ ≥ 0 and |cos| ≤ 1. This is the Euler product working as a positivity source.
   - The Γ part increases with |t|.
   - The pole term Re 1/(s−1) = (σ−1)/((σ−1)²+t²) DECREASES with |t|. Lagarias offsets it with the Γ poles at the negative even integers, shifting the odd ones by inequality (2.21).

   This is the same lesson as Route B's √m wall = pole echo. Lagarias gives a SECOND gauge for the pole: trade it against the Γ poles, instead of our renormalization v_L + J_−. This is a candidate knob for Round 5, (c).

2. **The margin is quantified (Lemma 3.3, conditional on RH).** 0 ≤ ξ′/ξ(σ) ≤ 0.047(σ − 1/2), and ξ′/ξ(1) ≈ 0.023095.
   - With Garunkštis's σ ≥ 1, the unconditional floor of the blurred counter's speed at σ = 1 is ≈ 0.0231. That is tiny.
   - Under RH the floor shrinks linearly to 0 at the critical line: "впритык", made quantitative.
   - This is the natural normalisation for the σ-flow / W = δ·H of Proshka Round 4 (7a1d9a53 §5.3). Under RH, H(δ, t)/δ ≥ ξ′/ξ(1/2+δ)/δ → Σ 2/γ² ≈ 0.046 as δ → 0.

3. **Zero-spacing input (Lemma 3.5, unconditional).** For each |t| ≥ 21 there is a zero within distance 2, or two zeros within distance 5. This is the kind of height-local density fact the Round-4 height-local counter transport (Proshka B, 07c813f7) needs: the counter must step at bounded intervals.

4. **Ladder.** Literature has σ ≥ 10 (Lagarias), then σ ≥ 1 (Garunkštis), then near the strip (Broughan). These are exactly the "proved top rungs" of the σ-flow. Every step below σ = 1 that is uniform in t is a zero-free-region statement.

## Follow-up literature (found via Consensus MCP, 2026-11-05)

- **Garunkštis**, "On a positivity property of the Riemann ξ-function", Lith. Math. J. 42 (2002), DOI 10.1023/A:1016158125685. Proves that the infimum is attained at t = 0 for σ ≥ 1.
- **Broughan**, "Extension of the Riemann ξ-function's logarithmic derivative positivity region to near the critical strip", Canad. Math. Bull. 52 (2009) 186–194, DOI 10.4153/CMB-2009-021-3.
  - Number fields: the constant 9 is improved to 8.
  - For ℚ: the inequality is extended to σ ≥ 1 for t sufficiently large or small, and to σ ≥ 1 + 1/(log t − 5) for all t ≠ 0.
- **Goldštein et al.**, J. Math. Inequal. 18 (2024) 829–845, DOI 10.7153/jmi-2024-18-45. Gives explicit bounds for Re Σ 1/(s−ρ) and studies positivity in 1/2 < σ < 1 under hypothetical off-line zeros.
- Full texts are available through the owner's institutional access (uni-due digibib / LibKey links in the Consensus results).

## Status labels

- Lemma 3.1 correction: Mythos algebra plus sympy check. FACT for the algebra; the content of the Correction itself is NOT READ.
- Syntheses 1–4: HYPOTHESIS / assessment, except quoted statements from the preprint, which are FACT (preprint text).
