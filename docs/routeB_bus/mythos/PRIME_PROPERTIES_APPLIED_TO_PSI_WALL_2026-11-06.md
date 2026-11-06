# Prime properties applied to the wall ψ(x) − x (2026-11-06)

Status: internal Mythos analysis. CHALLENGER / NOT_RH.

Labels:
- FACT — a theorem, or a formula from a cited source.
- HYP — hypothesis.
- SPEC — speculation.

The wall. After the exact pole cancellation (a4ab9e92; DH fails without a pole, 535d2c27), every Route B receiver reduces to the pole-subtracted prime fluctuation:

    D_N(t) = Σ_{n≤N} (Λ(n) − 1) n^{−1/2−it}   ⇔   ψ(x) − x

- It is the head of Z_N: 96–106% of the mass, DIAG in `SYNTHESIS_PRIMES_HEAD_TAIL_2026-11-06.md`.
- It is the counter drawdown in the window route.
- It is the estimate (C) of a4ab9e92.

“Passes” means: the property gives an unconditional, non-circular handle on THIS single term (modulus q = 1) at the √x scale.

## Table (rows = dictionary `PRIME_PROPERTIES_VS_ZEROS_DICTIONARY_2026-11-06.md`)

| # | Property | What it does to ψ(x) − x | Passes? |
|---|---|---|---|
| 1 | Euler product, Λ ≥ 0 | Λ ≥ 0 plus no real zeros in (0, 1) ⇒ Landau's lemma: a ONE-sided bound ψ(x) − x ≥ −Cx^θ already excludes zeros in Re s > θ (FACT, Ingham ch. IV). This is why every receiver is one-sided. Gives no bound. | form only |
| 2 | PNT density | error x·exp(−c(log x)^{3/5}(log log x)^{−1/5}) (Vinogradov–Korobov). DMV: Euler product + good integer counting cannot do better (FACT). | no |
| 3 | √-error | the target itself | — |
| 4 | Lattice ℤ, Poisson, functional equation | exact explicit formula (transfer only); Ω±(√x) (Landau); positive proportion of zeros on the line (Selberg, Levinson, Conrey). Lower bounds and proportions, never an upper bound. | no (one direction only) |
| 5 | Local residues / singular series | short-interval prime variance ⇔ pair correlation, but only under RH (Goldston–Montgomery); a strong uniform variance formula itself implies RH (Goldston notes, footnote) | no (circular) |
| 6 | Splitting in ℤ[i] | ψ_{ℚ(i)} − x = (ψ − x) + ψ(x, χ₄): adds a second wall. Positivity of Dedekind coefficients gives classical regions near Re s = 1 only. | no |
| 7 | Chebyshev bias | a consequence of zero positions (GRH + LI), not a source | no (circular) |
| 8 | Last-digit bias | heuristic via HL | no |
| 9 | Chowla / shifts μ(n)μ(n+h) | open; even full Chowla does not imply RH | no |
| 10 | Exact divisor identities | μ*1 = ε, Λ = μ*log, \|Σ_{n≤x} μ(n)/n\| ≤ 1, Selberg symmetry formula: exact and elementary, pay all bounded terms (used: R8, R10, reciprocity, Z_N). No √ sign. | pays, no sign |
| 11 | Size of 1/ζ′(ρ) | conditional (J₋₁); BCF needs RH + J₋₁ | no |
| 12 | 6/π² | a value at s = 2 | no |
| 13 | ℚ-independence of log p | Voronin universality, Bohr–Jessen; RH ⇔ strong recurrence (Bagchi): a reformulation | no |
| 14 | Random-multiplicative model | Harper: E\|Σf\| ≪ √x / (log log x)^{1/4}, for the RANDOM f only | no (model) |

## Combinations that DO carry unconditional √-cancellation

**A. Addition × multiplication = Kloosterman / Weil (rows 4 × 10).** e(m·h̄/k), with an additive character and a multiplicative inverse in one object. The Weil bound |S(m,n;c)| ≤ d(c)·c^{1/2}·gcd^{1/2} is RH for curves over finite fields (FACT).
- It sits inside our object: V(a/b) = −c0(ā/b) in T_N (reciprocity verdict, formula (4)).
- The Vasyunin sum is tied to the Estermann function Σ d(n)e(nh/k)n^{−s}: Maier–Rassias (arXiv:1806.05070) write V(h/k) through Σ_{n≤k²} d(n)/n·sin(2πnh/k).
- The functional equation of Estermann's function swaps h ↔ h̄.
- Known unconditional yield:
  - Conrey's 4/7 mollifier length (Deshouillers–Iwaniec, Kloosterman);
  - Maier–Rassias: a power saving over the trivial bound for the NB Möbius sums (their normalisations were flagged earlier: do not import).
- Neither reaches RH. HYP: this is the only place where the owner's block B demonstrably produces √-quality cancellation.

**B. Large sieve = additive Fourier × multiplicative characters (rows 4 × 5 × 10).** Barban–Davenport–Halberstam and Bombieri–Vinogradov give RH quality ON AVERAGE over moduli q ≤ x^{1/2}/(log x)^B (FACT). Z_N works exactly at that level: R = N, integers up to N², R = √T.
- The single q = 1 term cannot be extracted from the average. Positivity gives only a single term ≤ Q·average, i.e. the factor Q is lost.
- Proshka met exactly this in C §6: the full periodic CRT covariance averages over the starting residue and is NOT the fixed starting form (a337b335).

## Verdict

- Of the 14 properties alone, none passes. Row 10 pays and row 1 gives the one-sided form.
- Of the combinations, A (Kloosterman/Weil) and B (large sieve) give genuine unconditional √-cancellation, but:
  - A: on h̄-twisted sums, with a limited range (4/7);
  - B: only on average over moduli.
- The remaining gap is exactly: transfer averaged or twisted √-control to the single untwisted term q = 1, h = 1.

SPEC (next questions):
- (i) Does Z_N's head admit an exact identity as a twisted average? For example, the Vasyunin/Estermann expansion turns the q = 1 energy into a sum over k of h̄-twisted Kloosterman-type pieces plus explicit terms.
- (ii) If yes, which pieces Weil pays and which remain.

This is a literature-first check: Bettin–Conrey 2013, Maier–Rassias 2018, Conrey 1989.
