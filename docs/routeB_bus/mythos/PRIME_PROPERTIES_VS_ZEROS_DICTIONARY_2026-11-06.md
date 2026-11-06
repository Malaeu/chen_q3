# Prime properties vs zero properties: dictionary and ablation plan (2026-11-06)

Owner's thesis (2026-11-06): RH must come from the elementary properties of the integer primes — the ones that make them different from fakes — and from how those properties are mirrored on the zero side. This file collects both sides.

Status tags:
- THEOREM — proved;
- CONDITIONAL — proved under stated hypotheses;
- HEURISTIC — derived, not proved;
- OPEN — unknown.

"Used" says whether Route B already exploits the property: R8–R12 are Proshka verdicts on `proshka_inbox_2026-10-31`; the other ids are Codex runs on `rh_clean`.

## 1. Dictionary

| # | Property of the integer primes | Formula / statement | Which fake world lacks it | Mirror on the zero side | Status | Used |
|---|---|---|---|---|---|---|
| 1 | Unique factorisation | Euler product ζ = Π(1−p^{−s})^{−1} | none: every Beurling system has it | ζ ≠ 0 for Re s > 1 | THEOREM | yes, everywhere |
| 2 | Density 1/log n | ψ(x) ~ x | DH (no Euler product) | ζ ≠ 0 on Re s = 1 | THEOREM | yes (R4 B, R8) |
| 3 | √-error | ψ(x) − x = O(√x log²x) | DMV (Diamond–Montgomery–Vorhauer 2006) | all zeros on Re s = ½ | ⇔ RH | target |
| 4 | Additive lattice ℤ: n+1, Poisson summation | θ(1/x) = √x·θ(x); gcd(n, n+1) = 1 | generic Beurling systems | functional equation; symmetry ρ ↔ 1−ρ; zero density N(T) ≈ (T/2π)·log(T/2πe) via Γ | THEOREM | partly (Γ, pole: R4 B, R6 B) |
| 5 | Local residues: p > 3 is 6k±1; admissible patterns; singular series | Hardy–Littlewood constants, e.g. twin constant 2Π(1−1/(p−1)²) | Cramér random primes | pair / n-level correlations of zeros: Goldston–Montgomery (pair correlation ⇔ variance of primes in short intervals); Bogomolny–Keating (zero correlations from HL k-tuples with singular series) | CONDITIONAL / HEURISTIC | **no** |
| 6 | Splitting in ℤ[i]: p ≡ 1 mod 4 splits, 3 inert, 2 ramified | p = a² + b² ⇔ p ≡ 1 mod 4 | — | zeros of ζ_{ℚ(i)} = zeros of ζ ∪ zeros of L(s,χ₄) | THEOREM | **no** |
| 7 | Chebyshev bias (squares of primes are residues) | π(x;4,3) > π(x;4,1) at density 0.9959 | — | behaviour of L(s,χ) near ½; bias size from the zero distribution (Rubinstein–Sarnak) | CONDITIONAL (GRH+LI) | **no** |
| 8 | Consecutive-prime last-digit bias | Lemke Oliver–Soundararajan 2016 | Cramér random primes | through HL k-tuples → zero correlations | HEURISTIC | **no** |
| 9 | Möbius at shifts | Σ μ(n)μ(n+h) = o(x) (Chowla) | Beurling systems have no "n+h" | unknown | OPEN (log-averaged k = 2 and odd k: Tao, Tao–Teräväinen) | **no** |
| 10 | Exact divisor identities | μ*1 = ε; Λ = μ*log; Σ_{n≤x} μ(n)⌊x/n⌋ = 1 | Beurling: analogues exist | — | THEOREM | yes (R8, R10, reciprocity) |
| 11 | Size of 1/ζ′(ρ) (Lehmer pairs) | M(x) ≈ Σ x^ρ/(ρζ′(ρ)) | — | J₋₁ = Σ\|ζ′(ρ)\|^{−2} | CONDITIONAL | tested: ec1e2e96, no signal for t ≤ 1000 |
| 12 | Coprimality density 6/π² = 1/ζ(2) | gcd statistics | — | value at s = 2, not zeros | THEOREM | yes (Vasyunin Gram) |
| 13 | No multiplicative relations among primes | log p linearly independent over ℚ | special Beurling systems (q with log-relations) | conjectured LI of ordinates; Bohr–Jessen statistics for σ > ½ | THEOREM for log p; OPEN for ordinates | partly (Kronecker shelf) |
| 14 | Random-multiplicative behaviour | Harper 2020: E\|Σ_{n≤x} f(n)\| ≍ √x/(log log x)^{1/4} for random multiplicative f | — | multiplicative chaos (Saksman–Webb 2020) | THEOREM (random model) | **no** |

## 2. Known facts that constrain the search

- **RH among Beurling systems goes both ways.** DMV built a system with RH-quality integers and RH false. Broucke (2020, arXiv:2004.11501) built a Beurling system with RH true and maximally oscillating integers. Unique factorisation plus density decides nothing.
- **Unique factorisation + RH-quality integer counting ⇏ RH.** This is DMV.
- **Functional equation without an Euler product ⇏ RH.** This is DH.
- **Consequence.** The decisive information must sit in the coupling between rows 1–3 and rows 4–9: additive lattice, local residues, shifts. Integers have that coupling; fakes do not.

## 3. Ablation plan (Codex)

Goal: find which property, or which combination, carries the √-scale cancellation in our actual object.

Universal functional, defined for any generalised-integer system:

    W(X) = (1/log X) ∫_1^X (M_P(x)/x)² dx

This is the weak-Mertens functional. Route B condition (26)/(25) is a weighted subsequence version of it.

| System | What it keeps | What it breaks |
|---|---|---|
| S0: true primes | everything | — (baseline) |
| S1: Cramér–Beurling, random primes with density 1/log x, several seeds | factorisation, density | local residues, additive lattice |
| S2: hybrid, true primes ≤ y and random above, for several y | local residues for small p | local residues for large p |
| S3: perturbed primes p(1 + ε_p), real numbers | local statistics, approximately | integrality, n+1 |
| S4: true support, random signs on primes (Rademacher multiplicative) | support and factorisation pattern | μ(p) = −1 coherence; this is Harper's regime |
| S5: Liouville λ instead of μ | everything | square-free restriction; adds the Pólya bias √x/ζ(½) |

For each system measure:
- W(X) up to X = 10^7, or 10^8 where feasible;
- the distribution of M_P(x)/√x;
- the sign-change rate;
- the log-scale variance.

**Honest prior (DIAG limits).** Random fakes (S1, S4) may look RH-like numerically: random systems tend to have √-cancellation. If S0, S1 and S4 all give bounded W, the property that distinguishes integers is invisible to this functional in the finite range. It must then be used structurally inside a proof, not found numerically. That outcome is still informative: it tells Proshka which properties are NOT the discriminator.
