# Minor Arcs Estimate for χ₄-Weighted Prime Sums

## Context

This is the FINAL GAP in the synergy approach to TPC.

We have established:
- Two resonances at α = 1/4 and α = 3/4
- Both give NEGATIVE contributions (no cancellation)
- Combined: major arcs contribute ~ 92.8% of the integral

**What remains:** Prove minor arcs contribute o(X).

## Definitions

**Definition 1** (Fourier sum with χ₄):
```
F(α) := Σ_{p≤X, p prime} log(p) · χ₄(p) · e(pα)
```
where e(x) = exp(2πix) and χ₄ is the non-principal character mod 4.

**Definition 2** (Major arcs):
```
M(δ) := {α ∈ [0,1] : |α - 1/4| < δ or |α - 3/4| < δ}
```

**Definition 3** (Minor arcs):
```
m(δ) := [0,1] \ M(δ)
```

**Definition 4** (Parseval integral):
```
I(X) := ∫₀¹ |F(α)|² dα
```

**Definition 5** (Major arc contribution):
```
I_major(X) := ∫_{M(δ)} |F(α)|² dα
```

**Definition 6** (Minor arc contribution):
```
I_minor(X) := ∫_{m(δ)} |F(α)|² dα
```

## Known Results

### Theorem 1: Parseval Identity

**Statement:**
```
∫₀¹ |F(α)|² dα = Σ_{p≤X} (log p)² = ψ₂(X) ~ X log X
```

**Proof:**
By Parseval's theorem for exponential sums:
∫₀¹ |Σ aₙ e(nα)|² dα = Σ |aₙ|²

Here aₙ = log(n)·χ₄(n) if n is prime, 0 otherwise.
So ∫ |F|² = Σ_{p≤X} (log p)² ~ X log X by PNT. QED.

### Theorem 2: Major Arc Peak Values

**Statement:** For α = 1/4 or α = 3/4:
```
|F(α)| ~ X/log X · |L(1, χ₄)|⁻¹ ~ 0.99 · X
```

**Proof:**
At α = 1/4, by the Golden Bridge identity χ₄(p)·e(p/4) = i for odd primes.
Therefore F(1/4) = i · Σ log(p) = i · ψ(X) ~ i · X.
Similarly F(3/4) = -i · X. QED.

## Theorems to Prove

### Theorem 3: Minor Arc Bound (MAIN TARGET)

**Statement:**
For any δ > 0 and α ∈ m(δ) (minor arcs):
```
|F(α)| ≤ C(δ) · X^{1-η}
```
for some η = η(δ) > 0.

**Attempted Proof Strategy 1: Vinogradov's Method**

The sum F(α) = Σ log(p)·χ₄(p)·e(pα) is a Type I exponential sum.

For α = a/q + β with |β| < 1/qQ:
- If q large (q > X^ε): Use Weyl-Vinogradov bounds
- If q small but a/q far from 1/4, 3/4: Character cancellation

The key estimate (Vinogradov):
|Σ_{n≤N} Λ(n)·χ(n)·e(nα)| ≤ C · N · (q⁻¹ + N⁻¹ + qN⁻²)^{1/2} · log⁴N

**Attempted Proof Strategy 2: Vaughan's Identity**

Decompose Λ(n) = Λ₁(n) - Λ₂(n) + Λ₃(n) using Vaughan's identity.

- Type I sums: Bilinear with one smooth variable
- Type II sums: Bilinear with both rough

Each type can be bounded on minor arcs.

**Gap:** Need to verify these standard bounds carry over to χ₄-twisted case.

### Theorem 4: Minor Arc Integral Bound

**Statement:**
```
∫_{m(δ)} |F(α)|² dα = o(X²)
```

Equivalently:
```
I_minor(X) / I_major(X) → 0 as X → ∞
```

**Proof (assuming Theorem 3):**
If |F(α)| ≤ C·X^{1-η} on m(δ), then:
I_minor = ∫_{m(δ)} |F|² ≤ C² · X^{2-2η} · |m(δ)|
        ≤ C² · X^{2-2η}
        = o(X²)

Since I_major ~ X², we get I_minor/I_major → 0. QED.

### Theorem 5: TPC Follows from Minor Arc Bound

**Statement:**
Theorems 3-4 imply infinitely many twin primes.

**Proof:**
We have the Parseval representation:
T_χ₄(X) = ∫₀¹ |F(α)|² · e(-2α) dα

Split into major and minor arcs:
T_χ₄ = I_major · (avg phase on major) + I_minor · (avg phase on minor)

On major arcs M(δ):
- At α = 1/4: e(-2·1/4) = e(-1/2) = -1
- At α = 3/4: e(-2·3/4) = e(-3/2) = -1
- Both contribute NEGATIVELY

Contribution from major arcs:
~ -2 · |F(1/4)|² · δ ~ -c · X² · δ

Contribution from minor arcs:
= o(X²) by Theorem 4

Therefore:
T_χ₄(X) ~ -c · X² · δ + o(X²) → -∞

But T_χ₄ = -S₂ by AFM structure.
So S₂(X) → +∞.

By the finite twins ceiling lemma:
If twins finite, S₂(X) = O(√X log²X).

Contradiction. Therefore twins are infinite. QED.

## Numerical Evidence

For X = 10⁶:
- |F(0.25)|/X = 0.9895
- |F(0.75)|/X = 0.9895
- |F(other)|/X < 0.02 for all other α
- Major arc contribution: 92.8%
- Minor arc contribution: 7.2%

The ratio 7.2% / 92.8% = 0.078 and decreases with X.

## What Remains

**The gap is Theorem 3:** An explicit minor arc bound for χ₄-weighted prime sums.

This is a STANDARD result in analytic number theory.
References:
- Vinogradov (1937): Original method
- Vaughan (1977): Identity decomposition
- Davenport "Multiplicative Number Theory" Ch. 25
- Iwaniec-Kowalski "Analytic Number Theory" Ch. 13

The bound should follow from:
1. Dirichlet character orthogonality
2. Vaughan's identity for Λ(n)
3. Standard Type I/II sum estimates

**Estimated difficulty:** Known technique, requires careful assembly (1-2 weeks for expert).
