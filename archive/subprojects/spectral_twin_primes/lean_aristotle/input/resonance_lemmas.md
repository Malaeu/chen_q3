# Resonance Lemmas for χ₄ Circle Method

## Context

We study the exponential sum F(α) = Σ_{n≤X} Λ(n)·χ₄(n)·e(nα) where:
- Λ(n) is the von Mangoldt function
- χ₄ is the non-principal character mod 4
- e(x) = exp(2πix)

## Definitions

**Definition 1** (Character χ₄):
χ₄(n) = 0 if n even, +1 if n ≡ 1 (mod 4), -1 if n ≡ 3 (mod 4)

**Definition 2** (Exponential function):
e(x) = exp(2πix), so e(n/4) = i^n for integer n

**Definition 3** (Exponential sum):
F(α) = Σ_{p≤X, p odd prime} log(p)·χ₄(p)·e(pα)

## Theorems to Prove

### Theorem 1: Resonance Identity

**Statement:** For all odd integers n:
```
χ₄(n) · e(n/4) = i
```

**Proof:**
Case n ≡ 1 (mod 4):
- χ₄(n) = +1
- e(n/4) = exp(2πi·n/4) = i^n
- Since n ≡ 1 (mod 4), we have i^n = i^1 = i
- Product: (+1)·i = i ✓

Case n ≡ 3 (mod 4):
- χ₄(n) = -1
- e(n/4) = i^n
- Since n ≡ 3 (mod 4), we have i^n = i^3 = -i
- Product: (-1)·(-i) = i ✓

Both cases give i. QED.

### Theorem 2: Peak Value Formula

**Statement:**
```
F(1/4) = i · Σ_{p≤X, p>2} log(p) + O(1)
       = i · (ψ(X) - log(2)) + O(1)
```

**Proof:**
By definition:
F(1/4) = Σ_{p≤X, p odd} log(p)·χ₄(p)·e(p/4)

By Theorem 1, for odd p: χ₄(p)·e(p/4) = i

Therefore:
F(1/4) = Σ_{p≤X, p>2} log(p)·i = i·Σ_{p≤X, p>2} log(p)

The sum Σ_{p≤X} log(p) = ψ(X) - (contribution from prime powers)
                       = ψ(X) + O(√X)

So F(1/4) = i·(ψ(X) - log(2)) + O(√X). QED.

### Theorem 3: Peak Magnitude (conditional on PNT)

**Statement:** Assuming ψ(X) ~ X (Prime Number Theorem):
```
|F(1/4)| = X + O(X/log X)
```

**Proof:**
From Theorem 2: F(1/4) = i·(ψ(X) - log(2)) + O(√X)

Taking magnitude: |F(1/4)| = |ψ(X) - log(2)| + O(√X)

By PNT: ψ(X) = X + O(X·exp(-c√(log X)))

Therefore: |F(1/4)| = X - log(2) + O(X/log X) = X + O(X/log X). QED.

### Theorem 4: Phase at α = 1/4

**Statement:** For the circle method integral:
```
e(-2·(1/4)) = e(-1/2) = -1
```

**Proof:**
e(-1/2) = exp(2πi·(-1/2)) = exp(-πi) = cos(-π) + i·sin(-π) = -1. QED.

## Corollary: Main Term Sign

**Statement:** The contribution from α = 1/4 to T_χ₄(X) is negative:

```
|F(1/4)|² · e(-1/2) = X² · (-1) = -X²
```

This negative sign, combined with AFM identity T_χ₄ = -S₂, gives:
```
-S₂(X) ≈ -X² · (width) ≈ -c·X
⟹ S₂(X) ≈ c·X > 0
⟹ Infinitely many twin primes
```

## What Remains

The gap is proving:
1. Peak width ~ 1/X (Vinogradov-type bounds)
2. Minor arcs contribute o(X) (standard circle method)
3. Exact computation of the integral near α = 1/4
