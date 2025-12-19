# Large Sieve v2: Minor Arcs Estimate from Orthogonality

## PROVEN AXIOMS (from v1, do NOT re-prove)

### Axiom 1: Large Sieve Integral (Orthogonality)
This is the KEY result from v1:
```lean
large_sieve_integral : ∀ (N : ℕ) (a : ℕ → ℂ),
  ∫ α in Icc 0 1, ‖Σ n in range N, a n * e(n * α)‖² = Σ n in range N, ‖a n‖²
```

This is Parseval's identity for exponential sums!

### Axiom 2: Prime Number Theorem Bound
```lean
h_prime_number_theorem : ∀ n : ℕ,
  Σ p in filter Prime (range (n + 1)), log p ≤ n * log 4
```

### Axiom 3: Coefficient L² Bound
```lean
F_coeff_L2 : ∀ X ≥ 2, Σ n in range ⌊X⌋, ‖F_coeff X n‖² ≤ 2 * X * log X
where F_coeff X n = Λ(n) * χ₄(n)
```

### Axiom 4: χ₄ and e Definitions
```lean
χ₄ (n : ℤ) := if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1
e (x : ℝ) := exp(2πi * x)
F (X α : ℝ) := Σ n in range ⌊X⌋, Λ(n) * χ₄(n) * e(n * α)
```

## NEW TARGET: Minor Arcs Bound from Large Sieve

### Theorem 1: Parseval for F
```lean
theorem parseval_for_F (X : ℝ) (hX : X ≥ 2) :
  ∫ α in Icc 0 1, ‖F X α‖² = Σ n in range ⌊X⌋, ‖Λ(n) * χ₄(n)‖² := by
  -- Direct application of large_sieve_integral with a n = Λ(n) * χ₄(n)
  sorry -- PROVE THIS!
```

### Theorem 2: Total Integral Bound
```lean
theorem total_integral_bound (X : ℝ) (hX : X ≥ 2) :
  ∫ α in Icc 0 1, ‖F X α‖² ≤ 2 * X * log X := by
  -- Combine parseval_for_F with F_coeff_L2
  sorry -- PROVE THIS!
```

### Theorem 3: Major Arc Contribution
At α = 1/4, by Golden Bridge: χ₄(n)·e(n/4) = i for odd n
So F(1/4) = i · Σ_{n odd} Λ(n) = i · (ψ(X) - log 2) ≈ i·X

```lean
theorem major_arc_contribution (X : ℝ) (hX : X ≥ 100) :
  ‖F X (1/4)‖² ≥ (X - X/(log X))² := by
  -- Use Golden Bridge: χ₄(n)·e(n/4) = i
  -- Sum over odd n: F(1/4) = i · Σ Λ(n) for n odd
  -- By PNT: Σ Λ(n) = X + o(X)
  sorry -- PROVE THIS!
```

### Theorem 4: Minor Arcs Bound (THE MAIN TARGET)
```lean
theorem minor_arcs_estimate (X : ℝ) (hX : X ≥ 100) (δ : ℝ) (hδ : 0 < δ) :
  let minor := {α : ℝ | |α - 1/4| > δ ∧ |α - 3/4| > δ} ∩ Icc 0 1
  ∫ α in minor, ‖F X α‖² ≤
    2 * X * log X - 2 * (X - X/(log X))² * δ := by
  -- By total_integral_bound: ∫_{[0,1]} |F|² ≤ 2X log X
  -- By major_arc_contribution: |F(1/4)|² ≥ (X - X/log X)²
  -- The major arcs around 1/4 and 3/4 capture most of the integral
  -- Minor arcs = Total - Major
  sorry -- PROVE THIS!
```

### Corollary: Minor Arcs are o(X²)
```lean
theorem minor_arcs_vanish (δ : ℝ) (hδ : 0 < δ) :
  (fun X => ∫ α in {α | |α - 1/4| > δ ∧ |α - 3/4| > δ} ∩ Icc 0 1, ‖F X α‖²)
  =o[atTop] (fun X => X²) := by
  -- From minor_arcs_estimate:
  -- Minor ≤ 2X log X - 2(X - X/log X)² δ
  --       ≤ 2X log X - 2X²(1 - 1/log X)² δ
  --       = 2X log X - 2X² δ + O(X²/log X)
  -- For large X: this is ≤ 2X log X which is o(X²)
  sorry -- PROVE THIS!
```

## THE CHAIN

```
large_sieve_integral (AXIOM)
    ↓
parseval_for_F
    ↓
total_integral_bound: ∫|F|² ≤ 2X log X
    ↓                      ↓
major_arc_contribution: |F(1/4)|² ≥ X²
    ↓
minor_arcs_estimate: ∫_{minor} |F|² ≤ 2X log X - 2X²δ
    ↓
minor_arcs_vanish: ∫_{minor} |F|² = o(X²)
    ↓
T_chi4 ≈ Major arcs contribution ≈ -S₂
    ↓
S₂ ~ X → TPC!!!
```

## EXPECTED OUTPUT

Complete Lean4 proofs using the axioms above.
