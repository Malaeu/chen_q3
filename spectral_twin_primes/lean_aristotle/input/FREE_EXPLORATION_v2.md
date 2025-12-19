# Circle Method v2: Complete TPC from Conditional Estimates

## PROVEN AXIOMS (from v1, do NOT re-prove)

### Axiom 1: Interval Integral Equality
```lean
intervalIntegral_eq_setIntegral_Icc :
  ∀ f a b, a ≤ b → ∫ x in a..b, f x = ∫ x in Ioc a b, f x
```

### Axiom 2: Ioc equals Icc for Integration
```lean
setIntegral_Ioc_eq_setIntegral_Icc :
  ∫ x in Ioc a b, f x = ∫ x in Icc a b, f x
```

### Axiom 3: Integrand Continuity
```lean
continuous_integrand : Continuous (integrand X)
integrable_integrand : IntegrableOn (integrand X) (Icc 0 1) volume
```

### Axiom 4: T equals Integral over Icc
```lean
T_eq_integral_Icc : T_chi4 X = ∫ α in Icc 0 1, integrand X α
```

### Axiom 5: Arithmetic Bound
```lean
arithmetic_bound_tight : ∀ X > 100, 1 + X/(log X)² ≤ X/log X
```

### Axiom 6: Minor Arcs Bound (Conditional)
```lean
minor_arcs_bound :
  (props : CircleMethodProps) → (ests : CircleMethodEstimates_Tight) →
  ∀ X > 100, ‖Minor X‖ ≤ X / log X
```

### Axiom 7: TwinPrimeAxioms Structure
```lean
structure TwinPrimeAxioms where
  S2_linear : ∃ c > 0, ∀ X > 100, S2 X ≥ c * X
  infinite_twins_of_unbounded_T : (∀ B, ∃ X, ‖T_chi4 X‖ > B) → TPC
```

## NEW TARGET: Prove T_split Theorem

The v1 output had `T_split` with `exact?` holes. We need to complete it.

### Theorem 1: T Splits into Minor + Major
```lean
theorem T_split_complete (props : CircleMethodProps) (X : ℝ) :
  T_chi4 X = Minor X + Major X := by
  -- Given: arcs_union says minor ∪ major = Icc 0 1
  -- Given: arcs_disjoint says they are disjoint
  -- Given: both are measurable
  -- Use setIntegral_union to split the integral
  sorry -- PROVE THIS!
```

**Proof approach:**
1. Rewrite T_chi4 using T_eq_integral_Icc
2. Apply arcs_union: Icc 0 1 = minor_arcs ∪ major_arcs
3. Apply setIntegral_union (since disjoint and measurable)
4. Minor and Major are exactly the integrals over each arc

### Theorem 2: S2 Lower Bound from Circle Method
Given the resonance at α = 1/4 and α = 3/4:
```lean
theorem S2_lower_bound_from_resonance
  (props : CircleMethodProps)
  (ests : CircleMethodEstimates_Tight)
  (h_major : ∀ X > 100, Major X = -S2 X + O(X / (log X)²)) :
  ∃ c > 0, ∀ X > 100, S2 X ≥ c * X / (log X)² := by
  sorry -- PROVE THIS!
```

### Theorem 3: TPC from Complete Circle Method
```lean
theorem TPC_from_circle_method
  (props : CircleMethodProps)
  (ests : CircleMethodEstimates_Tight)
  (h_S2_linear : ∃ c > 0, ∀ X > 100, S2 X ≥ c * X) :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ p.Prime ∧ (p + 2).Prime := by
  -- This was almost proven in v1!
  -- Use infinite_twins_of_unbounded_T
  -- Show |T| → ∞ using |T| ≥ |Major| - |Minor| - errors
  -- |Major| ≈ S2 ≥ cX (by h_S2_linear)
  -- |Minor| ≤ X/log X (by minor_arcs_bound)
  -- So |T| ≥ cX - X/log X → ∞
  sorry -- PROVE THIS!
```

## EXPECTED OUTPUT

Complete Lean4 proofs of:
1. `T_split_complete`
2. `S2_lower_bound_from_resonance`
3. `TPC_from_circle_method`

Using the axioms above.
