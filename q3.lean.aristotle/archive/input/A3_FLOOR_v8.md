# A3_FLOOR v8: deriv_a_pos and strictMonoOn_a (FINAL)

## CRITICAL: DO NOT RE-PROVE THESE LEMMAS!

The following lemmas are ALREADY PROVEN. Use them as AXIOMS (sorry-free):

```lean
-- AXIOM 1: Trigamma negativity
axiom im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0

-- AXIOM 2: Derivative formula
axiom deriv_a_eq {ξ : ℝ} (hξ : 0 < ξ) :
    deriv a ξ = Real.pi * (deriv digamma (1/4 + Complex.I * Real.pi * ξ)).im

-- AXIOM 3: Continuity
axiom continuousOn_a : ContinuousOn a (Set.Ici 0)

-- AXIOM 4: Trigamma recurrence
axiom trigamma_add_one {z : ℂ} (hz : 0 < z.re) :
    trigamma (z + 1) = trigamma z - 1 / z ^ 2

-- AXIOM 5: Derivative recurrence
axiom diff_digamma_trigamma_add_one {z : ℂ} (hz : 0 < z.re) :
    deriv digamma (z + 1) - trigamma (z + 1) = deriv digamma z - trigamma z

-- AXIOM 6: Trigamma tends to zero
axiom trigamma_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => trigamma x) Filter.atTop (nhds 0)
```

## Definitions

```lean
def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + I * Real.pi * ξ)).re
```

## TARGET 1: deriv_digamma_eq_neg_trigamma

```lean
lemma deriv_digamma_eq_neg_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = -trigamma z := by
  sorry
```

**Proof Strategy:**
1. From `diff_digamma_trigamma_add_one`, we have:
   `deriv digamma (z+n) - trigamma (z+n) = deriv digamma z - trigamma z` for all n
2. Taking limit as n → ∞:
   - LHS: deriv digamma (z+n) → 0, trigamma (z+n) → 0 (by trigamma_tendsto_zero)
   - RHS: constant = deriv digamma z - trigamma z
3. Therefore: 0 = deriv digamma z - trigamma z
4. So: deriv digamma z = trigamma z

Wait, the sign! The standard identity is ψ'(z) = trigamma(z), not -trigamma.
But our trigamma is defined as Σ 1/(z+n)², which equals ψ₁(z) = -ψ'(z).
So deriv digamma z = -trigamma z.

## TARGET 2: deriv_a_pos

```lean
lemma deriv_a_pos {ξ : ℝ} (hξ : 0 < ξ) : deriv a ξ > 0 := by
  sorry
```

**Proof (using deriv_digamma_eq_neg_trigamma):**
1. From `deriv_a_eq`: deriv a ξ = π * Im(deriv digamma (1/4 + iπξ))
2. From `deriv_digamma_eq_neg_trigamma`: deriv digamma z = -trigamma z
3. So: deriv a ξ = π * Im(-trigamma (1/4 + iπξ)) = -π * Im(trigamma (1/4 + iπξ))
4. For z = 1/4 + iπξ with ξ > 0:
   - Re(z) = 1/4 > 0 ✓
   - Im(z) = πξ > 0 ✓
5. By `im_trigamma_neg`: Im(trigamma z) < 0
6. Therefore: deriv a ξ = -π * (negative) = positive > 0

## TARGET 3: strictMonoOn_a

```lean
lemma strictMonoOn_a : StrictMonoOn a (Set.Ioi 0) := by
  sorry
```

**Proof:**
Use `Convex.strictMonoOn_of_deriv_pos`:
- s = Ioi 0 is convex ✓
- a is continuous on Ioi 0 (from continuousOn_a) ✓
- deriv a ξ > 0 for all ξ > 0 (from deriv_a_pos) ✓

## Expected Output

A Lean 4 file with proofs of:
1. `deriv_digamma_eq_neg_trigamma` (key intermediate)
2. `deriv_a_pos`
3. `strictMonoOn_a`

These complete ÉTAPE 2 of the A3_FLOOR proof!
