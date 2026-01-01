# A3_FLOOR v4: Monotonicity of a(ξ)

## Previously Proven (use as axioms/context)

The following lemmas are ALREADY PROVEN in `A3_FLOOR_v3_trigamma_foundations.lean`:

```lean
-- Trigamma negativity (KEY!)
lemma im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0

-- Derivative formula
lemma deriv_a_eq {ξ : ℝ} (hξ : 0 < ξ) :
    deriv a ξ = Real.pi * (deriv (fun z : ℂ => digamma z) (1/4 + I * Real.pi * ξ)).im

-- Continuity
lemma continuousOn_a : ContinuousOn a (Ici 0)

-- Trigamma summability
lemma trigamma_summable {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => 1 / (z + n)^2)

-- Digamma recurrence
lemma digamma_add_one {z : ℂ} (hz : 0 < z.re) :
    digamma (z + 1) = digamma z + 1 / z
```

## Definitions (reminder)

```lean
def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2

def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + I * Real.pi * ξ)).re
```

## Current Goal: Prove Monotonicity

### Theorem 1: deriv_a_pos

```lean
lemma deriv_a_pos {ξ : ℝ} (hξ : 0 < ξ) : deriv a ξ > 0 := by
  sorry
```

**Proof Strategy:**
1. From `deriv_a_eq`: `deriv a ξ = π * Im(deriv digamma (1/4 + iπξ))`
2. The derivative of digamma is `-trigamma`: `deriv digamma z = -trigamma z`
3. So: `deriv a ξ = π * Im(-trigamma (1/4 + iπξ)) = -π * Im(trigamma (1/4 + iπξ))`
4. For z = 1/4 + iπξ with ξ > 0:
   - Re(z) = 1/4 > 0 ✓
   - Im(z) = πξ > 0 (since ξ > 0) ✓
5. By `im_trigamma_neg`: Im(trigamma z) < 0
6. Therefore: `deriv a ξ = -π * (negative) = positive > 0`

### Theorem 2: strictMonoOn_a

```lean
lemma strictMonoOn_a : StrictMonoOn a (Ioi 0) := by
  sorry
```

**Proof Strategy:**
1. Use `Convex.strictMonoOn_of_deriv_pos` from Mathlib
2. The domain `Ioi 0` is convex ✓
3. We have `continuousOn_a` restricted to `Ioi 0` ✓
4. We have `deriv_a_pos` for all ξ > 0 ✓
5. Conclude: a is strictly monotone increasing on (0, ∞)

## Key Lemma Needed

You may need to prove this intermediate result:

```lean
lemma deriv_digamma_eq_neg_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = -trigamma z := by
  sorry
```

This follows from the standard identity: ψ'(z) = Σ 1/(z+n)² = trigamma(z), and differentiating ψ.

## Hints

1. **For deriv_digamma_eq_neg_trigamma:**
   - The digamma function ψ = Γ'/Γ
   - Its derivative is ψ' = d/dz(Γ'/Γ) = (Γ''Γ - (Γ')²)/Γ²
   - This equals Σ 1/(z+n)² = trigamma(z)
   - Sign convention: check if Mathlib uses + or - trigamma

2. **For deriv_a_pos:**
   - Key chain: deriv_a_eq → deriv_digamma → im_trigamma_neg → positivity

3. **For strictMonoOn_a:**
   - Use `Convex.strictMonoOn_of_deriv_pos` or similar from Mathlib
   - May need `DifferentiableOn` which follows from the derivative formula

## Expected Output

A Lean 4 file with proofs of:
1. `deriv_digamma_eq_neg_trigamma` (if needed)
2. `deriv_a_pos`
3. `strictMonoOn_a`

These are the key monotonicity results needed for the A3 floor theorem.
