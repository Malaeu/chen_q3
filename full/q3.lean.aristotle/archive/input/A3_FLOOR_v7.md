# A3_FLOOR v7: deriv_a_pos and strictMonoOn_a (FINAL for Monotonicity)

## Goal
Prove the TWO remaining lemmas for monotonicity of a(ξ):
1. `deriv_a_pos`: a'(ξ) > 0 for ξ > 0
2. `strictMonoOn_a`: a is strictly increasing on (0,∞)

## Already Proven (use as axioms)

From v3-v6, we have these PROVEN lemmas:

```lean
-- v3: Trigamma foundations
lemma im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0

lemma deriv_a_eq {ξ : ℝ} (hξ : 0 < ξ) :
    deriv a ξ = Real.pi * (deriv (fun z : ℂ => digamma z) (1/4 + I * Real.pi * ξ)).im

lemma continuousOn_a : ContinuousOn a (Ici 0)

-- v6: Derivative foundations
lemma trigamma_add_one {z : ℂ} (hz : 0 < z.re) :
    trigamma (z + 1) = trigamma z - 1 / z ^ 2

lemma diff_digamma_trigamma_add_one {z : ℂ} (hz : 0 < z.re) :
    deriv digamma (z + 1) - trigamma (z + 1) = deriv digamma z - trigamma z

lemma trigamma_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => trigamma x) Filter.atTop (nhds 0)
```

## Definitions

```lean
def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + I * Real.pi * ξ)).re
```

## TARGET 1: deriv_a_pos

```lean
lemma deriv_a_pos {ξ : ℝ} (hξ : 0 < ξ) : deriv a ξ > 0 := by
  sorry
```

### Proof Strategy

The key insight: `deriv digamma z = -trigamma z` for Re(z) > 0.

1. From `deriv_a_eq`:
   ```
   deriv a ξ = π * Im(deriv digamma (1/4 + iπξ))
   ```

2. Use `deriv digamma z = -trigamma z`:
   ```
   deriv a ξ = π * Im(-trigamma (1/4 + iπξ))
             = -π * Im(trigamma (1/4 + iπξ))
   ```

3. For z = 1/4 + iπξ with ξ > 0:
   - Re(z) = 1/4 > 0 ✓
   - Im(z) = πξ > 0 ✓

4. By `im_trigamma_neg`: Im(trigamma z) < 0

5. Therefore:
   ```
   deriv a ξ = -π * (negative) = positive > 0
   ```

### Key Lemma Needed

```lean
lemma deriv_digamma_eq_neg_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = -trigamma z := by
  -- From v6 we have:
  -- diff_digamma_trigamma_add_one: deriv digamma (z+1) - trigamma (z+1) = deriv digamma z - trigamma z
  -- trigamma_tendsto_zero: lim trigamma x = 0 as x → ∞
  --
  -- Taking limit as n → ∞ of (deriv digamma (z+n) - trigamma (z+n)):
  -- LHS → 0 - 0 = 0 (both tend to 0)
  -- RHS = deriv digamma z - trigamma z (constant)
  -- Therefore: deriv digamma z = trigamma z
  --
  -- Wait, the sign! Check: trigamma = Σ 1/(z+n)² is the SECOND derivative of log Γ.
  -- And digamma = Γ'/Γ is the FIRST derivative of log Γ.
  -- So deriv digamma = d/dz (Γ'/Γ) = ... need to check sign carefully.
  sorry
```

## TARGET 2: strictMonoOn_a

```lean
lemma strictMonoOn_a : StrictMonoOn a (Ioi 0) := by
  sorry
```

### Proof Strategy

Use Mathlib's `Convex.strictMonoOn_of_deriv_pos`:

```lean
theorem Convex.strictMonoOn_of_deriv_pos {s : Set ℝ} {f : ℝ → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hf' : ∀ x ∈ interior s, 0 < deriv f x) : StrictMonoOn f s
```

Apply with:
- s = Ioi 0 (convex ✓)
- f = a
- hf = continuousOn_a restricted to Ioi 0 ✓
- hf' = deriv_a_pos ✓

Note: interior (Ioi 0) = Ioi 0 for the reals.

## Expected Output

A Lean 4 file with proofs of:
1. `deriv_digamma_eq_neg_trigamma` (if needed as intermediate)
2. `deriv_a_pos`
3. `strictMonoOn_a`

These complete ÉTAPE 2 of the A3_FLOOR proof!
