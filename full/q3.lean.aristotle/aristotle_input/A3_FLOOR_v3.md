# A3_FLOOR v3: Monotonicity of a(ξ) and P_A Lower Bound

## Previously Proven (use as context)

The following lemmas are already proven in `A3_FLOOR_COMBINED.lean`:

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
```

## Current Goal

Prove the **monotonicity of a(ξ)** and use it to establish the **P_A lower bound**.

## Definitions (reminder)

```lean
def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2

def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + I * Real.pi * ξ)).re

def B_min : ℝ := 3
def t_sym : ℝ := 3 / 50
def c_star : ℝ := 11 / 10

def w (B t ξ : ℝ) : ℝ := max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)
def g (B t ξ : ℝ) : ℝ := a ξ * w B t ξ
def P_A (B t θ : ℝ) : ℝ := 2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)
```

## Theorem Statement

```lean
-- Step 1: deriv digamma = -trigamma
lemma deriv_digamma_eq_neg_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = -trigamma z := by
  sorry

-- Step 2: a'(ξ) > 0 for ξ > 0 (using im_trigamma_neg)
lemma deriv_a_pos {ξ : ℝ} (hξ : 0 < ξ) : deriv a ξ > 0 := by
  -- From deriv_a_eq: deriv a ξ = π * Im(deriv digamma (1/4 + iπξ))
  -- From deriv_digamma_eq_neg_trigamma: deriv digamma z = -trigamma z
  -- So: deriv a ξ = π * Im(-trigamma (1/4 + iπξ)) = -π * Im(trigamma (1/4 + iπξ))
  -- From im_trigamma_neg: Im(trigamma z) < 0 when Re(z) > 0 and Im(z) > 0
  -- For z = 1/4 + iπξ with ξ > 0: Re(z) = 1/4 > 0, Im(z) = πξ > 0
  -- So Im(trigamma z) < 0, hence -Im(trigamma z) > 0, hence deriv a ξ > 0
  sorry

-- Step 3: a is strictly monotone increasing on (0, ∞)
lemma strictMonoOn_a : StrictMonoOn a (Ioi 0) := by
  -- Follows from deriv_a_pos and continuousOn_a
  sorry

-- Step 4: a(0) value (sample bound)
lemma a_zero : a 0 = Real.log Real.pi - (digamma (1/4)).re := by
  simp [a]

-- Step 5: Key sample bounds for P_A estimation
-- a(1/2) ≥ 29/50 (numerical: ≈ 0.621)
-- a(3/2) ≥ -3/5 (numerical: ≈ -0.168)
-- These follow from monotonicity + continuity + sample evaluation

-- Step 6: P_A lower bound (MAIN GOAL)
theorem P_A_ge_c_star {B t θ : ℝ} (hB : B ≥ B_min) (ht : t = t_sym)
    (hθ : θ ∈ Icc (-1/2 : ℝ) (1/2)) :
    P_A B t θ ≥ c_star := by
  sorry
```

## Proof Strategy

### For `deriv_digamma_eq_neg_trigamma`:
The digamma function satisfies ψ'(z) = ∑_{n=0}^∞ 1/(z+n)² = trigamma(z).
But we define digamma = Γ'/Γ, so need to verify:
- deriv(Γ'/Γ) = (Γ'' Γ - (Γ')²) / Γ²
- This equals -trigamma by standard Γ identities

### For `deriv_a_pos`:
1. Use `deriv_a_eq`: deriv a ξ = π * Im(deriv digamma (1/4 + iπξ))
2. Use `deriv_digamma_eq_neg_trigamma`: deriv digamma z = -trigamma z
3. Substitute: deriv a ξ = π * Im(-trigamma (1/4 + iπξ)) = -π * Im(trigamma (1/4 + iπξ))
4. Apply `im_trigamma_neg` with z = 1/4 + iπξ:
   - Re(z) = 1/4 > 0 ✓
   - Im(z) = πξ > 0 (since ξ > 0) ✓
   - Therefore Im(trigamma z) < 0
5. Conclude: deriv a ξ = -π * (negative) = positive > 0

### For `strictMonoOn_a`:
Use Convex.strictMonoOn_of_deriv_pos with:
- Domain: Ioi 0 (convex)
- continuousOn_a restricted to Ioi 0
- deriv_a_pos

### For `P_A_ge_c_star`:
1. P_A(θ) = 2π ∑_{m∈ℤ} g(θ+m) where g = a · w
2. For B ≥ 3 and t = 3/50, w is supported on [-B, B]
3. Only finitely many m contribute (those with |θ+m| ≤ B)
4. Use strictMonoOn_a to bound a values
5. Sum contributions and show total ≥ 11/10

## Hints for Aristotle

1. **For deriv_digamma**: Use `Complex.deriv_Gamma_div_Gamma` if available, or derive from series definition.

2. **For deriv_a_pos**: The key insight is that the chain of equalities transforms Im(trigamma) negativity into a positivity result.

3. **For strictMonoOn_a**: Use `Convex.strictMonoOn_of_deriv_pos` from Mathlib.

4. **For P_A_ge_c_star**: This may require numerical bounds. If too hard, prove the structural lemmas first.

## Priority

1. **HIGH**: `deriv_a_pos` - this is the key monotonicity result
2. **HIGH**: `strictMonoOn_a` - follows easily from above
3. **MEDIUM**: `deriv_digamma_eq_neg_trigamma` - needed for deriv_a_pos
4. **LOW**: `P_A_ge_c_star` - may need additional numerical work

## Expected Output

A Lean 4 file with proofs of as many lemmas as possible, especially:
- `deriv_a_pos`
- `strictMonoOn_a`

If `P_A_ge_c_star` is too complex, focus on the monotonicity results which are the foundation.
