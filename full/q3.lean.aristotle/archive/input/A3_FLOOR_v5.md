# A3_FLOOR v5: Monotonicity of a(x) - FINAL PUSH

## CONTEXT: Already Proven Lemmas (USE AS GIVEN)

From v3 and v4 Aristotle runs, these are PROVEN and available:

```lean
-- Core definitions
noncomputable def digamma (z : C) : C := (deriv Complex.Gamma z) / (Complex.Gamma z)
noncomputable def trigamma (z : C) : C := sum' n : N, 1 / (z + n)^2
noncomputable def a (x : R) : R := Real.log Real.pi - (digamma (1/4 + I * Real.pi * x)).re

-- PROVEN: Trigamma imaginary part is negative
lemma im_trigamma_neg {z : C} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0

-- PROVEN: Derivative formula for a
lemma deriv_a_eq {x : R} (hx : 0 < x) :
    deriv a x = Real.pi * (deriv (fun z : C => digamma z) (1/4 + I * Real.pi * x)).im

-- PROVEN: Continuity
lemma continuousOn_a : ContinuousOn a (Set.Ici 0)

-- PROVEN: Trigamma summability
lemma trigamma_summable {z : C} (hz : 0 < z.re) :
    Summable (fun n : N => 1 / (z + n)^2)

-- PROVEN: Digamma recurrence
lemma digamma_add_one {z : C} (hz : 0 < z.re) :
    digamma (z + 1) = digamma z + 1 / z

-- PROVEN: Derivative of digamma recurrence
lemma deriv_digamma_add_one {z : C} (hz : 0 < z.re) :
    deriv digamma (z + 1) = deriv digamma z - 1 / z ^ 2
```

## GOAL: Prove These 3 Lemmas

### Lemma 1: deriv_digamma_eq_neg_trigamma

```lean
lemma deriv_digamma_eq_neg_trigamma {z : C} (hz : 0 < z.re) :
    deriv digamma z = -trigamma z := by
  sorry
```

**Proof outline:**
- By definition, digamma z = (deriv Gamma z) / (Gamma z)
- Taking derivative: d/dz[digamma z] = d/dz[(Gamma'/Gamma)]
- Standard identity: psi'(z) = -sum_{n=0}^infty 1/(z+n)^2 = -trigamma(z)
- This follows from differentiating the Weierstrass product for Gamma

### Lemma 2: deriv_a_pos (KEY!)

```lean
lemma deriv_a_pos {x : R} (hx : 0 < x) : deriv a x > 0 := by
  sorry
```

**Proof chain:**
1. `deriv_a_eq` gives: `deriv a x = pi * Im(deriv digamma (1/4 + i*pi*x))`
2. `deriv_digamma_eq_neg_trigamma` gives: `deriv digamma z = -trigamma z`
3. So: `deriv a x = pi * Im(-trigamma (1/4 + i*pi*x)) = -pi * Im(trigamma (1/4 + i*pi*x))`
4. For z = 1/4 + i*pi*x with x > 0:
   - Re(z) = 1/4 > 0 (check)
   - Im(z) = pi*x > 0 since x > 0 (check)
5. By `im_trigamma_neg`: Im(trigamma z) < 0
6. Therefore: `deriv a x = -pi * (negative) = positive > 0`

### Lemma 3: strictMonoOn_a

```lean
lemma strictMonoOn_a : StrictMonoOn a (Set.Ioi 0) := by
  sorry
```

**Proof:**
- Use Mathlib's `Convex.strictMonoOn_of_deriv_pos` or `StrictMonoOn.of_deriv_pos`
- Set.Ioi 0 is convex (it's an open ray)
- a is continuous on Ioi 0 (from continuousOn_a)
- a is differentiable on Ioi 0 (from deriv_a_eq existing)
- deriv a x > 0 for all x in Ioi 0 (from deriv_a_pos)
- Conclude: a is strictly monotone increasing on (0, infinity)

## CRITICAL HINTS

1. **For deriv_digamma_eq_neg_trigamma:**
   - May need to use the limit definition of trigamma
   - Or use Mathlib's `Complex.deriv_cpow` and series manipulation
   - The recurrence `deriv_digamma_add_one` telescopes to give the series

2. **For deriv_a_pos:**
   - The key is combining deriv_a_eq with deriv_digamma_eq_neg_trigamma
   - Then apply im_trigamma_neg with hz := 1/4 > 0 and hzi := pi*x > 0

3. **For strictMonoOn_a:**
   - Key Mathlib lemmas: `StrictMonoOn`, `Convex.strictMonoOn_of_deriv_pos`
   - May need `DifferentiableOn a (Set.Ioi 0)` which follows from deriv_a_eq

## Expected Output

Three proven lemmas that establish:
1. The derivative of digamma equals negative trigamma
2. The function a(x) has positive derivative for x > 0
3. The function a(x) is strictly increasing on (0, infinity)

These complete Stage 2 (Monotonicity) of the A3_FLOOR roadmap.
