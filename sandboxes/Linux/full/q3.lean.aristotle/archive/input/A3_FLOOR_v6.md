# A3_FLOOR v6: deriv_a_pos - SINGLE FOCUSED GOAL

## ALREADY PROVEN (from v3, v4, v5) - USE AS AXIOMS

```lean
-- Definitions
noncomputable def digamma (z : C) : C := (deriv Complex.Gamma z) / (Complex.Gamma z)
noncomputable def trigamma (z : C) : C := sum' n : N, 1 / (z + n)^2
noncomputable def a (x : R) : R := Real.log Real.pi - (digamma (1/4 + I * Real.pi * x)).re

-- KEY LEMMA 1: Trigamma imaginary part is NEGATIVE
lemma im_trigamma_neg {z : C} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0

-- KEY LEMMA 2: Derivative formula
lemma deriv_a_eq {x : R} (hx : 0 < x) :
    deriv a x = Real.pi * (deriv (fun z => digamma z) (1/4 + I * Real.pi * x)).im

-- Recurrence relations
lemma deriv_digamma_add_one {z : C} (hz : 0 < z.re) :
    deriv digamma (z + 1) = deriv digamma z - 1 / z ^ 2

lemma trigamma_add_one {z : C} (hz : 0 < z.re) :
    trigamma (z + 1) = trigamma z - 1 / z ^ 2

-- The difference is periodic!
lemma diff_digamma_trigamma_add_one {z : C} (hz : 0 < z.re) :
    deriv digamma (z + 1) - trigamma (z + 1) = deriv digamma z - trigamma z

-- Trigamma goes to zero
lemma trigamma_tendsto_zero : Filter.Tendsto (fun x : R => trigamma x) Filter.atTop (nhds 0)
```

## SINGLE GOAL: Prove deriv_a_pos

```lean
lemma deriv_a_pos {x : R} (hx : 0 < x) : deriv a x > 0 := by
  sorry
```

## PROOF STRATEGY (Follow This Exactly!)

### Step 1: Establish deriv digamma = -trigamma

The key identity we need is:
```lean
deriv digamma z = -trigamma z   (for Re(z) > 0)
```

**Proof of this identity:**
- Define f(z) = deriv digamma z + trigamma z
- From diff_digamma_trigamma_add_one: f(z+1) = f(z) (f is 1-periodic)
- From trigamma_tendsto_zero: trigamma(n) -> 0 as n -> infinity
- The derivative of digamma also tends to 0 (by differentiating digamma recurrence)
- So f(n) -> 0 as n -> infinity
- But f is 1-periodic, so f must be identically 0
- Therefore: deriv digamma z = -trigamma z

### Step 2: Apply to deriv_a_pos

With deriv digamma z = -trigamma z, we have:

1. From deriv_a_eq:
   `deriv a x = pi * Im(deriv digamma (1/4 + i*pi*x))`

2. Substituting deriv digamma = -trigamma:
   `deriv a x = pi * Im(-trigamma (1/4 + i*pi*x))`
   `deriv a x = -pi * Im(trigamma (1/4 + i*pi*x))`

3. For z = 1/4 + i*pi*x with x > 0:
   - Re(z) = 1/4 > 0 ✓
   - Im(z) = pi*x > 0 (since x > 0 and pi > 0) ✓

4. By im_trigamma_neg with hz := 1/4 > 0 and hzi := pi*x > 0:
   `Im(trigamma z) < 0`

5. Therefore:
   `deriv a x = -pi * (negative number) = positive > 0`

## HINTS FOR LEAN

1. You may need to prove the intermediate lemma:
```lean
lemma deriv_digamma_eq_neg_trigamma {z : C} (hz : 0 < z.re) :
    deriv digamma z = -trigamma z
```

2. For the periodicity argument, use:
- `diff_digamma_trigamma_add_one` shows f(z+1) = f(z)
- `trigamma_tendsto_zero` + limit of deriv digamma = 0
- A 1-periodic function that tends to 0 at infinity must be 0

3. For deriv_a_pos, the chain is:
```
deriv_a_eq
  -> substitute deriv digamma = -trigamma
  -> apply im_trigamma_neg with z = 1/4 + i*pi*x
  -> conclude positivity
```

4. Key Mathlib lemmas that may help:
- `mul_pos` for pi * (positive) > 0
- `neg_neg` for -(-x) = x
- `Real.pi_pos` for pi > 0

## EXPECTED OUTPUT

A Lean 4 proof of:
```lean
lemma deriv_a_pos {x : R} (hx : 0 < x) : deriv a x > 0
```

This is the KEY lemma for Stage 2 (Monotonicity) of A3_FLOOR.
