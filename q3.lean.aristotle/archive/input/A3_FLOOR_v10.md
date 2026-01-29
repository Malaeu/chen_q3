# A3_FLOOR v10: Correct Sign Monotonicity

## Goal
Prove `deriv_a_neg` and `strictAntiOn_a` with **real definitions** (not opaque) and **correct sign**.

**Critical:** In v9 the sign was WRONG (a' > 0). The canonical sign from symbol_floor.tex is **a' < 0**.

---

## Setup (Use Real Definitions)

```lean
import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

-- Real definitions (NOT opaque!)
def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * ξ)).re
```

---

## Previously Proven Lemmas (from v3, v8)

### Lemma 1: im_trigamma_neg
```lean
theorem im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0 := by
  -- Proven in v3 and v8
  sorry
```

### Lemma 2: deriv_a_eq (CRITICAL: NO minus sign!)
```lean
theorem deriv_a_eq {ξ : ℝ} (hξ : 0 < ξ) :
    deriv a ξ = Real.pi * (deriv digamma (1/4 + Complex.I * Real.pi * ξ)).im := by
  -- Proven in v3 and v8 with PLUS sign
  sorry
```

### Lemma 3: continuousOn_a
```lean
theorem continuousOn_a : ContinuousOn a (Set.Ici 0) := by
  -- Proven in v3 and v8
  sorry
```

### Lemma 4: deriv_digammaSeq_tendsto_trigamma
```lean
lemma deriv_digammaSeq_tendsto_trigamma (z : ℂ) (hz : 0 < z.re) :
    Filter.Tendsto (fun n => deriv (fun z => digammaSeq z n) z) Filter.atTop (nhds (trigamma z)) := by
  -- Proven in v8
  sorry
```

---

## Target Lemmas

### Target 1: deriv_digamma_eq_trigamma
**Statement:**
```lean
theorem deriv_digamma_eq_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = trigamma z := by
  sorry
```

**Proof Outline:**
1. The digamma function ψ(z) = Γ'(z)/Γ(z) is meromorphic with simple poles at non-positive integers
2. Its derivative is the trigamma function: ψ'(z) = Σ 1/(z+n)²
3. Use `deriv_digammaSeq_tendsto_trigamma` and the fact that digammaSeq → digamma
4. Show that deriv commutes with the limit (uniform convergence on compacts)

**Key insight:** From the series representation and Weierstrass theorem on uniform convergence.

---

### Target 2: deriv_a_neg
**Statement:**
```lean
theorem deriv_a_neg {ξ : ℝ} (hξ : 0 < ξ) : deriv a ξ < 0 := by
  sorry
```

**Proof:**
```
deriv a ξ = π * (deriv digamma z).im      [by deriv_a_eq]
         = π * (trigamma z).im            [by deriv_digamma_eq_trigamma]
         = π * (negative)                 [by im_trigamma_neg, since z = 1/4 + iπξ has Im > 0]
         < 0                              ✓
```

Where z = 1/4 + i·π·ξ has:
- z.re = 1/4 > 0
- z.im = π·ξ > 0 (since ξ > 0)

---

### Target 3: strictAntiOn_a
**Statement:**
```lean
theorem strictAntiOn_a : StrictAntiOn a (Set.Ioi 0) := by
  sorry
```

**Proof:**
```
1. a is continuous on [0, ∞) by continuousOn_a
2. deriv a ξ < 0 for all ξ > 0 by deriv_a_neg
3. Set.Ioi 0 is convex
4. Apply strictAntiOn_of_deriv_neg:
   - Convexity of Ioi 0 ✓
   - Continuity on Ioi 0 (from continuousOn_a restricted) ✓
   - deriv a < 0 on interior (which is Ioi 0 itself) ✓
```

---

## Chain of Dependencies

```
deriv_digammaSeq_tendsto_trigamma (v8)
              ↓
    deriv_digamma_eq_trigamma ←── NEW TARGET 1
              ↓
         deriv_a_eq (v3/v8)
              ↓
         deriv_a_neg ←────────── NEW TARGET 2
              ↓
       im_trigamma_neg (v3/v8)
              ↓
       strictAntiOn_a ←───────── NEW TARGET 3
              ↓
       continuousOn_a (v3/v8)
```

---

## Numerical Evidence

From symbol_floor.tex Lemma 5.5:
```
a'(ξ) = -2π²ξ Σ (n + 1/4) / ((n + 1/4)² + π²ξ²)²
```

For ξ = 1:
- Every term in the sum is positive (since n + 1/4 > 0)
- The factor -2π²ξ < 0
- Therefore a'(1) < 0 ✓

Computed values:
- a(0) ≈ 3.09 (maximum)
- a(1/2) ≈ 0.58
- a(1) ≈ -0.37
- a(2) ≈ -0.88

The function a is strictly DECREASING on (0, ∞).

---

## Important Notes

1. **v9 had the wrong sign** because:
   - Used `opaque` definitions
   - Had a minus sign in deriv_a_eq: `deriv a ξ = -π * ...`
   - Proved a' > 0 (WRONG)

2. **This v10 uses:**
   - Real definitions from v3/v8
   - Correct deriv_a_eq with PLUS sign
   - Will prove a' < 0 (CORRECT)

3. **Key tactic hint:** For deriv_digamma_eq_trigamma, consider using:
   - The functional equation approach (differentiate Γ(z+1) = z·Γ(z))
   - Or the series representation approach (uniform convergence)

---

## References

- symbol_floor.tex, Lemma 5.5 (Digamma monotonicity)
- A3_FLOOR_v3_trigamma_foundations.lean
- A3_FLOOR_v8_monotonicity.lean
- PROSHKA_REQUEST_3.md, §7 (Key invariants)
