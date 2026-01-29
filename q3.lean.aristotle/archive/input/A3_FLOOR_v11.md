# A3_FLOOR v11: Trigamma sign + monotonicity chain (correct sign)

## Goal
1) Prove `im_trigamma_eq_tsum_im` and `im_trigamma_neg` from the trigamma series.
2) Prove `deriv_a_neg` and `strictAntiOn_a` using the correct sign.

**Keep scope small:** do NOT expand Gamma product or other heavy analysis. Use existing mathlib lemmas where possible.

---

## Setup (Lean)

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
def a (xi : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * xi)).re

/-- Imaginary part of one term is negative (z has positive re/im). -/
lemma im_one_div_sq_add_nat_neg {z : ℂ} (n : ℕ) (hz : 0 < z.re) (hzi : 0 < z.im) :
    (1 / (z + n)^2).im < 0 := by
  norm_num [sq, Complex.normSq, Complex.div_im]
  exact add_neg
    (mul_neg_of_pos_of_neg (div_pos (by positivity) (by positivity))
      (div_neg_of_neg_of_pos (by linarith) (by positivity)))
    (mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) (by positivity))
      (div_pos (by positivity) (by positivity)))

/-- Trigamma series is summable for Re z > 0. -/
lemma summable_trigamma_series {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => 1 / (z + n)^2) := by
  -- Compare with 1/n^2.
  have h_comparison : ∃ N : ℕ, ∀ n ≥ N, ‖1 / (z + n)^2‖ ≤ 1 / n^2 := by
    norm_num [Complex.normSq, Complex.sq_norm]
    exact ⟨Nat.ceil (2 * |z.re| + 2 * |z.im| + 1), fun n hn =>
      inv_anti₀
        (sq_pos_of_pos <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
          rintro rfl; norm_num at hn; linarith [abs_nonneg z.re, abs_nonneg z.im])
        (by cases abs_cases z.re <;> cases abs_cases z.im <;>
          nlinarith [Nat.ceil_le.mp hn])⟩
  have h_abs_summable : Summable (fun n : ℕ => ‖1 / (z + n)^2‖) := by
    rw [← summable_nat_add_iff h_comparison.choose]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      h_comparison.choose_spec _ (Nat.le_add_left _ _))
      (by
        simpa using
          summable_nat_add_iff h_comparison.choose |>.2
            (Real.summable_one_div_nat_pow.2 one_lt_two))
  exact h_abs_summable.of_norm

-- Already proven in v3/v8 (use as axioms here to focus the task).
axiom deriv_digamma_eq_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = trigamma z

axiom deriv_a_eq {xi : ℝ} (hxi : 0 < xi) :
    deriv a xi = Real.pi * (deriv digamma (1/4 + Complex.I * Real.pi * xi)).im

axiom continuousOn_a : ContinuousOn a (Set.Ici 0)
```

---

## Targets

### 1) im_trigamma_eq_tsum_im
```lean
lemma im_trigamma_eq_tsum_im {z : ℂ} (hz : 0 < z.re) :
    (trigamma z).im = ∑' n : ℕ, (1 / (z + n)^2).im := by
  -- Hint: use Complex.im_tsum with summable_trigamma_series.
  sorry
```

### 2) im_trigamma_neg
```lean
theorem im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0 := by
  -- Hint: rewrite with im_trigamma_eq_tsum_im; show each term < 0; use tsum_nonpos.
  sorry
```

### 3) deriv_a_neg
```lean
theorem deriv_a_neg {xi : ℝ} (hxi : 0 < xi) : deriv a xi < 0 := by
  -- Hint: deriv_a_eq -> deriv_digamma_eq_trigamma -> im_trigamma_neg.
  -- z = 1/4 + i*pi*xi has re>0 and im>0.
  sorry
```

### 4) strictAntiOn_a
```lean
theorem strictAntiOn_a : StrictAntiOn a (Set.Ioi 0) := by
  -- Hint: strictAntiOn_of_deriv_neg (Mathlib.Analysis.Calculus.Deriv.MeanValue).
  -- Need convexity of Ioi 0, continuity, and deriv_a_neg on Ioi 0.
  sorry
```

---

## Notes / Hints

- For `im_trigamma_eq_tsum_im`: use `Complex.im_tsum` + `summable_trigamma_series`.
- For `im_trigamma_neg`: show summability of `(fun n => (1 / (z + n)^2).im)` via
  `Complex.imCLM.summable` and then use `tsum_nonpos`.
- For `strictAntiOn_a`: use `convex_Ioi` and `ContinuousOn` restriction.

