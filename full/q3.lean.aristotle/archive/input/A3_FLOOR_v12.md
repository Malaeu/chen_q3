# A3_FLOOR v12: Finish im_trigamma_neg (no holes)

## Goal
Close the remaining hole in `im_trigamma_neg` with a clean Lean proof.
Keep the scope minimal: do NOT expand Gamma product or other heavy analysis.

---

## Setup (Lean)

```lean
import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2

theorem im_one_div_sq_add_nat_neg {z : ℂ} (n : ℕ) (hz : 0 < z.re) (hzi : 0 < z.im) :
    (1 / (z + n)^2).im < 0 := by
  norm_num [sq, Complex.normSq, Complex.div_im]
  exact add_neg
    (mul_neg_of_pos_of_neg (div_pos (by positivity) (by positivity))
      (div_neg_of_neg_of_pos (by linarith) (by positivity)))
    (mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) (by positivity))
      (div_pos (by positivity) (by positivity)))

lemma summable_trigamma_series {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => 1 / (z + n)^2) := by
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

lemma im_trigamma_eq_tsum_im {z : ℂ} (hz : 0 < z.re) :
    (trigamma z).im = ∑' n : ℕ, (1 / (z + n)^2).im := by
  have hsum : Summable (fun n : ℕ => 1 / (z + n)^2) := summable_trigamma_series hz
  simpa [trigamma] using (Complex.im_tsum hsum)
```

---

## Target

```lean
theorem im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0 := by
  -- Rewrite to a sum of imaginary parts.
  -- Use Summable.tsum_lt_tsum with g = 0 and i = 0.
  -- hle : ∀ n, f n ≤ 0 from im_one_div_sq_add_nat_neg
  -- hlt : f 0 < 0
  -- hsum : Summable f via Complex.imCLM.summable (summable_trigamma_series hz)
  -- summable_zero for g
  sorry
```

---

## Hint (one possible skeleton)

```lean
  rw [im_trigamma_eq_tsum_im hz]
  have hsum : Summable (fun n : ℕ => (1 / (z + n)^2).im) := by
    have hsum' : Summable (fun n : ℕ => (1 : ℂ) / (z + n)^2) := summable_trigamma_series hz
    simpa using (Complex.imCLM.summable hsum')
  have hle : ∀ n, (1 / (z + n)^2).im ≤ 0 :=
    fun n => le_of_lt (im_one_div_sq_add_nat_neg n hz hzi)
  have hlt : (1 / (z + 0)^2).im < 0 := im_one_div_sq_add_nat_neg 0 hz hzi
  have hsum_lt : ∑' n, (1 / (z + n)^2).im < ∑' n, (0 : ℝ) :=
    Summable.tsum_lt_tsum (i := 0) hle hlt hsum (by simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))))
  simpa using hsum_lt
```

