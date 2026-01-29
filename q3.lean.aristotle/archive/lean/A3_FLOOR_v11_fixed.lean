import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

-- Real definitions (not opaque).
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

lemma im_trigamma_eq_tsum_im {z : ℂ} (hz : 0 < z.re) :
    (trigamma z).im = ∑' n : ℕ, (1 / (z + n)^2).im := by
  have hsum : Summable (fun n : ℕ => 1 / (z + n)^2) := summable_trigamma_series hz
  simpa [trigamma] using (Complex.im_tsum hsum)

/-- Imaginary part of trigamma is negative for z with positive re/im. -/
theorem im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0 := by
  rw [im_trigamma_eq_tsum_im hz]
  have hsum : Summable (fun n : ℕ => (1 / (z + n)^2).im) := by
    have hsum' : Summable (fun n : ℕ => (1 : ℂ) / (z + n)^2) := summable_trigamma_series hz
    simpa using (Complex.imCLM.summable hsum')
  have hsum_neg : Summable (fun n : ℕ => -(1 / (z + n)^2).im) := by
    simpa using hsum.neg
  have hpos : 0 < ∑' n : ℕ, -(1 / (z + n)^2).im := by
    refine Summable.tsum_pos hsum_neg ?_ 0 ?_
    · intro n
      exact neg_nonneg.mpr (le_of_lt (im_one_div_sq_add_nat_neg n hz hzi))
    · exact neg_pos.mpr (im_one_div_sq_add_nat_neg 0 hz hzi)
  have hneg : 0 < -(∑' n : ℕ, (1 / (z + n)^2).im) := by
    have htsum : ∑' n : ℕ, -(1 / (z + n)^2).im = -∑' n : ℕ, (1 / (z + n)^2).im := by
      exact tsum_neg (f := fun n : ℕ => (1 / (z + n)^2).im)
    have hpos' := hpos
    rw [htsum] at hpos'
    exact hpos'
  nlinarith

-- Dependencies from v3/v8 (treat as proven in upstream files).
axiom deriv_digamma_eq_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = trigamma z

axiom deriv_a_eq {xi : ℝ} (hxi : 0 < xi) :
    deriv a xi = Real.pi * (deriv digamma (1/4 + Complex.I * Real.pi * xi)).im

axiom continuousOn_a : ContinuousOn a (Set.Ici 0)

/-- a'(xi) < 0 for xi > 0. -/
theorem deriv_a_neg {xi : ℝ} (hxi : 0 < xi) : deriv a xi < 0 := by
  have hzre : 0 < (1/4 + Complex.I * Real.pi * xi).re := by
    have hre : (1/4 + Complex.I * Real.pi * xi).re = (1/4 : ℝ) := by
      simp [mul_assoc]
    nlinarith [hre]
  have hzim : 0 < (1/4 + Complex.I * Real.pi * xi).im := by
    have him : (1/4 + Complex.I * Real.pi * xi).im = Real.pi * xi := by
      simp [mul_assoc]
    have hpos : 0 < Real.pi * xi := mul_pos Real.pi_pos hxi
    nlinarith [him, hpos]
  calc
    deriv a xi = Real.pi * (deriv digamma (1/4 + Complex.I * Real.pi * xi)).im :=
      deriv_a_eq hxi
    _ = Real.pi * (trigamma (1/4 + Complex.I * Real.pi * xi)).im := by
      congr 1
      exact congrArg Complex.im (deriv_digamma_eq_trigamma hzre)
    _ < 0 := by
      exact mul_neg_of_pos_of_neg Real.pi_pos (im_trigamma_neg hzre hzim)

/-- a is strictly decreasing on (0, ∞). -/
theorem strictAntiOn_a : StrictAntiOn a (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (D := Set.Ioi 0)
  · exact convex_Ioi 0
  · exact continuousOn_a.mono Set.Ioi_subset_Ici_self
  · intro x hx
    have hx' : 0 < x := by simpa using hx
    exact deriv_a_neg hx'
