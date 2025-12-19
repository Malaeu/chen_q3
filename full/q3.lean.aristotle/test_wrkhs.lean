import Mathlib

noncomputable def w_RKHS (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n
noncomputable def w_max : ℝ := 2 / Real.exp 1

-- Key lemma: log(n)/√n ≤ 2/e for n ≥ 2
lemma log_div_sqrt_le (n : ℕ) (hn : n ≥ 2) : Real.log n / Real.sqrt n ≤ 2 / Real.exp 1 := by
  have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  -- Rearrange to: log(n) ≤ (2/e) * √n
  rw [div_le_iff₀ h_sqrt_pos]
  -- Use: log(√n/e) ≤ √n/e - 1, i.e., log(√n) - 1 ≤ √n/e - 1
  have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt n / Real.exp 1 by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt (by positivity : (0:ℝ) < n), Real.log_exp] at h1
  -- h1: (1/2) * log(n) - 1 ≤ √n / e - 1
  -- So: (1/2) * log(n) ≤ √n / e
  -- So: log(n) ≤ 2 * √n / e
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have h3 := Real.add_one_le_exp 1
  have h4 : Real.sqrt n ≥ 0 := Real.sqrt_nonneg n
  nlinarith

lemma w_RKHS_le_w_max (n : ℕ) : w_RKHS n ≤ w_max := by
  unfold w_RKHS w_max
  rcases le_or_gt n 1 with hn | hn
  · interval_cases n <;> simp [ArithmeticFunction.vonMangoldt] <;> positivity
  · have h_log_bound : ArithmeticFunction.vonMangoldt n ≤ Real.log n := 
      ArithmeticFunction.vonMangoldt_le_log
    have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n 
        ≤ Real.log n / Real.sqrt n := by gcongr
      _ ≤ 2 / Real.exp 1 := log_div_sqrt_le n hn
