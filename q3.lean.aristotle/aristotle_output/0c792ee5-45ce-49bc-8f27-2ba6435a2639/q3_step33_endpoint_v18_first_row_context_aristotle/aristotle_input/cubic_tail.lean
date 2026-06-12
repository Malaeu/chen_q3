import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000

/-
Tail bound for the cubic series: ∑_{n≥0} c/((n+d)^3) ≤ c/(2(d-1/2)²).
Uses integral comparison: ∑ 1/(n+d)^3 ≤ 1/d^3 + ∫_d^∞ 1/x^3 dx = 1/d^3 + 1/(2d^2).
-/
lemma cubic_tail_series_bound (c d : ℝ) (hc : 0 ≤ c) (hd : 1 / 2 < d) :
    ∑' (n : ℕ), c / ((↑n + d) ^ 3) ≤ c / (2 * (d - 1 / 2) ^ 2) := by
  by_contra! h_contra;
  -- We use telescoping series to find an upper bound for the sum.
  have h_telescope : ∀ (N : ℕ), ∑ k ∈ Finset.range N, c / (k + d : ℝ) ^ 3 ≤ c / (2 * (d - 1 / 2) ^ 2) - c / (2 * (N + d - 1 / 2) ^ 2) := by
    intro N
    have h_telescope_step : ∀ k : ℕ, c / (k + d : ℝ) ^ 3 ≤ c / (2 * (k + d - 1 / 2) ^ 2) - c / (2 * (k + d + 1 / 2) ^ 2) := by
      intro k; rw [ div_sub_div, div_le_div_iff₀ ] <;> try positivity;
      · nlinarith [ show 0 ≤ c * ( k + d ) ^ 3 by positivity, show 0 ≤ c * ( k + d ) ^ 2 by positivity, show 0 ≤ c * ( k + d ) by positivity, show 0 ≤ c by positivity ];
      · exact mul_pos ( mul_pos two_pos ( sq_pos_of_pos ( by linarith ) ) ) ( mul_pos two_pos ( sq_pos_of_pos ( by linarith ) ) );
      · exact mul_ne_zero two_ne_zero ( pow_ne_zero 2 ( by linarith ) );
    induction' N with N ih <;> norm_num [ Finset.sum_range_succ ] at *;
    convert add_le_add ih ( h_telescope_step N ) using 1 ; ring;
  -- Taking the limit of the telescoping series as $N$ approaches infinity, we get:
  have h_limit : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, c / (k + d : ℝ) ^ 3) Filter.atTop (nhds (∑' (n : ℕ), c / (n + d : ℝ) ^ 3)) := by
    exact ( Summable.hasSum <| by exact ( by { by_contra h; rw [ tsum_eq_zero_of_not_summable h ] at h_contra; exact h_contra.not_ge <| by positivity } ) ) |> HasSum.tendsto_sum_nat;
  exact h_contra.not_ge <| le_of_tendsto_of_tendsto' h_limit tendsto_const_nhds fun N => le_trans ( h_telescope N ) <| sub_le_self _ <| div_nonneg hc <| mul_nonneg zero_le_two <| sq_nonneg _