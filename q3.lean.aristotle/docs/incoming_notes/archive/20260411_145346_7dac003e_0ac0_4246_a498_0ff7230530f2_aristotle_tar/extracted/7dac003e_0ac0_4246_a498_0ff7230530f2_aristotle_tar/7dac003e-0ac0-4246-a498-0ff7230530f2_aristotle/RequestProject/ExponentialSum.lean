import Mathlib

open Complex Finset Filter
open scoped BigOperators Real Topology

noncomputable section

/-- The exponential sum S_α(j, T) = ∑_{t ∈ range T} e^{2πi·j·α·t} -/
def expSum (α : ℝ) (j : ℤ) (T : ℕ) : ℂ :=
  ∑ t ∈ Finset.range T, exp (2 * π * I * (j * α * t))

/-
For α not an integer, the exponential sum is bounded by 2/|e^{2πiα} - 1|.
    More precisely, |∑_{n=0}^{N-1} e^{2πinα}| ≤ 2/|e^{2πiα} - 1|
-/
lemma expSum_bound {α : ℝ} (hα : ∀ n : ℤ, α ≠ n) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, exp (2 * π * I * α * n)‖ ≤
      2 / ‖exp (2 * π * I * α) - 1‖ := by
        -- Use geom_sum_eq to rewrite the sum as (exp(2πiα)^N - 1)/(exp(2πiα) - 1). The key fact is exp(2πiαn) = exp(2πiα)^n.
        have h_geom_sum : (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * α * n)) = ((Complex.exp (2 * Real.pi * Complex.I * α))^N - 1) / (Complex.exp (2 * Real.pi * Complex.I * α) - 1) := by
          rw [ ← geom_sum_mul, eq_div_iff ];
          · norm_num [ ← Complex.exp_nat_mul, mul_comm ];
          · rw [ Ne.eq_def, sub_eq_zero, Complex.exp_eq_one_iff ];
            exact fun ⟨ n, hn ⟩ => hα n <| by norm_num [ Complex.ext_iff ] at hn; nlinarith [ Real.pi_pos ] ;
        rw [ h_geom_sum, norm_div ];
        gcongr;
        exact le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] )

/-
For α not an integer, (1/N) * |∑_{n=0}^{N-1} e^{2πinα}| → 0 as N → ∞
-/
theorem expSum_cesaro_tendsto_zero {α : ℝ} (hα : ∀ n : ℤ, α ≠ n) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N,
      exp (2 * π * I * α * ↑n)‖) atTop (nhds 0) := by
        -- By expSum_bound, ‖∑ n ∈ range N, exp(...)‖ ≤ C where C = 2/‖exp(2πiα)-1‖ is a constant.
        set C := 2 / ‖exp (2 * Real.pi * Complex.I * α) - 1‖
        have h_bound : ∀ N, ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * α * n)‖ ≤ C := by
          exact fun N => expSum_bound hα N;
        exact squeeze_zero ( fun _ => by positivity ) ( fun N => mul_le_mul_of_nonneg_left ( h_bound N ) ( by positivity ) ) ( by simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const C )

/-
The Cesàro mean version: (1/H) ∑_{j=1}^{H} |S_α(j, T)| / T → 0 as T → ∞,
    for any fixed H and irrational α
-/
theorem cesaro_mean_expSum_tendsto_zero {α : ℝ} (hα : Irrational α) (H : ℕ) :
    Tendsto (fun T : ℕ =>
      (1 / (H : ℝ)) * ∑ j ∈ Finset.range H,
        (1 / (T : ℝ)) * ‖expSum α (↑j + 1) T‖) atTop (nhds 0) := by
          -- We show that for each $j \in \{1, \ldots, H\}$, $|S_\alpha(j, T)| / T \to 0$ as $T \to \infty$
          have h_expSum_div_T_tendsto_zero (j : ℕ) (hj : j ∈ Finset.range H) :
              Tendsto (fun T : ℕ => (1 / (T : ℝ)) * ‖expSum α ((j + 1 : ℤ)) T‖) atTop (nhds 0) := by
                convert expSum_cesaro_tendsto_zero _;
                rotate_left;
                exact ( j + 1 ) * α;
                · exact fun n hn => hα ⟨ n / ( j + 1 ), by push_cast; rw [ ← hn, mul_div_cancel_left₀ _ ( Nat.cast_add_one_ne_zero j ) ] ⟩;
                · exact Finset.sum_congr rfl fun _ _ => by push_cast; ring;
          simpa using tendsto_const_nhds.mul ( tendsto_finset_sum _ h_expSum_div_T_tendsto_zero )

end