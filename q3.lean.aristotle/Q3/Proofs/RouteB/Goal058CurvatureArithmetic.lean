import Mathlib

/-!
# Goal 058 curvature arithmetic

This file records the two elementary arithmetic estimates used by the
curvature route on the production schedule `m = N = k + 2`.  It makes no
claim that the full normalized curvature is uniformly bounded.
-/

noncomputable section

namespace Q3.RouteB

open Filter Topology BigOperators

/-- The logarithmic loss on the production schedule `k ↦ k + 2` is
sublinear. -/
theorem goal058_schedule_log_sq_div_tendsto_zero :
    Tendsto (fun k : ℕ => (Real.log (k + 2 : ℝ)) ^ 2 / (k + 2 : ℝ))
      atTop (𝓝 0) := by
  have hbase := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hshift : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using hbase.comp hshift

private theorem telescoping_reciprocal_tail_hasSum (N : ℕ) (hN : 0 < N) :
    HasSum (fun k : ℕ =>
      1 / ((N + k : ℕ) : ℝ) - 1 / ((N + k + 1 : ℕ) : ℝ))
      (1 / (N : ℝ)) := by
  let a : ℕ → ℝ := fun k => 1 / ((N + k : ℕ) : ℝ)
  have ha : Tendsto a atTop (𝓝 0) := by
    have hden : Tendsto (fun k : ℕ => ((N + k : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add] using
        tendsto_atTop_add_const_left atTop (N : ℝ) tendsto_natCast_atTop_atTop
    simpa [a, one_div] using hden.inv_tendsto_atTop
  have hsum (n : ℕ) :
      ∑ k ∈ Finset.range n, (a k - a (k + 1)) = a 0 - a n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have ht : Tendsto (fun x : ℕ => a 0 - a x) atTop (𝓝 (a 0 - 0)) :=
      tendsto_const_nhds.sub ha
    convert ht using 1
    · ext n
      exact hsum n
    · simp [a]
  · intro k
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num

/-- The reciprocal-square tail beginning at `N + 1` is at most `1 / N`. -/
theorem one_div_nat_sq_tail_le_one_div (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, 1 / (((N + k + 1 : ℕ) : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
  let f : ℕ → ℝ := fun k => 1 / (((N + k + 1 : ℕ) : ℝ) ^ 2)
  let g : ℕ → ℝ := fun k =>
    1 / ((N + k : ℕ) : ℝ) - 1 / ((N + k + 1 : ℕ) : ℝ)
  have hg : Summable g := (telescoping_reciprocal_tail_hasSum N hN).summable
  have hf : Summable f := by
    have hpow : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have hinj : Function.Injective (fun k : ℕ => N + k + 1) := by
      intro a b hab
      exact Nat.add_left_cancel (Nat.add_right_cancel hab)
    refine (hpow.comp_injective hinj).congr ?_
    intro k
    simp [f, one_div]
  calc
    (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k := by
      apply hf.tsum_le_tsum
      · intro k
        dsimp [f, g]
        have hNk : (0 : ℝ) < ((N + k : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_pos_left hN k
        have hcast : ((N + k + 1 : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by
          push_cast
          ring
        have hNk1 : (0 : ℝ) < ((N + k + 1 : ℕ) : ℝ) := by positivity
        have hprod :
            ((N + k : ℕ) : ℝ) * ((N + k + 1 : ℕ) : ℝ) ≤
              ((N + k + 1 : ℕ) : ℝ) ^ 2 := by
          rw [hcast]
          nlinarith
        calc
          1 / (((N + k + 1 : ℕ) : ℝ) ^ 2) ≤
              1 / (((N + k : ℕ) : ℝ) * ((N + k + 1 : ℕ) : ℝ)) := by
                exact one_div_le_one_div_of_le (mul_pos hNk hNk1) hprod
          _ = 1 / ((N + k : ℕ) : ℝ) -
              1 / ((N + k + 1 : ℕ) : ℝ) := by
                rw [hcast]
                field_simp
                ring
      · exact hg
    _ = 1 / (N : ℝ) := (telescoping_reciprocal_tail_hasSum N hN).tsum_eq

/-- The forced-zero curvature tail has the production bound requested in the
Goal 058 bookkeeping task. -/
theorem forcedZeroCurvatureTail_le (L : ℝ) (N : ℕ) (hN : 0 < N) :
    (L ^ 2 / (4 * Real.pi ^ 2)) *
        (∑' k : ℕ, 1 / (((N + k + 1 : ℕ) : ℝ) ^ 2)) ≤
      L ^ 2 / (4 * Real.pi ^ 2 * (N : ℝ)) := by
  have hc : 0 ≤ L ^ 2 / (4 * Real.pi ^ 2) := by positivity
  calc
    (L ^ 2 / (4 * Real.pi ^ 2)) *
        (∑' k : ℕ, 1 / (((N + k + 1 : ℕ) : ℝ) ^ 2)) ≤
      (L ^ 2 / (4 * Real.pi ^ 2)) * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (one_div_nat_sq_tail_le_one_div N hN) hc
    _ = L ^ 2 / (4 * Real.pi ^ 2 * (N : ℝ)) := by
      field_simp

#print axioms goal058_schedule_log_sq_div_tendsto_zero
#print axioms forcedZeroCurvatureTail_le

end Q3.RouteB
