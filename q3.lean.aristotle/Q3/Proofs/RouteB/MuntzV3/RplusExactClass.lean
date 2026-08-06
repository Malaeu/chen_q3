/-
Production port source: ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject/MuntzV3RplusExactClass.lean
Source SHA-256: e97f34aae6e851dc81a619587f3925c1e05a215fba90fe4d9f469441e6ee8144
Body copied byte-for-byte; import path rewritten only.
Port date: 2026-08-06
-/

import Q3.Proofs.RouteB.MuntzV3.MellinCompactSupportAnalyticity

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology BigOperators

namespace EStarMuntzZeroMassContinuation

/-- The right tail is entire under the exact measurable/Icc-zero/Ico-Lipschitz v3 class. -/
theorem rplus_analyticOnNhd_shiftedHalfPlane_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let N : ℕ+ := ⟨Nat.ceil b + 1, Nat.succ_pos _⟩
  let S : Finset ℕ+ := Finset.Icc 1 N
  have hbN : b < (N : ℝ) := by
    have hceil : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
    have hstep : (Nat.ceil b : ℝ) < (Nat.ceil b + 1 : ℕ) := by
      exact_mod_cast Nat.lt_succ_self (Nat.ceil b)
    exact lt_of_le_of_lt hceil hstep
  have htail :
      ∀ u : ℝ, Λ < u → ∀ n : ℕ+, n ∉ S → h ((n : ℝ) * u) = 0 := by
    intro u hu n hn
    apply hsupp
    simp only [Set.mem_Icc, not_and_or]
    right
    apply not_le_of_gt
    have hnN : N < n := by
      simp only [S, Finset.mem_Icc, PNat.one_le, true_and] at hn
      exact lt_of_not_ge hn
    have hNn : (N : ℝ) < (n : ℝ) := by exact_mod_cast hnN
    have hu1 : 1 < u := lt_of_le_of_lt hΛ hu
    have hnpos : 0 < (n : ℝ) := by positivity
    nlinarith
  have hsum :
      ∀ u : ℝ, Λ < u →
        (∑' n : ℕ+, h ((n : ℝ) * u)) = ∑ n ∈ S, h ((n : ℝ) * u) := by
    intro u hu
    exact tsum_eq_sum fun n hn => htail u hu n hn
  let g : ℝ → ℂ := fun u =>
    Real.sqrt u * ∑ n ∈ S, h ((n : ℝ) * u)
  have hgmeas : Measurable g := by
    apply Measurable.mul
    · exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable
    · apply Finset.measurable_sum
      intro n hn
      exact hmeas.comp (measurable_const.mul measurable_id)
  let f : ℝ → ℂ := Set.Ioc Λ b |>.indicator (Estar h)
  have hfg : f = (Set.Ioc Λ b).indicator g := by
    funext u
    by_cases hu : u ∈ Set.Ioc Λ b
    · simp only [f, g, Set.indicator_of_mem hu]
      unfold Estar
      rw [hsum u hu.1]
    · simp [f, hu]
  have hfmeas : Measurable f := by
    rw [hfg]
    exact hgmeas.indicator measurableSet_Ioc
  have hEstar_zero :
      ∀ u : ℝ, Λ < u → b < u → Estar h u = 0 := by
    intro u hu hub
    unfold Estar
    rw [hsum u hu]
    have hzero : ∑ n ∈ S, h ((n : ℝ) * u) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      apply hsupp
      simp only [Set.mem_Icc, not_and_or]
      right
      apply not_le_of_gt
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.prop
      nlinarith
    rw [hzero, mul_zero]
  let C : ℝ := ‖h 0‖ + (K : ℝ) * |b|
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound_Ico : ∀ u ∈ Set.Ico (0 : ℝ) b, ‖h u‖ ≤ C := by
    intro u hu
    have hb : 0 < b := lt_of_le_of_lt hu.1 hu.2
    have hdist := hlip.dist_le_mul u hu 0 ⟨le_rfl, hb⟩
    calc
      ‖h u‖ ≤ dist (h u) (h 0) + ‖h 0‖ := by
        rw [dist_eq_norm]
        exact norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * dist u 0 + ‖h 0‖ := by gcongr
      _ ≤ (K : ℝ) * |b| + ‖h 0‖ := by
        gcongr
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1, abs_of_pos hb]
        exact hu.2.le
      _ = C := by simp [C, add_comm]
  have hendpoint_ae :
      ∀ᵐ u : ℝ, ∀ n ∈ S, (n : ℝ) * u ≠ b := by
    rw [Filter.eventually_all_finset]
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hu_ae : ∀ᵐ u : ℝ, u ≠ b / (n : ℝ) := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hu_ae] with u hu
    intro hnu
    apply hu
    apply (eq_div_iff hn0).2
    simpa [mul_comm] using hnu
  let D : ℝ := Real.sqrt |b| * ((S.card : ℝ) * C)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hfbound : ∀ᵐ u : ℝ, ‖f u‖ ≤ D := by
    filter_upwards [hendpoint_ae] with u huend
    rw [hfg]
    by_cases hui : u ∈ Set.Ioc Λ b
    · rw [Set.indicator_of_mem hui]
      have hsum_bound :
          ‖∑ n ∈ S, h ((n : ℝ) * u)‖ ≤ (S.card : ℝ) * C := by
        calc
          ‖∑ n ∈ S, h ((n : ℝ) * u)‖
              ≤ ∑ n ∈ S, ‖h ((n : ℝ) * u)‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ S, C := by
            apply Finset.sum_le_sum
            intro n hn
            by_cases hnu : (n : ℝ) * u ∈ Set.Icc (0 : ℝ) b
            · exact hbound_Ico ((n : ℝ) * u)
                ⟨hnu.1, lt_of_le_of_ne hnu.2 (huend n hn)⟩
            · simpa [hsupp ((n : ℝ) * u) hnu] using hC
          _ = (S.card : ℝ) * C := by simp
      have hb0 : 0 ≤ b := by linarith [hΛpos, hui.1, hui.2]
      have hsqrt : Real.sqrt u ≤ Real.sqrt |b| := by
        rw [abs_of_nonneg hb0]
        exact Real.sqrt_le_sqrt hui.2
      calc
        ‖g u‖ = Real.sqrt u * ‖∑ n ∈ S, h ((n : ℝ) * u)‖ := by
          simp [g, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u)]
        _ ≤ Real.sqrt u * ((S.card : ℝ) * C) :=
          mul_le_mul_of_nonneg_left hsum_bound (Real.sqrt_nonneg u)
        _ ≤ D := by
          exact mul_le_mul_of_nonneg_right hsqrt (mul_nonneg (Nat.cast_nonneg _) hC)
    · simp [hui, hD]
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    apply (locallyIntegrableOn_const D).mono hfmeas.aestronglyMeasurable
    filter_upwards [hfbound] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg hD] using hu
  have htop : ∀ A : ℝ, f =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop b] with x hx
      symm
      simp [f, not_and_of_not_right _ (by linarith : ¬ x ≤ b)]
    · rfl
  have hbot : ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-B)) := by
    intro B
    apply (isBigO_zero (fun x : ℝ => x ^ (-B)) (𝓝[>] (0 : ℝ))).congr'
    · filter_upwards [
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hΛpos)] with x hx
      symm
      simp [f, (by linarith : ¬ Λ < x)]
    · rfl
  have heq : Rplus h Λ = mellin f := by
    funext s
    unfold Rplus mellin
    simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    by_cases huLambda : Λ < u
    · by_cases hu0 : 0 < u
      · by_cases huIoc : u ∈ Set.Ioc Λ b
        · simp [huLambda, hu0, huIoc, smul_eq_mul, mul_comm]
        · have hu_gt_b : b < u := by
            simp only [Set.mem_Ioc] at huIoc
            push_neg at huIoc
            tauto
          rw [hEstar_zero u huLambda hu_gt_b]
          simp
      · linarith
    · simp [huLambda]
  have hdiff : Differentiable ℂ (Rplus h Λ) := by
    intro s
    rw [heq]
    exact mellin_differentiableAt_of_isBigO_rpow hlocal
      (htop (s.re + 1)) (by linarith) (hbot (s.re - 1)) (by linarith)
  exact hdiff.differentiableOn.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

end EStarMuntzZeroMassContinuation
