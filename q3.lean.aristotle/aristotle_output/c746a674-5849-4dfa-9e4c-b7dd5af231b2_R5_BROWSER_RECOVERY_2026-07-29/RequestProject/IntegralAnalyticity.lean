import RequestProject.ConcreteAnalyticity

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology BigOperators

namespace EStarMuntzZeroMassContinuation

/-- The locally finite dilation sum defining `Estar` is measurable. -/
theorem Estar_measurable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hmeas : Measurable h) : Measurable (Estar h) := by
  have hsummable : ∀ u : ℝ, Summable (fun n : ℕ+ => h ((n : ℝ) * u)) := by
    intro u
    by_cases hu : 0 < u
    · let N := Nat.ceil (b / u)
      apply summable_of_ne_finset_zero (s := Finset.Icc 1 ⟨N + 1, Nat.succ_pos _⟩)
      intro n hn
      apply hsupp
      simp only [Finset.mem_Icc, not_and, PNat.one_le, true_implies] at hn
      have hn' : (⟨N + 1, Nat.succ_pos _⟩ : ℕ+) < n := lt_of_not_ge hn
      have hn' : N + 1 < (n : ℕ) := hn'
      have hceil : b / u ≤ N := Nat.le_ceil (b / u)
      have hNn : N < (n : ℕ) := lt_of_le_of_lt (Nat.le_add_right N 1) hn'
      have hnreal : b / u < (n : ℝ) := lt_of_le_of_lt hceil (by exact_mod_cast hNn)
      simp only [mem_Icc, not_and_or]
      right
      apply not_le_of_gt
      rw [← div_lt_iff₀ hu]
      exact hnreal
    · apply summable_of_ne_finset_zero (s := ∅)
      intro n hn
      apply hsupp
      simp only [mem_Icc, not_and_or]
      left
      have hprod : (n : ℝ) * u ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hu)
      exact not_le_of_gt (lt_of_le_of_lt hprod ha)
  have hsum_meas : Measurable (fun u : ℝ => ∑' n : ℕ+, h ((n : ℝ) * u)) := by
    let e : ℕ ≃ ℕ+ := Equiv.pnatEquivNat.symm
    let F : ℕ → ℝ → ℂ := fun N u =>
      ∑ n ∈ Finset.range N, h (((e n : ℕ) : ℝ) * u)
    apply measurable_of_tendsto_metrizable (f := F)
    · intro N
      apply Finset.measurable_sum
      intro n hn
      exact hmeas.comp (measurable_const.mul measurable_id)
    · apply tendsto_pi_nhds.2
      intro u
      exact ((Equiv.hasSum_iff e).2 (hsummable u).hasSum).tendsto_sum_nat
  unfold Estar
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable.mul hsum_meas

/-- Away from zero, the locally finite dilation sum is locally integrable. -/
theorem Estar_locallyIntegrableOn_Ioi
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) :
    LocallyIntegrableOn (Estar h) (Set.Ioi 0) := by
  -- Use that Estar is continuous on (0, ∞)
  have hcont : ContinuousOn (Estar h) (Set.Ioi 0) := by
    have hcont_h : Continuous h := hlip.continuous
    refine continuousOn_of_forall_continuousAt fun u₀ hu₀ => ?_
    have hu₀pos : 0 < u₀ := hu₀
    -- Choose a neighborhood where we have uniform bounds
    let c := u₀ / 2
    let d := 2 * u₀
    have hc : 0 < c := by positivity
    have hd : c < d := by simp [c, d]; linarith
    -- Choose N such that for n > N, n * u > b for all u in [c, d]
    let N_nat := Nat.ceil (b / c)
    let N : ℕ+ := ⟨N_nat, Nat.ceil_pos.mpr (div_pos (by linarith : 0 < b) hc)⟩
    -- The key: for u in (c, d), only n ≤ N can give nonzero h(n * u)
    have hN_prop : ∀ u ∈ Set.Ioo c d, ∀ n : ℕ+, (n : ℕ) > N_nat → h ((n : ℝ) * u) = 0 := by
      intro u hu n hn
      apply hsupp
      simp only [mem_Icc, not_and_or]
      right
      have h1 : (n : ℝ) > N_nat := by exact_mod_cast hn
      have h2 : u > c := hu.1
      have hbu : (n : ℝ) * u > b := by
        have hN_le : (N_nat : ℝ) ≥ b / c := Nat.le_ceil (b / c)
        calc (n : ℝ) * u > N_nat * c := by nlinarith
          _ ≥ b := by nlinarith [div_mul_cancel₀ b (ne_of_gt hc)]
      exact not_le_of_gt hbu
    -- On (c, d), the tsum equals a finite sum
    have hsame : ∀ u ∈ Set.Ioo c d, 
        (∑' n : ℕ+, h ((n : ℝ) * u)) = ∑ n ∈ Finset.Icc 1 N, h ((n : ℝ) * u) := by
      intro u hu
      have hsumm : Summable (fun n : ℕ+ => h ((n : ℝ) * u)) := 
        summable_of_ne_finset_zero (s := Finset.Icc 1 N) fun n hn => hN_prop u hu n (by
          simp only [Finset.mem_Icc, PNat.one_le, true_and] at hn
          exact not_le.mp hn)
      exact tsum_eq_sum (s := Finset.Icc 1 N) fun n hn => hN_prop u hu n (by
          simp only [Finset.mem_Icc, PNat.one_le, true_and] at hn
          exact not_le.mp hn)
    -- u₀ is in the interval (c, d)
    have hu₀_in : u₀ ∈ Set.Ioo c d := by simp [c, d]; constructor <;> linarith
    -- Define the finite sum function
    let F : ℝ → ℂ := fun u => ∑ n ∈ Finset.Icc 1 N, h ((n : ℝ) * u)
    -- F is continuous (finite sum of continuous functions)
    have hF_cont : Continuous F := by
      apply continuous_finset_sum
      intro n _
      exact hcont_h.comp (continuous_const.mul continuous_id)
    have hF_cont_at : ContinuousAt F u₀ := hF_cont.continuousAt
    -- sqrt is continuous at u₀
    have hsqrt_cont : ContinuousAt (fun u => (Real.sqrt u : ℂ)) u₀ := 
      Complex.continuous_ofReal.continuousAt.comp Real.continuous_sqrt.continuousAt
    -- On a neighborhood of u₀, Estar h = sqrt * F
    have hEstar_eq : ∀ᶠ u in nhds u₀, Estar h u = Real.sqrt u * F u := by
      have hc' : c < u₀ := by show u₀ / 2 < u₀; linarith
      have hd' : u₀ < d := by show u₀ < 2 * u₀; linarith
      filter_upwards [Ioo_mem_nhds hc' hd']
      intro u hu
      unfold Estar
      rw [hsame u hu]
    -- Conclude continuity
    rw [continuousAt_congr hEstar_eq]
    exact ContinuousAt.mul hsqrt_cont hF_cont_at
  exact hcont.locallyIntegrableOn measurableSet_Ioi

end EStarMuntzZeroMassContinuation
