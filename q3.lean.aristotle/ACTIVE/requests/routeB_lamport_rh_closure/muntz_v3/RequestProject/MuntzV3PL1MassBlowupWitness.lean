import RequestProject.MuntzV3PL2RawPoleMismatch

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace EStarMuntzZeroMassContinuation

noncomputable def pl1Witness (u : ℝ) : ℂ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (1 : ℂ)) u

theorem rawZetaMul_norm_tendsto_atTop
    (M : ℂ → ℂ) (m : ℂ)
    (hM : ContinuousAt M 1) (hM1 : M 1 = m) (hm : m ≠ 0) :
    Filter.Tendsto (fun w : ℂ => ‖riemannZeta w * M w‖)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) Filter.atTop := by
  have hnum :
      Tendsto (fun w : ℂ => ‖((w - 1) * riemannZeta w) * M w‖)
        (𝓝[≠] 1) (𝓝 ‖m‖) := by
    simpa [hM1] using
      (riemannZeta_residue_one.mul (hM.tendsto.mono_left inf_le_left)).norm
  have hden :
      Tendsto (fun w : ℂ => (‖w - 1‖ : ℝ)⁻¹) (𝓝[≠] 1) atTop :=
    (tendsto_norm_sub_self_nhdsNE (1 : ℂ)).inv_tendsto_nhdsGT_zero
  have hblow := hnum.pos_mul_atTop (norm_pos_iff.mpr hm) hden
  apply hblow.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  rw [← norm_inv, ← norm_mul]
  congr 1
  field_simp

private theorem pl1Witness_on_Ico {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    pl1Witness u = (u : ℂ) := by
  by_cases h0 : u = 0
  · simp [pl1Witness, h0]
  · have hu0 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h0)
    simp [pl1Witness, Set.mem_Ioc, hu0, hu.2.le, Complex.cpow_one]

private theorem pl1Witness_mellin_eq (s : ℂ) (hs : -1 < s.re) :
    Mellin pl1Witness s = 1 / (s + 1) := by
  have h1 := hasMellin_cpow_Ioc (s := s) (1 : ℂ) (by norm_num; linarith)
  have hbridge : Mellin pl1Witness s = mellin pl1Witness s := by
    unfold Mellin mellin
    apply integral_congr_ae
    filter_upwards with u
    simp only [smul_eq_mul]
    rw [mul_comm]
  rw [hbridge]
  change mellin
      ((Set.Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (1 : ℂ))) s =
    1 / (s + 1)
  exact h1.2

theorem exists_rawZetaMellin_norm_blowup_at_one :
    ∃ (h : ℝ → ℂ) (b : ℝ) (K : NNReal),
      Measurable h ∧
      (∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0) ∧
      LipschitzOnWith K h (Set.Ico (0 : ℝ) b) ∧
      (∫ u in Set.Ioi (0 : ℝ), h u ≠ 0) ∧
      Filter.Tendsto (fun w : ℂ => ‖riemannZeta w * Mellin h w‖)
        (nhdsWithin 1 {(1 : ℂ)}ᶜ) Filter.atTop := by
  have hmeas : Measurable pl1Witness := by
    change Measurable
      ((Set.Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (1 : ℂ)))
    simpa only [Complex.cpow_one, pow_one] using
      (Complex.continuous_ofReal.pow 1).measurable.indicator
        (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))
  have hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → pl1Witness u = 0 := by
    intro u hu
    simp only [pl1Witness, Set.indicator_apply]
    have hout : u ∉ Set.Ioc (0 : ℝ) 1 := by
      intro hui
      exact hu ⟨hui.1.le, hui.2⟩
    simp [hout]
  have hlip : LipschitzOnWith (1 : NNReal) pl1Witness (Set.Ico (0 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [pl1Witness_on_Ico hx, pl1Witness_on_Ico hy]
    simpa using (Complex.isometry_ofReal.dist_eq x y).le
  have hmellin : Mellin pl1Witness 1 = (1 / 2 : ℂ) := by
    have hm := pl1Witness_mellin_eq (1 : ℂ) (by norm_num)
    norm_num at hm
    exact hm
  have hmass : ∫ u in Set.Ioi (0 : ℝ), pl1Witness u = (1 / 2 : ℂ) := by
    simpa [Mellin] using hmellin
  have hana : AnalyticOnNhd ℂ (Mellin pl1Witness) {s : ℂ | 0 < s.re} := by
    simpa [Mellin] using
      (mellin_compactSupport_analyticOnNhd pl1Witness 1 1 hmeas hsupp hlip)
  have hcont : ContinuousAt (Mellin pl1Witness) 1 :=
    (hana 1 (by norm_num)).continuousAt
  refine ⟨pl1Witness, 1, 1, hmeas, hsupp, hlip, ?_, ?_⟩
  · rw [hmass]
    norm_num
  · apply rawZetaMul_norm_tendsto_atTop
      (Mellin pl1Witness) (Mellin pl1Witness 1) hcont rfl
    rw [hmellin]
    norm_num

end EStarMuntzZeroMassContinuation
