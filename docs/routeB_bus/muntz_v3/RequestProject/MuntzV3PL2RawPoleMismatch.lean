import RequestProject.MellinCompactSupportAnalyticity

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace EStarMuntzZeroMassContinuation

noncomputable def pl2Witness (u : ℝ) : ℂ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (1 : ℂ)) u -
    (3 / 2 : ℂ) •
      (Set.Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (2 : ℂ)) u

theorem rawZetaMul_not_continuousAt_one
    (M : ℂ → ℂ) (d : ℂ)
    (hM1 : M 1 = 0) (hMd : HasDerivAt M d 1) (hd : d ≠ 0) :
    ¬ ContinuousAt (fun w : ℂ => riemannZeta w * M w) 1 := by
  intro hcont
  have hslope : Tendsto (slope M 1) (𝓝[≠] 1) (𝓝 d) :=
    hasDerivAt_iff_tendsto_slope.mp hMd
  have hprod : Tendsto (fun w : ℂ => riemannZeta w * M w) (𝓝[≠] 1) (𝓝 d) := by
    have hmul := riemannZeta_residue_one.mul hslope
    have heq : (fun w : ℂ => (w - 1) * riemannZeta w * slope M 1 w) =ᶠ[𝓝[≠] 1]
        (fun w => riemannZeta w * M w) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
      simp only [slope, hM1, vsub_eq_sub, sub_zero, smul_eq_mul]
      field_simp
    simpa using hmul.congr' heq
  have hzero : Tendsto (fun w : ℂ => riemannZeta w * M w) (𝓝[≠] 1) (𝓝 0) := by
    convert hcont.tendsto.mono_left inf_le_left using 1
    simp [hM1]
  exact hd (tendsto_nhds_unique hprod hzero)

private theorem pl2Witness_poly_on_Ico {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    pl2Witness u = (u : ℂ) - (3 / 2 : ℂ) * (u : ℂ) ^ 2 := by
  by_cases h0 : u = 0
  · simp [pl2Witness, h0]
  · have hu0 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h0)
    simp [pl2Witness, Set.mem_Ioc, hu0, hu.2.le, Complex.cpow_one, smul_eq_mul]

private theorem pl2Witness_mellin_eq (s : ℂ) (hs : -1 < s.re) :
    Mellin pl2Witness s =
      1 / (s + 1) - (3 / 2 : ℂ) * (1 / (s + 2)) := by
  have h1 := hasMellin_cpow_Ioc (s := s) (1 : ℂ) (by norm_num; linarith)
  have h2 := hasMellin_cpow_Ioc (s := s) (2 : ℂ) (by norm_num; linarith)
  have hscaled := hasMellin_const_smul h2.1 (3 / 2 : ℂ)
  have hsub := hasMellin_sub h1.1 hscaled.1
  have hbridge : Mellin pl2Witness s = mellin pl2Witness s := by
    unfold Mellin mellin
    apply integral_congr_ae
    filter_upwards with u
    simp only [smul_eq_mul]
    rw [mul_comm]
  rw [hbridge]
  calc
    mellin pl2Witness s =
        mellin ((Set.Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (1 : ℂ))) s -
          mellin (fun t => (3 / 2 : ℂ) •
            (Set.Ioc (0 : ℝ) 1).indicator (fun x => (x : ℂ) ^ (2 : ℂ)) t) s := by
      change mellin (fun t =>
        (Set.Ioc (0 : ℝ) 1).indicator (fun x => (x : ℂ) ^ (1 : ℂ)) t -
          (3 / 2 : ℂ) •
            (Set.Ioc (0 : ℝ) 1).indicator (fun x => (x : ℂ) ^ (2 : ℂ)) t) s = _
      exact hsub.2
    _ = 1 / (s + 1) - (3 / 2 : ℂ) * (1 / (s + 2)) := by
      rw [h1.2, hscaled.2, h2.2]
      simp [smul_eq_mul]

private theorem pl2Witness_hasDerivAt :
    HasDerivAt (Mellin pl2Witness) (-(1 : ℂ) / 12) 1 := by
  have hrat : HasDerivAt
      (fun s : ℂ => 1 / (s + 1) - (3 / 2 : ℂ) * (1 / (s + 2)))
      (-(1 : ℂ) / 12) 1 := by
    have h1 := ((hasDerivAt_id (1 : ℂ)).add_const 1).inv (by norm_num)
    have h2 := ((hasDerivAt_id (1 : ℂ)).add_const 2).inv (by norm_num)
    convert h1.sub (HasDerivAt.const_mul (3 / 2 : ℂ) h2) using 1
    · funext s
      simp [one_div]
    · norm_num
  apply hrat.congr_of_eventuallyEq
  filter_upwards [
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show -1 < (1 : ℂ).re by norm_num)
  ] with s hs
  exact pl2Witness_mellin_eq s hs

theorem exists_rawZetaMellin_not_continuousAt_one :
    ∃ (h : ℝ → ℂ) (b : ℝ) (K : NNReal),
      Measurable h ∧
      (∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0) ∧
      LipschitzOnWith K h (Set.Ico (0 : ℝ) b) ∧
      (∫ u in Set.Ioi (0 : ℝ), h u = 0) ∧
      deriv (Mellin h) 1 ≠ 0 ∧
      ¬ ContinuousAt (fun w : ℂ => riemannZeta w * Mellin h w) 1 := by
  have hmass : ∫ u in Set.Ioi (0 : ℝ), pl2Witness u = 0 := by
    have hm := pl2Witness_mellin_eq (1 : ℂ) (by norm_num)
    norm_num at hm
    simpa [Mellin] using hm
  have hM1 : Mellin pl2Witness 1 = 0 := mellin_one_eq_zero pl2Witness hmass
  have hderiv : deriv (Mellin pl2Witness) 1 ≠ 0 := by
    rw [pl2Witness_hasDerivAt.deriv]
    norm_num
  refine ⟨pl2Witness, 1, 2, ?_, ?_, ?_, hmass, hderiv, ?_⟩
  · apply Measurable.sub
    · simpa only [Complex.cpow_one, pow_one] using
        (Complex.continuous_ofReal.pow 1).measurable.indicator
          (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))
    · simpa only [Complex.cpow_two] using
        ((Complex.continuous_ofReal.pow 2).measurable.indicator
          (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))).const_smul
            (3 / 2 : ℂ)
  · intro u hu
    simp only [pl2Witness, Set.indicator_apply]
    have hout : u ∉ Set.Ioc (0 : ℝ) 1 := by
      intro hui
      exact hu ⟨hui.1.le, hui.2⟩
    simp [hout]
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [pl2Witness_poly_on_Ico hx, pl2Witness_poly_on_Ico hy]
    have hfac :
        ((x : ℂ) - (3 / 2 : ℂ) * (x : ℂ) ^ 2) -
            ((y : ℂ) - (3 / 2 : ℂ) * (y : ℂ) ^ 2) =
          ((x - y : ℝ) : ℂ) * (1 - (3 / 2 : ℂ) * ((x + y : ℝ) : ℂ)) := by
      push_cast
      ring
    have hcoef_cast :
        1 - (3 / 2 : ℂ) * ((x + y : ℝ) : ℂ) =
          ((1 - (3 / 2 : ℝ) * (x + y) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [dist_eq_norm, hfac, norm_mul, hcoef_cast]
    simp only [Complex.norm_real, Real.norm_eq_abs, NNReal.coe_ofNat, Real.dist_eq]
    have hcoef : |1 - (3 / 2 : ℝ) * (x + y)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    nlinarith [abs_nonneg (x - y)]
  · exact rawZetaMul_not_continuousAt_one (Mellin pl2Witness) (-(1 : ℂ) / 12)
      hM1 pl2Witness_hasDerivAt (by norm_num)

end EStarMuntzZeroMassContinuation
