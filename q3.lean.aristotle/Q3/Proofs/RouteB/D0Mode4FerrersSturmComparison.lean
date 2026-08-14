import Q3.Proofs.RouteB.D0Mode4FerrersInteriorZeroSimplicity

/-!
# Goal 058 G3: interior Sturm comparison on one nodal interval

This file proves the source-faithful comparison step for two accepted
mode-four Ferrers solutions with the same prolate potential and different
spectral parameters.  It uses only interior regularity, the stored derivative
series, the stored ODE, and simplicity of the two endpoint zeros of the lower
solution.  It does not count zeros or identify a source PSWF mode.
-/

namespace Q3.RouteB

/-! ### Contract plants

These small kernel-checked declarations pin the comparison direction, the
one-nodal-interval guard, the common-potential cancellation, and exclusion of
the singular endpoints.  The production proof below additionally consumes
the actual `HasDerivAt` fields of both accepted solutions.
-/

private theorem sturmParameterDirectionPlant :
    Real.sin 0 = 0 ∧
      Real.sin Real.pi = 0 ∧
      (Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi ∧
        Real.sin (2 * (Real.pi / 2)) = 0) := by
  refine ⟨Real.sin_zero, Real.sin_pi, ?_, ?_⟩
  · exact ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩
  · rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

private theorem sturmCounterDirectionPlant :
    ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin x ≠ 0 := by
  intro x hx
  exact (Real.sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans (half_lt_self Real.pi_pos))).ne'

private theorem sturmNodalIntervalGuardPlant :
    ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, Real.sin (2 * x) = 0 := by
  refine ⟨Real.pi / 2, ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩, ?_⟩
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

private theorem sturmPotentialMismatchPlant
    (GLo GHi ΛLo ΛHi x u v : ℝ) :
    u * ((GHi * x ^ 2 - (ΛHi + GHi)) * v) -
        ((GLo * x ^ 2 - (ΛLo + GLo)) * u) * v =
      ((ΛLo - ΛHi) + (GHi - GLo) * (x ^ 2 - 1)) * u * v := by
  ring

private theorem sturmSingularEndpointGuardPlant :
    (-1 : ℝ) ∉ Set.Ioo (-1 : ℝ) 1 ∧
      (1 : ℝ) ∉ Set.Ioo (-1 : ℝ) 1 := by
  simp

private noncomputable def mode4FerrersSturmWronskian
    {mProject K : ℕ} {ΛLo ΛHi : ℝ}
    (SLo : Mode4FerrersRegularEvenProlateSolution mProject K ΛLo)
    (SHi : Mode4FerrersRegularEvenProlateSolution mProject K ΛHi)
    (x : ℝ) : ℝ :=
  (1 - x ^ 2) *
    (mode4FerrersSeries SLo.coefficients x *
        mode4FerrersFirstDerivativeSeries SHi.coefficients x -
      mode4FerrersFirstDerivativeSeries SLo.coefficients x *
        mode4FerrersSeries SHi.coefficients x)

private theorem mode4FerrersSturmWronskian_hasDerivAt
    {mProject K : ℕ} {ΛLo ΛHi x : ℝ}
    (SLo : Mode4FerrersRegularEvenProlateSolution mProject K ΛLo)
    (SHi : Mode4FerrersRegularEvenProlateSolution mProject K ΛHi)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (mode4FerrersSturmWronskian SLo SHi)
      ((ΛLo - ΛHi) *
        mode4FerrersSeries SLo.coefficients x *
        mode4FerrersSeries SHi.coefficients x)
      x := by
  have hLo :=
    SLo.ferrersSeries_hasDerivAt_firstDerivativeSeries x hx
  have hLo' :=
    SLo.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx
  have hHi :=
    SHi.ferrersSeries_hasDerivAt_firstDerivativeSeries x hx
  have hHi' :=
    SHi.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx
  have hFactor : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa [id_eq, mul_comm] using
      (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
  have hCross :
      HasDerivAt
        (fun y : ℝ =>
          mode4FerrersSeries SLo.coefficients y *
              mode4FerrersFirstDerivativeSeries SHi.coefficients y -
            mode4FerrersFirstDerivativeSeries SLo.coefficients y *
              mode4FerrersSeries SHi.coefficients y)
        (mode4FerrersFirstDerivativeSeries SLo.coefficients x *
              mode4FerrersFirstDerivativeSeries SHi.coefficients x +
            mode4FerrersSeries SLo.coefficients x *
              mode4FerrersSecondDerivativeSeries SHi.coefficients x -
          (mode4FerrersSecondDerivativeSeries SLo.coefficients x *
              mode4FerrersSeries SHi.coefficients x +
            mode4FerrersFirstDerivativeSeries SLo.coefficients x *
              mode4FerrersFirstDerivativeSeries SHi.coefficients x))
        x :=
    (hLo.mul hHi').sub (hLo'.mul hHi)
  have hRaw := hFactor.mul hCross
  have hODELo := SLo.prolateDifferentialEquation x hx
  have hODEHi := SHi.prolateDifferentialEquation x hx
  have hODELoMul := congrArg
    (fun z : ℝ => z * mode4FerrersSeries SHi.coefficients x) hODELo
  have hODEHiMul := congrArg
    (fun z : ℝ => mode4FerrersSeries SLo.coefficients x * z) hODEHi
  change HasDerivAt (mode4FerrersSturmWronskian SLo SHi) _ x at hRaw
  apply hRaw.congr_deriv
  ring_nf at hODELoMul hODEHiMul ⊢
  linarith

private theorem continuous_nonzero_on_interval_has_constant_sign
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hnz : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 < f x) ∨
      (∀ x ∈ Set.Ioo a b, f x < 0) := by
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by
    dsimp [c]
    constructor <;> linarith
  have hfc : f c ≠ 0 := hnz c hc
  rcases lt_or_gt_of_ne hfc with hfcNeg | hfcPos
  · right
    intro x hx
    have hfxNe : f x ≠ 0 := hnz x hx
    by_contra hnot
    have hfxPos : 0 < f x :=
      lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hfxNe)
    have hsub : Set.uIcc c x ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨hc.1.le, hc.2.le⟩ ⟨hx.1.le, hx.2.le⟩
    have hzero : (0 : ℝ) ∈ Set.uIcc (f c) (f x) :=
      Set.mem_uIcc_of_le hfcNeg.le hfxPos.le
    obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_uIcc (hcont.mono hsub) hzero
    have hzOpen : z ∈ Set.Ioo a b := by
      rw [Set.mem_uIcc] at hz
      rcases hz with hz | hz <;> constructor <;> linarith [hc.1, hc.2, hx.1, hx.2]
    exact (hnz z hzOpen) hz0
  · left
    intro x hx
    have hfxNe : f x ≠ 0 := hnz x hx
    by_contra hnot
    have hfxNeg : f x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hnot) hfxNe
    have hsub : Set.uIcc x c ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨hx.1.le, hx.2.le⟩ ⟨hc.1.le, hc.2.le⟩
    have hzero : (0 : ℝ) ∈ Set.uIcc (f x) (f c) :=
      Set.mem_uIcc_of_le hfxNeg.le hfcPos.le
    obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_uIcc (hcont.mono hsub) hzero
    have hzOpen : z ∈ Set.Ioo a b := by
      rw [Set.mem_uIcc] at hz
      rcases hz with hz | hz <;> constructor <;> linarith [hc.1, hc.2, hx.1, hx.2]
    exact (hnz z hzOpen) hz0

private theorem derivative_pos_at_left_zero_of_pos_right
    {f : ℝ → ℝ} {f' a b : ℝ}
    (hab : a < b)
    (hf : HasDerivAt f f' a)
    (hfa : f a = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)
    (hf'Ne : f' ≠ 0) :
    0 < f' := by
  have htend : Filter.Tendsto (slope f a) (nhdsWithin a (Set.Ioi a)) (nhds f') :=
    (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
      (nhdsWithin_mono a (by
        intro x hx
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hx)))
  have hIio : Set.Iio b ∈ nhdsWithin a (Set.Ioi a) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)
  have hevent : ∀ᶠ x in nhdsWithin a (Set.Ioi a), 0 ≤ slope f a x := by
    filter_upwards [self_mem_nhdsWithin, hIio] with x hax hxb
    rw [slope_def_field, hfa]
    simpa only [sub_zero] using
      div_nonneg (hpos x ⟨hax, hxb⟩).le (sub_nonneg.mpr hax.le)
  have hf'Nonneg : 0 ≤ f' := ge_of_tendsto htend hevent
  exact lt_of_le_of_ne hf'Nonneg (Ne.symm hf'Ne)

private theorem derivative_neg_at_right_zero_of_pos_left
    {f : ℝ → ℝ} {f' a b : ℝ}
    (hab : a < b)
    (hf : HasDerivAt f f' b)
    (hfb : f b = 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)
    (hf'Ne : f' ≠ 0) :
    f' < 0 := by
  have htend : Filter.Tendsto (slope f b) (nhdsWithin b (Set.Iio b)) (nhds f') :=
    (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
      (nhdsWithin_mono b (by
        intro x hx
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_lt hx)))
  have hIoi : Set.Ioi a ∈ nhdsWithin b (Set.Iio b) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)
  have hevent : ∀ᶠ x in nhdsWithin b (Set.Iio b), slope f b x ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin, hIoi] with x hxb hax
    rw [slope_def_field, hfb]
    simpa only [sub_zero] using
      div_nonpos_of_nonneg_of_nonpos
        (hpos x ⟨hax, hxb⟩).le (sub_nonpos.mpr hxb.le)
  have hf'Nonpos : f' ≤ 0 := le_of_tendsto htend hevent
  exact lt_of_le_of_ne hf'Nonpos hf'Ne

private theorem value_nonneg_at_left_of_pos_right
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousAt f a)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    0 ≤ f a := by
  have htend : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds (f a)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hIio : Set.Iio b ∈ nhdsWithin a (Set.Ioi a) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)
  apply ge_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin, hIio] with x hax hxb
  exact (hpos x ⟨hax, hxb⟩).le

private theorem value_nonneg_at_right_of_pos_left
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousAt f b)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    0 ≤ f b := by
  have htend : Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds (f b)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hIoi : Set.Ioi a ∈ nhdsWithin b (Set.Iio b) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)
  apply ge_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin, hIoi] with x hxb hax
  exact (hpos x ⟨hax, hxb⟩).le

private theorem wronskian_strictAnti_on_nodal_interval
    {mProject K : ℕ} {ΛLo ΛHi x1 x2 su sv : ℝ}
    (SLo : Mode4FerrersRegularEvenProlateSolution mProject K ΛLo)
    (SHi : Mode4FerrersRegularEvenProlateSolution mProject K ΛHi)
    (hΛ : ΛLo < ΛHi)
    (hx1 : x1 ∈ Set.Ioo (-1 : ℝ) 1)
    (hx2 : x2 ∈ Set.Ioo (-1 : ℝ) 1)
    (hxx : x1 < x2)
    (hz1 : mode4FerrersSeries SLo.coefficients x1 = 0)
    (hz2 : mode4FerrersSeries SLo.coefficients x2 = 0)
    (hsu : su ≠ 0)
    (huPos :
      ∀ x ∈ Set.Ioo x1 x2,
        0 < su * mode4FerrersSeries SLo.coefficients x)
    (hvPos :
      ∀ x ∈ Set.Ioo x1 x2,
        0 < sv * mode4FerrersSeries SHi.coefficients x) :
    False := by
  let scaledW : ℝ → ℝ := fun x =>
    (su * sv) * mode4FerrersSturmWronskian SLo SHi x
  have hGlobal : Set.Icc x1 x2 ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨hx1.1.trans_le hx.1, hx.2.trans_lt hx2.2⟩
  have hScaledDeriv :
      ∀ x ∈ Set.Icc x1 x2,
        HasDerivAt scaledW
          ((su * sv) * ((ΛLo - ΛHi) *
            mode4FerrersSeries SLo.coefficients x *
            mode4FerrersSeries SHi.coefficients x)) x := by
    intro x hx
    simpa [scaledW] using
      (mode4FerrersSturmWronskian_hasDerivAt SLo SHi (hGlobal hx)).const_mul
        (su * sv)
  have hScaledContinuous : ContinuousOn scaledW (Set.Icc x1 x2) :=
    fun x hx => (hScaledDeriv x hx).continuousAt.continuousWithinAt
  have hScaledStrictAnti : StrictAntiOn scaledW (Set.Icc x1 x2) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x1 x2) hScaledContinuous
    intro x hx
    have hxOpen : x ∈ Set.Ioo x1 x2 := by
      simpa [interior_Icc, hxx.ne] using hx
    have hxClosed : x ∈ Set.Icc x1 x2 := ⟨hxOpen.1.le, hxOpen.2.le⟩
    rw [(hScaledDeriv x hxClosed).deriv]
    have hprod :
        0 < (su * mode4FerrersSeries SLo.coefficients x) *
          (sv * mode4FerrersSeries SHi.coefficients x) :=
      mul_pos (huPos x hxOpen) (hvPos x hxOpen)
    have heq :
        (su * sv) * ((ΛLo - ΛHi) *
            mode4FerrersSeries SLo.coefficients x *
            mode4FerrersSeries SHi.coefficients x) =
          (ΛLo - ΛHi) *
            ((su * mode4FerrersSeries SLo.coefficients x) *
              (sv * mode4FerrersSeries SHi.coefficients x)) := by
      ring
    rw [heq]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hΛ) hprod
  have hLoDeriv1 :=
    SLo.ferrersSeries_hasDerivAt_firstDerivativeSeries x1 hx1
  have hLoDeriv2 :=
    SLo.ferrersSeries_hasDerivAt_firstDerivativeSeries x2 hx2
  have hScaledLoDeriv1 :
      HasDerivAt
        (fun x => su * mode4FerrersSeries SLo.coefficients x)
        (su * mode4FerrersFirstDerivativeSeries SLo.coefficients x1) x1 := by
    simpa using hLoDeriv1.const_mul su
  have hScaledLoDeriv2 :
      HasDerivAt
        (fun x => su * mode4FerrersSeries SLo.coefficients x)
        (su * mode4FerrersFirstDerivativeSeries SLo.coefficients x2) x2 := by
    simpa using hLoDeriv2.const_mul su
  have hLoFirstNe :
      mode4FerrersFirstDerivativeSeries SLo.coefficients x1 ≠ 0 := by
    rw [← hLoDeriv1.deriv]
    exact SLo.interior_zero_simple hx1 hz1
  have hLoSecondNe :
      mode4FerrersFirstDerivativeSeries SLo.coefficients x2 ≠ 0 := by
    rw [← hLoDeriv2.deriv]
    exact SLo.interior_zero_simple hx2 hz2
  have hLeftDerivPos :
      0 < su * mode4FerrersFirstDerivativeSeries SLo.coefficients x1 :=
    derivative_pos_at_left_zero_of_pos_right hxx hScaledLoDeriv1
      (by simp [hz1]) huPos (mul_ne_zero hsu hLoFirstNe)
  have hRightDerivNeg :
      su * mode4FerrersFirstDerivativeSeries SLo.coefficients x2 < 0 :=
    derivative_neg_at_right_zero_of_pos_left hxx hScaledLoDeriv2
      (by simp [hz2]) huPos (mul_ne_zero hsu hLoSecondNe)
  have hHiDeriv1 :=
    SHi.ferrersSeries_hasDerivAt_firstDerivativeSeries x1 hx1
  have hHiDeriv2 :=
    SHi.ferrersSeries_hasDerivAt_firstDerivativeSeries x2 hx2
  have hScaledHiValue1 :
      0 ≤ sv * mode4FerrersSeries SHi.coefficients x1 :=
    value_nonneg_at_left_of_pos_right
      (f := fun x => sv * mode4FerrersSeries SHi.coefficients x)
      (a := x1) (b := x2) hxx
      (by simpa using (hHiDeriv1.const_mul sv).continuousAt) hvPos
  have hScaledHiValue2 :
      0 ≤ sv * mode4FerrersSeries SHi.coefficients x2 :=
    value_nonneg_at_right_of_pos_left
      (f := fun x => sv * mode4FerrersSeries SHi.coefficients x)
      (a := x1) (b := x2) hxx
      (by simpa using (hHiDeriv2.const_mul sv).continuousAt) hvPos
  have hFactor1 : 0 < 1 - x1 ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hx1.2) (by linarith [hx1.1] : 0 < x1 + 1)]
  have hFactor2 : 0 < 1 - x2 ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hx2.2) (by linarith [hx2.1] : 0 < x2 + 1)]
  have hLeftEq :
      scaledW x1 =
        -(1 - x1 ^ 2) *
          ((su * mode4FerrersFirstDerivativeSeries SLo.coefficients x1) *
            (sv * mode4FerrersSeries SHi.coefficients x1)) := by
    dsimp [scaledW, mode4FerrersSturmWronskian]
    rw [hz1]
    ring
  have hRightEq :
      scaledW x2 =
        -(1 - x2 ^ 2) *
          ((su * mode4FerrersFirstDerivativeSeries SLo.coefficients x2) *
            (sv * mode4FerrersSeries SHi.coefficients x2)) := by
    dsimp [scaledW, mode4FerrersSturmWronskian]
    rw [hz2]
    ring
  have hLeftNonpos : scaledW x1 ≤ 0 := by
    rw [hLeftEq]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hFactor1.le)
      (mul_nonneg hLeftDerivPos.le hScaledHiValue1)
  have hRightNonneg : 0 ≤ scaledW x2 := by
    rw [hRightEq]
    exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr hFactor2.le)
      (mul_nonpos_of_nonpos_of_nonneg hRightDerivNeg.le hScaledHiValue2)
  have hDecrease : scaledW x2 < scaledW x1 :=
    hScaledStrictAnti (Set.left_mem_Icc.mpr hxx.le)
      (Set.right_mem_Icc.mpr hxx.le) hxx
  linarith

/-- If two accepted mode-four Ferrers solutions share the same prolate
potential and the higher spectral parameter has no zero inside a nodal
interval of the lower solution, their weighted Wronskian is forced to be both
strictly decreasing and bounded in the opposite direction at the endpoints.
Hence the higher-parameter solution has an interior zero. -/
theorem exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval
    {mProject K : ℕ}
    {ΛLo ΛHi x1 x2 : ℝ}
    (SLo :
      Mode4FerrersRegularEvenProlateSolution
        mProject K ΛLo)
    (SHi :
      Mode4FerrersRegularEvenProlateSolution
        mProject K ΛHi)
    (hΛ : ΛLo < ΛHi)
    (hx1 : x1 ∈ Set.Ioo (-1 : ℝ) 1)
    (hx2 : x2 ∈ Set.Ioo (-1 : ℝ) 1)
    (hxx : x1 < x2)
    (hz1 :
      mode4FerrersSeries SLo.coefficients x1 = 0)
    (hz2 :
      mode4FerrersSeries SLo.coefficients x2 = 0)
    (hNodal :
      ∀ x ∈ Set.Ioo x1 x2,
        mode4FerrersSeries SLo.coefficients x ≠ 0) :
    ∃ x ∈ Set.Ioo x1 x2,
      mode4FerrersSeries SHi.coefficients x = 0 := by
  by_contra hNoZero
  have hHiNonzero :
      ∀ x ∈ Set.Ioo x1 x2,
        mode4FerrersSeries SHi.coefficients x ≠ 0 := by
    intro x hx hz
    exact hNoZero ⟨x, hx, hz⟩
  have hsub : Set.Icc x1 x2 ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨hx1.1.le.trans hx.1, hx.2.trans hx2.2.le⟩
  have hLoSign :=
    continuous_nonzero_on_interval_has_constant_sign hxx
      (SLo.continuousOn_closed.mono hsub) hNodal
  have hHiSign :=
    continuous_nonzero_on_interval_has_constant_sign hxx
      (SHi.continuousOn_closed.mono hsub) hHiNonzero
  rcases hLoSign with hLoPos | hLoNeg
  · rcases hHiSign with hHiPos | hHiNeg
    · exact wronskian_strictAnti_on_nodal_interval (su := (1 : ℝ)) (sv := (1 : ℝ))
        SLo SHi hΛ hx1 hx2 hxx
        hz1 hz2 (by norm_num)
        (by simpa using hLoPos) (by simpa using hHiPos)
    · exact wronskian_strictAnti_on_nodal_interval (su := (1 : ℝ)) (sv := (-1 : ℝ))
        SLo SHi hΛ hx1 hx2 hxx
        hz1 hz2 (by norm_num)
        (by simpa using hLoPos) (by
          intro x hx
          have := hHiNeg x hx
          simpa using (neg_pos.mpr this))
  · rcases hHiSign with hHiPos | hHiNeg
    · exact wronskian_strictAnti_on_nodal_interval (su := (-1 : ℝ)) (sv := (1 : ℝ))
        SLo SHi hΛ hx1 hx2 hxx
        hz1 hz2 (by norm_num)
        (by
          intro x hx
          have := hLoNeg x hx
          simpa using (neg_pos.mpr this))
        (by simpa using hHiPos)
    · exact wronskian_strictAnti_on_nodal_interval (su := (-1 : ℝ)) (sv := (-1 : ℝ))
        SLo SHi hΛ hx1 hx2 hxx
        hz1 hz2 (by norm_num)
        (by
          intro x hx
          have := hLoNeg x hx
          simpa using (neg_pos.mpr this))
        (by
          intro x hx
          have := hHiNeg x hx
          simpa using (neg_pos.mpr this))

#print axioms exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval

end Q3.RouteB
