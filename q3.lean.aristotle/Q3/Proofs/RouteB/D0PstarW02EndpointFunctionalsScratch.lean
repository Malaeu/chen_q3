import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
import Q3.Proofs.RouteB.D0PstarSourceW02ModePairing

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace Q3.RouteB.D0Pstar

private theorem sourceW02EndpointPlusWeight_memLp
    (i : PairIndex) :
    MemLp (fun x : ℝ => (Real.exp (x / 2) : ℂ)) 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  apply MemLp.of_bound (by fun_prop) (Real.exp (L_m i / 2))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rcases hx with ⟨hx0, hxL⟩
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith)

private theorem sourceW02EndpointMinusWeight_memLp
    (i : PairIndex) :
    MemLp (fun x : ℝ => (Real.exp (-x / 2) : ℂ)) 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rcases hx with ⟨hx0, hxL⟩
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa using Real.exp_le_one_iff.mpr (by linarith)

private noncomputable def sourceW02EndpointPlusWeightLp
    (i : PairIndex) :
    MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
  (sourceW02EndpointPlusWeight_memLp i).toLp
    (fun x : ℝ => (Real.exp (x / 2) : ℂ))

private noncomputable def sourceW02EndpointMinusWeightLp
    (i : PairIndex) :
    MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
  (sourceW02EndpointMinusWeight_memLp i).toLp
    (fun x : ℝ => (Real.exp (-x / 2) : ℂ))

private theorem coeFn_sourceW02EndpointPlusWeightLp
    (i : PairIndex) :
    ((sourceW02EndpointPlusWeightLp i :
        MeasureTheory.Lp ℂ 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))]
        (fun x : ℝ => (Real.exp (x / 2) : ℂ)) := by
  exact MemLp.coeFn_toLp _

private theorem coeFn_sourceW02EndpointMinusWeightLp
    (i : PairIndex) :
    ((sourceW02EndpointMinusWeightLp i :
        MeasureTheory.Lp ℂ 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))]
        (fun x : ℝ => (Real.exp (-x / 2) : ℂ)) := by
  exact MemLp.coeFn_toLp _

/-- Bounded positive endpoint moment on the whole ambient Hilbert space. -/
noncomputable def sourceW02EndpointPlusFunctional
    (i : PairIndex) : H_m i →L[ℂ] ℂ :=
  (innerSL ℂ (sourceW02EndpointPlusWeightLp i)).comp
    (logWindowL2Equiv i).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Bounded negative endpoint moment on the whole ambient Hilbert space. -/
noncomputable def sourceW02EndpointMinusFunctional
    (i : PairIndex) : H_m i →L[ℂ] ℂ :=
  (innerSL ℂ (sourceW02EndpointMinusWeightLp i)).comp
    (logWindowL2Equiv i).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem sourceW02EndpointPlusFunctional_apply_eq_integral
    (i : PairIndex) (x : H_m i) :
    sourceW02EndpointPlusFunctional i x =
      ∫ t : ℝ in Set.Icc 0 (L_m i),
        (((logWindowL2Equiv i).symm x :
            MeasureTheory.Lp ℂ 2
              (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) t *
          (Real.exp (t / 2) : ℂ) := by
  rw [sourceW02EndpointPlusFunctional]
  change
    inner ℂ (sourceW02EndpointPlusWeightLp i)
        ((logWindowL2Equiv i).symm x) = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_sourceW02EndpointPlusWeightLp i] with t ht
  rw [ht]
  simp only [RCLike.inner_apply', Complex.conj_ofReal]
  ring

theorem sourceW02EndpointMinusFunctional_apply_eq_integral
    (i : PairIndex) (x : H_m i) :
    sourceW02EndpointMinusFunctional i x =
      ∫ t : ℝ in Set.Icc 0 (L_m i),
        (((logWindowL2Equiv i).symm x :
            MeasureTheory.Lp ℂ 2
              (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) t *
          (Real.exp (-t / 2) : ℂ) := by
  rw [sourceW02EndpointMinusFunctional]
  change
    inner ℂ (sourceW02EndpointMinusWeightLp i)
        ((logWindowL2Equiv i).symm x) = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_sourceW02EndpointMinusWeightLp i] with t ht
  rw [ht]
  simp only [RCLike.inner_apply', Complex.conj_ofReal]
  ring

/-!
The logarithmic inverse is not needed to obtain the source-mode values.  The
same two moments can be represented by bounded vectors directly in `H_m` and
then transported by the already-public scalar change-of-variables theorem.
This route avoids any dependency on the private implementation theorem behind
`logWindowL2Equiv`.
-/

private theorem sourceW02PhysicalEndpointPlusWeight_memLp
    (i : PairIndex) :
    MemLp
      (fun u : ℝ =>
        (Real.exp (Real.log (lambda_m i * u) / 2) : ℂ))
      2 (dStar.restrict (I_m i)) := by
  have hm_real : (0 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hlam : 0 < lambda_m i := by
    rw [lambda_m]
    exact Real.sqrt_pos.2 hm_real
  have hlam_sq : lambda_m i * lambda_m i = (i.m : ℝ) := by
    rw [lambda_m, Real.mul_self_sqrt]
    exact hm_real.le
  have hinv :
      IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    apply ne_of_gt
    exact (inv_pos.mpr hlam).trans_le hu.1
  letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      simpa [I_m] using hinv.setLIntegral_lt_top⟩
  have hmeas :
      Measurable
        (fun u : ℝ =>
          (Real.exp (Real.log (lambda_m i * u) / 2) : ℂ)) := by
    exact
      ((Real.measurable_exp.comp
        ((Real.measurable_log.comp
          (measurable_const.mul measurable_id)).div_const 2)).complex_ofReal)
  apply MemLp.of_bound hmeas.aestronglyMeasurable (Real.exp (L_m i / 2))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hu_pos : 0 < u :=
    (inv_pos.mpr hlam).trans_le hu.1
  have harg_pos : 0 < lambda_m i * u := mul_pos hlam hu_pos
  have harg_upper : lambda_m i * u ≤ (i.m : ℝ) := by
    calc
      lambda_m i * u ≤ lambda_m i * lambda_m i :=
        mul_le_mul_of_nonneg_left hu.2 hlam.le
      _ = (i.m : ℝ) := hlam_sq
  have hlog_upper :
      Real.log (lambda_m i * u) ≤ L_m i := by
    rw [show L_m i = Real.log (i.m : ℝ) by rfl]
    exact Real.strictMonoOn_log.monotoneOn harg_pos hm_real harg_upper
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith)

private theorem sourceW02PhysicalEndpointMinusWeight_memLp
    (i : PairIndex) :
    MemLp
      (fun u : ℝ =>
        (Real.exp (-Real.log (lambda_m i * u) / 2) : ℂ))
      2 (dStar.restrict (I_m i)) := by
  have hm_real : (0 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hlam : 0 < lambda_m i := by
    rw [lambda_m]
    exact Real.sqrt_pos.2 hm_real
  have hinv :
      IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    apply ne_of_gt
    exact (inv_pos.mpr hlam).trans_le hu.1
  letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      simpa [I_m] using hinv.setLIntegral_lt_top⟩
  have hmeas :
      Measurable
        (fun u : ℝ =>
          (Real.exp (-Real.log (lambda_m i * u) / 2) : ℂ)) := by
    exact
      ((Real.measurable_exp.comp
        ((Real.measurable_log.comp
          (measurable_const.mul measurable_id)).neg.div_const 2)).complex_ofReal)
  apply MemLp.of_bound hmeas.aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hu_pos : 0 < u :=
    (inv_pos.mpr hlam).trans_le hu.1
  have harg_lower : 1 ≤ lambda_m i * u := by
    calc
      1 = lambda_m i * (lambda_m i)⁻¹ := by
        exact (mul_inv_cancel₀ hlam.ne').symm
      _ ≤ lambda_m i * u :=
        mul_le_mul_of_nonneg_left hu.1 hlam.le
  have hlog_nonneg : 0 ≤ Real.log (lambda_m i * u) :=
    Real.log_nonneg harg_lower
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa using Real.exp_le_one_iff.mpr (by linarith)

private noncomputable def sourceW02PhysicalEndpointPlusWeight
    (i : PairIndex) : H_m i :=
  (sourceW02PhysicalEndpointPlusWeight_memLp i).toLp
    (fun u : ℝ =>
      (Real.exp (Real.log (lambda_m i * u) / 2) : ℂ))

private noncomputable def sourceW02PhysicalEndpointMinusWeight
    (i : PairIndex) : H_m i :=
  (sourceW02PhysicalEndpointMinusWeight_memLp i).toLp
    (fun u : ℝ =>
      (Real.exp (-Real.log (lambda_m i * u) / 2) : ℂ))

private theorem coeFn_sourceW02PhysicalEndpointPlusWeight
    (i : PairIndex) :
    ((sourceW02PhysicalEndpointPlusWeight i : H_m i) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          (Real.exp (Real.log (lambda_m i * u) / 2) : ℂ)) := by
  exact MemLp.coeFn_toLp _

private theorem coeFn_sourceW02PhysicalEndpointMinusWeight
    (i : PairIndex) :
    ((sourceW02PhysicalEndpointMinusWeight i : H_m i) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          (Real.exp (-Real.log (lambda_m i * u) / 2) : ℂ)) := by
  exact MemLp.coeFn_toLp _

/-- Positive endpoint moment represented directly on the physical window. -/
noncomputable def sourceW02PhysicalEndpointPlusFunctional
    (i : PairIndex) : H_m i →L[ℂ] ℂ :=
  innerSL ℂ (sourceW02PhysicalEndpointPlusWeight i)

/-- Negative endpoint moment represented directly on the physical window. -/
noncomputable def sourceW02PhysicalEndpointMinusFunctional
    (i : PairIndex) : H_m i →L[ℂ] ℂ :=
  innerSL ℂ (sourceW02PhysicalEndpointMinusWeight i)

theorem sourceW02PhysicalEndpointPlusFunctional_apply_eq_integral
    (i : PairIndex) (x : H_m i) :
    sourceW02PhysicalEndpointPlusFunctional i x =
      ∫ u : ℝ,
        (x : ℝ → ℂ) u *
          (Real.exp (Real.log (lambda_m i * u) / 2) : ℂ)
        ∂(dStar.restrict (I_m i)) := by
  rw [sourceW02PhysicalEndpointPlusFunctional]
  change inner ℂ (sourceW02PhysicalEndpointPlusWeight i) x = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_sourceW02PhysicalEndpointPlusWeight i] with u hu
  rw [hu]
  simp only [RCLike.inner_apply', Complex.conj_ofReal]
  ring

theorem sourceW02PhysicalEndpointMinusFunctional_apply_eq_integral
    (i : PairIndex) (x : H_m i) :
    sourceW02PhysicalEndpointMinusFunctional i x =
      ∫ u : ℝ,
        (x : ℝ → ℂ) u *
          (Real.exp (-Real.log (lambda_m i * u) / 2) : ℂ)
        ∂(dStar.restrict (I_m i)) := by
  rw [sourceW02PhysicalEndpointMinusFunctional]
  change inner ℂ (sourceW02PhysicalEndpointMinusWeight i) x = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_sourceW02PhysicalEndpointMinusWeight i] with u hu
  rw [hu]
  simp only [RCLike.inner_apply', Complex.conj_ofReal]
  ring

theorem sourceW02PhysicalEndpointPlusFunctional_apply_mode
    (i : PairIndex) (n : ℤ) :
    sourceW02PhysicalEndpointPlusFunctional i (V_n_m i n) =
      ∫ x in Set.Icc 0 (L_m i),
        logWindowZeroExtendedMode i n x *
          (Real.exp (x / 2) : ℂ) := by
  rw [sourceW02PhysicalEndpointPlusFunctional_apply_eq_integral]
  have hv :
      (V_n_m i n : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    exact MemLp.coeFn_toLp _
  calc
    (∫ u : ℝ,
        (V_n_m i n : ℝ → ℂ) u *
          (Real.exp (Real.log (lambda_m i * u) / 2) : ℂ)
        ∂(dStar.restrict (I_m i))) =
      ∫ u : ℝ,
        (fun x : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i)) *
            (Real.exp (x / 2) : ℂ))
          (Real.log (lambda_m i * u))
        ∂(dStar.restrict (I_m i)) := by
          apply integral_congr_ae
          filter_upwards [hv] with u hu
          rw [hu]
    _ = ∫ x in Set.Icc 0 (L_m i),
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i))) *
            (Real.exp (x / 2) : ℂ) := by
          simpa using
            (integral_comp_logWindow_dStar i
              (fun x : ℝ =>
                ((Real.sqrt (L_m i))⁻¹ : ℂ) *
                    Complex.exp
                      (2 * Real.pi * Complex.I * n * (x / L_m i)) *
                  (Real.exp (x / 2) : ℂ)))
    _ = ∫ x in Set.Icc 0 (L_m i),
          logWindowZeroExtendedMode i n x *
            (Real.exp (x / 2) : ℂ) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          rw [logWindowZeroExtendedMode, Set.indicator_of_mem hx]

theorem sourceW02PhysicalEndpointMinusFunctional_apply_mode
    (i : PairIndex) (n : ℤ) :
    sourceW02PhysicalEndpointMinusFunctional i (V_n_m i n) =
      ∫ x in Set.Icc 0 (L_m i),
        logWindowZeroExtendedMode i n x *
          (Real.exp (-x / 2) : ℂ) := by
  rw [sourceW02PhysicalEndpointMinusFunctional_apply_eq_integral]
  have hv :
      (V_n_m i n : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    exact MemLp.coeFn_toLp _
  calc
    (∫ u : ℝ,
        (V_n_m i n : ℝ → ℂ) u *
          (Real.exp (-Real.log (lambda_m i * u) / 2) : ℂ)
        ∂(dStar.restrict (I_m i))) =
      ∫ u : ℝ,
        (fun x : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i)) *
            (Real.exp (-x / 2) : ℂ))
          (Real.log (lambda_m i * u))
        ∂(dStar.restrict (I_m i)) := by
          apply integral_congr_ae
          filter_upwards [hv] with u hu
          rw [hu]
    _ = ∫ x in Set.Icc 0 (L_m i),
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i))) *
            (Real.exp (-x / 2) : ℂ) := by
          simpa using
            (integral_comp_logWindow_dStar i
              (fun x : ℝ =>
                ((Real.sqrt (L_m i))⁻¹ : ℂ) *
                    Complex.exp
                      (2 * Real.pi * Complex.I * n * (x / L_m i)) *
                  (Real.exp (-x / 2) : ℂ)))
    _ = ∫ x in Set.Icc 0 (L_m i),
          logWindowZeroExtendedMode i n x *
            (Real.exp (-x / 2) : ℂ) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          rw [logWindowZeroExtendedMode, Set.indicator_of_mem hx]

#print axioms sourceW02EndpointPlusFunctional
#print axioms sourceW02EndpointMinusFunctional
#print axioms sourceW02EndpointPlusFunctional_apply_eq_integral
#print axioms sourceW02EndpointMinusFunctional_apply_eq_integral
#print axioms sourceW02PhysicalEndpointPlusFunctional
#print axioms sourceW02PhysicalEndpointMinusFunctional
#print axioms sourceW02PhysicalEndpointPlusFunctional_apply_mode
#print axioms sourceW02PhysicalEndpointMinusFunctional_apply_mode

end Q3.RouteB.D0Pstar
