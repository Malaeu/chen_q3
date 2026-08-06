import Q3.Proofs.RouteB.D0KTrialStage1
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

private theorem lambda_m_one_lt (i : PairIndex) :
    1 < lambda_m i := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  simpa [lambda_m] using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
      Real.sqrt 1 < Real.sqrt i.m)

private theorem lambda_m_pos (i : PairIndex) :
    0 < lambda_m i :=
  zero_lt_one.trans (lambda_m_one_lt i)

private theorem lambda_m_mul_self (i : PairIndex) :
    lambda_m i * lambda_m i = (i.m : ℝ) := by
  rw [lambda_m, Real.mul_self_sqrt]
  positivity

private theorem logWindow_image (i : PairIndex) :
    (fun u : ℝ => Real.log (lambda_m i * u)) '' I_m i =
      Set.Icc 0 (L_m i) := by
  have hlam : 0 < lambda_m i := lambda_m_pos i
  have hlam_one : 1 < lambda_m i := lambda_m_one_lt i
  have hab : (lambda_m i)⁻¹ ≤ lambda_m i := by
    calc
      (lambda_m i)⁻¹ ≤ 1 := (inv_le_one₀ hlam).2 hlam_one.le
      _ ≤ lambda_m i := hlam_one.le
  have hcont :
      ContinuousOn
        (fun u : ℝ => Real.log (lambda_m i * u))
        (Set.Icc (lambda_m i)⁻¹ (lambda_m i)) := by
    apply (continuousOn_const.mul continuousOn_id).log
    intro u hu
    exact ne_of_gt (mul_pos hlam ((inv_pos.mpr hlam).trans_le hu.1))
  have hmono :
      MonotoneOn
        (fun u : ℝ => Real.log (lambda_m i * u))
        (Set.Icc (lambda_m i)⁻¹ (lambda_m i)) := by
    intro a ha b hb hab'
    exact Real.strictMonoOn_log.monotoneOn
      (mul_pos hlam ((inv_pos.mpr hlam).trans_le ha.1))
      (mul_pos hlam ((inv_pos.mpr hlam).trans_le hb.1))
      (mul_le_mul_of_nonneg_left hab' hlam.le)
  rw [I_m]
  rw [hcont.image_Icc_of_monotoneOn hab hmono]
  have hlam_ne : lambda_m i ≠ 0 := ne_of_gt hlam
  rw [mul_inv_cancel₀ hlam_ne, Real.log_one, lambda_m_mul_self]
  rfl

private theorem logWindow_hasDerivWithinAt
    (i : PairIndex) (u : ℝ) (hu : u ∈ I_m i) :
    HasDerivWithinAt
      (fun v : ℝ => Real.log (lambda_m i * v))
      u⁻¹ (I_m i) u := by
  have hlam : 0 < lambda_m i := lambda_m_pos i
  have hu_pos : 0 < u := by
    exact (inv_pos.mpr hlam).trans_le hu.1
  have hmul :
      HasDerivAt (fun v : ℝ => lambda_m i * v) (lambda_m i) u := by
    simpa only [id_eq, mul_one] using
      (HasDerivAt.const_mul (lambda_m i) (hasDerivAt_id u))
  have hlog :=
    (Real.hasDerivAt_log (mul_ne_zero hlam.ne' hu_pos.ne')).comp u hmul
  convert hlog.hasDerivWithinAt using 1
  field_simp

private theorem logWindow_monotoneOn (i : PairIndex) :
    MonotoneOn
      (fun u : ℝ => Real.log (lambda_m i * u))
      (I_m i) := by
  have hlam : 0 < lambda_m i := lambda_m_pos i
  intro a ha b hb hab
  exact Real.strictMonoOn_log.monotoneOn
    (mul_pos hlam ((inv_pos.mpr hlam).trans_le ha.1))
    (mul_pos hlam ((inv_pos.mpr hlam).trans_le hb.1))
    (mul_le_mul_of_nonneg_left hab hlam.le)

/-- Exact source-locked logarithmic transport
`L²([lambda_m⁻¹,lambda_m],du/u) -> L²([0,L_m],dx)` at the scalar
integral level.  The statement is unrestricted in `F`; Mathlib's
monotone change-of-variables theorem handles the non-integrable case by the
Bochner-integral convention on both sides. -/
theorem integral_comp_logWindow_dStar
    (i : PairIndex) (F : ℝ → ℂ) :
    (∫ u : ℝ, F (Real.log (lambda_m i * u))
      ∂(dStar.restrict (I_m i))) =
      ∫ x : ℝ in Set.Icc 0 (L_m i), F x := by
  have hlam : 0 < lambda_m i := lambda_m_pos i
  have hdensity_meas :
      Measurable (fun u : ℝ => ENNReal.ofReal u⁻¹) :=
    measurable_inv.ennreal_ofReal
  have hdensity_top :
      ∀ᵐ u : ℝ ∂(volume.restrict (I_m i)),
        ENNReal.ofReal u⁻¹ < ⊤ := by
    filter_upwards [] with u
    exact ENNReal.ofReal_lt_top
  have hweighted :
      (∫ u : ℝ, F (Real.log (lambda_m i * u))
          ∂(dStar.restrict (I_m i))) =
        ∫ u : ℝ in I_m i,
          u⁻¹ • F (Real.log (lambda_m i * u)) := by
    rw [dStar]
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      hdensity_meas hdensity_top _ measurableSet_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    have hu_pos : 0 < u :=
      (inv_pos.mpr hlam).trans_le hu.1
    change (ENNReal.ofReal u⁻¹).toReal •
        F (Real.log (lambda_m i * u)) =
      u⁻¹ • F (Real.log (lambda_m i * u))
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hu_pos.le)]
  have hchange :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      (f := fun u : ℝ => Real.log (lambda_m i * u))
      (f' := fun u : ℝ => u⁻¹)
      (s := I_m i)
      measurableSet_Icc
      (logWindow_hasDerivWithinAt i)
      (logWindow_monotoneOn i)
      F
  rw [logWindow_image i] at hchange
  exact hweighted.trans hchange.symm

private theorem pointwise_V_mode_inner
    (i : PairIndex) (n r : ℤ) (x : ℝ) :
    inner ℂ
        (((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * n * (x / L_m i)))
        (((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * r * (x / L_m i))) =
      ((L_m i)⁻¹ : ℂ) *
        Complex.exp
          (2 * Real.pi * Complex.I * (r - n) * (x / L_m i)) := by
  rw [RCLike.inner_apply']
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_inv₀, Complex.conj_ofReal, map_mul, map_ofNat,
    Complex.conj_I, map_intCast, map_div₀]
  rw [mul_mul_mul_comm]
  rw [← Complex.exp_add]
  congr 1
  · norm_cast
    have hsqrt_ne : Real.sqrt (L_m i) ≠ 0 :=
      (Real.sqrt_pos.mpr (logLength_pos i)).ne'
    field_simp [hsqrt_ne, (logLength_pos i).ne']
    exact (Real.sq_sqrt (logLength_pos i).le).symm
  · ring_nf

private theorem logWindow_mode_inner_integral
    (i : PairIndex) (n r : ℤ) :
    (∫ x : ℝ in Set.Icc 0 (L_m i),
      ((L_m i)⁻¹ : ℂ) *
        Complex.exp
          (2 * Real.pi * Complex.I * (r - n) * (x / L_m i))) =
      if n = r then 1 else 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (logLength_pos i).le]
  by_cases hnr : n = r
  · subst r
    simp [(logLength_pos i).ne']
  · rw [if_neg hnr]
    rw [intervalIntegral.integral_const_mul]
    have hdiff : (r - n : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hnr)
    have hLne : (L_m i : ℂ) ≠ 0 := by
      exact_mod_cast (logLength_pos i).ne'
    have hc :
        (2 * Real.pi * Complex.I * (r - n : ℂ) / (L_m i : ℂ)) ≠ 0 := by
      apply div_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
          · exact Complex.I_ne_zero
        · exact_mod_cast hdiff
      · exact hLne
    have hphase :
        (fun x : ℝ =>
          Complex.exp
            (2 * Real.pi * Complex.I * (r - n) * (x / L_m i))) =
          (fun x : ℝ =>
            Complex.exp
              ((2 * Real.pi * Complex.I * (r - n : ℂ) /
                (L_m i : ℂ)) * x)) := by
      funext x
      congr 1
      field_simp [hLne]
    rw [hphase, integral_exp_mul_complex hc]
    have hupper :
        Complex.exp
            ((2 * Real.pi * Complex.I * (r - n : ℂ) /
              (L_m i : ℂ)) * (L_m i : ℂ)) = 1 := by
      rw [div_mul_cancel₀ _ hLne]
      convert Complex.exp_int_mul_two_pi_mul_I (r - n) using 2
      push_cast
      ring
    rw [hupper]
    simp

/-- The literal source-locked logarithmic Fourier modes form an orthonormal
family in `H_m`.  The frequency difference is `r-n`, fixed by conjugate
linearity in the first inner-product argument. -/
theorem V_n_m_orthonormal (i : PairIndex) :
    Orthonormal ℂ (V_n_m i) := by
  rw [orthonormal_iff_ite]
  intro n r
  rw [MeasureTheory.L2.inner_def]
  have hn_ae :
      (V_n_m i n : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    apply MemLp.coeFn_toLp
  have hr_ae :
      (V_n_m i r : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * r *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    apply MemLp.coeFn_toLp
  calc
    _ = ∫ u : ℝ,
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n *
                  (Real.log (lambda_m i * u) / L_m i)))
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * r *
                  (Real.log (lambda_m i * u) / L_m i)))
            ∂(dStar.restrict (I_m i)) := by
      apply integral_congr_ae
      filter_upwards [hn_ae, hr_ae] with u hnu hru
      rw [hnu, hru]
    _ = ∫ x : ℝ in Set.Icc 0 (L_m i),
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i)))
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * r * (x / L_m i))) := by
      simpa only [Complex.ofReal_div] using
        (integral_comp_logWindow_dStar i
          (fun x : ℝ =>
            inner ℂ
              (((Real.sqrt (L_m i))⁻¹ : ℂ) *
                Complex.exp
                  (2 * Real.pi * Complex.I * n *
                    ((x : ℂ) / (L_m i : ℂ))))
              (((Real.sqrt (L_m i))⁻¹ : ℂ) *
                Complex.exp
                  (2 * Real.pi * Complex.I * r *
                    ((x : ℂ) / (L_m i : ℂ))))))
    _ = ∫ x : ℝ in Set.Icc 0 (L_m i),
          ((L_m i)⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * (r - n) * (x / L_m i)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      exact pointwise_V_mode_inner i n r x
    _ = if n = r then 1 else 0 :=
      logWindow_mode_inner_integral i n r

#print axioms integral_comp_logWindow_dStar
#print axioms V_n_m_orthonormal

end Q3.RouteB.D0Pstar
