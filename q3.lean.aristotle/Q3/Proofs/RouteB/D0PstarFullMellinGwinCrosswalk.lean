import Q3.Proofs.RouteB.D0PstarProjectedMellinCoordinate

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# Selected full Mellin/Gwin crosswalk

This is Goal 056 / Phase 4F.  The module gives the literal unnormalized full
`gTrial_m` object its multiplicative Mellin coordinate and identifies that
coordinate with the selected Müntz `Gwin` convention.  The only normalized
statement is the definitionally algebraic scaled corollary.

No residual-integral linearity, Phase-4B contract, decay statement, `SlotS2`,
route promotion, or RH claim is proved here.
-/

/-- The multiplicative Mellin coordinate of the literal unnormalized full D0
trial on the selected source window. -/
noncomputable def selectedFullMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  ∫ u : ℝ,
      (gTrial_m i h hLp : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))

/-- The literal unnormalized full D0 coordinate is exactly the selected Müntz
window transform at argument `-i*z`. -/
theorem selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedFullMellinCoordinate S k z =
      selectedGwinTransformCoordinate S k z := by
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam_one : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam_pos : 0 < lambda_m i := zero_lt_one.trans hlam_one
  have hrep :
      (fun u : ℝ => (gTrial_m i h hLp : H_m i) u)
        =ᵐ[dStar.restrict (I_m i)]
      E_star h := by
    unfold gTrial_m
    apply MemLp.coeFn_toLp
  have hdensity_meas :
      Measurable (fun u : ℝ => ENNReal.ofReal u⁻¹) :=
    measurable_inv.ennreal_ofReal
  have hdensity_top :
      ∀ᵐ u : ℝ ∂(volume.restrict (I_m i)),
        ENNReal.ofReal u⁻¹ < ⊤ := by
    filter_upwards [] with u
    exact ENNReal.ofReal_lt_top
  calc
    selectedFullMellinCoordinate S k z =
        ∫ u : ℝ,
          (gTrial_m i h hLp : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by
            rfl
    _ = ∫ u : ℝ,
          E_star h u * (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by
            apply integral_congr_ae
            filter_upwards [hrep] with u hu
            rw [hu]
    _ = ∫ u : ℝ in I_m i,
          u⁻¹ • (E_star h u * (u : ℂ) ^ (-Complex.I * z)) := by
            rw [dStar]
            rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
              hdensity_meas hdensity_top _ measurableSet_Icc]
            apply setIntegral_congr_fun measurableSet_Icc
            intro u hu
            have hu_pos : 0 < u :=
              (inv_pos.mpr hlam_pos).trans_le hu.1
            change (ENNReal.ofReal u⁻¹).toReal •
                (E_star h u * (u : ℂ) ^ (-Complex.I * z)) =
              u⁻¹ • (E_star h u * (u : ℂ) ^ (-Complex.I * z))
            rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hu_pos.le)]
    _ = ∫ u : ℝ in I_m i,
          EStarMuntzZeroMassContinuation.Estar h u *
            (u : ℂ) ^ ((-Complex.I * z) - 1) := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro u hu
            have hu_pos : 0 < u :=
              (inv_pos.mpr hlam_pos).trans_le hu.1
            have hu_ne : (u : ℂ) ≠ 0 :=
              Complex.ofReal_ne_zero.mpr hu_pos.ne'
            change u⁻¹ •
                (E_star h u * (u : ℂ) ^ (-Complex.I * z)) =
              EStarMuntzZeroMassContinuation.Estar h u *
                (u : ℂ) ^ ((-Complex.I * z) - 1)
            rw [Complex.cpow_sub _ _ hu_ne, Complex.cpow_one]
            simp only [E_star,
              EStarMuntzZeroMassContinuation.Estar]
            rw [Complex.real_smul]
            push_cast
            rw [div_eq_mul_inv]
            ring
    _ = ∫ u : ℝ in Set.Ioo (lambda_m i)⁻¹ (lambda_m i),
          EStarMuntzZeroMassContinuation.Estar h u *
            (u : ℂ) ^ ((-Complex.I * z) - 1) := by
            rw [I_m, MeasureTheory.integral_Icc_eq_integral_Ioo]
    _ = selectedGwinTransformCoordinate S k z := by
            rfl

/-- Scaling the full-coordinate equality by the exact selected trial
normalizer gives the already locked scaled Müntz coordinate. -/
theorem
    selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    (selectedTrialNormalizer S k : ℂ) *
        selectedFullMellinCoordinate S k z =
      selectedScaledGwinTransformCoordinate S k z := by
  rw [selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate]
  rfl

#print axioms selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
#print axioms selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate

end Q3.RouteB.D0Pstar
