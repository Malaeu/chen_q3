import Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualContract
import Q3.Proofs.RouteB.D0PstarFullMellinGwinCrosswalk

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# Object-first Galerkin residual Mellin crosswalk

This is Goal 056 / Phase 4G.  The module proves integrability of the literal
`H_m` representative against the selected Mellin kernel, distributes the
literal normalized projection-minus-full residual coordinate, and then
discharges the Phase-4B named crosswalk contract unconditionally.

No scalar-surrogate residual, residual-decay estimate, compact-open limit,
strict `SlotS2`, route promotion, or RH claim is introduced here.
-/

/-- An `H_m` representative times the selected Mellin kernel is integrable on
the exact multiplicative window.

The proof uses only the finite `du/u` measure of the positive compact window,
the `L² -> L¹` inclusion on finite measure spaces, and compact boundedness
of the complex-power kernel.  It is private because the current production
consumer needs only the two exact selected-coordinate theorems below.
-/
private theorem integrable_H_m_mul_mellinKernel
    (i : PairIndex) (f : H_m i) (z : ℂ) :
    Integrable
      (fun u : ℝ => f u * (u : ℂ) ^ (-Complex.I * z))
      (dStar.restrict (I_m i)) := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam_one : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam_pos : 0 < lambda_m i := zero_lt_one.trans hlam_one
  have hinv :
      IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    apply ne_of_gt
    exact (inv_pos.mpr hlam_pos).trans_le hu.1
  letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      simpa [I_m] using hinv.setLIntegral_lt_top⟩
  have hf :
      Integrable (fun u : ℝ => f u) (dStar.restrict (I_m i)) :=
    (Lp.memLp f).integrable fact_one_le_two_ennreal.elim
  have hkernel_cont :
      ContinuousOn
        (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z))
        (I_m i) := by
    intro u hu
    have hu_pos : 0 < u :=
      (inv_pos.mpr hlam_pos).trans_le hu.1
    exact
      (Complex.continuousAt_ofReal_cpow_const
        u (-Complex.I * z) (Or.inr hu_pos.ne')).continuousWithinAt
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.bddAbove_image hkernel_cont.norm
  have hkernel_meas :
      AEStronglyMeasurable
        (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z))
        (dStar.restrict (I_m i)) :=
    hkernel_cont.aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc
  have hkernel_bound :
      ∀ᵐ u : ℝ ∂(dStar.restrict (I_m i)),
        ‖(u : ℂ) ^ (-Complex.I * z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hC (mem_image_of_mem _ hu)
  exact hf.mul_bdd hkernel_meas hkernel_bound

/-- The Mellin coordinate of the literal normalized Galerkin residual is the
projected coordinate minus the exactly normalized full coordinate.

The subtraction is performed only after both product integrands have been
proved integrable.  The `Lp` quotient relations are used only almost
everywhere; no raw-transform or `Gwin` equality enters this theorem.
-/
theorem selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedGalerkinResidualMellinCoordinate S k z =
      selectedProjectedMellinCoordinate S k z -
        (selectedTrialNormalizer S k : ℂ) *
          selectedFullMellinCoordinate S k z := by
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  let hNonzero := S.source.trialNonzero i
  let s : ℂ := selectedTrialNormalizer S k
  have hobject :
      selectedNormalizedGalerkinResidual S k =
        (kTrial_m_N i h hLp hNonzero : H_m i) -
          s • gTrial_m i h hLp := by
    simp only [selectedNormalizedGalerkinResidual, kTrial_m_N,
      selectedTrialNormalizer, i, h, s]
    rw [smul_sub]
    rfl
  have hres_rep :
      (fun u : ℝ => (selectedNormalizedGalerkinResidual S k) u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        (kTrial_m_N i h hLp hNonzero : H_m i) u -
          s * (gTrial_m i h hLp : H_m i) u) := by
    rw [hobject]
    filter_upwards
      [Lp.coeFn_sub
        (kTrial_m_N i h hLp hNonzero : H_m i)
        (s • gTrial_m i h hLp),
       Lp.coeFn_smul s (gTrial_m i h hLp)] with u hsub hsmul
    rw [hsub]
    change
      (kTrial_m_N i h hLp hNonzero : H_m i) u -
          (s • gTrial_m i h hLp : H_m i) u =
        (kTrial_m_N i h hLp hNonzero : H_m i) u -
          s * (gTrial_m i h hLp : H_m i) u
    rw [hsmul]
    rfl
  have hproj_int := integrable_H_m_mul_mellinKernel
    i (kTrial_m_N i h hLp hNonzero : H_m i) z
  have hfull_int := integrable_H_m_mul_mellinKernel
    i (gTrial_m i h hLp) z
  calc
    selectedGalerkinResidualMellinCoordinate S k z =
        ∫ u : ℝ,
          ((kTrial_m_N i h hLp hNonzero : H_m i) u -
            s * (gTrial_m i h hLp : H_m i) u) *
              (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by
            unfold selectedGalerkinResidualMellinCoordinate
            apply integral_congr_ae
            filter_upwards [hres_rep] with u hu
            rw [hu]
    _ = ∫ u : ℝ,
          (kTrial_m_N i h hLp hNonzero : H_m i) u *
              (u : ℂ) ^ (-Complex.I * z) -
            (s * (gTrial_m i h hLp : H_m i) u) *
              (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by
            congr 1
            funext u
            ring
    _ = (∫ u : ℝ,
          (kTrial_m_N i h hLp hNonzero : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i))) -
        ∫ u : ℝ,
          (s * (gTrial_m i h hLp : H_m i) u) *
            (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by
            rw [integral_sub hproj_int]
            simpa only [mul_assoc] using hfull_int.const_mul s
    _ = (∫ u : ℝ,
          (kTrial_m_N i h hLp hNonzero : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i))) -
        s * (∫ u : ℝ,
          (gTrial_m i h hLp : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i))) := by
            congr 1
            calc
              (∫ u : ℝ,
                  (s * (gTrial_m i h hLp : H_m i) u) *
                    (u : ℂ) ^ (-Complex.I * z)
                  ∂(dStar.restrict (I_m i))) =
                  ∫ u : ℝ,
                    s * ((gTrial_m i h hLp : H_m i) u *
                      (u : ℂ) ^ (-Complex.I * z))
                    ∂(dStar.restrict (I_m i)) := by
                      congr 1
                      funext u
                      ring
              _ = s * (∫ u : ℝ,
                    (gTrial_m i h hLp : H_m i) u *
                      (u : ℂ) ^ (-Complex.I * z)
                    ∂(dStar.restrict (I_m i))) := by
                      rw [integral_const_mul]
    _ = selectedProjectedMellinCoordinate S k z -
        s * selectedFullMellinCoordinate S k z := by
          rfl
    _ = selectedProjectedMellinCoordinate S k z -
        (selectedTrialNormalizer S k : ℂ) *
          selectedFullMellinCoordinate S k z := by
          rfl

/-- The Phase-4B named object-first residual crosswalk now holds
unconditionally for every selected source datum.

This theorem consumes the already-proved Phase-4E projected/raw equality and
Phase-4F scaled-full/Gwin equality only after the literal residual-coordinate
linearity theorem above has been established.
-/
theorem D0PstarMuntzGalerkinResidualCrosswalkContract_proved
    (S : ProlateCanonicalSourceData) :
    D0PstarMuntzGalerkinResidualCrosswalkContract S := by
  intro k z
  rw [selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull]
  rw [selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate]
  rw [
    selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate]
  rfl

#print axioms selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull
#print axioms D0PstarMuntzGalerkinResidualCrosswalkContract_proved

end Q3.RouteB.D0Pstar
