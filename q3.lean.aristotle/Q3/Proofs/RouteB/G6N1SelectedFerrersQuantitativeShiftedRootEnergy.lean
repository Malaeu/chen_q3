import Q3.Proofs.RouteB.G6N1SelectedFerrersFixedKShiftedRootEnergy
import Q3.Proofs.RouteB.D0PstarSourceWeilOddTailExplicitCoercivity

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 2400000

open Complex Filter MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Selected Ferrers quantitative shifted root energy

This is the first W5 extraction from the fixed-`k` W4 theorem.  It exposes the
exact Fourier-decay budget already used by W4 and bounds the literal shifted
archimedean energy by one universal integrable envelope times the square of
that budget.  The remaining cofinal problem is therefore an estimate on the
explicit packet `L¹`, derivative and jump ledgers; no uniform rate is asserted
here.
-/

/-- The explicit decay budget constructed in W4: the ordinary `L¹` mass plus
the derivative and repaired jump ledgers. -/
noncomputable def selectedFerrersAbelFourierDecayBudget (k : ℕ) : ℝ :=
  2 *
    ((∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖) +
      (selectedFerrersAbelLogDerivativeBudget k +
        selectedFerrersAbelLogJumpBudget k) / (2 * Real.pi))

private theorem selectedFerrersAbelLogDerivativeBudget_nonneg' (k : ℕ) :
    0 ≤ selectedFerrersAbelLogDerivativeBudget k := by
  unfold selectedFerrersAbelLogDerivativeBudget
  exact intervalIntegral.integral_nonneg_of_forall
    (logLength_pos (selectedFerrersPreAnchorIndex k)).le
    (fun x => norm_nonneg _)

private theorem selectedFerrersAbelLogJumpBudget_nonneg' (k : ℕ) :
    0 ≤ selectedFerrersAbelLogJumpBudget k := by
  unfold selectedFerrersAbelLogJumpBudget
  positivity

theorem selectedFerrersAbelFourierDecayBudget_nonneg (k : ℕ) :
    0 ≤ selectedFerrersAbelFourierDecayBudget k := by
  unfold selectedFerrersAbelFourierDecayBudget
  have hA : 0 ≤ ∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖ :=
    integral_nonneg_of_ae (Eventually.of_forall fun x => norm_nonneg _)
  positivity [selectedFerrersAbelLogDerivativeBudget_nonneg' k,
    selectedFerrersAbelLogJumpBudget_nonneg' k]

private theorem selectedFerrersAbelLogZeroExtension_fourier_norm_le_integral_norm'
    (k : ℕ) (t : ℝ) :
    ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
      ∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖ := by
  rw [Real.fourier_eq]
  calc
    ‖∫ x : ℝ, Real.fourierChar (-⟪x, t⟫) •
        selectedFerrersAbelLogZeroExtension k x‖ ≤
        ∫ x : ℝ, ‖Real.fourierChar (-⟪x, t⟫) •
          selectedFerrersAbelLogZeroExtension k x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]

/-- The W4 pointwise decay theorem with its actual constructed constant rather
than an existential witness. -/
theorem selectedFerrersAbelLogZeroExtension_fourier_decay_quantitative
    (k : ℕ) (t : ℝ) :
    ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
      selectedFerrersAbelFourierDecayBudget k / (1 + |t|) := by
  let A : ℝ := ∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖
  let D : ℝ :=
    (selectedFerrersAbelLogDerivativeBudget k +
      selectedFerrersAbelLogJumpBudget k) / (2 * Real.pi)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg_of_ae (Eventually.of_forall fun x => norm_nonneg _)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity [selectedFerrersAbelLogDerivativeBudget_nonneg' k,
      selectedFerrersAbelLogJumpBudget_nonneg' k]
  have hden : 0 < 1 + |t| := by positivity
  change ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
    (2 * (A + D)) / (1 + |t|)
  by_cases ht : |t| ≤ 1
  · have hfour :=
      selectedFerrersAbelLogZeroExtension_fourier_norm_le_integral_norm' k t
    change ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤ A at hfour
    apply hfour.trans
    apply (le_div_iff₀ hden).2
    nlinarith [abs_nonneg t]
  · have ht1 : 1 < |t| := lt_of_not_ge ht
    have ht0 : t ≠ 0 := abs_pos.mp (by linarith)
    have hfour := selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
      k ht0
    have hrewrite :
        (selectedFerrersAbelLogDerivativeBudget k +
          selectedFerrersAbelLogJumpBudget k) /
            (2 * Real.pi * |t|) = D / |t| := by
      dsimp only [D]
      field_simp
    rw [hrewrite] at hfour
    apply hfour.trans
    apply (div_le_div_iff₀ (abs_pos.mpr ht0) hden).2
    nlinarith [abs_nonneg t]

/-- The universal (index-independent) integral left after the literal shifted
archimedean symbol is dominated by the W4 Fourier envelope. -/
noncomputable def selectedFerrersShiftedEnergyUniversalIntegral : ℝ :=
  ∫ t : ℝ,
    (vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2

theorem selectedFerrersShiftedEnergyUniversalIntegral_nonneg :
    0 ≤ selectedFerrersShiftedEnergyUniversalIntegral := by
  unfold selectedFerrersShiftedEnergyUniversalIntegral
  exact integral_nonneg_of_ae
    (Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem selectedFerrersShiftedEnergyUniversalIntegral_finite :
    Integrable (fun t : ℝ =>
      (vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2) :=
  vModeLogGrowthEnvelope_sq_div_one_add_abs_sq_integrable

/-- The fully explicit W5 majorant.  Its only `k`-dependence is the square of
the W4 packet budget. -/
noncomputable def selectedFerrersShiftedEnergyMajorant (k : ℕ) : ℝ :=
  (2 * (|Real.log Real.pi| + Real.log 4 + 7)) *
    (selectedFerrersAbelFourierDecayBudget k) ^ 2 *
      selectedFerrersShiftedEnergyUniversalIntegral

private theorem shiftedSqrtWeight_sq_le_envelope' (t : ℝ) :
    sourceArchimedeanShiftedSqrtWeight t ^ 2 ≤
      (2 * (|Real.log Real.pi| + Real.log 4 + 7)) *
        vModeLogGrowthEnvelope t := by
  have henv : 1 ≤ vModeLogGrowthEnvelope t := by
    unfold vModeLogGrowthEnvelope
    have : 0 ≤ Real.log (2 + |t|) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hsymbol := abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope t
  rw [sourceArchimedeanShiftedSqrtWeight_sq]
  have hleabs : sourceArchimedeanMultiplier t ≤
      |sourceArchimedeanMultiplier t| := le_abs_self _
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith [abs_nonneg (Real.log Real.pi)]

private theorem fourier_congr_ae'
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) (t : ℝ) :
    𝓕 f t = 𝓕 g t := by
  rw [Real.fourier_eq', Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- The literal shifted form energy of the selected W3 vector is bounded by
the universal envelope times the square of the explicit W4 budget. -/
theorem selectedFerrersAbelLimit_shiftedEnergy_le_majorant (k : ℕ) :
    (sourceArchimedeanShiftedSesquilinearForm
      (selectedFerrersPreAnchorIndex k)
      (⟨selectedFerrersAbelLimitHm k,
        selectedFerrersAbelLimit_mem_sourceArchimedeanShiftedFormDomain k⟩)
      (⟨selectedFerrersAbelLimitHm k,
        selectedFerrersAbelLimit_mem_sourceArchimedeanShiftedFormDomain k⟩)).re ≤
      selectedFerrersShiftedEnergyMajorant k := by
  let i := selectedFerrersPreAnchorIndex k
  let x : sourceArchimedeanShiftedFormDomain i :=
    ⟨selectedFerrersAbelLimitHm k,
      selectedFerrersAbelLimit_mem_sourceArchimedeanShiftedFormDomain k⟩
  let D : ℝ := 2 * (|Real.log Real.pi| + Real.log 4 + 7)
  let C : ℝ := selectedFerrersAbelFourierDecayBudget k
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hC : 0 ≤ C := selectedFerrersAbelFourierDecayBudget_nonneg k
  have hcross :=
    coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension
      i (selectedFerrersAbelLimitHm k)
  have hrep := sourceLogWindowZeroExtension_selectedFerrersAbelLimitHm_ae k
  have hfourier : ∀ t : ℝ,
      𝓕 (sourceLogWindowZeroExtension i (selectedFerrersAbelLimitHm k)) t =
        𝓕 (selectedFerrersAbelLogZeroExtension k) t :=
    fun t => fourier_congr_ae' hrep t
  have hleft :=
    integrable_sourceArchimedeanShiftedMultiplier_mul_fourierNorm_sq i x
  have hright : Integrable (fun t : ℝ =>
      D * C ^ 2 *
        ((vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2)) :=
    vModeLogGrowthEnvelope_sq_div_one_add_abs_sq_integrable.const_mul
      (D * C ^ 2)
  rw [sourceArchimedeanShiftedSesquilinearForm_re_self_eq_integral_norm_sq]
  change
    (∫ t : ℝ,
      (sourceArchimedeanMultiplier t +
        (|Real.log Real.pi| + Real.log 4 + 6)) *
      ‖(((sourceLogWindowFourierL2Isometry i
        (selectedFerrersAbelLimitHm k) :
          MeasureTheory.Lp ℂ 2 volume) : ℝ → ℂ) t)‖ ^ 2) ≤ _
  change (∫ t : ℝ,
      (sourceArchimedeanMultiplier t +
        (|Real.log Real.pi| + Real.log 4 + 6)) *
      ‖(((sourceLogWindowFourierL2Isometry i
        (selectedFerrersAbelLimitHm k) :
          MeasureTheory.Lp ℂ 2 volume) : ℝ → ℂ) t)‖ ^ 2) ≤
    D * C ^ 2 * selectedFerrersShiftedEnergyUniversalIntegral
  rw [show D * C ^ 2 * selectedFerrersShiftedEnergyUniversalIntegral =
      ∫ t : ℝ, D * C ^ 2 *
        ((vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2) by
    rw [integral_const_mul, selectedFerrersShiftedEnergyUniversalIntegral]]
  apply integral_mono_ae hleft hright
  filter_upwards [hcross] with t ht
  rw [ht, hfourier t]
  have henv : 1 ≤ vModeLogGrowthEnvelope t := by
    unfold vModeLogGrowthEnvelope
    have : 0 ≤ Real.log (2 + |t|) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hw := shiftedSqrtWeight_sq_le_envelope' t
  have hf := selectedFerrersAbelLogZeroExtension_fourier_decay_quantitative k t
  have hden : 0 < 1 + |t| := by positivity
  have hf0 : 0 ≤ ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ := norm_nonneg _
  have hsquare :
      ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ^ 2 ≤
        C ^ 2 / (1 + |t|) ^ 2 := by
    rw [← div_pow]
    exact (sq_le_sq₀ hf0 (div_nonneg hC hden.le)).2 hf
  have henv0 : 0 ≤ vModeLogGrowthEnvelope t := le_trans zero_le_one henv
  have henvsq : vModeLogGrowthEnvelope t ≤
      (vModeLogGrowthEnvelope t) ^ 2 := by nlinarith
  rw [← sourceArchimedeanShiftedSqrtWeight_sq]
  calc
    sourceArchimedeanShiftedSqrtWeight t ^ 2 *
        ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ^ 2
      ≤ (D * vModeLogGrowthEnvelope t) *
          (C ^ 2 / (1 + |t|) ^ 2) := by
        apply mul_le_mul
        · simpa [D] using hw
        · exact hsquare
        · exact sq_nonneg _
        · exact mul_nonneg hD henv0
    _ ≤ (D * vModeLogGrowthEnvelope t) *
          (C ^ 2 / (1 + |t|) ^ 2) *
            vModeLogGrowthEnvelope t := by
        exact le_mul_of_one_le_right
          (mul_nonneg (mul_nonneg hD henv0)
            (div_nonneg (sq_nonneg C) (sq_nonneg _))) henv
    _ = D * C ^ 2 *
        ((vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2) := by ring

#print axioms selectedFerrersAbelFourierDecayBudget
#print axioms selectedFerrersAbelFourierDecayBudget_nonneg
#print axioms selectedFerrersAbelLogZeroExtension_fourier_decay_quantitative
#print axioms selectedFerrersShiftedEnergyUniversalIntegral
#print axioms selectedFerrersShiftedEnergyUniversalIntegral_nonneg
#print axioms selectedFerrersShiftedEnergyUniversalIntegral_finite
#print axioms selectedFerrersShiftedEnergyMajorant
#print axioms selectedFerrersAbelLimit_shiftedEnergy_le_majorant

end Q3.RouteB.D0Pstar
