import Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
import Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierIntegralCrosswalk
import Q3.Proofs.RouteB.D0PstarShiftedArchFormDomain
import Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2

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
# Selected Ferrers fixed-`k` shifted root energy

This node assembles the W3 selected Abel limit, the W1 ordinary-Fourier to
synthesized-isometry crosswalk, and the repaired W4 fixed-`k` Fourier decay
against the literal source archimedean shifted square-root weight.  Every
constant may depend on `k`; no cofinal rate is asserted.
-/

/-- The W3 selected Abel limit as the literal vector in the production
`H_m` space. -/
noncomputable def selectedFerrersAbelLimitHm
    (k : ℕ) : H_m (selectedFerrersPreAnchorIndex k) :=
  (selectedFerrersAbelLimit_memLp k).toLp
    (selectedFerrersAbelLimit k)

/-- The chosen additive-log representative of the W3 `H_m` vector agrees
almost everywhere with the direct W4 representative.  Endpoint values are
not identified pointwise. -/
theorem sourceLogWindowZeroExtension_selectedFerrersAbelLimitHm_ae
    (k : ℕ) :
    sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
        (selectedFerrersAbelLimitHm k) =ᵐ[volume]
      selectedFerrersAbelLogZeroExtension k := by
  let i := selectedFerrersPreAnchorIndex k
  let x : H_m i := selectedFerrersAbelLimitHm k
  let y := (logWindowL2Equiv i).symm x
  have hxy : logWindowL2Equiv i y = x := by
    exact (logWindowL2Equiv i).apply_symm_apply x
  have hy := coeFn_logWindowL2Equiv i y
  rw [hxy] at hy
  have hycomp := hy.comp_tendsto
    (sourceExpWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
  have hylog :
      ∀ᵐ z : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))),
        (x : ℝ → ℂ) (Real.exp z / lambda_m i) = (y : ℝ → ℂ) z := by
    filter_upwards [hycomp] with z hz
    have hlam : lambda_m i ≠ 0 := by
      rw [lambda_m]
      exact (Real.sqrt_pos.2 (by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm))).ne'
    have harg : lambda_m i * (Real.exp z / lambda_m i) = Real.exp z := by
      field_simp
    simp only [Function.comp_apply] at hz
    rw [harg, Real.log_exp] at hz
    exact hz
  have hxrep := MemLp.coeFn_toLp (selectedFerrersAbelLimit_memLp k)
  change
    ((selectedFerrersAbelLimitHm k : H_m i) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)] selectedFerrersAbelLimit k at hxrep
  have hxcomp := hxrep.comp_tendsto
    (sourceExpWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
  have hinside :
      ∀ᵐ z : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))),
        (y : ℝ → ℂ) z = selectedFerrersAbelLogRepresentative k z := by
    filter_upwards [hylog, hxcomp] with z hyz hxz
    rw [← hyz]
    simpa [x, Function.comp_apply, selectedFerrersAbelLogRepresentative] using hxz
  have hinside' :
      ∀ᵐ z : ℝ ∂volume,
        z ∈ Set.Icc (0 : ℝ) (L_m i) →
          (y : ℝ → ℂ) z = selectedFerrersAbelLogRepresentative k z := by
    rw [← ae_restrict_iff' measurableSet_Icc]
    exact hinside
  filter_upwards [hinside'] with z hz
  unfold sourceLogWindowZeroExtension selectedFerrersAbelLogZeroExtension
  change Set.indicator (Set.Icc (0 : ℝ) (L_m i)) (y : ℝ → ℂ) z = _
  by_cases hmem : z ∈ Set.Icc (0 : ℝ) (L_m i)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hz hmem]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

private theorem fourier_congr_ae
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) (t : ℝ) :
    𝓕 f t = 𝓕 g t := by
  rw [Real.fourier_eq', Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

private theorem shiftedSqrtWeight_sq_le_envelope (t : ℝ) :
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

private theorem selectedFerrersShiftedWeightedFourier_memLp (k : ℕ) :
    MemLp
      (fun t : ℝ =>
        (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
          𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
            (selectedFerrersAbelLimitHm k)) t)
      2 volume := by
  obtain ⟨C, hC, hdecay⟩ :=
    selectedFerrersAbelLogZeroExtension_fourier_decay k
  have hae :=
    sourceLogWindowZeroExtension_selectedFerrersAbelLimitHm_ae k
  have hfourier : ∀ t : ℝ,
      𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
          (selectedFerrersAbelLimitHm k)) t =
        𝓕 (selectedFerrersAbelLogZeroExtension k) t :=
    fun t => fourier_congr_ae hae t
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ =>
        (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
          𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
            (selectedFerrersAbelLimitHm k)) t) volume := by
    exact ((Complex.continuous_ofReal.comp
      sourceArchimedeanShiftedSqrtWeight_continuous).mul
      (VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar (by fun_prop)
        (sourceLogWindowZeroExtension_integrable
          (selectedFerrersPreAnchorIndex k)
          (selectedFerrersAbelLimitHm k)))).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  let D : ℝ := 2 * (|Real.log Real.pi| + Real.log 4 + 7)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hdom :=
    vModeLogGrowthEnvelope_sq_div_one_add_abs_sq_integrable.const_mul
      (D * C ^ 2)
  refine hdom.mono' ?_ ?_
  · exact hmeas.norm.pow 2
  · filter_upwards [] with t
    rw [Real.norm_eq_abs]
    have henv : 1 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    have hw := shiftedSqrtWeight_sq_le_envelope t
    have hf := hdecay t
    rw [← hfourier t] at hf
    have hden : 0 < 1 + |t| := by positivity
    change |‖(sourceArchimedeanShiftedSqrtWeight t : ℂ) *
        𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
          (selectedFerrersAbelLimitHm k)) t‖ ^ 2| ≤
      D * C ^ 2 *
        ((vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2)
    rw [abs_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sourceArchimedeanShiftedSqrtWeight_nonneg t)]
    have henv0 : 0 ≤ vModeLogGrowthEnvelope t :=
      le_trans zero_le_one henv
    have hf0 : 0 ≤ ‖𝓕 (sourceLogWindowZeroExtension
        (selectedFerrersPreAnchorIndex k) (selectedFerrersAbelLimitHm k)) t‖ :=
      norm_nonneg _
    have hC0 : 0 ≤ C := hC
    have hsquare :
        ‖𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
            (selectedFerrersAbelLimitHm k)) t‖ ^ 2 ≤
          C ^ 2 / (1 + |t|) ^ 2 := by
      rw [← div_pow]
      exact (sq_le_sq₀ hf0 (div_nonneg hC0 hden.le)).2 hf
    have henvsq : vModeLogGrowthEnvelope t ≤
        (vModeLogGrowthEnvelope t) ^ 2 := by nlinarith
    rw [mul_pow]
    change
      (sourceArchimedeanShiftedSqrtWeight t ^ 2) *
          ‖𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
            (selectedFerrersAbelLimitHm k)) t‖ ^ 2 ≤
        D * C ^ 2 *
          ((vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2)
    calc
      (sourceArchimedeanShiftedSqrtWeight t ^ 2) *
          ‖𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
            (selectedFerrersAbelLimitHm k)) t‖ ^ 2
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

/-- The exact W3 selected Abel limit belongs, for every fixed `k`, to the
literal source archimedean shifted form domain. -/
theorem selectedFerrersAbelLimit_mem_sourceArchimedeanShiftedFormDomain
    (k : ℕ) :
    selectedFerrersAbelLimitHm k ∈
      sourceArchimedeanShiftedFormDomain
        (selectedFerrersPreAnchorIndex k) := by
  rw [mem_sourceArchimedeanShiftedFormDomain_iff]
  have hcross :=
    coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension
      (selectedFerrersPreAnchorIndex k) (selectedFerrersAbelLimitHm k)
  exact MemLp.ae_eq
    (by
      filter_upwards [hcross] with t ht
      simp only [ht])
    (selectedFerrersShiftedWeightedFourier_memLp k)

#print axioms selectedFerrersAbelLimitHm
#print axioms sourceLogWindowZeroExtension_selectedFerrersAbelLimitHm_ae
#print axioms selectedFerrersAbelLimit_mem_sourceArchimedeanShiftedFormDomain

end Q3.RouteB.D0Pstar
