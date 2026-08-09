import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Q3.RouteB.D0Pstar

private theorem fourierLogWindowMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) 2 volume := by
  have hweighted :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hweighted.of_le ?_ ?_
  · have hfi : Integrable (logWindowZeroExtendedMode i n) := by
      apply IntegrableOn.integrable_indicator
      · apply Continuous.integrableOn_Icc
        fun_prop
      · exact measurableSet_Icc
    exact (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hfi).aestronglyMeasurable
  · filter_upwards [] with t
    have henv : 1 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) henv)]
    nlinarith [norm_nonneg (𝓕 (logWindowZeroExtendedMode i n) t)]

private noncomputable def fourierLogWindowModeLp
    (i : PairIndex) (n : ℤ) :
    MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
  (fourierLogWindowMode_memLp i n).toLp
    (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t)

private theorem coeFn_fourierLogWindowModeLp
    (i : PairIndex) (n : ℤ) :
    (fourierLogWindowModeLp i n : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) := by
  exact MemLp.coeFn_toLp (fourierLogWindowMode_memLp i n)

private theorem fourierLogWindowModeLp_orthonormal
    (i : PairIndex) :
    Orthonormal ℂ (fourierLogWindowModeLp i) := by
  rw [orthonormal_iff_ite]
  intro n r
  rw [MeasureTheory.L2.inner_def]
  have hn := coeFn_fourierLogWindowModeLp i n
  have hr := coeFn_fourierLogWindowModeLp i r
  calc
    _ = ∫ t : ℝ,
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            𝓕 (logWindowZeroExtendedMode i r) t := by
      apply integral_congr_ae
      filter_upwards [hn, hr] with t hnt hrt
      rw [hnt, hrt]
      simp only [RCLike.inner_apply']
    _ = if n = r then 1 else 0 := by
      by_cases hnr : n = r
      · subst r
        rw [if_pos rfl]
        have h := sourceModeCosineCorrelation_control_diag_zero i n
        simp only [mul_zero, Real.cos_zero,
          Complex.ofReal_one, mul_one] at h
        exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (by simpa using h)
      · rw [if_neg hnr]
        have h := sourceModeCosineCorrelation_control_offdiag_zero i hnr
        simp only [mul_zero, Real.cos_zero,
          Complex.ofReal_one, mul_one] at h
        exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (by simpa using h)

/-- The whole-line `L²` isometry synthesized from the complete literal
`V_n_m` basis and the exact forward Fourier images of those modes.

This declaration makes no claim that the image of an arbitrary `H_m` vector
is represented by a separately defined pointwise Fourier integral. -/
noncomputable def sourceLogWindowFourierL2Isometry
    (i : PairIndex) :
    H_m i →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
  (fourierLogWindowModeLp_orthonormal i).orthogonalFamily.linearIsometry.comp
    (V_n_m_hilbertBasis i).repr.toLinearIsometry

private theorem sourceLogWindowFourierL2Isometry_apply_mode
    (i : PairIndex) (n : ℤ) :
    sourceLogWindowFourierL2Isometry i (V_n_m i n) =
      fourierLogWindowModeLp i n := by
  change
    (fourierLogWindowModeLp_orthonormal i).orthogonalFamily.linearIsometry
        ((V_n_m_hilbertBasis i).repr (V_n_m i n)) =
      fourierLogWindowModeLp i n
  rw [← V_n_m_hilbertBasis_apply]
  rw [(V_n_m_hilbertBasis i).repr_self]
  rw [OrthogonalFamily.linearIsometry_apply_single]
  rw [LinearIsometry.toSpanSingleton_apply]
  simp

/-- On every literal production mode, the synthesized isometry agrees almost
everywhere with the existing forward Fourier transform of the zero extension. -/
theorem coeFn_sourceLogWindowFourierL2Isometry_apply_mode
    (i : PairIndex) (n : ℤ) :
    ((sourceLogWindowFourierL2Isometry i (V_n_m i n) :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)]
        (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) := by
  rw [sourceLogWindowFourierL2Isometry_apply_mode]
  exact coeFn_fourierLogWindowModeLp i n


#print axioms sourceLogWindowFourierL2Isometry
#print axioms coeFn_sourceLogWindowFourierL2Isometry_apply_mode

end Q3.RouteB.D0Pstar
