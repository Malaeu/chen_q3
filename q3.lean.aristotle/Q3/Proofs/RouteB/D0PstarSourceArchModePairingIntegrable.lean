import Q3.Proofs.RouteB.D0PstarExactArchSymbolWeightedModeL2

/-!
# Goal 057 B3.0C: source archimedean mode-pairing integrability

This file proves that the correctly oriented archimedean cross-mode
integrand is integrable for every fixed production mode pair.

The first Fourier mode is conjugated, matching the source Weil form's
antilinear-first convention.  The result supplies only an `L¹` carrier; it
does not define the pairing integral, the full source Weil form, or an
associated operator graph.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar

private theorem logWindowZeroExtendedMode_integrable_for_pairing
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

private theorem fourier_logWindowZeroExtendedMode_memLp_two
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) 2 volume := by
  have hweighted :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hweighted.of_le ?_ ?_
  · have hfi := logWindowZeroExtendedMode_integrable_for_pairing i n
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

private theorem conj_fourier_logWindowZeroExtendedMode_memLp_two
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ => conj (𝓕 (logWindowZeroExtendedMode i n) t))
      2 volume := by
  have hleft := fourier_logWindowZeroExtendedMode_memLp_two i n
  refine hleft.congr_norm ?_ ?_
  · exact Complex.continuous_conj.comp_aestronglyMeasurable hleft.1
  · filter_upwards [] with t
    exact (norm_conj _).symm

/--
For every fixed source mode pair, the conjugate-first exact archimedean
Fourier integrand belongs to `L¹`.
-/
theorem sourceArchimedeanModePairing_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable
      (fun t : ℝ =>
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t) := by
  have hleft := conj_fourier_logWindowZeroExtendedMode_memLp_two i n
  have hright :=
    sourceArchimedeanMultiplier_mul_fourier_logWindowZeroExtendedMode_memLp i r
  simpa only [Pi.mul_apply, mul_assoc] using hleft.integrable_mul hright

end Q3.RouteB.D0Pstar
