import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination
import Q3.Proofs.A_Star_Properties

/-!
# Goal 057 B3.0B3: exact archimedean-symbol weighted-mode L2 transfer

This file transfers the global exact-symbol domination from B3.0B2 through
the logarithmic-envelope weighted-mode certificate from B3.0B1.

The result is fixed-mode weighted `L²` membership only.  It supplies neither
a uniform cofinal-mode estimate nor a source form-domain or associated-
operator-domain theorem.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace Q3.RouteB.D0Pstar

private theorem sourceArchimedeanMultiplier_continuous :
    Continuous sourceArchimedeanMultiplier := by
  have hrepr : sourceArchimedeanMultiplier =
      fun t : ℝ => -Q3.a_star t / (2 * Real.pi) := by
    funext t
    exact sourceArchimedeanMultiplier_eq_neg_aStar_scaled t
  rw [hrepr]
  exact Q3.a_star_continuous_thm.neg.div_const (2 * Real.pi)

private theorem logWindowZeroExtendedMode_integrable_for_exactArch
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

/--
For every fixed source mode, the exact source archimedean multiplier times
its literal zero-extended Fourier transform belongs to `L²`.
-/
theorem sourceArchimedeanMultiplier_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume := by
  let C : ℝ := |Real.log Real.pi| + Real.log 4 + 7
  have hbase :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hbase.of_le_mul (c := C) ?_ ?_
  · have hfi : Integrable (logWindowZeroExtendedMode i n) :=
      logWindowZeroExtendedMode_integrable_for_exactArch i n
    have hsourceComplex :
        Continuous (fun t : ℝ => (sourceArchimedeanMultiplier t : ℂ)) :=
      Complex.continuous_ofReal.comp sourceArchimedeanMultiplier_continuous
    have hfourier :
        Continuous (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) := by
      exact VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar (by fun_prop) hfi
    exact (hsourceComplex.mul hfourier).aestronglyMeasurable
  · filter_upwards [] with t
    have hdom := abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope t
    have henv_nonneg : 0 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      positivity
    have hfourier_nonneg :
        0 ≤ ‖𝓕 (logWindowZeroExtendedMode i n) t‖ := norm_nonneg _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg henv_nonneg]
    dsimp [C]
    nlinarith

end Q3.RouteB.D0Pstar
