import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 200000

/-!
Standalone OmegaPrime derivative row-17 analytic payload.

The active RawProduct18 route needs an `OmegaPrime` derivative source through
order 17.  Existing generated Taylor-remainder payloads expose the public
termwise/closed-form bridges only through `_of_le16`; this file adds only the
missing row-17 analytic bridge and deliberately does not clone the old
`order16Abs` certificate structure.

This is not yet the rational source consumed by the RawProduct18 budget.  The
next proof object must replace the `tsum` majorant below by a checked rational
tail/prefix bound.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

namespace Step33Sub0OmegaPrimeOrder17Payload

/-- Public `C^17` source for the OmegaPrime closed form. -/
theorem step22OmegaArchWeightDerivClosedForm_contDiff17 :
    ContDiff Real 17 step22OmegaArchWeightDerivClosedForm := by
  let z : Real -> Complex :=
    fun t : Real =>
      (1 / 4 : Complex) + Complex.I * (((t / 2 : Real) : Complex))
  have hzCont : ContDiff Real 17 z := by
    have hdiv : ContDiff Real 17 (fun t : Real => t / 2) := by
      fun_prop
    have hcast :
        ContDiff Real 17
          (fun t : Real => (((t / 2 : Real) : Real) : Complex)) :=
      Complex.ofRealCLM.contDiff.comp hdiv
    have hmul :
        ContDiff Real 17
          (fun t : Real =>
            Complex.I * (((t / 2 : Real) : Real) : Complex)) :=
      (contDiff_const : ContDiff Real 17 (fun _ : Real => Complex.I)).mul
        hcast
    simpa [z] using
      (contDiff_const :
        ContDiff Real 17 (fun _ : Real => (1 / 4 : Complex))).add hmul
  have hTrigamma :
      ContDiff Real 17 (fun t : Real => trigamma (z t)) := by
    rw [contDiff_iff_contDiffAt]
    intro eta
    have hzPos : 0 < (z eta).re := by
      dsimp [z]
      norm_num [Complex.add_re, Complex.mul_re]
    exact
      ((trigamma_analyticAt_of_re_pos hzPos).contDiffAt.restrict_scalars
          Real).comp eta hzCont.contDiffAt
  have hIm : ContDiff Real 17 (fun t : Real => (trigamma (z t)).im) :=
    Complex.imCLM.contDiff.comp hTrigamma
  change
    ContDiff Real 17
      (fun t : Real =>
        -((trigamma
          ((1 / 4 : Complex) + Complex.I *
            (((t / 2 : Real) : Complex)))).im * (1 / 2 : Real)))
  simpa [z] using
    (hIm.mul
      (contDiff_const : ContDiff Real 17
        (fun _ : Real => (1 / 2 : Real)))).neg

/-- Locally uniform summability for the new trigamma derivative layer. -/
theorem omegaPrimeTrigammaSeries_deriv_layer17_summableLocallyUniformlyOn :
      SummableLocallyUniformlyOn
        (fun n : Nat =>
          iteratedDerivWithin 17
            (fun t : Real =>
              Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
                t n) Set.univ)
        Set.univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K _hK _hKc
  exact ⟨Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant 17,
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant_summable 17,
    fun n t _ =>
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_norm_le_majorant
        17 n t⟩

/-- Differentiability payload for the new trigamma derivative layer. -/
theorem omegaPrimeTrigammaSeries_deriv_layer17_differentiableAt :
    ∀ n r, r ∈ Set.univ ->
      DifferentiableAt Real
        (iteratedDerivWithin 17
          (fun t : Real =>
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
              t n) Set.univ)
        r := by
  intro n r _hr
  exact
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_differentiableAt
      n 17 r

/-- Termwise differentiation bridge for the missing row 17. -/
theorem omegaPrimeTrigammaSeries_iteratedDeriv17_eq_tsum
    (eta : Real) :
    iteratedDeriv 17
        Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries eta =
      ∑' n : Nat,
        iteratedDeriv 17
          (fun t : Real =>
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
              t n) eta := by
  have h :=
    iteratedDerivWithin_tsum (ι := Nat) (𝕜 := Real) (F := Real)
      (m := 17) (s := Set.univ) isOpen_univ (Set.mem_univ eta)
      (fun t _ =>
        Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm_summable
          t)
      (fun k hk1 hk17 => by
        by_cases hk16 : k <= 16
        · exact
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries_deriv_layers_summableLocallyUniformlyOn_payload
              k hk1 hk16
        · have hk_eq : k = 17 := by omega
          subst k
          exact
            omegaPrimeTrigammaSeries_deriv_layer17_summableLocallyUniformlyOn)
      (fun n k r hk17 _hr => by
        by_cases hk16 : k <= 16
        · exact
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries_deriv_layer_differentiableAt_payload
              n k r hk16 (Set.mem_univ r)
        · have hk_eq : k = 17 := by omega
          subst k
          exact
            omegaPrimeTrigammaSeries_deriv_layer17_differentiableAt
              n r (Set.mem_univ r))
  simpa [
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries,
    iteratedDerivWithin_univ] using h

/-- Norm-majorant consequence of the row-17 termwise bridge. -/
theorem omegaPrimeTrigammaSeries_iteratedDeriv17_norm_le_tsum_majorant
    (eta : Real) :
    ‖iteratedDeriv 17
        Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries eta‖ <=
      ∑' n : Nat,
        Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
          17 n := by
  have hEq := omegaPrimeTrigammaSeries_iteratedDeriv17_eq_tsum eta
  rw [hEq]
  have hBound :
      ∀ n : Nat,
        ‖iteratedDeriv 17
            (fun t : Real =>
              Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
                t n) eta‖ <=
          Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
            17 n := by
    intro n
    simpa [iteratedDerivWithin_univ] using
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_norm_le_majorant
        17 n eta
  have hSummDeriv :
      Summable
        (fun n : Nat =>
          iteratedDeriv 17
            (fun t : Real =>
              Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
                t n) eta) :=
    (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant_summable
      17).of_norm_bounded
      hBound
  have hNorm :
      ‖∑' n : Nat,
          iteratedDeriv 17
            (fun t : Real =>
              Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
                t n) eta‖ <=
        ∑' n : Nat,
          ‖iteratedDeriv 17
            (fun t : Real =>
              Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
                t n) eta‖ :=
    norm_tsum_le_tsum_norm hSummDeriv.norm
  have hAbsSum :
      (∑' n : Nat,
        ‖iteratedDeriv 17
          (fun t : Real =>
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeriesTerm
              t n) eta‖) <=
        ∑' n : Nat,
          Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
            17 n := by
    exact Summable.tsum_le_tsum hBound hSummDeriv.norm
      (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant_summable
        17)
  exact hNorm.trans hAbsSum

/-- `C^17` source for the trigamma series via the public OmegaPrime form. -/
theorem omegaPrimeTrigammaSeries_contDiff17 :
    ContDiff Real 17
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries := by
  rw [
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries_eq_neg_two_closedForm]
  change
    ContDiff Real 17
      (fun eta : Real => (-2 : Real) *
        step22OmegaArchWeightDerivClosedForm eta)
  simpa [smul_eq_mul] using
    ContDiff.const_smul (-2 : Real)
      step22OmegaArchWeightDerivClosedForm_contDiff17

/-- Order-17 OmegaPrime analytic majorant before rational tail certification. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TsumAbs :
    Real :=
  (1 / 2 : Real) *
    (∑' n : Nat,
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
        17 n)

/--
Analytic order-17 OmegaPrime source.  This is proof-grade as a `tsum`
domination, but it is not yet the rational budget source required by the
RawProduct18 payload generator.
-/
theorem iteratedDeriv17_norm_le_half_tsum_majorant
    (eta : Real) :
    ‖iteratedDeriv 17 step22OmegaArchWeightDerivClosedForm eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TsumAbs := by
  have hfun :
      step22OmegaArchWeightDerivClosedForm =
        fun t : Real =>
          (-1 / 2 : Real) *
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries
              t := by
    funext t
    have h :=
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_eq_trigamma_series
        t
    calc
      step22OmegaArchWeightDerivClosedForm t =
          -((1 / 2 : Real) *
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries
              t) := by
            simpa using h
      _ = (-1 / 2 : Real) *
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries
              t := by
            ring
  have hSmooth :
      ContDiffAt Real 17
        Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries eta :=
    omegaPrimeTrigammaSeries_contDiff17.contDiffAt
  have hMajorant :=
    omegaPrimeTrigammaSeries_iteratedDeriv17_norm_le_tsum_majorant eta
  rw [hfun]
  rw [iteratedDeriv_const_mul hSmooth (-1 / 2 : Real)]
  rw [norm_mul, Real.norm_eq_abs]
  have hhalf : |(-1 / 2 : Real)| = (1 / 2 : Real) := by
    norm_num
  rw [hhalf]
  exact mul_le_mul_of_nonneg_left hMajorant (by norm_num)

theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_tsum
    (eta : Real)
    (_heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖iteratedDeriv 17 step22OmegaArchWeightDerivClosedForm eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TsumAbs :=
  iteratedDeriv17_norm_le_half_tsum_majorant eta

end Step33Sub0OmegaPrimeOrder17Payload

end Step33
end PSDpd
end Q3
