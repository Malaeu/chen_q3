import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderLanding

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
First refined-subchunk hRaw landing for the active Step33A.1-A route.

This file does not claim that the full Taylor payload is closed.  It checks the
receiver stack from the first direct endpoint certificate to the sharp
raw-center coefficient bound.  The remaining analytic premise is the already
isolated shifted-digamma `m=6` norm bound.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral
namespace RawOmegaATaylorModelCertificate

def primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat :=
  ((-151365635111474049 : Rat) / 500000000000000000)

/-- Minimal adapter certificate for the raw-center receiver.

Only `coeff 0` is consumed by
`raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`.
The full refined Taylor payload remains a separate proof-data target. -/
def primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert :
    RawOmegaATaylorModelCertificate 11 ((3 : Real) / 10)
      0 0 ((1 : Real) / 10) 0 0 where
  center := ((1 : Rat) / 20)
  radius := ((1 : Rat) / 20)
  degree := 16
  coeff := fun _ => primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0
  remainder := ((1 : Rat) / 1000000000000000000)

/-- First-subchunk `hRawCenterCoeffAbs` bridge.

Once the current `DIGAMMA_SHIFT16_M6_MAIN_NORM_BLOCKER` is closed, this theorem
turns the checked endpoint facade into the sharp raw-center coefficient bound
needed by the refined payload lane. -/
theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_norm
    (hMain :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  change
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      (primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.coeff 0 : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000)
  apply
    (raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance
        (cert := primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert)
        (a := ((499999999999999999999 : Real) / 10000000000000000000000))
        (b := ((1 : Real) / 20))
        (anchor := ((1 : Real) / 20))
        (etaRadius := ((1 : Real) / 10000000000000000000000))
        (scaleLower := 95492965855137201461330258023e-30)
        (scaleUpper := 95492965855137201461330258024e-30)
        (cosLower := (1 : Real))
        (cosUpper := (1 : Real))
        (rawLower := ((-151365635111474049064509243331 : Real) /
          500000000000000000000000000000))
        (rawUpper := ((-151365635111474048935490756669 : Real) /
          500000000000000000000000000000))
        (sampleRadius := ((64509243331 : Real) /
          500000000000000000000000000000)))
  · exact
      primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm
        hMain hLogPiLower hLogPiUpper
  · norm_num
  · norm_num
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleLower
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleUpper
  any_goals norm_num
  · change
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real) <=
        -(151365635111474049 / 500000000000000000)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]
  · change
      -(151365635111474048935490756669 /
          500000000000000000000000000000) <=
        64509243331 / 500000000000000000000000000000 +
          ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_norm_closedLogPi
    (hMain :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_norm
      hMain
      primaryFiniteRow0Parent0Split100Sub0LogPiLower_le
      primaryFiniteRow0Parent0Split100Sub0LogPi_le_upper

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_expanded_asymptotic_bound_closedLogPi
    (hExpanded :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          (let z : Complex := Q3.PSDpd.Step33.step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_norm_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_expanded_asymptotic_bound
        hExpanded)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_first_omitted_term_bound_closedLogPi
    (hFirstOmitted :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          (let z : Complex := Q3.PSDpd.Step33.step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (‖Q3.PSDpd.Step33.step33Shift16DigammaPoint‖⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_norm_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_first_omitted_term_bound
        hFirstOmitted)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
    (hReFirstOmitted :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          (let z : Complex := Q3.PSDpd.Step33.step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_norm_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound
        hReFirstOmitted)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_integral_remainder_bound_closedLogPi
    (hIntegral :
      Q3.digammaM6IntegralRemainderBound
        Q3.PSDpd.Step33.step33Shift16DigammaPoint) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_generic_integral_remainder
        hIntegral)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_closedLogPi
    (N : Nat) (shiftRad defectRad : Real)
    (hShift :
      ‖Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (N : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (N : Complex))‖ <=
        shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (n : Complex))‖) <=
        defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope
        N shiftRad defectRad hShift hDefects hTotal)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
    (payload : Q3.PSDpd.Step33.Step33Shift16M6FiniteTelescopeScalarPayload) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope_scalar_payload
        payload)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shifted_integral_remainder_and_defect_sum_closedLogPi
    (shiftRad defectRad : Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (n : Complex))‖) <=
        defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shifted_integral_remainder_and_defect_sum
        shiftRad defectRad hShiftIntegral hShiftRad hDefects hTotal)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum_closedLogPi
    (seriesN gammaN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (n : Complex))‖) <=
        defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum
        seriesN gammaN shiftRad defectRad shiftReRad shiftImRad tailRadius
        digammaReLower digammaReUpper digammaImLower digammaImUpper
        mainReLower mainReUpper mainImLower mainImUpper
        hTailNorm hReLower hReUpper hImLower hImUpper
        hMainReLower hMainReUpper hMainImLower hMainImUpper
        hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
        hDefects hTotal)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_term_payload_closedLogPi
    (payload : Q3.PSDpd.Step33.Step33Shift16M6FiniteTelescopeTermPayload) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
      payload.toScalarPayload

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shifted_integral_remainder_component_interval_defects_closedLogPi
    (shiftRad defectRad : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_term_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_integral_remainder_component_interval_defects
        shiftRad defectRad
        termReLower termReUpper termImLower termImUpper
        termReRad termImRad termRad
        hShiftIntegral hShiftRad
        hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
        hReLowerContain hReUpperContain hImLowerContain hImUpperContain
        hTermRad hDefectSum hTotal)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects_closedLogPi
    (seriesN gammaN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_term_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects
        seriesN gammaN shiftRad defectRad shiftReRad shiftImRad tailRadius
        digammaReLower digammaReUpper digammaImLower digammaImUpper
        mainReLower mainReUpper mainImLower mainImUpper
        termReLower termReUpper termImLower termImUpper
        termReRad termImRad termRad hTailNorm hReLower hReUpper hImLower
        hImUpper hMainReLower hMainReUpper hMainImLower hMainImUpper
        hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
        hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
        hReLowerContain hReUpperContain hImLowerContain hImUpperContain
        hTermRad hDefectSum hTotal)

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects_closedLogPi
    (shiftRad defectRad shiftReRad shiftImRad : Real)
    (errorReLower errorReUpper errorImLower errorImUpper : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hErrorReLower :
      errorReLower <=
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re)
    (hErrorReUpper :
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re <=
      errorReUpper)
    (hErrorImLower :
      errorImLower <=
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im)
    (hErrorImUpper :
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im <=
      errorImUpper)
    (hShiftReLower : -shiftReRad <= errorReLower)
    (hShiftReUpper : errorReUpper <= shiftReRad)
    (hShiftImLower : -shiftImRad <= errorImLower)
    (hShiftImUpper : errorImUpper <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_term_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects
        shiftRad defectRad shiftReRad shiftImRad
        errorReLower errorReUpper errorImLower errorImUpper
        termReLower termReUpper termImLower termImUpper
        termReRad termImRad termRad
        hErrorReLower hErrorReUpper hErrorImLower hErrorImUpper
        hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
        hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
        hReLowerContain hReUpperContain hImLowerContain hImUpperContain
        hTermRad hDefectSum hTotal)

/-- Component variant of the first-subchunk `hRawCenterCoeffAbs` bridge.

This keeps the landing useful if the external high-order digamma proof returns
separate real/imaginary m=6 error bounds instead of a single complex norm
bound. -/
theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_component_abs
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  change
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      (primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.coeff 0 : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000)
  apply
    (raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance
        (cert := primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert)
        (a := ((499999999999999999999 : Real) / 10000000000000000000000))
        (b := ((1 : Real) / 20))
        (anchor := ((1 : Real) / 20))
        (etaRadius := ((1 : Real) / 10000000000000000000000))
        (scaleLower := 95492965855137201461330258023e-30)
        (scaleUpper := 95492965855137201461330258024e-30)
        (cosLower := (1 : Real))
        (cosUpper := (1 : Real))
        (rawLower := ((-151365635111474049064509243331 : Real) /
          500000000000000000000000000000))
        (rawUpper := ((-151365635111474048935490756669 : Real) /
          500000000000000000000000000000))
        (sampleRadius := ((64509243331 : Real) /
          500000000000000000000000000000)))
  · exact
      primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_component_abs
        hMainRe hMainIm hLogPiLower hLogPiUpper
  · norm_num
  · norm_num
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleLower
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleUpper
  any_goals norm_num
  · change
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real) <=
        -(151365635111474049 / 500000000000000000)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]
  · change
      -(151365635111474048935490756669 /
          500000000000000000000000000000) <=
        64509243331 / 500000000000000000000000000000 +
          ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_component_abs_closedLogPi
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_main_component_abs
      hMainRe hMainIm
      primaryFiniteRow0Parent0Split100Sub0LogPiLower_le
      primaryFiniteRow0Parent0Split100Sub0LogPi_le_upper

/-- First-subchunk `hRawCenterCoeffAbs` bridge for the live shift16/N16
rectangular route.

This is the current route-A endpoint landing surface: the high-order analytic
backend only has to supply a proof-grade ball around
`digamma(129/4 + i/40)` plus the two generated main-interval arithmetic
comparisons.  The older m6 wrappers above remain compatibility support. -/
theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_rect_centered_complex_main_error
    (shiftedPsiMain : Complex) (shiftedErr : Real)
    (hShiftAbs :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          shiftedPsiMain‖ <= shiftedErr)
    (hMainLower :
      ((-85314634821843642073465861701640867472353398314119326820557162830783014314359848985502357 : Real) / (16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          ((1 : Real) / (20 : Real)) 16 (shiftedPsiMain.re - ((1401849775127188496093756428729 : Real) / (2000000000000000000000000000000 : Real))) -
          ((shiftedErr + ((1 : Real) / (2000000000000000000000000000000 : Real))) + (shiftedErr + ((1 : Real) / (2000000000000000000000000000000 : Real)))))
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          ((1 : Real) / (20 : Real)) 16 (shiftedPsiMain.re - ((1401849775127188496093756428729 : Real) / (2000000000000000000000000000000 : Real))) +
          ((shiftedErr + ((1 : Real) / (2000000000000000000000000000000 : Real))) + (shiftedErr + ((1 : Real) / (2000000000000000000000000000000 : Real)))) <=
        ((-426573174109218210367240990627486922998187245419326080653670377242934688213891611916507071 : Real) / (80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  have hShiftAbsGenerated :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            ((1 : Real) / (20 : Real)) 16 + (16 : Complex)) -
          shiftedPsiMain‖ <= shiftedErr := by
    simpa [Q3.PSDpd.Step33.step33Shift16DigammaPoint_eq_generated] using
      hShiftAbs
  change
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      (primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.coeff 0 : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000)
  apply
    (raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance
        (cert := primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert)
        (a := ((499999999999999999999 : Real) / 10000000000000000000000))
        (b := ((1 : Real) / 20))
        (anchor := ((1 : Real) / 20))
        (etaRadius := ((1 : Real) / 10000000000000000000000))
        (scaleLower := 95492965855137201461330258023e-30)
        (scaleUpper := 95492965855137201461330258024e-30)
        (cosLower := (1 : Real))
        (cosUpper := (1 : Real))
        (rawLower := ((-151365635111474049064509243331 : Real) /
          500000000000000000000000000000))
        (rawUpper := ((-151365635111474048935490756669 : Real) /
          500000000000000000000000000000))
        (sampleRadius := ((64509243331 : Real) /
          500000000000000000000000000000)))
  · exact
      primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16_centeredComplexMainError_invSumGenerated
        shiftedPsiMain shiftedErr hShiftAbsGenerated hMainLower hMainUpper
  · norm_num
  · norm_num
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleLower
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleUpper
  any_goals norm_num
  · change
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real) <=
        -(151365635111474049 / 500000000000000000)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]
  · change
      -(151365635111474048935490756669 /
          500000000000000000000000000000) <=
        64509243331 / 500000000000000000000000000000 +
          ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]

/-- Shortest first-subchunk `hRawCenterCoeffAbs` bridge for the current fixed
shift16 center.

This avoids exposing the generated `hMainLower` / `hMainUpper` arithmetic to
the high-order backend: once the backend proves the fixed ball around
`digamma(129/4 + i/40)`, the already checked log-pi endpoint facade supplies
the direct endpoint certificate. -/
theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_complex_main_error
    (hShiftAbs :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  change
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      (primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.coeff 0 : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000)
  apply
    (raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance
        (cert := primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert)
        (a := ((499999999999999999999 : Real) / 10000000000000000000000))
        (b := ((1 : Real) / 20))
        (anchor := ((1 : Real) / 20))
        (etaRadius := ((1 : Real) / 10000000000000000000000))
        (scaleLower := 95492965855137201461330258023e-30)
        (scaleUpper := 95492965855137201461330258024e-30)
        (cosLower := (1 : Real))
        (cosUpper := (1 : Real))
        (rawLower := ((-151365635111474049064509243331 : Real) /
          500000000000000000000000000000))
        (rawUpper := ((-151365635111474048935490756669 : Real) /
          500000000000000000000000000000))
        (sampleRadius := ((64509243331 : Real) /
          500000000000000000000000000000)))
  · exact
      primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint
        (by
          simpa [Q3.PSDpd.Step33.step33Shift16DigammaPoint,
            Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter,
            Q3.PSDpd.Step33.step33Shift16DigammaFixedRe,
            Q3.PSDpd.Step33.step33Shift16DigammaFixedIm,
            Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius] using
            hShiftAbs)
        hLogPiLower hLogPiUpper
  · norm_num
  · norm_num
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleLower
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleUpper
  any_goals norm_num
  · change
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real) <=
        -(151365635111474049 / 500000000000000000)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]
  · change
      -(151365635111474048935490756669 /
          500000000000000000000000000000) <=
        64509243331 / 500000000000000000000000000000 +
          ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]

/-- Component version of the fixed-center first-subchunk hRaw bridge.

This is the most convenient landing if the high-order backend proves separate
real and imaginary fixed-center bounds instead of a complex norm bound. -/
theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_component_abs
    (hRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  change
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      (primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.coeff 0 : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000)
  apply
    (raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance
        (cert := primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert)
        (a := ((499999999999999999999 : Real) / 10000000000000000000000))
        (b := ((1 : Real) / 20))
        (anchor := ((1 : Real) / 20))
        (etaRadius := ((1 : Real) / 10000000000000000000000))
        (scaleLower := 95492965855137201461330258023e-30)
        (scaleUpper := 95492965855137201461330258024e-30)
        (cosLower := (1 : Real))
        (cosUpper := (1 : Real))
        (rawLower := ((-151365635111474049064509243331 : Real) /
          500000000000000000000000000000))
        (rawUpper := ((-151365635111474048935490756669 : Real) /
          500000000000000000000000000000))
        (sampleRadius := ((64509243331 : Real) /
          500000000000000000000000000000)))
  · exact
      primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_component_abs
        hRe hIm hLogPiLower hLogPiUpper
  · norm_num
  · norm_num
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleLower
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      primaryK11Ell_div_pi_tightScaleUpper
  any_goals norm_num
  · change
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real) <=
        -(151365635111474049 / 500000000000000000)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]
  · change
      -(151365635111474048935490756669 /
          500000000000000000000000000000) <=
        64509243331 / 500000000000000000000000000000 +
          ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0]

/-- Rectangular interval version of the fixed-center hRaw bridge.

This is the most generator-friendly landing surface: generated high-order rows
may prove lower/upper bounds around the fixed Re/Im center, and Lean converts
them to the fixed component absolute-error interface above. -/
theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_rect_interval
    (hReLower :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).re)
    (hReUpper :
      (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).re <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hImLower :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).im)
    (hImUpper :
      (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).im <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  have hRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius := by
    rw [abs_le]
    constructor
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
  have hIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius := by
    rw [abs_le]
    constructor
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_component_abs
      hRe hIm hLogPiLower hLogPiUpper

/-- First-subchunk `hRawCenterCoeffAbs` bridge for the shift32 series payload.

This is the direct payload-facing hRaw receiver for the current first anchor:
generated data supplies the shift32 digamma series prefix/tail rectangle and
the independent `log pi` interval; Lean composes it through the fixed-rectangle
landing above. -/
theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_rect_shift32_series_prefix_tail_abs
    (N : Nat)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        imPrefixLower - imTailRadius)
    (hImUpperFinal :
      imPrefixUpper + imTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  have hRect :=
    step33Shift16Digamma_fixed_rect_interval_of_shift32_series_prefix_tail_abs
      N gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius hGammaLower hGammaUpper
      hRePrefixLower hRePrefixUpper hReTail hReLowerFinal hReUpperFinal
      hImPrefixLower hImPrefixUpper hImTail hImLowerFinal hImUpperFinal
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_rect_interval
      hRect.1 hRect.2.1 hRect.2.2.1 hRect.2.2.2 hLogPiLower hLogPiUpper

theorem primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_rect_shift32_series_prefix_tail_abs_closedLogPi
    (N : Nat)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        imPrefixLower - imTailRadius)
    (hImUpperFinal :
      imPrefixUpper + imTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
      ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
        ((64509243331 : Real) / 500000000000000000000000000000) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_fixed_rect_shift32_series_prefix_tail_abs
      N gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius hGammaLower hGammaUpper
      hRePrefixLower hRePrefixUpper hReTail hReLowerFinal hReUpperFinal
      hImPrefixLower hImPrefixUpper hImTail hImLowerFinal hImUpperFinal
      primaryFiniteRow0Parent0Split100Sub0LogPiLower_le
      primaryFiniteRow0Parent0Split100Sub0LogPi_le_upper

/-- First-subchunk exact-integral proof-data receiver from the sharp raw-center
bound and a full-cell residual-derivative interval bound.

This is the live `primary_finite` row `0`, parent chunk `0`, subchunk `0`
landing surface selected by the Step33A.1-A margin ledger.  It does not close
the shifted-digamma blocker; it only packages the checked local data once the
raw-center and derivative interval bounds are available. -/
def primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_hRawCenterCoeffAbs_and_deriv_interval_bounds
    (hRawCenterCoeffAbs :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
        ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
          ((64509243331 : Real) / 500000000000000000000000000000))
    (hDerivLower :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ((-94119513411 : Real) / 500000000000000000000000000000) <=
          deriv primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.residual eta)
    (hDerivUpper :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        deriv primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.residual eta <=
          ((1866608532757 : Real) / 500000000000000000000000000000)) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert := by
  apply
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell
      (cert := primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert)
      (sampleRadius :=
        ((64509243331 : Real) / 500000000000000000000000000000))
      (mesh := ((1 : Real) / 20))
      (anchor := ((1 : Real) / 20))
      (derivLower :=
        ((-94119513411 : Real) / 500000000000000000000000000000))
      (derivUpper :=
        ((1866608532757 : Real) / 500000000000000000000000000000))
      (derivSlope :=
        ((1866608532757 : Real) / 500000000000000000000000000000))
  · exact hDerivLower
  · exact hDerivUpper
  · norm_num
  · norm_num
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num
  · norm_num
  · norm_num
  · simpa [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert] using
      hRawCenterCoeffAbs
  · exact
      primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.residual_differentiableOn_Icc
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioc_zero
        ((1 : Real) / 10) 0)

/-- Preferred direct-norm version of the first-subchunk exact-integral
proof-data receiver.

The active direct proof-input worklist prefers this surface when generated
proof data can establish the residual-derivative norm bound directly.  The
legacy interval-bounds wrapper above remains useful when the generator emits
two-sided derivative intervals instead. -/
def primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_hRawCenterCoeffAbs_and_deriv_norm_bound
    (hRawCenterCoeffAbs :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 ((3 : Real) / 10) 0 ((1 : Real) / 20) -
        ((primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0 : Rat) : Real)| <=
          ((64509243331 : Real) / 500000000000000000000000000000))
    (hResidualDerivBoundOnCell :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖deriv primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.residual eta‖ <=
          ((1866608532757 : Real) / 500000000000000000000000000000)) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert := by
  let derivCert :
      ResidualDerivativeDirectNormCert
        primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert :=
    { cellL := (0 : Real)
      cellU := ((1 : Real) / 10)
      derivSlope :=
        ((1866608532757 : Real) / 500000000000000000000000000000) }
  apply
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell
      (cert := primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert)
      (derivCert := derivCert)
      (sampleRadius :=
        ((64509243331 : Real) / 500000000000000000000000000000))
      (mesh := ((1 : Real) / 20))
      (anchor := ((1 : Real) / 20))
  · intro eta heta
    simpa [derivCert] using hResidualDerivBoundOnCell eta heta
  · rfl
  · rfl
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num
  · norm_num
  · norm_num
  · simpa [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert] using
      hRawCenterCoeffAbs
  · exact
      primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert.residual_differentiableOn_Icc
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert, derivCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert]
  · simpa [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat] using
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioc_zero
        ((1 : Real) / 10) 0)

end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
