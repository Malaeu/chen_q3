import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-bearing coefficient rows for the active Step33A.1-A ShapeSqDeriv
Taylor interval certificate.

This file is intentionally isolated from `Q3.Main`: it imports the generated
endpoint package and the high-order power-series bridge, then closes only the
first coefficient row.  It does not claim the full ShapeSqDeriv Taylor payload;
rows `1..15` and the full-cell order-16 bound remain open obligations.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated :
    Real :=
  ((-46448578038952412672149872160407802487877144879577655939872927993464875466132202360827276104665062142415173687016462681408869026457238530060336008763092149959616648869724829277353 : Real) /
    (312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated :
    Real :=
  ((-3715886243116193013422691188469113889347186857741575631430658701842124693104660254420490862373908779177392095867429176165007789167568948045769667316015512783831667117451096516791 : Real) /
    (25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated :
    Real :=
  (-1 : Real) / 25

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated :
    Real :=
  (1 : Real) / 25

/-- First proof-grade coefficient row for the active ShapeSqDeriv center
power series.

The generated endpoint package already proves a derivative interval for
`deriv (fun t => E(t)^2)` at the row anchor `1/20`.  The high-order support
file proves that the zeroth coefficient of the chosen local ShapeSqDeriv
power series is the zeroth normalized center jet.  This lemma performs only
that transfer for `j = 0`.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff0_interval_generated :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 0 ∧
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 0 <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated := by
  have hCoeff :
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 0 =
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv ((1 : Real) / 20) := by
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff
        ⟨0, by norm_num⟩
    simpa using h.symm
  have hCenterMem :
      ((1 : Real) / 20) ∈
        Set.Icc
          ((499999999999999999999 : Real) /
            (10000000000000000000000 : Real))
          ((1 : Real) / 20) := by
    constructor <;> norm_num
  constructor
  · rw [hCoeff]
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated] using
      primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hDerivLower
        ((1 : Real) / 20) hCenterMem
  · rw [hCoeff]
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated] using
      primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hDerivUpper
        ((1 : Real) / 20) hCenterMem

/-- Local second-derivative bridge for the active ShapeSqDeriv center.

This is deliberately coarse: it only rewrites the derivative of
`ShapeSqDeriv` at the center into the product-rule form
`2 * E' * E' + 2 * E * E''`.  The interval lemma below supplies broad
rational bounds from already checked anchor and `E''` norm facts.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_center_deriv_formula :
    deriv primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
        ((1 : Real) / 20) =
      2 *
          centeredBSplineImagTransformRealClosedFormDerivClosedForm
            11 ((3 : Real) / 10) ((1 : Real) / 20) *
          centeredBSplineImagTransformRealClosedFormDerivClosedForm
            11 ((3 : Real) / 10) ((1 : Real) / 20) +
        2 *
          centeredBSplineImagTransformRealClosedForm
            11 ((3 : Real) / 10) ((1 : Real) / 20) *
          deriv
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedFormDerivClosedForm
                11 ((3 : Real) / 10) t)
            ((1 : Real) / 20) := by
  have hfun :
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv =
        (fun eta : Real =>
          2 *
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) eta *
            centeredBSplineImagTransformRealClosedFormDerivClosedForm
              11 ((3 : Real) / 10) eta) := by
    funext eta
    simp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv,
      deriv_centeredBSplineImagTransformRealClosedForm_sq,
      centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm]
  rw [hfun]
  let A : Real -> Real := fun eta : Real =>
    2 *
      centeredBSplineImagTransformRealClosedForm
        11 ((3 : Real) / 10) eta
  let B : Real -> Real := fun eta : Real =>
    centeredBSplineImagTransformRealClosedFormDerivClosedForm
      11 ((3 : Real) / 10) eta
  have hA : DifferentiableAt Real A ((1 : Real) / 20) := by
    dsimp [A]
    exact
      (CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformRealClosedForm_differentiableAt
        11 ((3 : Real) / 10) ((1 : Real) / 20)).const_mul 2
  have hB : DifferentiableAt Real B ((1 : Real) / 20) := by
    dsimp [B]
    exact primaryK11ShapeDerivClosedForm_differentiableAt_of_pos (by norm_num)
  have hprod := deriv_mul hA hB
  have hprod' :
      deriv (fun eta : Real => A eta * B eta) ((1 : Real) / 20) =
        deriv A ((1 : Real) / 20) * B ((1 : Real) / 20) +
          A ((1 : Real) / 20) * deriv B ((1 : Real) / 20) := by
    simpa [Pi.mul_apply] using hprod
  have hAderiv :
      deriv A ((1 : Real) / 20) =
        2 *
          centeredBSplineImagTransformRealClosedFormDerivClosedForm
            11 ((3 : Real) / 10) ((1 : Real) / 20) := by
    dsimp [A]
    rw [deriv_const_mul]
    · rw [centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm]
    · exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformRealClosedForm_differentiableAt
          11 ((3 : Real) / 10) ((1 : Real) / 20)
  have hBderiv :
      deriv B ((1 : Real) / 20) =
        deriv
          (fun t : Real =>
            centeredBSplineImagTransformRealClosedFormDerivClosedForm
              11 ((3 : Real) / 10) t)
          ((1 : Real) / 20) := by
    rfl
  change deriv (fun eta : Real => A eta * B eta) ((1 : Real) / 20) = _
  rw [hprod', hAderiv, hBderiv]

/-- Second proof-grade coefficient row for the active ShapeSqDeriv center
power series.

The interval is intentionally wide.  It uses the checked anchor facts
`0 <= E <= 1`, `-1/10 <= E' <= 0`, and the existing uniform bound
`|E''| <= 1/100` at the center to prove
`-1/25 <= coeff 1 <= 1/25`.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff1_interval_generated :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 1 ∧
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 1 <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated := by
  let c : Real := (1 : Real) / 20
  let E : Real :=
    centeredBSplineImagTransformRealClosedForm
      11 ((3 : Real) / 10) c
  let D : Real :=
    centeredBSplineImagTransformRealClosedFormDerivClosedForm
      11 ((3 : Real) / 10) c
  let DD : Real :=
    deriv
      (fun t : Real =>
        centeredBSplineImagTransformRealClosedFormDerivClosedForm
          11 ((3 : Real) / 10) t)
      c
  have hCoeff :
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 1 =
        deriv primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv c := by
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff
        ⟨1, by norm_num⟩
    dsimp [c]
    simpa [iteratedDeriv] using h.symm
  have hDerivFormula :
      deriv primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv c =
        2 * D * D + 2 * E * DD := by
    dsimp [c, E, D, DD]
    exact primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_center_deriv_formula
  have hCenterMem :
      c ∈
        Set.Icc
          ((499999999999999999999 : Real) /
            (10000000000000000000000 : Real))
          ((1 : Real) / 20) := by
    dsimp [c]
    constructor <;> norm_num
  have hE0 : (0 : Real) <= E := by
    dsimp [E, c]
    linarith [primaryFiniteRow0Parent0Split100Sub0ShapeAnchorValueBounds_generated.1]
  have hE1 : E <= (1 : Real) := by
    dsimp [E, c]
    linarith [primaryFiniteRow0Parent0Split100Sub0ShapeAnchorValueBounds_generated.2]
  have hDLower : ((-1 : Real) / 10) <= D := by
    dsimp [D, c]
    linarith [primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated.1]
  have hDUpper : D <= (0 : Real) := by
    dsimp [D, c]
    linarith [primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated.2]
  have hDDNorm :=
    primaryFiniteRow0Parent0Split100Sub0ShapeDerivClosedForm_second_deriv_bound_cubic
      c hCenterMem
  have hDDAbs : |DD| <= ((1 : Real) / 100) := by
    dsimp [DD] at hDDNorm
    simpa [Real.norm_eq_abs] using hDDNorm
  have hDDLower : ((-1 : Real) / 100) <= DD := by
    linarith [(abs_le.mp hDDAbs).1]
  have hDDUpper : DD <= ((1 : Real) / 100) :=
    (abs_le.mp hDDAbs).2
  have hDTerm :
      (0 : Real) <= 2 * D * D ∧
        2 * D * D <= ((1 : Real) / 50) := by
    exact
      const_mul_mul_interval_bounds_of_four_corners
        (scale := (2 : Real))
        (a := ((-1 : Real) / 10)) (b := (0 : Real))
        (c := ((-1 : Real) / 10)) (d := (0 : Real))
        (x := D) (y := D)
        (lower := (0 : Real)) (upper := ((1 : Real) / 50))
        hDLower hDUpper hDLower hDUpper
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hEDTerm :
      ((-1 : Real) / 50) <= 2 * E * DD ∧
        2 * E * DD <= ((1 : Real) / 50) := by
    exact
      const_mul_mul_interval_bounds_of_four_corners
        (scale := (2 : Real))
        (a := (0 : Real)) (b := (1 : Real))
        (c := ((-1 : Real) / 100)) (d := ((1 : Real) / 100))
        (x := E) (y := DD)
        (lower := ((-1 : Real) / 50))
        (upper := ((1 : Real) / 50))
        hE0 hE1 hDDLower hDDUpper
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · rw [hCoeff, hDerivFormula]
    dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated]
    linarith [hDTerm.1, hEDTerm.1]
  · rw [hCoeff, hDerivFormula]
    dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated]
    linarith [hDTerm.2, hEDTerm.2]

end Step33
end PSDpd
end Q3
