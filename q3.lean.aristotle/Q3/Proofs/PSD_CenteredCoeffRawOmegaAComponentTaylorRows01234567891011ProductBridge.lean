import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows01234567891011Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Step33A.1-A component product bridge using the rows-0..11 partial-sharp
ShapeSqDeriv Taylor source.

This file keeps the existing assembled P45 coefficient stream.  The row11
ShapeSqDeriv coefficient stream is definitionally the generated stream, so it
matches the `ShapeSqDerivTaylorCoeff` stream used by the current assembled raw
derivative coefficients; only the ShapeSqDeriv error budget changes.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget :
    Real :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget :
    Real :=
  primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget

def primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget :
    Real :=
  (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs : Real) *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
    primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget :
    Real :=
  (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget) +
    (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011_abs_budget_compare :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_rows01234567891011_abs_budget_compare :
    primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget <=
      primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_rows01234567891011_error_budget_compare :
    (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs : Real) *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
      primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs <=
      primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_final_scale_product_budget_compare :
    (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
          primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget) +
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
          primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget) <=
      primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_component_product_source
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    |(((3 : Real) / 10) / Real.pi) *
          (step22OmegaArchWeightDerivClosedForm eta *
              (centeredBSplineImagTransformRealClosedForm 11
                ((3 : Real) / 10) eta) ^ 2 +
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta *
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta) -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff eta *
              rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta +
            rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff eta *
              rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta)| <=
      primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget := by
  have hRadius :
      |eta - (((1 : Rat) / 20 : Rat) : Real)| <= (1 : Real) / 20 := by
    rw [abs_le]
    constructor
    · have hLeft := hEta.1
      norm_num at hLeft ⊢
      linarith
    · have hRight := hEta.2
      norm_num at hRight ⊢
      linarith
  have hScaleInterval :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_mem_tightInterval
  have hScale :
      |(((3 : Real) / 10) / Real.pi) -
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)| <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) :=
    primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_error_of_active_interval
      hScaleInterval.1 hScaleInterval.2
  have hOmegaPrimeErr :=
    primaryFiniteRow0Parent0Split100Sub0_omegaPrime_factor_error hEta
  have hShapeSqErr :
      |(centeredBSplineImagTransformRealClosedForm 11
            ((3 : Real) / 10) eta) ^ 2 -
          rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta| <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs := by
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqTightFullCellTaylorSource eta
        hEta
    simpa [Real.norm_eq_abs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff] using h
  have hOmegaErr :=
    primaryFiniteRow0Parent0Split100Sub0_omega_factor_error hEta
  have hShapeSqDerivErr :
      |primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta -
          rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta| <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs := by
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567891011TaylorSource
        eta hEta
    simpa [Real.norm_eq_abs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff] using h
  exact
    primaryFiniteRow0Parent0Split100Sub0_product_component_factor_witness_bridge
      (scale := (((3 : Real) / 10) / Real.pi))
      (nominalScale :=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real))
      (omegaPrime := step22OmegaArchWeightDerivClosedForm eta)
      (omegaPrimeNominal :=
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff eta)
      (shapeSq :=
        (centeredBSplineImagTransformRealClosedForm 11
          ((3 : Real) / 10) eta) ^ 2)
      (shapeSqNominal :=
        rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta)
      (omega :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
      (omegaNominal :=
        rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff eta)
      (shapeSqDeriv := primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta)
      (shapeSqDerivNominal :=
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta)
      (scaleErr :=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real))
      (omegaPrimeErr :=
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs :
          Real))
      (shapeSqErr :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs)
      (omegaErr :=
        (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs : Real))
      (shapeSqDerivErr :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs)
      (omegaPrimeNominalAbs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudget)
      (shapeSqNominalAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget)
      (omegaNominalAbs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudget)
      (shapeSqDerivNominalAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget)
      (omegaPrimeAbs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget)
      (shapeSqAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget)
      (omegaAbs := primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget)
      (shapeSqDerivAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget)
      (nominalScaleAbs :=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real))
      (omegaPrimeShapeAbs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget)
      (omegaShapeDerivAbs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget)
      (omegaPrimeShapeErr :=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget)
      (omegaShapeDerivErr :=
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget)
      (budget :=
        primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget)
      hScale hOmegaPrimeErr hShapeSqErr hOmegaErr hShapeSqDerivErr
      (primaryFiniteRow0Parent0Split100Sub0_omegaPrime_nominal_abs_budget hRadius)
      (primaryFiniteRow0Parent0Split100Sub0_shapeSq_nominal_abs_budget hRadius)
      (primaryFiniteRow0Parent0Split100Sub0_omega_nominal_abs_budget hRadius)
      (primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_nominal_abs_budget
        hRadius)
      primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_bound
      primaryFiniteRow0Parent0Split100Sub0_omegaPrime_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_shapeSq_tight_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omega_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeShape_tight_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_rows01234567891011_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeShape_tight_error_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_rows01234567891011_error_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_final_scale_product_budget_compare

theorem primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_rows01234567891011ProductSource
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    |primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta| <=
      primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget := by
  have h :=
    primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_component_product_source
      hEta
  rw [primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_eq_tightProductActual]
  rw [primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct]
  exact h

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_rows01234567891011_enclosure
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖(primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta) -
      rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget := by
  have hSource :=
    primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_rows01234567891011ProductSource
      hEta
  have hCross :=
    primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk
      eta
  have hEq :
      (primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
          rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta) -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta =
        primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
          rawOmegaATaylorPolynomial
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta := by
    rw [← hCross]
    ring
  rw [hEq, Real.norm_eq_abs]
  exact hSource

end Step33
end PSDpd
end Q3
