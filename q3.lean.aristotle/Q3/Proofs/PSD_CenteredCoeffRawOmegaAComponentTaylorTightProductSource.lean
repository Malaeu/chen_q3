import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqTightFullCellSource

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-grade, nonfinal component product source for Step33A.1-A sub0.

This file replaces the half-cell generated ShapeSq wrappers by the checked
full-cell same-coefficient ShapeSq/ShapeSqDeriv sources.  The resulting product
budget is deliberately coarse and is only a source certificate for the next
component Taylor remainder bridge.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget : Real :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget : Real :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget : Real :=
  primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget *
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget

def primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget : Real :=
  primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget : Real :=
  (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs : Real) *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget +
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget : Real :=
  (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs : Real) *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
    primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget :
    Real :=
  (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget) +
    (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSq_tight_abs_budget_compare :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget +
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_abs_budget_compare :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrimeShape_tight_abs_budget_compare :
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget <=
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_tight_abs_budget_compare :
    primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget <=
      primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrimeShape_tight_error_budget_compare :
    (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs : Real) *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget +
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs <=
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_tight_error_budget_compare :
    (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs : Real) *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget +
      primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs <=
      primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_tight_final_scale_product_budget_compare :
    (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
          primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget) +
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
          primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget) <=
      primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget]
  exact le_rfl

theorem primaryFiniteRow0Parent0Split100Sub0_tight_component_product_source
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
      primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
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
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs := by
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTightTaylorSource eta hEta
    simpa [Real.norm_eq_abs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff] using h
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
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs)
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
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget)
      (nominalScaleAbs :=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real))
      (omegaPrimeShapeAbs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget)
      (omegaShapeDerivAbs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget)
      (omegaPrimeShapeErr :=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget)
      (omegaShapeDerivErr :=
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget)
      (budget :=
        primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget)
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
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeShape_tight_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_tight_abs_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeShape_tight_error_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_omegaShapeDeriv_tight_error_budget_compare
      primaryFiniteRow0Parent0Split100Sub0_tight_final_scale_product_budget_compare

end Step33
end PSDpd
end Q3
