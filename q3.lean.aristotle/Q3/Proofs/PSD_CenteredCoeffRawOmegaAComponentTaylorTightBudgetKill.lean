import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Fail-closed constant certificate for the coarse Step33A.1-A sub0 component
Taylor source.

The checked source in `PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge`
bounds the full Taylor residual by
`primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget`.
This file proves that the symmetric interval of radius that budget is wider
than the active target residual interval.  It does not kill the Step33A.1-A
route; it only marks the current coarse source as too large for the final
budget receiver.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

theorem primaryFiniteRow0Parent0Split100Sub0_tightProductAssemblyErrorBudget_width_fail :
    ((1866608532757 : Real) / 500000000000000000000000000000 -
        (-(94119513411 : Real) / 500000000000000000000000000000)) <
      2 * primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
  have hCoreWidth :
      ((1866608532757 : Real) / 500000000000000000000000000000 -
          (-(94119513411 : Real) / 500000000000000000000000000000)) <
        2 * ((primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs :
            Real) *
          (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
            Real) *
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs) := by
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs,
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
      Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderAbs,
      Fin.sum_univ_succ
    ]
  have hCoreLe :
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
          (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
            Real) *
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs <=
        primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
    have hScaleErrNonneg :
        0 <= (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs :
          Real) := by
      norm_num [primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs]
    have hScaleAbsNonneg :
        0 <= (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound :
          Real) := by
      norm_num [primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound,
        primaryFiniteRow0Parent0Split100Sub0TightScaleUpper]
    have hOmegaRemNonneg :
        0 <= (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
          Real) := by
      norm_num [primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs,
        primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
        primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper,
        primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs,
        Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderAbs]
    have hOmegaPrimeRemNonneg :
        0 <= (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs :
          Real) := by
      norm_num [
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs,
        Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderAbs]
    have hShapeRemNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs := by
      norm_num [
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs,
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
        Fin.sum_univ_succ
      ]
    have hOmegaNomNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudget]
      positivity
    have hOmegaPrimeNomNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudget]
      positivity
    have hShapeSqNomNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget]
      positivity
    have hShapeNomNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget]
      positivity
    have hShapeFullRemNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs := by
      have hAnchor :
          0 <=
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated :
              Real) := by
        norm_num [
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated]
      have hScaled :
          0 <=
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs *
              ((1 : Real) / 20) := by
        positivity
      dsimp [
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs]
      linarith
    have hOmegaAbsLower :
        (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
          Real) <= primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget]
      linarith
    have hShapeAbsLower :
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs <=
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget]
      linarith
    have hOmegaAbsNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget := by
      linarith
    have hShapeAbsNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget := by
      linarith
    have hOmegaPrimeAbsNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget]
      linarith
    have hShapeTightAbsNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudget]
      linarith
    have hOmegaPrimeShapeAbsNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget]
      positivity
    have hOmegaPrimeShapeErrNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget]
      positivity
    have hOmegaShapeDerivErrNonneg :
        0 <= primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget]
      positivity
    have hCoreToShape :
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
            (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
              Real) *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs <=
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
            primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget := by
      have hProd :
          (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
              Real) *
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs <=
            primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget :=
        mul_le_mul hOmegaAbsLower hShapeAbsLower hShapeRemNonneg hOmegaAbsNonneg
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hProd hScaleErrNonneg
    have hShapeToBudget :
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
            primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget <=
          primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
      have hAddPrime :
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
              primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget <=
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
              (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
                primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget) := by
        dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget]
        nlinarith [mul_nonneg hScaleErrNonneg hOmegaPrimeShapeAbsNonneg]
      have hAddErr :
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
              (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
                primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget) <=
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
                (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
                  primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget) +
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
                (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
                  primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget) := by
        nlinarith [
          mul_nonneg hScaleAbsNonneg
            (add_nonneg hOmegaPrimeShapeErrNonneg hOmegaShapeDerivErrNonneg)]
      calc
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
            primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightAbsBudget
            <=
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
            (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
              primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget) := hAddPrime
        _ <=
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
              (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
                primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightAbsBudget) +
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
              (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
                primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivTightErrBudget) := hAddErr
        _ = primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
          rfl
    exact hCoreToShape.trans hShapeToBudget
  nlinarith

end Step33
end PSDpd
end Q3
