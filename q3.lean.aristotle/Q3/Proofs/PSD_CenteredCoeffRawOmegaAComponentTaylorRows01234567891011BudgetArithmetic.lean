import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorRows01234567891011ProductBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Exact rational arithmetic for the rows-0..11 Step33A.1-A component product
budget.

This file keeps the arithmetic split away from the analytic product bridge:
the bridge file proves the source inequality, while this file evaluates the
constant budget in `Rat` before transporting it back to `Real`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0TargetResidualWidthRat : Rat :=
  (1866608532757 : Rat) / 500000000000000000000000000000 -
    (-(94119513411 : Rat) / 500000000000000000000000000000)

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudgetRat :
    Rat :=
  ∑ i : Fin 16,
    |primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff i| *
      ((1 : Rat) / 20) ^ i.1

def primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudgetRat : Rat :=
  ∑ i : Fin 17,
    |primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff i| *
      ((1 : Rat) / 20) ^ i.1

def primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudgetRat :
    Rat :=
  ∑ i : Fin 17,
    |primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff i| *
      ((1 : Rat) / 20) ^ i.1

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudgetRat :
    Rat :=
  ∑ i : Fin 16,
    |primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff i| *
      ((1 : Rat) / 20) ^ i.1

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbsRat :
    Rat :=
  (∑ j : Fin 16,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs j *
        ((1 : Rat) / 20) ^ j.1) +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs *
      ((1 : Rat) / 20) ^ 16 / (Nat.factorial 16 : Rat)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbsRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbsRat *
      ((1 : Rat) / 20)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbsRat :
    Rat :=
  (∑ j : Fin 16,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs j *
        ((1 : Rat) / 20) ^ j.1) +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs *
      ((1 : Rat) / 20) ^ 16 / (Nat.factorial 16 : Rat)

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudgetRat : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudgetRat +
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudgetRat : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudgetRat +
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs

def primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudgetRat : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudgetRat +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbsRat

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudgetRat +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbsRat

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudgetRat *
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTightAbsBudgetRat

def primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudgetRat *
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudgetRat

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudgetRat +
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudgetRat *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbsRat

def primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudgetRat +
    primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudgetRat *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbsRat

def primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs *
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudgetRat +
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudgetRat) +
    primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudgetRat +
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudgetRat)

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_omegaAbs_rowsRemainder_width_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0TargetResidualWidthRat <
      2 *
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
          (primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudgetRat *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbsRat)) := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011ProductAssemblyErrorBudget_width_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0TargetResidualWidthRat <
      2 *
        primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudgetRat := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011TaylorRemainderAbs_eq_rat :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs =
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbsRat :
        Real) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbsRat,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow2CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow3CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow4CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow5CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow6CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow8CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow9CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow10CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
    Fin.sum_univ_succ
  ]

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_omegaRemainder_shapeSqDerivNominal_width_fail :
    ((1866608532757 : Real) / 500000000000000000000000000000 -
        (-(94119513411 : Real) / 500000000000000000000000000000)) <
      2 * ((primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound :
          Real) *
        ((primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
            Real) *
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget)) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound,
    primaryFiniteRow0Parent0Split100Sub0TightScaleUpper,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCenter_generated,
    Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderAbs,
    Fin.sum_univ_succ
  ]

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011ProductAssemblyErrorBudget_width_fail :
    ((1866608532757 : Real) / 500000000000000000000000000000 -
        (-(94119513411 : Real) / 500000000000000000000000000000)) <
      2 * primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget := by
  have hCoreWidth :=
    primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_omegaRemainder_shapeSqDerivNominal_width_fail
  have hScaleAbsNonneg :
      0 <= (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound :
        Real) := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound,
      primaryFiniteRow0Parent0Split100Sub0TightScaleUpper]
  have hScaleErrNonneg :
      0 <= (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs :
        Real) := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs]
  have hOmegaRemNonneg :
      0 <= (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
        Real) := by
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs,
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
  have hShapeNomNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget]
    positivity
  have hRowsRemNonneg :
      0 <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs := by
    rw [primaryFiniteRow0Parent0Split100Sub0_rows01234567891011TaylorRemainderAbs_eq_rat]
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbsRat,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow2CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow3CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow4CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow5CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow6CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow8CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow9CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow10CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
      Fin.sum_univ_succ
    ]
  have hOmegaNomNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaNominalAbsBudget]
    positivity
  have hOmegaAbsNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget]
    linarith
  have hShapeRowsAbsNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011AbsBudget]
    linarith
  have hOmegaShapeDerivAbsNonneg :
      0 <=
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget]
    positivity
  have hShapeSqNomNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqNominalAbsBudget]
    positivity
  have hOmegaPrimeNomNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeNominalAbsBudget]
    positivity
  have hOmegaPrimeAbsNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeAbsBudget]
    linarith
  have hShapeDerivTightRemNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs := by
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs,
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
      Fin.sum_univ_succ
    ]
  have hShapeSqTightFullRemNonneg :
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
    dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs]
    linarith
  have hShapeSqTightAbsNonneg :
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
    nlinarith [
      mul_nonneg hOmegaPrimeRemNonneg hShapeSqNomNonneg,
      mul_nonneg hOmegaPrimeAbsNonneg hShapeSqTightFullRemNonneg]
  have hCoreToOmegaShapeErr :
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          ((primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
              Real) *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget := by
    have hExtra :
        0 <=
          primaryFiniteRow0Parent0Split100Sub0OmegaAbsBudget *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs :=
      mul_nonneg hOmegaAbsNonneg hRowsRemNonneg
    have hTerm :
        (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
            Real) *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget <=
          primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget := by
      dsimp [primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget]
      linarith
    exact mul_le_mul_of_nonneg_left hTerm hScaleAbsNonneg
  have hOmegaShapeErrToErrSum :
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
            primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget) := by
    nlinarith [mul_nonneg hScaleAbsNonneg hOmegaPrimeShapeErrNonneg]
  have hErrSumToBudget :
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightErrBudget +
            primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011ErrBudget) <=
        primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget := by
    have hScalePartNonneg :
        0 <=
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) *
            (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeTightAbsBudget +
              primaryFiniteRow0Parent0Split100Sub0OmegaShapeDerivRows01234567891011AbsBudget) := by
      nlinarith [
        mul_nonneg hScaleErrNonneg
          (add_nonneg hOmegaPrimeShapeAbsNonneg hOmegaShapeDerivAbsNonneg)]
    dsimp [primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget]
    linarith
  have hCoreToBudget :
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          ((primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
              Real) *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivNominalAbsBudget) <=
        primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget :=
    hCoreToOmegaShapeErr.trans
      (hOmegaShapeErrToErrSum.trans hErrSumToBudget)
  nlinarith

end Step33
end PSDpd
end Q3
