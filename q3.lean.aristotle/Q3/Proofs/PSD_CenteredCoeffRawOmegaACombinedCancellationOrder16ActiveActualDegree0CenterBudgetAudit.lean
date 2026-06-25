import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0Source
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18BudgetAudit
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16RawProduct17BudgetAudit
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-!
Degree-0 center and budget audit for the active-actual order-16 source.

This file closes only the degree-0 center/budget interface requested by
`PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0Source`.
It uses the checked normal form
`D^16(ComponentProductActual) = D^17(RawProductActual)` at the cell center for
the anchor and the already-checked RawProduct18 audit for the uniform D17
source.  It does not spend the killed rawProduct17 zero-model budget.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0 : Rat :=
  0

def primaryFiniteRow0Parent0Split100Sub0Degree0OmegaPrimeActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs j.1)
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert.order16Abs
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem
    primaryFiniteRow0Parent0Split100Sub0_degree0_omegaPrimeActualDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Degree0OmegaPrimeActualDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Degree0OmegaPrimeActualDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast]
  · simp [hk]

def primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs j.1)
      (primaryFiniteRow0Parent0Split100Sub0Degree0OmegaPrimeActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem
    primaryFiniteRow0Parent0Split100Sub0_degree0_omegaActualDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast,
      primaryFiniteRow0Parent0Split100Sub0_degree0_omegaPrimeActualDerivativeMajorantRat_cast]
  · simp [hk]

def primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorant17Rat
    (k : Nat) : Rat :=
  if _hk : k < 18 then
    if _hk16 : k <= 16 then
      primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorantRat k
    else
      primaryFiniteRow0Parent0Split100Sub0Degree0OmegaPrimeActualDerivativeMajorantRat
        16
  else
    0

theorem
    primaryFiniteRow0Parent0Split100Sub0_degree0_omegaActualDerivativeMajorant17Rat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorant17Rat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17 k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorant17Rat
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
  by_cases hk : k < 18
  · simp [hk]
    by_cases hk16 : k <= 16
    · simp [hk16,
        primaryFiniteRow0Parent0Split100Sub0_degree0_omegaActualDerivativeMajorantRat_cast]
    · simp [hk16,
        primaryFiniteRow0Parent0Split100Sub0_degree0_omegaPrimeActualDerivativeMajorantRat_cast]
  · simp [hk]

def primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqDerivActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs j.1)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem
    primaryFiniteRow0Parent0Split100Sub0_degree0_shapeSqDerivActualDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqDerivActualDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
        k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqDerivActualDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast]
  · simp [hk]

def primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if hk : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0Order18CenteredTaylorDerivMajorant16Rat
      (fun j : Fin 16 =>
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs j.1)
      (primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqDerivActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20)
      ⟨k, hk⟩
  else
    0

theorem
    primaryFiniteRow0Parent0Split100Sub0_degree0_shapeSqActualDerivativeMajorantRat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorantRat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
        k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorantRat
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
  by_cases hk : k < 17
  · simp [hk,
      primaryFiniteRow0Parent0Split100Sub0_order18_centeredTaylorDerivMajorant16Rat_cast,
      primaryFiniteRow0Parent0Split100Sub0_degree0_shapeSqDerivActualDerivativeMajorantRat_cast]
  · simp [hk]

def primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorant17Rat
    (k : Nat) : Rat :=
  if _hk : k < 18 then
    if _hk16 : k <= 16 then
      primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorantRat k
    else
      primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqDerivActualDerivativeMajorantRat
        16
  else
    0

theorem
    primaryFiniteRow0Parent0Split100Sub0_degree0_shapeSqActualDerivativeMajorant17Rat_cast
    (k : Nat) :
    (primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorant17Rat
        k : Real) =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17
        k := by
  unfold primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorant17Rat
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17
  by_cases hk : k < 18
  · simp [hk]
    by_cases hk16 : k <= 16
    · simp [hk16,
        primaryFiniteRow0Parent0Split100Sub0_degree0_shapeSqActualDerivativeMajorantRat_cast]
    · simp [hk16,
        primaryFiniteRow0Parent0Split100Sub0_degree0_shapeSqDerivActualDerivativeMajorantRat_cast]
  · simp [hk]

def primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0RawProduct17MajorantRat :
    Rat :=
  ∑ i ∈ Finset.range (17 + 1),
    (Nat.choose 17 i : Rat) *
      primaryFiniteRow0Parent0Split100Sub0Degree0OmegaActualDerivativeMajorant17Rat i *
      primaryFiniteRow0Parent0Split100Sub0Degree0ShapeSqActualDerivativeMajorant17Rat
        (17 - i)

theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_rawProduct17Majorant_eq_rat :
    primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17 =
      (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0RawProduct17MajorantRat :
        Real) := by
  unfold primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant
  unfold primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0RawProduct17MajorantRat
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Rat.cast_mul, Rat.cast_mul]
  rw [primaryFiniteRow0Parent0Split100Sub0_degree0_omegaActualDerivativeMajorant17Rat_cast]
  rw [primaryFiniteRow0Parent0Split100Sub0_degree0_shapeSqActualDerivativeMajorant17Rat_cast]
  norm_num

def primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0RawProduct17MajorantRat

def primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Order17Abs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat

def primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0PolyErrorAbs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs +
    primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
      primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Order17Abs / 20

theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_center_abs_le_rawProduct17 :
    ‖iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          ((1 : Real) / 20)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0RawProduct17MajorantRat :
        Real) := by
  have hCenter :
      ((1 : Real) / 20) ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
    norm_num
  have hRaw :=
    primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_centeredTaylor17
      ((1 : Real) / 20) hCenter
  rw [
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_rawProduct17]
  simpa [
    primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_rawProduct17Majorant_eq_rat]
    using hRaw

theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_center_enclosure_of_rawProduct17 :
    ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
              ((1 : Real) / 20) -
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0 :
          Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs :
        Real) := by
  have hScale :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound
  have hRaw :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_center_abs_le_rawProduct17
  have hScaleNonneg :
      0 <= (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound :
        Real) := by
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound,
      primaryFiniteRow0Parent0Split100Sub0TightScaleUpper]
  rw [primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0, Rat.cast_zero,
    sub_zero]
  calc
    ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
            ((1 : Real) / 20)‖ =
        |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| *
          ‖iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
              ((1 : Real) / 20)‖ := by
          rw [norm_mul, Real.norm_eq_abs]
    _ <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0RawProduct17MajorantRat :
            Real) :=
          mul_le_mul hScale hRaw (norm_nonneg _) hScaleNonneg
    _ =
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs :
          Real) := by
          simp [primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs]

theorem primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_hCenter_generated :
    ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
              ((1 : Real) / 20) -
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0 :
          Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs :
        Real) :=
  primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_center_enclosure_of_rawProduct17

theorem primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_budget_pass_rat :
    (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs :
        Real) +
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Order17Abs :
          Real) *
          ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0PolyErrorAbs :
          Real) := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0PolyErrorAbs]
  ring_nf
  exact le_rfl

theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_directPayloadBudget_fail_q :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0PolyErrorAbs := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_directPayloadBudget_fail_rat :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
        Real) <
      (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0PolyErrorAbs :
        Real) := by
  exact_mod_cast
    primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_directPayloadBudget_fail_q

theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_budget_generated :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
              (by norm_num : 0 <= 29)
              (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0))
            eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0PolyErrorAbs :
          Real) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17
      (coeff0 := primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff0)
      (coeffErrorAbs :=
        primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0CoeffErrorAbs)
      (activeScaleAbs :=
        primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound)
      (order17Abs :=
        primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Order17Abs)
      (polyErrorAbs :=
        primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0PolyErrorAbs)
      primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound
      primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_hCenter_generated
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_rat
      primaryFiniteRow0Parent0Split100Sub0_activeActual_degree0_budget_pass_rat

end Step33
end PSDpd
end Q3
