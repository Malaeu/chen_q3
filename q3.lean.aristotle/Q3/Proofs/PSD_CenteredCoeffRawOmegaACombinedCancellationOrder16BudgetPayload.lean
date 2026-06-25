import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-!
Exact rational order-16 budget audit for the Step33A.1-A sub0 combined
cancellation route.

This file is fail-closed: it records the rational mirror of the checked
centered-Taylor factor-majorant budget and proves that the resulting order-16
Taylor-remainder contribution is already wider than the current one-cell
combined-cancellation half-width.  It therefore does not provide the
order-16 source interval row, degree-15 Horner range rows, target-budget rows,
or a full `Step33Sub0CombinedCancellationSourceIntervalCert.Valid` payload.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Concrete rational order-16 absolute source budget for the active subcell. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16Abs :
    Rat :=
  10000000000000000000000000000000000000000000000000000000000000000000000

private def primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
    (jetAbs : Nat -> Rat) (order16Abs radius : Rat) (k : Nat) : Rat :=
  (∑ j ∈ Finset.range 16,
      if k <= j then
        ((Nat.factorial j : Rat) / (Nat.factorial (j - k) : Rat)) *
          jetAbs j * radius ^ (j - k)
      else
        0) +
    order16Abs * radius ^ (16 - k) / (Nat.factorial (16 - k) : Rat)

private def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedOrder16Abs
      ((1 : Rat) / 20) k
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs
      ((1 : Rat) / 20) k
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16MajorantRat :
    Rat :=
  (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Rat) *
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat i *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorantRat (16 - i)) +
    (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Rat) *
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorantRat i *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorantRat (16 - i))

private def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16BudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16MajorantRat

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_activeScaleAbs :
    |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16BudgetRat_le_declaredAbs :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16BudgetRat <=
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16Abs := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth <
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16BudgetRat *
        ((1 : Rat) / 20) ^ 16 / (Nat.factorial 16 : Rat) := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail :
    (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth :
        Real) <
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16BudgetRat :
        Real) *
        ((1 : Real) / 20) ^ 16 / (Nat.factorial 16 : Real) := by
  have hRat :=
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail_rat
  have hReal :
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth :
          Real) <
        ((primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16BudgetRat *
          ((1 : Rat) / 20) ^ 16 / (Nat.factorial 16 : Rat) : Rat) :
            Real) := by
    exact_mod_cast hRat
  simpa [Rat.cast_mul, Rat.cast_div, Rat.cast_pow] using hReal

end Step33
end PSDpd
end Q3
