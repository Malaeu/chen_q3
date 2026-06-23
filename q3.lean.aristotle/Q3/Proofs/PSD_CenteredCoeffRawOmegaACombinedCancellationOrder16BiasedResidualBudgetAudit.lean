import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-!
Exact rational budget audit for the Step33A.1-A sub0 biased residual route.

This file is fail-closed.  It mirrors the existing centered-Taylor factor
majorant arithmetic in `Rat` and proves that the symmetric whole-cell absolute
majorant is too large for the current biased residual slack.  It does not emit
segment rows, signed intervals, or a
`Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert.Valid`
payload.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorDerivMajorant16Rat
    (jetAbs : Nat -> Rat) (order16Abs radius : Rat) (k : Nat) : Rat :=
  (∑ j ∈ Finset.range 16,
      if k <= j then
        ((Nat.factorial j : Rat) / (Nat.factorial (j - k) : Rat)) *
          jetAbs j * radius ^ (j - k)
      else
        0) +
    order16Abs * radius ^ (16 - k) / (Nat.factorial (16 - k) : Rat)

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualOmegaPrimeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert.order16Abs
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualShapeSqDerivMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualOmegaMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0BiasedResidualOmegaPrimeMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualShapeSqMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0BiasedResidualShapeSqDerivMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualComponentProductActualOrder16MajorantRat :
    Rat :=
  (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Rat) *
        primaryFiniteRow0Parent0Split100Sub0BiasedResidualOmegaPrimeMajorantRat i *
        primaryFiniteRow0Parent0Split100Sub0BiasedResidualShapeSqMajorantRat (16 - i)) +
    (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Rat) *
        primaryFiniteRow0Parent0Split100Sub0BiasedResidualOmegaMajorantRat i *
        primaryFiniteRow0Parent0Split100Sub0BiasedResidualShapeSqDerivMajorantRat (16 - i))

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorSourceAbsRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0BiasedResidualComponentProductActualOrder16MajorantRat

def primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat :
    Rat :=
  max
    (primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorSourceAbsRat +
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper)
    (primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorSourceAbsRat -
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower)

theorem
    primaryFiniteRow0Parent0Split100Sub0_biasedResidual_centeredTaylorNeededAbs_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat <
      primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_centeredTaylor_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat <
      primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat :=
  primaryFiniteRow0Parent0Split100Sub0_biasedResidual_centeredTaylorNeededAbs_budget_fail_rat

theorem
    primaryFiniteRow0Parent0Split100Sub0_biasedResidual_centeredTaylorNeededAbs_not_budgeted_rat :
    ¬ primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat <=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_centeredTaylor_not_spendable :
    ¬ (primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat :
        Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
        Real) := by
  exact not_le_of_gt (by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_centeredTaylor_budget_fail_rat)

end Step33
end PSDpd
end Q3
