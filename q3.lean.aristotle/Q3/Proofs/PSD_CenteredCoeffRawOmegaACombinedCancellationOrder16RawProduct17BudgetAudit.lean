import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NormalForm

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-!
Exact rational budget audit for the Step33A.1-A sub0 rawProduct17 bridge.

The normal-form file proves a formal interface reducing the zero-model
remainder to a bound for `D^17(OmegaActual * ShapeSqActual)`.  This file mirrors
the checked centeredTaylor majorant in `Rat` and records the exact arithmetic
verdict for spending that majorant against the current zero-model threshold.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
    (jetAbs : Nat -> Rat) (order16Abs radius : Rat) (k : Nat) : Rat :=
  (∑ j ∈ Finset.range 16,
      if k <= j then
        ((Nat.factorial j : Rat) / (Nat.factorial (j - k) : Rat)) *
          jetAbs j * radius ^ (j - k)
      else
        0) +
    order16Abs * radius ^ (16 - k) / (Nat.factorial (16 - k) : Rat)

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedOrder16Abs
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17Rat
    (k : Nat) : Rat :=
  if k < 18 then
    if k <= 16 then
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorantRat k
    else
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat
        16
  else
    0

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17Rat
    (k : Nat) : Rat :=
  if k < 18 then
    if k <= 16 then
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorantRat k
    else
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorantRat
        16
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17MajorantRat :
    Rat :=
  ∑ i ∈ Finset.range (17 + 1),
    (Nat.choose 17 i : Rat) *
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17Rat i *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17Rat
        (17 - i)

def primaryFiniteRow0Parent0Split100Sub0RawProduct17LowerScaleBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0TightScaleLower *
    primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17MajorantRat

def primaryFiniteRow0Parent0Split100Sub0RawProduct17NominalScaleBudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17MajorantRat

theorem primaryFiniteRow0Parent0Split100Sub0_rawProduct17_lowerScaleBudget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs <
      primaryFiniteRow0Parent0Split100Sub0RawProduct17LowerScaleBudgetRat := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_rawProduct17_nominalScaleBudget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs <
      primaryFiniteRow0Parent0Split100Sub0RawProduct17NominalScaleBudgetRat := by
  native_decide

end Step33
end PSDpd
end Q3
