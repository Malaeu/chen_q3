import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincShapeSqPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Same-coefficient ShapeSqDeriv payload for Step33A.1-A sub0.

This file identifies the coefficient stream consumed by the active component
assembly with a proof-bearing `ShapeSqDerivTaylorIntervalCert.Valid` object.
The error/order budgets are intentionally coarse; this closes only the
same-coefficient proof object and does not claim the final component residual
budget is small enough.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Same coefficient stream as the active generated ShapeSqDeriv Taylor source. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff :
    Fin 16 -> Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated

/-- Coarse proof budget for the same-coefficient ShapeSqDeriv rows. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs
    (_ : Fin 16) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget + 1

/-- Coarse order-16 proof budget for the same-coefficient ShapeSqDeriv payload. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs :
    Real :=
  (∑ j : Fin 16,
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs j :
        Real) *
        ((1 : Real) / 20) ^ j.1) +
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs : Real) *
      ((1 : Real) / 20) ^ 16 / (Nat.factorial 16 : Real)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tightCoeff_eq_generated :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated := by
  rfl

/-- Proof-grade same-coefficient ShapeSqDeriv interval certificate.

The coefficient stream is the active generated stream.  The row and order
budgets are still coarse, so downstream residual/budget checks must remain
fail-closed until a sharper certificate is available or the coarse budget is
shown sufficient.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid :
    (ShapeSqDerivTaylorIntervalCert.singleAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs).Valid := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shape_derivative_abs
      (centerM := fun _ k =>
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs k)
      (cellM := fun k =>
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs k)
      ?hCoeffErrorNonneg ?hCenterMNonneg ?hCenterShapeDerivAbs
      ?hCenterBudget ?hCellMNonneg ?hCellShapeDerivAbs ?hOrder17Budget
  · intro j
    norm_num
      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
       primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]
  · intro j k hk
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs
    positivity
  · intro j k hk
    have hcenter :
        ((1 : Real) / 20) ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      norm_num
    have hk17 : k <= 17 := by
      omega
    exact
      primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational
        ((1 : Real) / 20) hcenter k hk17
  · intro j
    let n : Nat := j.1 + 1
    have hn_le : n <= 17 := by
      dsimp [n]
      omega
    have hsum :
        (∑ i ∈ Finset.range (j.1 + 1 + 1),
            ((j.1 + 1).choose i : Real) *
              primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs i *
              primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
                (j.1 + 1 - i)) =
          (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (j.1 + 1) := by
      simpa [n] using
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq n
    have hfac_ge_one_nat : 1 <= Nat.factorial j.1 :=
      Nat.succ_le_of_lt (Nat.factorial_pos j.1)
    have hfac_ge_one : (1 : Real) <= (Nat.factorial j.1 : Real) := by
      exact_mod_cast hfac_ge_one_nat
    have hpow_le :
        (24 : Real) ^ (j.1 + 1) <= (24 : Real) ^ (17 : Nat) :=
      pow_le_pow_right₀ (by norm_num) hn_le
    have hmain_nonneg :
        0 <= (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (j.1 + 1) := by
      positivity
    have hdiv_le :
        ((2 : Real) ^ (24 : Nat) * (24 : Real) ^ (j.1 + 1)) /
            (Nat.factorial j.1 : Real) <=
          (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (j.1 + 1) :=
      div_le_self hmain_nonneg hfac_ge_one
    have hmain_le_budget :
        (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (j.1 + 1) <=
          (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (17 : Nat) := by
      exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
    have hcoeff_abs_le_one :
        ‖(primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff j :
            Real)‖ <=
          (1 : Real) := by
      fin_cases j <;>
        norm_num
          [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCenter_generated]
    calc
      (∑ i ∈ Finset.range (j.1 + 1 + 1),
          ((j.1 + 1).choose i : Real) *
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs i *
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
              (j.1 + 1 - i)) /
          (Nat.factorial j.1 : Real) +
          ‖(primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff j :
            Real)‖
          <=
        (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (17 : Nat) + 1 := by
          rw [hsum]
          exact add_le_add (le_trans hdiv_le hmain_le_budget) hcoeff_abs_le_one
      _ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs
          j : Real) := by
          norm_num
            [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
             primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]
  · intro k hk
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs
    positivity
  · exact
      primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational
  · rw [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq]
    norm_num
      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs,
       primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTightTaylorSource :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta -
        rawOmegaATaylorPolynomial 15 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs := by
  exact
    ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource
      (data := ShapeSqDerivTaylorIntervalCert.singleAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs)
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs)
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
      (by
        unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs
        rfl)

end Step33
end PSDpd
end Q3
