import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincScaledPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Coarse ShapeSqDeriv interval payload induced by the proof-grade realSinc
coarse derivative majorant.

This file is intentionally coarse.  It proves that the checked rational
shape-derivative majorant is enough to build a `singleAbs` interval
certificate for the active ShapeSqDeriv receiver.  It does not claim that the
resulting constants are sharp enough for the final Taylor payload.
-/

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Coarse product budget for the active shape-square derivative layer. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget : Rat :=
  (2 : Rat) ^ (24 : Nat) * (24 : Rat) ^ (17 : Nat)

/-- Coarse center coefficients for the active ShapeSqDeriv interval cert. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
    (_ : Fin 16) : Rat :=
  0

/-- Coarse coefficient error budget for the active ShapeSqDeriv interval cert. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs
    (_ : Fin 16) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget

/-- Coarse order-16 derivative budget for the active ShapeSqDeriv interval
cert. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqOrder16Abs : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget

/-- Closed product sum for the rational coarse shape derivative budget. -/
theorem primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq
    (n : Nat) :
    (∑ i ∈ Finset.range (n + 1),
      (n.choose i : Real) *
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs i *
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs (n - i)) =
      (2 : Real) ^ (24 : Nat) * (24 : Real) ^ n := by
  calc
    (∑ i ∈ Finset.range (n + 1),
      (n.choose i : Real) *
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs i *
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs (n - i)) =
        ∑ i ∈ Finset.range (n + 1),
          (2 : Real) ^ (24 : Nat) * (12 : Real) ^ i *
            (12 : Real) ^ (n - i) * (n.choose i : Real) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs,
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs]
      ring
    _ = (2 : Real) ^ (24 : Nat) * ((12 : Real) + 12) ^ n := by
      rw [add_pow]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = (2 : Real) ^ (24 : Nat) * (24 : Real) ^ n := by
      norm_num

/-- Coarse proof-grade ShapeSqDeriv interval certificate induced by the
coarse realSinc payload. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_coarseTwo :
    (ShapeSqDerivTaylorIntervalCert.singleAbs
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqOrder16Abs).Valid := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shape_derivative_abs
      (centerM := fun _ k =>
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs k)
      (cellM := fun k =>
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs k)
      ?hCoeffErrorNonneg ?hCenterMNonneg ?hCenterShapeDerivAbs
      ?hCenterBudget ?hCellMNonneg ?hCellShapeDerivAbs ?hOrder17Budget
  · intro j
    norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]
  · intro j k hk
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs
    positivity
  · intro j k hk
    have hk17 : k <= 17 := by omega
    have hcenter : (1 : Real) / 20 ∈
        Set.Icc (0 : Real) ((1 : Real) / 10) := by
      norm_num
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
    calc
      (∑ i ∈ Finset.range (j.1 + 1 + 1),
          ((j.1 + 1).choose i : Real) *
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs i *
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
              (j.1 + 1 - i)) /
          (Nat.factorial j.1 : Real) +
          ‖(primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff j : Real)‖ =
        ((2 : Real) ^ (24 : Nat) * (24 : Real) ^ (j.1 + 1)) /
          (Nat.factorial j.1 : Real) := by
        rw [hsum]
        norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff]
      _ <= (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (j.1 + 1) :=
        hdiv_le
      _ <= (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs
            j : Real) := by
        exact le_trans hmain_le_budget (by
          norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs,
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget])
  · intro k hk
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
    unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs
    positivity
  · exact
      primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational
  · rw [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq]
    norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqOrder16Abs,
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]

end Step33
end PSDpd
end Q3
