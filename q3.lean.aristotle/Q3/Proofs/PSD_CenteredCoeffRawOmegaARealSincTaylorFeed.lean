import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincShapeSqPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

/-!
Coarse Taylor-source feed for the active Step33A.1-A ShapeSqDeriv layer.

This file checks only the interface from the proof-grade coarse ShapeSqDeriv
interval certificate into the existing Taylor-source receiver.  The resulting
budget is deliberately coarse and is not claimed to be sharp enough for the
final chunk certificate.
-/

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- The exact coarse ShapeSqDeriv interval certificate data used by the Taylor
source feed below. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData :
    ShapeSqDerivTaylorIntervalCert :=
  ShapeSqDerivTaylorIntervalCert.singleAbs
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqOrder16Abs

/-- Exact remainder expression required by
`ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource` for the
coarse certificate. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs :
    Real :=
  (∑ j : Fin 16,
      (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs j :
        Real) *
        ((1 : Real) / 20) ^ j.1) +
    (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqOrder16Abs : Real) *
      ((1 : Real) / 20) ^ 16 / (Nat.factorial 16 : Real)

/-- Feed the checked coarse ShapeSqDeriv interval certificate into the existing
degree-15 derivative Taylor-source receiver. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTaylorSource_of_coarseTwo :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta -
        rawOmegaATaylorPolynomial 15 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
          eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs := by
  exact
    ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource
      (data := primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData)
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs)
      (by
        simpa [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData] using
          primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_coarseTwo)
      (by
        unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData
        unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs
        rfl)

/-- Coarse anchor coefficient for the integrated shape-square Taylor model. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorCoeff :
    Rat :=
  0

/-- Coarse anchor error for the integrated shape-square Taylor model. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorErrorAbs :
    Real :=
  1

/-- Coarse integrated shape-square Taylor coefficients. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorCoeff :
    Fin 17 -> Rat :=
  integratedTaylorCoeff 15
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorCoeff

/-- Exact coarse remainder expression for the integrated shape-square Taylor
source. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorRemainderAbs :
    Real :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorErrorAbs +
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs *
      ((1 : Real) / 20)

/-- Feed the checked coarse derivative Taylor source into the integrated
shape-square Taylor-source receiver. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqTaylorSource_of_coarseTwo :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖(centeredBSplineImagTransformRealClosedForm 11
            ((3 : Real) / 10) eta) ^ 2 -
        rawOmegaATaylorPolynomial 16 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorCoeff
          eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorRemainderAbs := by
  exact
    shapeSqTaylor_bound_of_shapeSqDerivTaylor_source
      (k := 11) (ell := ((3 : Real) / 10))
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (radius := ((1 : Real) / 20))
      (center := (1 / 20 : Rat))
      (derivRemainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs)
      (anchorErrorAbs :=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorErrorAbs)
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorRemainderAbs)
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorCoeff
      (by norm_num)
      (by
        intro eta heta
        fun_prop)
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTaylorSource_of_coarseTwo
      (by
        intro eta heta
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor
        · have hLeft := heta.1
          norm_num at hLeft ⊢
          linarith
        · have hRight := heta.2
          norm_num at hRight ⊢
          linarith)
      (by
        have hE0 :=
          primaryFiniteRow0Parent0Split100Sub0ShapeAnchorValueBounds_generated.1
        have hE1 :=
          primaryFiniteRow0Parent0Split100Sub0ShapeAnchorValueBounds_generated.2
        have hCenterRatCast : ((1 / 20 : Rat) : Real) = (1 : Real) / 20 := by
          norm_num
        let E : Real :=
          centeredBSplineImagTransformRealClosedForm 11
            ((3 : Real) / 10) ((1 / 20 : Rat) : Real)
        have hE0' : 0 <= E := by
          dsimp [E]
          rw [hCenterRatCast]
          linarith [hE0]
        have hE1' : E <= 1 := by
          dsimp [E]
          rw [hCenterRatCast]
          linarith [hE1]
        have hSqNonneg : 0 <= E ^ 2 :=
          sq_nonneg E
        have hSqLeOne : E ^ 2 <= 1 := by
          nlinarith
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor
        · change
            -(primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorErrorAbs) <=
              E ^ 2 -
                (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorCoeff :
                  Real)
          norm_num [
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorCoeff,
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorErrorAbs]
          nlinarith
        · change
            E ^ 2 -
                (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorCoeff :
                  Real) <=
              primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorErrorAbs
          norm_num [
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorCoeff,
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorAnchorErrorAbs]
          exact abs_le.mpr ⟨by linarith [hE0'], hE1'⟩)
      (by
        unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorRemainderAbs
        rfl)

end Step33
end PSDpd
end Q3
