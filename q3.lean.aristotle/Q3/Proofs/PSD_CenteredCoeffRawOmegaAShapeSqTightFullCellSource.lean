import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivTightPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Full-cell same-coefficient ShapeSq Taylor source for Step33A.1-A sub0.

This bridges the checked same-coefficient ShapeSqDeriv Taylor source into the
integrated ShapeSq coefficient stream consumed by the component assembly.  The
budget is intentionally coarse and is not a final Step33A.1-A closure budget.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Coarse full-cell remainder obtained by integrating the checked
same-coefficient ShapeSqDeriv Taylor source and the generated ShapeSq anchor. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs :
    Real :=
  (primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated :
      Real) +
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs *
      ((1 : Real) / 20)

/-- The active generated ShapeSq coefficient stream is valid on the full
Step33A.1-A subcell when fed by the checked same-coefficient ShapeSqDeriv
source. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqTightFullCellTaylorSource :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖(centeredBSplineImagTransformRealClosedForm 11
            ((3 : Real) / 10) eta) ^ 2 -
        rawOmegaATaylorPolynomial 16 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated
          eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs := by
  have hCoeff :
      integratedTaylorCoeff 15
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated =
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated := by
    rw [primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tightCoeff_eq_generated]
    rfl
  have hSource :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖(centeredBSplineImagTransformRealClosedForm 11
              ((3 : Real) / 10) eta) ^ 2 -
          rawOmegaATaylorPolynomial 16 (1 / 20 : Rat)
            (integratedTaylorCoeff 15
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff
              primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated)
            eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs :=
    shapeSqTaylor_bound_of_shapeSqDerivTaylor_source
      (k := 11) (ell := ((3 : Real) / 10))
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (radius := ((1 : Real) / 20))
      (center := ((1 : Rat) / 20))
      (derivRemainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightTaylorRemainderAbs)
      (anchorErrorAbs :=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated :
          Real))
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated
      (by norm_num)
      (by
        intro eta heta
        fun_prop)
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTightTaylorSource
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
        have hLower :=
          primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hAnchorLower
        have hUpper :=
          primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hAnchorUpper
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor
        · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated,
            primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated]
            at hLower hUpper ⊢
          linarith
        · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated,
            primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated]
            at hLower hUpper ⊢
          linarith)
      (by
        dsimp
          [primaryFiniteRow0Parent0Split100Sub0ShapeSqTightFullCellTaylorRemainderAbs]
        exact le_rfl)
  intro eta hEta
  simpa [hCoeff] using hSource eta hEta

end Step33
end PSDpd
end Q3
