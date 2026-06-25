import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourceBudgetAudit

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Fail-closed kill for the collapsed degree-0 symmetric raw-D17 row class.

This file records the tempting full-cell symmetric estimate obtained from the
existing RawProduct18 majorant.  The estimate is proof-grade, but its own
degree-0 budget already fails.  Therefore wiring this symmetric row through the
raw/poly segment family cannot close the active Step33A.1-A gate.  This does
not rule out tight local signed raw rows or a direct whole-expression row.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- Symmetric raw-D17 radius inherited from the checked RawProduct18 majorant. -/
def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat

theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_symmetric_abs_nonneg :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat := by
  native_decide

/-- Proof-grade full-cell symmetric interval for the scaled raw D17 term. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_symmetric_interval :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      -(primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
          Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
          Real) := by
  intro eta hEta
  have hScale :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound
  have hRaw :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_rat
      eta hEta
  have hScaleNonneg :
      0 <= (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound :
        Real) := by
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound,
      primaryFiniteRow0Parent0Split100Sub0TightScaleUpper]
  have hAbs :
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
          Real) := by
    calc
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ =
          |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| *
            ‖iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ <=
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
            (primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat :
              Real) :=
            mul_le_mul hScale hRaw (norm_nonneg _) hScaleNonneg
      _ =
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
            Real) := by
            simp [
              primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat]
  simpa [Real.norm_eq_abs] using abs_le.mp hAbs

/-- Any same-segment subtraction from a symmetric raw interval keeps radius at
least the raw symmetric radius.  Hence adding an independent poly interval
cannot repair a budget failure already forced by the symmetric raw radius. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawPoly_subtraction_radius_ge_raw_symmetric_radius
    {rawAbs polyLower polyUpper : Rat}
    (_hRaw : 0 <= rawAbs)
    (hPoly : polyLower <= polyUpper) :
    rawAbs <= max (rawAbs + polyUpper) (rawAbs - polyLower) := by
  by_cases hUpper : 0 <= polyUpper
  · have hLe : rawAbs <= rawAbs + polyUpper := by
      linarith
    exact le_trans hLe (le_max_left _ _)
  · have hUpperLt : polyUpper < 0 := lt_of_not_ge hUpper
    have hLowerNonpos : polyLower <= 0 := le_trans hPoly (le_of_lt hUpperLt)
    have hLe : rawAbs <= rawAbs - polyLower := by
      linarith
    exact le_trans hLe (le_max_right _ _)

/-- Exact arithmetic kill: even the symmetric raw-D17 row alone is too large
for the current collapsed degree-0 direct budget. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_symmetric_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat /
          20 := by
  native_decide

/-- Real-valued spelling of the symmetric raw-D17 budget kill. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_symmetric_budget_not_spendable :
    ¬
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
            Real) *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) := by
  have h :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat /
              20 :
          Rat) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_symmetric_budget_fail_rat
  rw [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at h
  have hDiv :
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
          Real) /
          20 =
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0RawD17SymmetricAbsRat :
          Real) *
          ((1 : Real) / 20) := by
    ring
  rw [hDiv] at h
  exact not_le_of_gt h

end Step33
end PSDpd
end Q3
