import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqProductBounds

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Majorant receiver for the active Step33A.1-A ShapeSqDeriv layer.

This file composes the checked shape-square product-bound receiver with the
existing `ShapeSqDerivTaylorIntervalCert.Valid` receiver.  It deliberately does
not emit any numerical derivative bounds: the proof-grade shape derivative
majorants through order `17` remain the next payload obligation.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Local order-shift bridge used only by this receiver file.

This avoids depending on a freshly built `.olean` for the heavier endpoint
support module: the active `ShapeSqDeriv` is definitionally the first
derivative of the active shape-square source. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ_local
    (j : Nat) (eta : Real) :
    iteratedDeriv j primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta =
      iteratedDeriv (j + 1)
        (fun t : Real =>
          (centeredBSplineImagTransformRealClosedForm
            11 ((3 : Real) / 10) t) ^ 2)
        eta := by
  induction j generalizing eta with
  | zero =>
      simp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv]
  | succ j ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun :
          iteratedDeriv j primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv =
            iteratedDeriv (j + 1)
              (fun t : Real =>
                (centeredBSplineImagTransformRealClosedForm
                  11 ((3 : Real) / 10) t) ^ 2) := by
        funext x
        exact ih x
      rw [hfun]

/-- Build the compact active ShapeSqDeriv interval certificate from
proof-grade derivative majorants for the active shape function.

The center-jet hypotheses are intentionally budgeted: a one-sided absolute
majorant for the shape-square derivative only gives a coarse interval
`[-B/factorial, B/factorial]` for the normalized jet.  The caller must prove
that this interval fits inside the emitted `coeff` plus/minus `coeffErrorAbs`
budget.
The theorem closes only this checked receiver surface; it does not provide the
majorants `centerM` or `cellM`. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shape_derivative_abs
    {coeff coeffErrorAbs : Fin 16 -> Rat}
    {order16Abs : Rat}
    {centerM : Fin 16 -> Nat -> Real}
    {cellM : Nat -> Real}
    (hCoeffErrorNonneg :
      ∀ j : Fin 16, 0 <= (coeffErrorAbs j : Real))
    (hCenterMNonneg :
      ∀ j : Fin 16, ∀ k : Nat, k <= j.1 + 1 -> 0 <= centerM j k)
    (hCenterShapeDerivAbs :
      ∀ j : Fin 16, ∀ k : Nat, k <= j.1 + 1 ->
        ‖iteratedDeriv k
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t)
            ((1 : Real) / 20)‖ <=
          centerM j k)
    (hCenterBudget :
      ∀ j : Fin 16,
        (∑ i ∈ Finset.range ((j.1 + 1) + 1),
            ((j.1 + 1).choose i : Real) * centerM j i *
              centerM j (j.1 + 1 - i)) /
            (Nat.factorial j.1 : Real) +
          ‖(coeff j : Real)‖ <=
        (coeffErrorAbs j : Real))
    (hCellMNonneg :
      ∀ k : Nat, k <= 17 -> 0 <= cellM k)
    (hCellShapeDerivAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 17 ->
          ‖iteratedDeriv k
              (fun t : Real =>
                centeredBSplineImagTransformRealClosedForm
                  11 ((3 : Real) / 10) t)
              eta‖ <=
            cellM k)
    (hOrder17Budget :
      (∑ i ∈ Finset.range (17 + 1),
          ((17 : Nat).choose i : Real) * cellM i * cellM (17 - i)) <=
        (order16Abs : Real)) :
    (ShapeSqDerivTaylorIntervalCert.singleAbs coeff coeffErrorAbs
      order16Abs).Valid := by
  refine
    ShapeSqDerivTaylorIntervalCert.Valid.of_single_abs
      hCoeffErrorNonneg ?_ ?_
  · intro j
    let shapeSqDerivBound : Real :=
      ∑ i ∈ Finset.range ((j.1 + 1) + 1),
        ((j.1 + 1).choose i : Real) * centerM j i *
          centerM j (j.1 + 1 - i)
    have hProduct :
        ‖iteratedDeriv (j.1 + 1)
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t) ^ 2)
            ((1 : Real) / 20)‖ <=
          shapeSqDerivBound := by
      simpa [shapeSqDerivBound] using
        primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs
          (n := j.1 + 1) (M := centerM j) (eta := ((1 : Real) / 20))
          (hCenterMNonneg j) (hCenterShapeDerivAbs j)
    have hFactPos : 0 < (Nat.factorial j.1 : Real) := by positivity
    have hShift :
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
            ((1 : Real) / 20) =
          iteratedDeriv (j.1 + 1)
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t) ^ 2)
            ((1 : Real) / 20) :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ_local
        j.1 ((1 : Real) / 20)
    have hDiv :
        ‖iteratedDeriv j.1
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
            ((1 : Real) / 20) /
            (Nat.factorial j.1 : Real)‖ <=
          shapeSqDerivBound / (Nat.factorial j.1 : Real) := by
      have hRaw :=
        div_le_div_of_nonneg_right hProduct (le_of_lt hFactPos)
      rw [hShift]
      simpa [norm_div, Real.norm_eq_abs, abs_of_pos hFactPos] using hRaw
    have hTriangle :
        ‖iteratedDeriv j.1
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
            ((1 : Real) / 20) /
            (Nat.factorial j.1 : Real) -
          (coeff j : Real)‖ <=
          ‖iteratedDeriv j.1
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
              ((1 : Real) / 20) /
              (Nat.factorial j.1 : Real)‖ +
            ‖(coeff j : Real)‖ :=
      norm_sub_le _ _
    have hBudget : shapeSqDerivBound / (Nat.factorial j.1 : Real) +
        ‖(coeff j : Real)‖ <= (coeffErrorAbs j : Real) := by
      simpa [shapeSqDerivBound] using hCenterBudget j
    exact
      le_trans hTriangle
        (le_trans (add_le_add hDiv le_rfl) hBudget)
  · intro eta heta
    rw [primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ_local]
    have hProduct :
        ‖iteratedDeriv 17
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t) ^ 2)
            eta‖ <=
          ∑ i ∈ Finset.range (17 + 1),
            ((17 : Nat).choose i : Real) * cellM i * cellM (17 - i) := by
      simpa using
        primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs
          (n := 17) (M := cellM) (eta := eta)
          hCellMNonneg (hCellShapeDerivAbs eta heta)
    exact le_trans hProduct hOrder17Budget

end Step33
end PSDpd
end Q3
