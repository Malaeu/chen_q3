import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualLowDegreeBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Degree-0 active-actual order-16 source bridge.

This file records the smallest non-D46 source interface for the active-actual
Horner row path.  A degree-0 row needs:

* an anchor enclosure for
  `ActiveScaleCoeff * D^16(ComponentProductActual)` at `1/20`;
* a proof-grade uniform derivative bound for the same function, represented
  here through an explicit derivative-shift hypothesis and a `D^17` bound;
* the exact rational budget comparison.

It does not supply the numerical D16-center row, the D17 source bound, or a
concrete Horner payload.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- Constant coefficient row for the first low-degree active-actual source. -/
def primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
    (coeff0 : Rat) : Fin 1 -> Rat :=
  fun _ => coeff0

/--
Degree-0 active-actual source theorem on the whole active cell.

The theorem is intentionally conditional on the currently missing source rows:
`hCenter` for the D16 center value, `hOrder17` for the uniform D17 bound, and
`hDerivShift` for the derivative normalization.  This keeps the live gap at
`STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder
    {coeff0 coeffErrorAbs activeScaleAbs order17Abs polyErrorAbs : Rat}
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        (activeScaleAbs : Real))
    (hDiff :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        DifferentiableAt Real
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0) t) eta)
    (hDerivShift :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0) t) eta =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta)
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hOrder17 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
          (order17Abs : Real))
    (hBudget :
      (coeffErrorAbs : Real) +
          (activeScaleAbs : Real) * (order17Abs : Real) *
            ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
              coeff0) eta‖ <=
        (polyErrorAbs : Real) := by
  have hCenterMem :
      ((1 : Real) / 20) ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
    norm_num
  have hRadius :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖eta - ((1 : Real) / 20)‖ <= ((1 : Real) / 20) := by
    intro eta hEta
    rw [Real.norm_eq_abs]
    simpa using
      primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta
  have hActiveScaleAbsNonneg : 0 <= (activeScaleAbs : Real) :=
    (abs_nonneg primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff).trans
      hActiveScaleAbs
  have hDeriv :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖deriv
            (fun t : Real =>
              primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                  iteratedDeriv 16
                    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
                rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                  (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                    coeff0) t) eta‖ <=
          (activeScaleAbs : Real) * (order17Abs : Real) := by
    intro eta hEta
    rw [hDerivShift eta hEta]
    calc
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ =
          |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| *
            ‖iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ <= (activeScaleAbs : Real) * (order17Abs : Real) :=
        mul_le_mul hActiveScaleAbs (hOrder17 eta hEta) (norm_nonneg _)
          hActiveScaleAbsNonneg
  refine
    centered_residual_bound_of_anchor_and_deriv_bound
      (f := fun t : Real =>
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
      (p := rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff coeff0))
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (anchor := ((1 : Real) / 20)) (radius := ((1 : Real) / 20))
      (derivBound := (activeScaleAbs : Real) * (order17Abs : Real))
      (anchorError := (coeffErrorAbs : Real))
      (remainder := (polyErrorAbs : Real))
      hCenterMem hDiff hDeriv hRadius ?_ ?_
  · simpa [
      rawOmegaATaylorPolynomial,
      primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff]
      using hCenter
  · simpa [mul_assoc] using hBudget

/--
Degree-0 active-actual source theorem with the derivative-shift and
differentiability obligations discharged from a single `ContDiff17` source for
the component product.

This still does not provide the proof-grade D16 center enclosure, D17 uniform
bound, or rational budget row.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_contDiff17
    {coeff0 coeffErrorAbs activeScaleAbs order17Abs polyErrorAbs : Rat}
    (hSmooth :
      ContDiff Real 17
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual)
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        (activeScaleAbs : Real))
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hOrder17 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
          (order17Abs : Real))
    (hBudget :
      (coeffErrorAbs : Real) +
          (activeScaleAbs : Real) * (order17Abs : Real) *
            ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
              coeff0) eta‖ <=
        (polyErrorAbs : Real) := by
  have hD16Diff :
      Differentiable Real
        (iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual) :=
    hSmooth.differentiable_iteratedDeriv 16 (by norm_num)
  have hDiff :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        DifferentiableAt Real
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0) t) eta := by
    intro eta _hEta
    exact
      (hD16Diff.differentiableAt.const_mul
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff).sub
        (rawOmegaATaylorPolynomial_differentiableAt 0 ((1 : Rat) / 20)
          (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff coeff0)
          eta)
  have hDerivShift :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0) t) eta =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta := by
    intro eta _hEta
    have hD16DiffAt :
        DifferentiableAt Real
          (iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual) eta :=
      hD16Diff.differentiableAt
    have hScaledDiffAt :
        DifferentiableAt Real
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
          eta :=
      hD16DiffAt.const_mul
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
    have hPolyDiffAt :
        DifferentiableAt Real
          (rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
              coeff0)) eta :=
      rawOmegaATaylorPolynomial_differentiableAt 0 ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff coeff0)
        eta
    have hScaledDeriv :
        deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
          eta =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          deriv
            (iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual) eta :=
      deriv_const_mul
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff hD16DiffAt
    have hPolyDeriv :
        deriv
          (rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
              coeff0)) eta = 0 := by
      unfold rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
      simp
    have hDerivSub :
        deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0) t) eta =
          deriv
            (fun t : Real =>
              primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t)
            eta -
            deriv
              (rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0)) eta :=
      deriv_sub hScaledDiffAt hPolyDiffAt
    rw [hDerivSub, hScaledDeriv, hPolyDeriv, sub_zero]
    rw [← iteratedDeriv_succ]
  exact
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder
      hActiveScaleAbs hDiff hDerivShift hCenter hOrder17 hBudget

/--
Whole-cell degree-0 source, transported through the existing low-degree
zero-extension bridge into the fixed degree-29 Horner normalization.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source
    {coeff0 coeffErrorAbs activeScaleAbs order17Abs polyErrorAbs : Rat}
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        (activeScaleAbs : Real))
    (hDiff :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        DifferentiableAt Real
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0) t) eta)
    (hDerivShift :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 16
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                  coeff0) t) eta =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta)
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hOrder17 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
          (order17Abs : Real))
    (hBudget :
      (coeffErrorAbs : Real) +
          (activeScaleAbs : Real) * (order17Abs : Real) *
            ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
              (by norm_num : 0 <= 29)
              (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                coeff0)) eta‖ <=
        (polyErrorAbs : Real) := by
  have hLow :
      ∀ eta ∈ Set.Icc ((0 : Rat) : Real) (((1 : Rat) / 10 : Rat) : Real),
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
              (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                coeff0) eta‖ <=
          (polyErrorAbs : Real) := by
    intro eta hEta
    exact
      primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder
        hActiveScaleAbs hDiff hDerivShift hCenter hOrder17 hBudget eta
        (by simpa using hEta)
  intro eta hEta
  exact
    (primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree
      (d := 0) (cellL := 0) (cellU := (1 : Rat) / 10)
      (polyErrorAbs := polyErrorAbs) (by norm_num)
      (coeff :=
        primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff coeff0)
      hLow) eta (by simpa using hEta)

/--
Degree-0 active-actual source transported to the degree-29 Horner container,
with derivative-shift/differentiability discharged from `ContDiff17`.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17
    {coeff0 coeffErrorAbs activeScaleAbs order17Abs polyErrorAbs : Rat}
    (hSmooth :
      ContDiff Real 17
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual)
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        (activeScaleAbs : Real))
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hOrder17 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
          (order17Abs : Real))
    (hBudget :
      (coeffErrorAbs : Real) +
          (activeScaleAbs : Real) * (order17Abs : Real) *
            ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
              (by norm_num : 0 <= 29)
              (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                coeff0)) eta‖ <=
        (polyErrorAbs : Real) := by
  have hLow :
      ∀ eta ∈ Set.Icc ((0 : Rat) : Real) (((1 : Rat) / 10 : Rat) : Real),
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
              (primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff
                coeff0) eta‖ <=
          (polyErrorAbs : Real) := by
    intro eta hEta
    exact
      primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_contDiff17
        hSmooth hActiveScaleAbs hCenter hOrder17 hBudget eta
        (by simpa using hEta)
  intro eta hEta
  exact
    (primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree
      (d := 0) (cellL := 0) (cellU := (1 : Rat) / 10)
      (polyErrorAbs := polyErrorAbs) (by norm_num)
      (coeff :=
        primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff coeff0)
      hLow) eta (by simpa using hEta)

end Step33
end PSDpd
end Q3
