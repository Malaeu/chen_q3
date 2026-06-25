import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Degree-0 source receiver for the direct Step33A.1-A collapsed-expression route.

The previous degree-15 Taylor receiver is still valid, but it asks the generator
for an order-16 row of a collapsed expression that already contains a D16.  This
file records the cheaper route: a degree-0 row only needs a center enclosure and
a uniform signed bound for the derivative of the whole collapsed expression.

It emits no numeric rows and claims no Step33A.1-A closure.  The next live gap is
the proof-grade source for the signed D17 row:

`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_D17_SIGNED_SOURCE_GAP`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- Constant coefficient row for the degree-0 collapsed-expression source. -/
def primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
    (coeff0 : Rat) : Fin (0 + 1) -> Rat :=
  fun _ => coeff0

/--
Raw degree-0 collapsed-expression remainder receiver.

The derivative bound is stated for the residual
`CollapsedExpression - constant polynomial`, matching
`centered_residual_bound_of_anchor_and_deriv_bound` directly.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder
    {coeff0 coeffErrorAbs derivAbs polyErrorAbs : Rat}
    (hDiff :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        DifferentiableAt Real
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
                t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
                  coeff0) t) eta)
    (hDeriv :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖deriv
            (fun t : Real =>
              primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
                  t -
                rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                  (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
                    coeff0) t) eta‖ <=
          (derivAbs : Real))
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hBudget :
      (coeffErrorAbs : Real) + (derivAbs : Real) * ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              coeff0) eta‖ <=
        (polyErrorAbs : Real) := by
  refine
    centered_residual_bound_of_anchor_and_deriv_bound
      (f :=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression)
      (p := rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
          coeff0))
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (anchor := ((1 : Real) / 20)) (radius := ((1 : Real) / 20))
      (derivBound := (derivAbs : Real))
      (anchorError := (coeffErrorAbs : Real))
      (remainder := (polyErrorAbs : Real))
      ?_ hDiff hDeriv ?_ ?_ hBudget
  · norm_num
  · intro eta hEta
    simpa using
      primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta
  · simpa [
      rawOmegaATaylorPolynomial,
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff]
      using hCenter

/--
Degree-0 collapsed-expression receiver from a derivative bound for the whole
collapsed expression.  Since the degree-0 polynomial is constant, this is the
same derivative bound as the residual derivative bound.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_deriv_bound
    {coeff0 coeffErrorAbs derivAbs polyErrorAbs : Rat}
    (hDiffCollapsed :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        DifferentiableAt Real
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
          eta)
    (hDerivCollapsed :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta‖ <=
          (derivAbs : Real))
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hBudget :
      (coeffErrorAbs : Real) + (derivAbs : Real) * ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              coeff0) eta‖ <=
        (polyErrorAbs : Real) := by
  have hDiff :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        DifferentiableAt Real
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
                t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
                  coeff0) t) eta := by
    intro eta hEta
    exact
      (hDiffCollapsed eta hEta).sub
        (rawOmegaATaylorPolynomial_differentiableAt 0 ((1 : Rat) / 20)
          (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
            coeff0) eta)
  have hDeriv :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖deriv
            (fun t : Real =>
              primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
                  t -
                rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                  (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
                    coeff0) t) eta‖ <=
          (derivAbs : Real) := by
    intro eta hEta
    have hPolyDiffAt :
        DifferentiableAt Real
          (rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              coeff0)) eta :=
      rawOmegaATaylorPolynomial_differentiableAt 0 ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
          coeff0) eta
    have hDerivSub :
        deriv
          (fun t : Real =>
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
                t -
              rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
                  coeff0) t) eta =
          deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
            deriv
              (rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
                (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
                  coeff0)) eta :=
      deriv_sub (hDiffCollapsed eta hEta) hPolyDiffAt
    have hPolyDeriv :
        deriv
          (rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              coeff0)) eta = 0 := by
      unfold rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
      simp
    rw [hDerivSub, hPolyDeriv, sub_zero]
    exact hDerivCollapsed eta hEta
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder
      hDiff hDeriv hCenter hBudget

/--
Generator-facing signed-D17 form of the degree-0 collapsed receiver.

The derivative-shift identity and the signed D17 bound are still source rows;
this theorem only proves that they are the right rows to generate next.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_signedD17_source
    {coeff0 coeffErrorAbs derivAbs polyErrorAbs : Rat}
    (hDiffCollapsed :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        DifferentiableAt Real
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
          eta)
    (hDerivShift :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta)
    (hSignedD17 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta‖ <=
          (derivAbs : Real))
    (hCenter :
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            ((1 : Real) / 20) -
          (coeff0 : Real)‖ <=
        (coeffErrorAbs : Real))
    (hBudget :
      (coeffErrorAbs : Real) + (derivAbs : Real) * ((1 : Real) / 20) <=
        (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              coeff0) eta‖ <=
        (polyErrorAbs : Real) := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_deriv_bound
      hDiffCollapsed ?_ hCenter hBudget
  intro eta hEta
  rw [hDerivShift eta hEta]
  exact hSignedD17 eta hEta

end Step33
end PSDpd
end Q3
