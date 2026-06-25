import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Point-slope decision interface for the direct collapsed degree-0 route.

This file records the smallest post-sharp-budget fork chosen by the route
review.  It does not provide proof-grade point rows.  Instead it proves the
exact conditional obstruction: if a generated pointwise lower bound for the
already-subtracted signed derivative exceeds the derivative budget allowed by
the current biased residual slack, then the collapsed degree-0 class cannot be
spent.

The remaining proof object is a proof-grade point interval for

`ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)`

at the local centers `1 / 40` and `3 / 40`, with subtraction preserved before
taking an absolute value.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- The two local centers proposed for the cheap point-slope decision audit. -/
def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
    (i : Fin 2) : Rat :=
  if i.1 = 0 then (1 : Rat) / 40 else (3 : Rat) / 40

/-- The derivative magnitude that the current degree-0 budget can afford. -/
def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat :
    Rat :=
  20 *
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs -
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs)

/--
Any collapsed degree-0 source whose final polynomial error is the current
biased residual budget can only spend derivative magnitude up to
`CollapsedDegree0AllowedDerivAbsRat`.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_allowedDerivAbs_of_budget
    {derivAbs : Rat}
    (hBudget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real)) :
    (derivAbs : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat :
        Real) := by
  unfold primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat
  norm_num [Rat.cast_mul, Rat.cast_sub] at hBudget ⊢
  linarith

/--
Conditional point-slope kill.  A future generator should instantiate
`pointAbsLower` from proof-grade point rows for the already-subtracted signed
source.  If the exact rational comparison below goes the wrong way, the
degree-0 class is killed before emitting a full-cell signed-source payload.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointSlope_budget_impossible
    (i : Fin 2) {pointAbsLower derivAbs : Rat}
    (hPointLower :
      (pointAbsLower : Real) <=
        ‖primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            i : Real)‖)
    (hAbsAtPoint :
      ‖primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            i : Real)‖ <=
        (derivAbs : Real))
    (hBudget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real))
    (hPointExceedsAllowed :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat <
        pointAbsLower) :
    False := by
  have hAllowed :=
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_allowedDerivAbs_of_budget
      hBudget
  have hPointLeAllowed :
      (pointAbsLower : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat :
          Real) :=
    le_trans hPointLower (le_trans hAbsAtPoint hAllowed)
  exact not_lt_of_ge hPointLeAllowed (by exact_mod_cast hPointExceedsAllowed)

/-- One generated point row for the already-subtracted signed source. -/
structure Step33Sub0CollapsedDegree0PointRowCert where
  i : Fin 2
  lower : Rat
  upper : Rat

namespace Step33Sub0CollapsedDegree0PointRowCert

/-- Proof-bearing validity predicate for one signed-source point row. -/
structure Valid (cert : Step33Sub0CollapsedDegree0PointRowCert) :
    Prop where
  pointInterval :
    (cert.lower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            cert.i : Real) ∧
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            cert.i : Real) <=
        (cert.upper : Real)

namespace Valid

/--
If a proof-grade point row is strictly positive and its lower endpoint exceeds
the derivative budget allowed by the current residual slack, the degree-0 class
is killed.
-/
theorem positive_row_budget_impossible
    {cert : Step33Sub0CollapsedDegree0PointRowCert} (h : cert.Valid)
    {derivAbs : Rat}
    (hLowerNonneg : 0 <= cert.lower)
    (hBudget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real))
    (hAbsAtPoint :
      ‖primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            cert.i : Real)‖ <=
        (derivAbs : Real))
    (hPointExceedsAllowed :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat <
        cert.lower) :
    False := by
  have _hLowerNonnegReal : (0 : Real) <= (cert.lower : Real) := by
    exact_mod_cast hLowerNonneg
  refine
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointSlope_budget_impossible
      cert.i (pointAbsLower := cert.lower) (derivAbs := derivAbs) ?_
      hAbsAtPoint hBudget hPointExceedsAllowed
  have hPointLower := h.pointInterval.1
  exact le_trans hPointLower (le_abs_self _)

/--
If a proof-grade point row is strictly negative and the negative upper endpoint
exceeds the derivative budget allowed by the current residual slack, the
degree-0 class is killed.
-/
theorem negative_row_budget_impossible
    {cert : Step33Sub0CollapsedDegree0PointRowCert} (h : cert.Valid)
    {derivAbs : Rat}
    (hUpperNonpos : cert.upper <= 0)
    (hBudget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real))
    (hAbsAtPoint :
      ‖primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            cert.i : Real)‖ <=
        (derivAbs : Real))
    (hPointExceedsAllowed :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat <
        -cert.upper) :
    False := by
  have _hUpperNonposReal : (cert.upper : Real) <= 0 := by
    exact_mod_cast hUpperNonpos
  refine
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointSlope_budget_impossible
      cert.i (pointAbsLower := -cert.upper) (derivAbs := derivAbs) ?_
      hAbsAtPoint hBudget hPointExceedsAllowed
  have hPointUpper := h.pointInterval.2
  have hNegLe :
      -(cert.upper : Real) <=
        -primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            cert.i : Real) := by
    exact neg_le_neg hPointUpper
  have hNegLeCast :
      ((-cert.upper : Rat) : Real) <=
        -primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
            cert.i : Real) := by
    exact_mod_cast hNegLe
  exact le_trans hNegLeCast (neg_le_abs _)

end Valid
end Step33Sub0CollapsedDegree0PointRowCert

/-- Route-level name for the next missing proof object. -/
def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeDecisionGap :
    Prop :=
  ∀ i : Fin 2,
    ∃ pointLower pointUpper : Rat,
      (pointLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
              i : Real) ∧
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
              i : Real) <=
          (pointUpper : Real)

end Step33
end PSDpd
end Q3
