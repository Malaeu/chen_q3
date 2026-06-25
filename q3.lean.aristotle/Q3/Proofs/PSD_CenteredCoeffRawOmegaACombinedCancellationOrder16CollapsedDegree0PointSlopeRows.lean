import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeDecision
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0DerivativeShift
import Q3.Proofs.PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Point-row bridge for the collapsed degree-0 point-slope decision.

The signed-source segment layer already proves lower/upper rows for

`ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)`

on certified subsegments.  This file records the local-center bridge from such
segment rows to the `PointRowCert.Valid` predicate consumed by the point-slope
kill.  It does not generate sharper rows and does not close Step33A.1-A.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- The point-slope local centers are the raw-D17 local centers. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_pointSlopeLocalCenter_eq_rawD17LocalCenter
    (i : Fin 2) :
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
        i =
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i := by
  fin_cases i <;>
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter]

/-- Direct whole-expression point-row receiver for the signed Taylor-transfer
route.  A future generator should prove the `deriv` point interval by signed
Taylor transport from the active center, preserving the subtraction before any
absolute-value step. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRowValid_of_collapsedExpressionDeriv_point_interval
    (i : Fin 2) {lower upper : Rat}
    (hInterval :
      (lower : Real) <=
          deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
              i : Real) ∧
        deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
              i : Real) <=
          (upper : Real)) :
    (⟨i, lower, upper⟩ :
        Step33Sub0CollapsedDegree0PointRowCert).Valid where
  pointInterval := by
    have hEq :=
      primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_deriv_eq_activeActualD17_sub_nominalOrder16PolyDeriv
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
          i : Real)
    rw [hEq] at hInterval
    simpa
      [primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr]
      using hInterval

/-- Route-level name for the remaining signed Taylor-transfer payload.  This
is the exact proof object requested from the next generator: signed point rows
for the derivative of the whole collapsed expression at the two point-slope
local centers. -/
def
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedTaylorTransferGap :
    Prop :=
  ∀ i : Fin 2,
    ∃ pointLower pointUpper : Rat,
      (pointLower : Real) <=
          deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
              i : Real) ∧
        deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
              i : Real) <=
          (pointUpper : Real)

/-- A signed Taylor-transfer payload is sufficient to instantiate the existing
point-slope decision gap. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeDecisionGap_of_signedTaylorTransferGap
    (h :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedTaylorTransferGap) :
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeDecisionGap := by
  intro i
  rcases h i with ⟨pointLower, pointUpper, hInterval⟩
  refine ⟨pointLower, pointUpper, ?_⟩
  exact
    (primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRowValid_of_collapsedExpressionDeriv_point_interval
      i hInterval).pointInterval

private def primaryFiniteRow0Parent0Split100Sub0_min4
    (a b c d : Real) : Real :=
  min (min a b) (min c d)

private def primaryFiniteRow0Parent0Split100Sub0_max4
    (a b c d : Real) : Real :=
  max (max a b) (max c d)

private theorem primaryFiniteRow0Parent0Split100Sub0_min4_le_1
    (a b c d : Real) :
    primaryFiniteRow0Parent0Split100Sub0_min4 a b c d <= a := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_min4]
  exact le_trans (min_le_left _ _) (min_le_left _ _)

private theorem primaryFiniteRow0Parent0Split100Sub0_min4_le_2
    (a b c d : Real) :
    primaryFiniteRow0Parent0Split100Sub0_min4 a b c d <= b := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_min4]
  exact le_trans (min_le_left _ _) (min_le_right _ _)

private theorem primaryFiniteRow0Parent0Split100Sub0_min4_le_3
    (a b c d : Real) :
    primaryFiniteRow0Parent0Split100Sub0_min4 a b c d <= c := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_min4]
  exact le_trans (min_le_right _ _) (min_le_left _ _)

private theorem primaryFiniteRow0Parent0Split100Sub0_min4_le_4
    (a b c d : Real) :
    primaryFiniteRow0Parent0Split100Sub0_min4 a b c d <= d := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_min4]
  exact le_trans (min_le_right _ _) (min_le_right _ _)

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4_1
    (a b c d : Real) :
    a <= primaryFiniteRow0Parent0Split100Sub0_max4 a b c d := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_max4]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4_2
    (a b c d : Real) :
    b <= primaryFiniteRow0Parent0Split100Sub0_max4 a b c d := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_max4]
  exact le_trans (le_max_right _ _) (le_max_left _ _)

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4_3
    (a b c d : Real) :
    c <= primaryFiniteRow0Parent0Split100Sub0_max4 a b c d := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_max4]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4_4
    (a b c d : Real) :
    d <= primaryFiniteRow0Parent0Split100Sub0_max4 a b c d := by
  dsimp [primaryFiniteRow0Parent0Split100Sub0_max4]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointRemainder18
    (i : Fin 2) (k : Fin 18) : Real :=
  (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
      18 : Real) *
    ‖(primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) -
      (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
        Real)‖ ^ (18 - k.1) /
      (Nat.factorial (18 - k.1) : Real)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointLower18
    (i : Fin 2) (k : Fin 18) : Real :=
  centeredTaylorDerivPointLower18
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower
        j : Real))
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper
        j : Real))
    (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real)
    (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
    k
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointRemainder18
      i k)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointUpper18
    (i : Fin 2) (k : Fin 18) : Real :=
  centeredTaylorDerivPointUpper18
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower
        j : Real))
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper
        j : Real))
    (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real)
    (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
    k
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointRemainder18
      i k)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointRemainder18
    (i : Fin 2) (k : Fin 18) : Real :=
  (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
      18 : Real) *
    ‖(primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) -
      (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
        Real)‖ ^ (18 - k.1) /
      (Nat.factorial (18 - k.1) : Real)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointLower18
    (i : Fin 2) (k : Fin 18) : Real :=
  centeredTaylorDerivPointLower18
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower
        j : Real))
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper
        j : Real))
    (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real)
    (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
    k
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointRemainder18
      i k)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointUpper18
    (i : Fin 2) (k : Fin 18) : Real :=
  centeredTaylorDerivPointUpper18
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower
        j : Real))
    (fun j : Fin 18 =>
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper
        j : Real))
    (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real)
    (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
    k
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointRemainder18
      i k)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualPointLower19
    (i : Fin 2) (k : Fin 19) : Real :=
  if hk : k.1 < 18 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointLower18
      i ⟨k.1, hk⟩
  else
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower
      i k : Real)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualPointUpper19
    (i : Fin 2) (k : Fin 19) : Real :=
  if hk : k.1 < 18 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointUpper18
      i ⟨k.1, hk⟩
  else
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper
      i k : Real)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointLower19
    (i : Fin 2) (k : Fin 19) : Real :=
  if hk : k.1 < 18 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointLower18
      i ⟨k.1, hk⟩
  else
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower
      i k : Real)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointUpper19
    (i : Fin 2) (k : Fin 19) : Real :=
  if hk : k.1 < 18 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointUpper18
      i ⟨k.1, hk⟩
  else
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper
      i k : Real)

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_point_interval19
    (i : Fin 2) (k : Fin 19) :
    primaryFiniteRow0Parent0Split100Sub0OmegaActualPointLower19 i k <=
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) ∧
      iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) <=
        primaryFiniteRow0Parent0Split100Sub0OmegaActualPointUpper19 i k := by
  by_cases hk : k.1 < 18
  · have h :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_point_interval_generated
        i ⟨k.1, hk⟩
    simpa [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointLower19,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointUpper19,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointLower18,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointUpper18,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSignedPointRemainder18,
      hk] using h
  · have h :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_sharp_interval
        i k
        (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
          i)
    simpa [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointLower19,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointUpper19,
      hk] using h

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_point_interval19
    (i : Fin 2) (k : Fin 19) :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointLower19 i k <=
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) ∧
      iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointUpper19 i k := by
  by_cases hk : k.1 < 18
  · have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_point_interval_generated
        i ⟨k.1, hk⟩
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointLower19,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointUpper19,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointLower18,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointUpper18,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSignedPointRemainder18,
      hk] using h
  · have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_sharp_interval
        i k
        (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
          i)
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointLower19,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointUpper19,
      hk] using h

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLL
    (i : Fin 2) (k : Nat) : Real :=
  if hk : k < 19 then
    (Nat.choose 18 k : Real) *
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointLower19
        i ⟨18 - k, Nat.lt_succ_iff.mpr (Nat.sub_le 18 k)⟩ *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointLower19
        i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLU
    (i : Fin 2) (k : Nat) : Real :=
  if hk : k < 19 then
    (Nat.choose 18 k : Real) *
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointLower19
        i ⟨18 - k, Nat.lt_succ_iff.mpr (Nat.sub_le 18 k)⟩ *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointUpper19
        i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUL
    (i : Fin 2) (k : Nat) : Real :=
  if hk : k < 19 then
    (Nat.choose 18 k : Real) *
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointUpper19
        i ⟨18 - k, Nat.lt_succ_iff.mpr (Nat.sub_le 18 k)⟩ *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointLower19
        i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUU
    (i : Fin 2) (k : Nat) : Real :=
  if hk : k < 19 then
    (Nat.choose 18 k : Real) *
      primaryFiniteRow0Parent0Split100Sub0OmegaActualPointUpper19
        i ⟨18 - k, Nat.lt_succ_iff.mpr (Nat.sub_le 18 k)⟩ *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointUpper19
        i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower
    (i : Fin 2) (k : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0_min4
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLL i k)
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLU i k)
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUL i k)
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUU i k)

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper
    (i : Fin 2) (k : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0_max4
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLL i k)
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLU i k)
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUL i k)
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUU i k)

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawProduct18_point_term_interval
    (i : Fin 2) :
    ∀ k ∈ Finset.range (18 + 1),
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower i k <=
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) ∧
        primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) <=
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper
            i k := by
  intro k hk
  have hkLt : k < 19 := by
    simpa using Finset.mem_range.mp hk
  have hOmega :=
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_point_interval19
      i ⟨18 - k, Nat.lt_succ_iff.mpr (Nat.sub_le 18 k)⟩
  have hShapeSq :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_point_interval19
      i ⟨k, hkLt⟩
  have hLowerLL :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLL i k :=
    primaryFiniteRow0Parent0Split100Sub0_min4_le_1 _ _ _ _
  have hLowerLU :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLU i k :=
    primaryFiniteRow0Parent0Split100Sub0_min4_le_2 _ _ _ _
  have hLowerUL :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUL i k :=
    primaryFiniteRow0Parent0Split100Sub0_min4_le_3 _ _ _ _
  have hLowerUU :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUU i k :=
    primaryFiniteRow0Parent0Split100Sub0_min4_le_4 _ _ _ _
  have hUpperLL :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLL i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper i k :=
    primaryFiniteRow0Parent0Split100Sub0_le_max4_1 _ _ _ _
  have hUpperLU :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLU i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper i k :=
    primaryFiniteRow0Parent0Split100Sub0_le_max4_2 _ _ _ _
  have hUpperUL :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUL i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper i k :=
    primaryFiniteRow0Parent0Split100Sub0_le_max4_3 _ _ _ _
  have hUpperUU :
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUU i k <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper i k :=
    primaryFiniteRow0Parent0Split100Sub0_le_max4_4 _ _ _ _
  have hMul :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := (Nat.choose 18 k : Real))
      (a :=
        primaryFiniteRow0Parent0Split100Sub0OmegaActualPointLower19
          i ⟨18 - k, Nat.lt_succ_iff.mpr (Nat.sub_le 18 k)⟩)
      (b :=
        primaryFiniteRow0Parent0Split100Sub0OmegaActualPointUpper19
          i ⟨18 - k, Nat.lt_succ_iff.mpr (Nat.sub_le 18 k)⟩)
      (c :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointLower19
          i ⟨k, hkLt⟩)
      (d :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualPointUpper19
          i ⟨k, hkLt⟩)
      (x :=
        iteratedDeriv (18 - k)
          primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real))
      (y :=
        iteratedDeriv k
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real))
      (lower :=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower
          i k)
      (upper :=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper
          i k)
      hOmega.1
      hOmega.2
      hShapeSq.1
      hShapeSq.2
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLL,
          hkLt] using hLowerLL)
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLU,
          hkLt] using hLowerLU)
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUL,
          hkLt] using hLowerUL)
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUU,
          hkLt] using hLowerUU)
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLL,
          hkLt] using hUpperLL)
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerLU,
          hkLt] using hUpperLU)
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUL,
          hkLt] using hUpperUL)
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0RawProduct18PointCornerUU,
          hkLt] using hUpperUU)
  simpa [
    primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm,
    mul_assoc] using hMul

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLower
    (i : Fin 2) : Real :=
  ∑ k ∈ Finset.range (18 + 1),
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermLower i k

def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpper
    (i : Fin 2) : Real :=
  ∑ k ∈ Finset.range (18 + 1),
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointTermUpper i k

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawProduct18_point_sum_interval
    (i : Fin 2) :
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLower i <=
        (∑ k ∈ Finset.range (18 + 1),
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real)) ∧
      (∑ k ∈ Finset.range (18 + 1),
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real)) <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpper i := by
  constructor
  · dsimp [primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLower]
    exact
      Finset.sum_le_sum fun k hk =>
        (primaryFiniteRow0Parent0Split100Sub0_rawProduct18_point_term_interval
          i k hk).1
  · dsimp [primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpper]
    exact
      Finset.sum_le_sum fun k hk =>
        (primaryFiniteRow0Parent0Split100Sub0_rawProduct18_point_term_interval
          i k hk).2

theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_generated
    (i : Fin 2) :
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLower i <=
        iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) ∧
      iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) <=
        primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpper i := by
  have hSum :=
    primaryFiniteRow0Parent0Split100Sub0_rawProduct18_point_sum_interval i
  have hEq :
      iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) =
        ∑ k ∈ Finset.range (18 + 1),
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) := by
    rw [
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18,
      primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz]
  constructor
  · calc
      primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLower i <=
          (∑ k ∈ Finset.range (18 + 1),
            primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
              (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
                Real)) := hSum.1
      _ =
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) := hEq.symm
  · calc
      iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) =
        (∑ k ∈ Finset.range (18 + 1),
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real)) := hEq
      _ <= primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpper i :=
        hSum.2

namespace Step33Sub0CollapsedDegree0SignedSourceSegmentCert

/-- Forget a segment row down to a point-row candidate at local center `i`. -/
def toPointRowCert
    (cert : Step33Sub0CollapsedDegree0SignedSourceSegmentCert)
    (i : Fin 2) :
    Step33Sub0CollapsedDegree0PointRowCert where
  i := i
  lower := cert.lower
  upper := cert.upper

namespace Valid

/-- A valid signed-source segment gives a valid point row at any point inside
that segment. -/
theorem to_pointRowValid
    {cert : Step33Sub0CollapsedDegree0SignedSourceSegmentCert}
    (h : cert.Valid) (i : Fin 2)
    (hPointMem :
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
          i : Real) ∈
        Set.Icc (cert.cellL : Real) (cert.cellU : Real)) :
    (cert.toPointRowCert i).Valid where
  pointInterval := h.sourceInterval
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
      i : Real)
    hPointMem

end Valid
end Step33Sub0CollapsedDegree0SignedSourceSegmentCert

namespace Step33Sub0CollapsedDegree0RawPolySegmentCert

/-- Forget a raw/poly same-segment row down to a point-row candidate at local
center `i`. -/
def toPointRowCert
    (cert : Step33Sub0CollapsedDegree0RawPolySegmentCert) (i : Fin 2) :
    Step33Sub0CollapsedDegree0PointRowCert :=
  cert.toSignedSegmentCert.toPointRowCert i

namespace Valid

/-- A valid raw/poly same-segment row gives a valid point row at any point
inside that segment. -/
theorem to_pointRowValid
    {cert : Step33Sub0CollapsedDegree0RawPolySegmentCert}
    (h : cert.Valid) (i : Fin 2)
    (hPointMem :
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
          i : Real) ∈
        Set.Icc (cert.cellL : Real) (cert.cellU : Real)) :
    (cert.toPointRowCert i).Valid :=
  h.to_signedSegmentValid.to_pointRowValid i hPointMem

end Valid
end Step33Sub0CollapsedDegree0RawPolySegmentCert

/-- The existing two-segment signed-factor payload covers the two point-slope
local centers. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_point_mem
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
        i : Real) ∈
      Set.Icc
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
          i).cellL : Real)
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
          i).cellU : Real) := by
  have hMem :=
    primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment i
  simpa [
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly,
    Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert.toRawPolySegmentCert,
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment,
    primaryFiniteRow0Parent0Split100Sub0_pointSlopeLocalCenter_eq_rawD17LocalCenter
      i] using hMem

/-- The already-checked two-segment raw/poly payload can be viewed as point
rows at the two local centers.  These rows are still the existing coarse
two-segment rows; this theorem is only the receiver bridge. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_pointRow_valid
    (i : Fin 2) :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
      i).toPointRowCert i).Valid := by
  have hValid :
      (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
        i).Valid := by
    fin_cases i <;>
      simpa using
        (by
          first
          | exact
              primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_rawPoly_valid
          | exact
              primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_rawPoly_valid)
  exact
    hValid.to_pointRowValid i
      (primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_point_mem
        i)

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_pointRow_valid :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
      ⟨0, by decide⟩).toPointRowCert ⟨0, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_pointRow_valid
    ⟨0, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_pointRow_valid :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
      ⟨1, by decide⟩).toPointRowCert ⟨1, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_pointRow_valid
    ⟨1, by decide⟩

/-- The checked sharp two-segment signed-factor payload also covers the two
point-slope local centers. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_point_mem
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
        i : Real) ∈
      Set.Icc
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
          i).cellL : Real)
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
          i).cellU : Real) := by
  have hMem :=
    primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment i
  simpa [
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly,
    Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert.toRawPolySegmentCert,
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
    primaryFiniteRow0Parent0Split100Sub0_pointSlopeLocalCenter_eq_rawD17LocalCenter
      i] using hMem

/-- The checked sharp two-segment raw/poly payload can be viewed as point rows.
These rows are still symmetric raw/poly rows, not a point-slope budget
decision. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_pointRow_valid
    (i : Fin 2) :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      i).toPointRowCert i).Valid := by
  have hValid :
      (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
        i).Valid := by
    fin_cases i <;>
      simpa using
        (by
          first
          | exact
              primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_left_rawPoly_valid
          | exact
              primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_right_rawPoly_valid)
  exact
    hValid.to_pointRowValid i
      (primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_point_mem
        i)

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_left_pointRow_valid :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      ⟨0, by decide⟩).toPointRowCert ⟨0, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_pointRow_valid
    ⟨0, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_right_pointRow_valid :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      ⟨1, by decide⟩).toPointRowCert ⟨1, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_pointRow_valid
    ⟨1, by decide⟩

/-- Exact arithmetic obstruction for reusing the sharp two-segment raw/poly
rows as a point-slope sign decision: both local point rows still straddle
zero. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_pointRows_straddle_zero
    (i : Fin 2) :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      i).toPointRowCert i).lower < 0 ∧
      0 <
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
          i).toPointRowCert i).upper := by
  fin_cases i <;>
    native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_left_pointRow_straddles_zero :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      ⟨0, by decide⟩).toPointRowCert ⟨0, by decide⟩).lower < 0 ∧
      0 <
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
          ⟨0, by decide⟩).toPointRowCert ⟨0, by decide⟩).upper :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_pointRows_straddle_zero
    ⟨0, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_right_pointRow_straddles_zero :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      ⟨1, by decide⟩).toPointRowCert ⟨1, by decide⟩).lower < 0 ∧
      0 <
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
          ⟨1, by decide⟩).toPointRowCert ⟨1, by decide⟩).upper :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_pointRows_straddle_zero
    ⟨1, by decide⟩

end Step33
end PSDpd
end Q3
