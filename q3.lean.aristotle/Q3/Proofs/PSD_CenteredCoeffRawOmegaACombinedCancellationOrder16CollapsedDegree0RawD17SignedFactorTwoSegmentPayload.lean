import Q3.Proofs.PSD_CenteredCoeffRawOmegaARawD17LocalCenterJets18Payload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Two-segment raw-D17 signed-factor payload attempt.

The local factor rows come from
`PSD_CenteredCoeffRawOmegaARawD17LocalCenterJets18Payload`: each subsegment
has proof-grade `OmegaActual` and `ShapeSqActual` derivative intervals through
row 18.  This file wires those rows into the signed-factor receiver and records
the exact budget verdict.  It does not claim Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound_rawD17_twoSegment
    {x m lower upper : Real}
    (hAbs : ‖x‖ <= m)
    (hLower : lower <= -m)
    (hUpper : m <= upper) :
    lower <= x ∧ x <= upper := by
  rw [Real.norm_eq_abs] at hAbs
  have hBounds := abs_le.mp hAbs
  constructor <;> linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_const_mul_symmetric_corners_twoSegment
    {c a b : Real}
    (hc : 0 <= c) (ha : 0 <= a) (hb : 0 <= b) :
    -(c * a * b) <= c * (-a) * (-b) ∧
      -(c * a * b) <= c * (-a) * b ∧
      -(c * a * b) <= c * a * (-b) ∧
      -(c * a * b) <= c * a * b ∧
      c * (-a) * (-b) <= c * a * b ∧
      c * (-a) * b <= c * a * b ∧
      c * a * (-b) <= c * a * b ∧
      c * a * b <= c * a * b := by
  have hprod : 0 <= c * a * b := mul_nonneg (mul_nonneg hc ha) hb
  constructor
  · nlinarith [hprod]
  constructor
  · nlinarith [hprod]
  constructor
  · nlinarith [hprod]
  constructor
  · nlinarith [hprod]
  constructor
  · nlinarith [hprod]
  constructor
  · nlinarith [hprod]
  constructor
  · nlinarith [hprod]
  · nlinarith [hprod]

/-- `Nat` wrapper for local `OmegaActual` derivative lower rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaLower
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentLower
      i ⟨k, hk⟩
  else
    0

/-- `Nat` wrapper for local `OmegaActual` derivative upper rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaUpper
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentUpper
      i ⟨k, hk⟩
  else
    0

/-- `Nat` wrapper for local `ShapeSqActual` derivative lower rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqLower
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentLower
      i ⟨k, hk⟩
  else
    0

/-- `Nat` wrapper for local `ShapeSqActual` derivative upper rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqUpper
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentUpper
      i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaAbs
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentAbs
      i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqAbs
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentAbs
      i ⟨k, hk⟩
  else
    0

/-- Absolute row for one local signed Leibniz term. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbs
    (i : Fin 2) (k : Nat) : Rat :=
  (Nat.choose 18 k : Rat) *
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaAbs
      i (18 - k) *
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqAbs
      i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermLower
    (i : Fin 2) (k : Nat) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbs
    i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermUpper
    (i : Fin 2) (k : Nat) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbs
    i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum
    (i : Fin 2) : Rat :=
  ∑ k ∈ Finset.range (18 + 1),
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbs
      i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawAbs
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum
      i

/-- Local signed-factor segment certificate. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
    (i : Fin 2) :
    Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert where
  cellL := primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i
  cellU := primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i
  omegaLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaLower i
  omegaUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaUpper i
  shapeSqLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqLower i
  shapeSqUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqUpper i
  termLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermLower
      i
  termUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermUpper
      i
  rawLower :=
    -primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawAbs i
  rawUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawAbs i

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentOmegaAbs_nonneg
    (i : Fin 2) (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaAbs
        i k := by
  fin_cases i <;>
    interval_cases k <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentShapeSqAbs_nonneg
    (i : Fin 2) (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqAbs
        i k := by
  fin_cases i <;>
    interval_cases k <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentTermAbsSum_nonneg
    (i : Fin 2) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum
        i := by
  fin_cases i <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_termCorners
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
      i).termCornerRows := by
  intro k hk
  have hkLe : k <= 18 :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkLt : k < 19 := Nat.lt_succ_iff.mpr hkLe
  have hkSubLe : 18 - k <= 18 := Nat.sub_le 18 k
  have hkSubLt : 18 - k < 19 := Nat.lt_succ_iff.mpr hkSubLe
  have hChooseNonneg : 0 <= (Nat.choose 18 k : Real) := by positivity
  have hOmegaNonneg :
      0 <=
        (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaAbs
          i (18 - k) : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentOmegaAbs_nonneg
        i (18 - k) hkSubLe
  have hShapeNonneg :
      0 <=
        (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqAbs
          i k : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentShapeSqAbs_nonneg
        i k hkLe
  have hCorners :=
    primaryFiniteRow0Parent0Split100Sub0_const_mul_symmetric_corners_twoSegment
      hChooseNonneg hOmegaNonneg hShapeNonneg
  simpa [
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbs,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaAbs,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqAbs,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentUpper,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentLower,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentUpper,
    hkLt,
    hkSubLt,
    Rat.cast_neg,
    Rat.cast_mul,
    mul_assoc] using hCorners

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_rawAssembly
    (i : Fin 2) :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
        i).rawLower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
              i).termLower k : Real)) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
              i).termUpper k : Real)) <=
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
          i).rawUpper : Real) := by
  have hScaleAbs :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound
  have hActiveScaleNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff := by
    unfold primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
    positivity
  have hScaleLe :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) := by
    simpa [abs_of_nonneg hActiveScaleNonneg] using hScaleAbs
  have hTermSumNonneg :
      0 <=
        (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum
          i : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentTermAbsSum_nonneg
        i
  have hMulLe :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum
            i : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum
            i : Real) :=
    mul_le_mul_of_nonneg_right hScaleLe hTermSumNonneg
  have hMulLeSum :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbs
              i k : Real)) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbs
              i k : Real)) := by
    simpa [
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum,
      Rat.cast_sum] using hMulLe
  constructor
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum]
    rw [Rat.cast_neg, Rat.cast_mul, Rat.cast_sum]
    norm_num
    nlinarith
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermUpper,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSignedFactorTermAbsSum]
    rw [Rat.cast_mul, Rat.cast_sum]
    exact hMulLeSum

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_valid
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
      i).Valid := by
  refine
    { cellSubset := ?_
      factorRows := ?_
      termCorners :=
        primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_termCorners
          i
      rawAssembly :=
        primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_rawAssembly
          i }
  · intro eta hEta
    simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment]
      using
        primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_subset_cell
          i eta hEta
  · intro eta hEta k hk
    have hkLt : k < 19 := Finset.mem_range.mp hk
    have hOmega :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_interval
        i ⟨k, hkLt⟩ eta
        (by
          simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment]
            using hEta)
    have hShapeSq :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_interval
        i ⟨k, hkLt⟩ eta
        (by
          simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment]
            using hEta)
    simpa [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentOmegaUpper,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentShapeSqUpper,
      hkLt] using
      ⟨hOmega.1, hOmega.2, hShapeSq.1, hShapeSq.2⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
      ⟨0, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_valid
    ⟨0, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
      ⟨1, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_valid
    ⟨1, by decide⟩

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawPolyAbs
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawAbs i +
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat

def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
    (i : Fin 2) :
    Step33Sub0CollapsedDegree0RawPolySegmentCert :=
  (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment
    i).toRawPolySegmentCert
    (-primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat)
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat
    (-primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawPolyAbs i)
    (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawPolyAbs i)

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_rawPoly_valid
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
      i).Valid := by
  unfold primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
  refine
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment
      (primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_valid
        i)
      ?_ ?_ ?_
  · intro eta hEta
    have hFull :
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      exact
        primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_subset_cell
          i eta
          (by
            simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment]
              using hEta)
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_abs_le
        hFull
    simpa [Real.norm_eq_abs, abs_le] using hAbs
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawPolyAbs]
    simp [Rat.cast_neg, Rat.cast_add]
    ring_nf
    exact
      (le_rfl :
        -(primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
          Real) <=
        -(primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
          Real))
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegment,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawPolyAbs]
    simp [Rat.cast_neg, Rat.cast_add]

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_rawPoly_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
      ⟨0, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_rawPoly_valid
    ⟨0, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_rawPoly_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPoly
      ⟨1, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_rawPoly_valid
    ⟨1, by decide⟩

def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPolyAbsMax :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawPolyAbs
      ⟨0, by decide⟩ +
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentRawPolyAbs
      ⟨1, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPolyAbsMax /
          20 := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_budget_not_spendable :
    ¬
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPolyAbsMax :
            Real) *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) := by
  have h :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
            primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPolyAbsMax /
              20 :
          Rat) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_budget_fail_rat
  rw [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at h
  have hDiv :
      (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPolyAbsMax :
          Real) /
          20 =
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentRawPolyAbsMax :
          Real) *
          ((1 : Real) / 20) := by
    ring
  rw [hDiv] at h
  exact not_le_of_gt h

end Step33
end PSDpd
end Q3
