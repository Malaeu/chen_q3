import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18BudgetAudit
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
First proof-grade raw-D17 signed-factor payload for the collapsed degree-0
Step33A.1-A sub0 gate.

This is a full-cell smoke payload from the existing absolute derivative
majorants.  It validates the signed-factor receiver interface, but it is not a
spendable Step33A.1-A closure and does not revive the killed symmetric
RawProduct18 budget class.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound_rawD17
    {x m lower upper : Real}
    (hAbs : ‖x‖ <= m)
    (hLower : lower <= -m)
    (hUpper : m <= upper) :
    lower <= x ∧ x <= upper := by
  rw [Real.norm_eq_abs] at hAbs
  have hBounds := abs_le.mp hAbs
  constructor <;> linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_const_mul_symmetric_corners
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

/-- Lower row for the full-cell `OmegaActual` derivative enclosure. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17OmegaLower (k : Nat) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat k

/-- Upper row for the full-cell `OmegaActual` derivative enclosure. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17OmegaUpper (k : Nat) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat k

/-- Lower row for the full-cell `ShapeSqActual` derivative enclosure. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqLower (k : Nat) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat k

/-- Upper row for the full-cell `ShapeSqActual` derivative enclosure. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqUpper (k : Nat) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat k

/-- Absolute row for one signed Leibniz term. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs
    (k : Nat) : Rat :=
  (Nat.choose 18 k : Rat) *
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
      (18 - k) *
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
      k

/-- Lower row for one signed Leibniz term. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermLower
    (k : Nat) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs k

/-- Upper row for one signed Leibniz term. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermUpper
    (k : Nat) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs k

/-- Sum of the full-cell signed Leibniz absolute rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum :
    Rat :=
  ∑ k ∈ Finset.range (18 + 1),
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs k

/-- Full-cell active-scale raw radius induced by the signed-factor rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawAbs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum

/-- First full-cell signed-factor smoke segment. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0 :
    Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert where
  cellL := 0
  cellU := (1 : Rat) / 10
  omegaLower := primaryFiniteRow0Parent0Split100Sub0RawD17OmegaLower
  omegaUpper := primaryFiniteRow0Parent0Split100Sub0RawD17OmegaUpper
  shapeSqLower := primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqLower
  shapeSqUpper := primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqUpper
  termLower := primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermLower
  termUpper := primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermUpper
  rawLower := -primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawAbs
  rawUpper := primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawAbs

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactorTermAbs_nonneg
    (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs k := by
  interval_cases k <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_omegaMajorant18Rat_nonneg
    (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat k := by
  interval_cases k <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_shapeSqMajorant18Rat_nonneg
    (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
        k := by
  interval_cases k <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactorTermAbsSum_nonneg :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum := by
  native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_termCorners :
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.termCornerRows := by
  intro k hk
  have hkLe : k <= 18 :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkSubLe : 18 - k <= 18 := Nat.sub_le 18 k
  have hChooseNonneg : 0 <= (Nat.choose 18 k : Real) := by positivity
  have hOmegaNonneg :
      0 <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
          (18 - k) : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_omegaMajorant18Rat_nonneg
        (18 - k) hkSubLe
  have hShapeNonneg :
      0 <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
          k : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_shapeSqMajorant18Rat_nonneg
        k hkLe
  simpa [
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
    primaryFiniteRow0Parent0Split100Sub0RawD17OmegaLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17OmegaUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs,
    Rat.cast_neg,
    Rat.cast_mul,
    mul_assoc] using
    primaryFiniteRow0Parent0Split100Sub0_const_mul_symmetric_corners
      hChooseNonneg hOmegaNonneg hShapeNonneg

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_rawAssembly :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.rawLower :
        Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.termLower
              k : Real)) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.termUpper
              k : Real)) <=
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.rawUpper :
          Real) := by
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
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum :
          Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactorTermAbsSum_nonneg
  have hMulLe :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum :
            Real) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum :
            Real) :=
    mul_le_mul_of_nonneg_right hScaleLe hTermSumNonneg
  have hMulLeSum :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs k :
              Real)) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbs k :
              Real)) := by
    simpa [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum,
      Rat.cast_sum] using hMulLe
  constructor
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum]
    rw [Rat.cast_neg, Rat.cast_mul, Rat.cast_sum]
    norm_num
    nlinarith
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermUpper,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermAbsSum]
    rw [Rat.cast_mul, Rat.cast_sum]
    exact hMulLeSum

/-- The first full-cell raw-D17 signed-factor smoke segment validates the
receiver fields.  This theorem only certifies the payload shape; it does not
spend the killed symmetric RawProduct18 budget class. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_valid :
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.Valid := by
  refine
    { cellSubset := ?_
      factorRows := ?_
      termCorners :=
        primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_termCorners
      rawAssembly :=
        primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_rawAssembly }
  · intro eta hEta
    simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0]
      using hEta
  · intro eta hEta k hk
    have hkLe : k <= 18 :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hEtaCell :
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0]
        using hEta
    have hOmegaAbs :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18
        eta hEtaCell k hkLe
    have hShapeSqAbs :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18
        eta hEtaCell k hkLe
    have hOmega :
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.omegaLower
            k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta <=
            (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.omegaUpper
              k : Real) := by
      refine
        primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound_rawD17
          hOmegaAbs ?_ ?_
      · dsimp [
          primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
          primaryFiniteRow0Parent0Split100Sub0RawD17OmegaLower]
        rw [
          Rat.cast_neg,
          primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast]
      · dsimp [
          primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
          primaryFiniteRow0Parent0Split100Sub0RawD17OmegaUpper]
        rw [
          primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast]
    have hShapeSq :
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.shapeSqLower
            k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta <=
            (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.shapeSqUpper
              k : Real) := by
      refine
        primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound_rawD17
          hShapeSqAbs ?_ ?_
      · dsimp [
          primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
          primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqLower]
        rw [
          Rat.cast_neg,
          primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast]
      · dsimp [
          primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
          primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqUpper]
        rw [
          primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast]
    exact ⟨hOmega.1, hOmega.2, hShapeSq.1, hShapeSq.2⟩

/-- Symmetric signed-source radius induced by the full-cell raw-D17 smoke
payload and the existing nominal-polynomial derivative row. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawAbs +
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat

/-- Raw/poly same-segment row induced by the full-cell raw-D17 smoke payload. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawPolySegment0 :
    Step33Sub0CollapsedDegree0RawPolySegmentCert :=
  primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0.toRawPolySegmentCert
    (-primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat)
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat
    (-primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs)
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs

/-- The full-cell smoke payload wires through the existing raw/poly
same-segment bridge. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_rawPoly_segment0_valid :
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawPolySegment0.Valid := by
  unfold primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawPolySegment0
  refine
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment
      primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_valid
      ?_ ?_ ?_
  · intro eta hEta
    have hFull :
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0]
        using hEta
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_abs_le
        hFull
    simpa [Real.norm_eq_abs, abs_le] using hAbs
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs]
    simp [Rat.cast_neg, Rat.cast_add]
    ring_nf
    exact
      (le_rfl :
        -(primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
          Real) <=
        -(primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
          Real))
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs]
    simp [Rat.cast_neg, Rat.cast_add]

/-- Exact arithmetic kill for this full-cell smoke segment: the row is a valid
interface payload, but its own degree-0 budget is still too wide. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs /
          20 := by
  native_decide

/-- Real-valued spelling of the full-cell smoke-segment budget failure. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_not_spendable :
    ¬
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs :
            Real) *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) := by
  have h :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
            primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs /
              20 :
          Rat) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_fail_rat
  rw [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at h
  have hDiv :
      (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs :
          Real) /
          20 =
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0RawPolyAbs :
          Real) *
          ((1 : Real) / 20) := by
    ring
  rw [hDiv] at h
  exact not_le_of_gt h

end Step33
end PSDpd
end Q3
