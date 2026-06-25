import Q3.Proofs.PSD_CenteredCoeffRawOmegaARawD17LocalCenterJets18Payload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Sharp local center-jet rows for the Step33A.1-A sub0 raw-D17 two-segment
route.

Unlike the coarse local payload, this file does not use the old full-cell
absolute derivative majorants as the local center-jet rows.  It transports the
checked proof-grade center-jet rows at the active center `1 / 20` to the two
local centers `1 / 40` and `3 / 40`, using the checked order-18 centered Taylor
majorant bridge.  The order-18 remainder row is still the existing proof-grade
uniform row.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- The active source center for sharp transfer to the raw-D17 local centers. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Rat :=
  (1 : Rat) / 20

/-- Radius from the active source center `1 / 20` to each raw-D17 local center. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius : Rat :=
  (1 : Rat) / 40

/-- Left endpoint of the source-to-local transfer segment. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL
    (i : Fin 2) : Rat :=
  if i.1 = 0 then (1 : Rat) / 40 else (1 : Rat) / 20

/-- Right endpoint of the source-to-local transfer segment. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU
    (i : Fin 2) : Rat :=
  if i.1 = 0 then (1 : Rat) / 20 else (3 : Rat) / 40

private theorem primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSource_mem_segment
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real) ∈
      Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL i :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU i :
          Real) := by
  fin_cases i <;>
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU]

private theorem primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_sharpSourceSegment
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) ∈
      Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL i :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU i :
          Real) := by
  fin_cases i <;>
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU]

private theorem primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_subset_cell
    (i : Fin 2) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL i :
            Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU i :
            Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
  intro eta heta
  fin_cases i <;>
    simp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU] at heta ⊢ <;>
    constructor <;> linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_radius
    (i : Fin 2) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL i :
            Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU i :
            Real),
      ‖eta -
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius :
          Real) := by
  intro eta heta
  rw [Real.norm_eq_abs]
  fin_cases i <;>
    simp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius] at heta ⊢ <;>
    rw [abs_le] <;>
    constructor <;> linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_reflect_cell
    (i : Fin 2) :
    ∀ y ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL i :
            Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU i :
            Real),
      y <=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real) ->
        ∀ x ∈
            Set.Icc
              (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
                Real)
              (2 *
                  (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
                    Real) -
                y),
          2 *
              (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
                Real) -
            x ∈
              Set.Icc
                (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL
                  i : Real)
                (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU
                  i : Real) := by
  intro y hy hy_le x hx
  fin_cases i <;>
    simp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter] at hy hy_le hx ⊢ <;>
    constructor <;> linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_norm_div_factorial_le
    {x m : Real} (n : Nat) (h : ‖x‖ <= m) :
    ‖x / (Nat.factorial n : Real)‖ <=
      m / (Nat.factorial n : Real) := by
  have hfac_nonneg : 0 <= (Nat.factorial n : Real) := by positivity
  have hscaled :
      ‖x‖ / (Nat.factorial n : Real) <=
        m / (Nat.factorial n : Real) :=
    div_le_div_of_nonneg_right h hfac_nonneg
  simpa [norm_div, Real.norm_eq_abs, abs_of_nonneg hfac_nonneg] using hscaled

/-- Sharp source-center normalized `OmegaActual` row used for local transfer. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs
    (j : Fin 18) : Rat :=
  if _ : j.1 < 17 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs j.1
  else
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
        17 /
      (Nat.factorial 17 : Rat)

/-- Sharp source-center normalized `ShapeSqActual` row used for local transfer. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs
    (j : Fin 18) : Rat :=
  if _ : j.1 < 17 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs j.1
  else
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
      17 /
      (Nat.factorial 17 : Rat)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower
    (j : Fin 18) : Rat :=
  if _h : j.1 < 17 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetLower j.1
  else
    -primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
        17 /
      (Nat.factorial 17 : Rat)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper
    (j : Fin 18) : Rat :=
  if _h : j.1 < 17 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetUpper j.1
  else
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
        17 /
      (Nat.factorial 17 : Rat)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower
    (j : Fin 18) : Rat :=
  if _h : j.1 < 17 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetLower j.1
  else
    -primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
        17 /
      (Nat.factorial 17 : Rat)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper
    (j : Fin 18) : Rat :=
  if _h : j.1 < 17 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetUpper j.1
  else
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
        17 /
      (Nat.factorial 17 : Rat)

private theorem step22OmegaArchWeight_contDiff18_rawD17Sharp :
    ContDiff Real 18
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight := by
  rw [show (18 : WithTop ENat) = (17 : WithTop ENat) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  constructor
  · exact fun eta =>
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt
        eta
  · constructor
    · intro h
      norm_num at h
    · have hDeriv :
          deriv Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight =
            step22OmegaArchWeightDerivClosedForm := by
        funext eta
        exact step22OmegaArchWeight_deriv_eq_closedForm eta
      rw [hDeriv]
      exact
        Step33Sub0OmegaPrimeOrder17Payload.step22OmegaArchWeightDerivClosedForm_contDiff17

private theorem primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17Sharp :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
  simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
    step22OmegaArchWeight_contDiff18_rawD17Sharp

private theorem primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17Sharp :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  fun_prop

private theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_order18_on_rawD17Segment_sharp
    (i : Fin 2) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      ‖iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
          18 : Real) := by
  intro eta heta
  have hcell :=
    primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_subset_cell
      i eta heta
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18
      eta hcell 18 (by norm_num)
  simpa [primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast]
    using hAbs

private theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_on_rawD17Segment_sharp
    (i : Fin 2) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      ‖iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
          18 : Real) := by
  intro eta heta
  have hcell :=
    primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_subset_cell
      i eta heta
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18
      eta hcell 18 (by norm_num)
  simpa [primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast]
    using hAbs

private theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpSourceCenterJet_abs
    (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs
        j : Real) := by
  by_cases hj : j.1 < 17
  · have hBase :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_centerJet_abs_bound
        j.1 hj
    rw [Real.norm_eq_abs]
    simpa [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter,
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
      hj] using hBase
  · have hj_eq : j.1 = 17 := by
      have hj_le : j.1 <= 17 := Nat.le_of_lt_succ j.2
      omega
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real)
        (by
          norm_num [
            primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter])
        17 (by norm_num)
    have hAbsRat :
        ‖iteratedDeriv 17 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real)‖ <=
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
            17 : Real) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast]
        using hAbs
    have hDiv :=
      primaryFiniteRow0Parent0Split100Sub0_norm_div_factorial_le
        (n := 17) hAbsRat
    simpa [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs,
      hj, hj_eq, Rat.cast_div] using hDiv

private theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpSourceCenterJet_abs
    (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs
        j : Real) := by
  by_cases hj : j.1 < 17
  · have hBase :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_centerJet_abs_bound
        j.1 hj
    rw [Real.norm_eq_abs]
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter,
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
      hj] using hBase
  · have hj_eq : j.1 = 17 := by
      have hj_le : j.1 <= 17 := Nat.le_of_lt_succ j.2
      omega
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real)
        (by
          norm_num [
            primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter])
        17 (by norm_num)
    have hAbsRat :
        ‖iteratedDeriv 17 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real)‖ <=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
            17 : Real) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast]
        using hAbs
    have hDiv :=
      primaryFiniteRow0Parent0Split100Sub0_norm_div_factorial_le
        (n := 17) hAbsRat
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs,
      hj, hj_eq, Rat.cast_div] using hDiv

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpSourceCenterJet18_signed_interval
    (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower
        j : Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper
          j : Real) := by
  by_cases hj : j.1 < 17
  · have hSigned :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval
        ⟨j.1, hj⟩
    simpa [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetLower,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetUpper,
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
      hj] using hSigned
  · have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpSourceCenterJet_abs
        j
    rw [Real.norm_eq_abs] at hAbs
    have hBounds := abs_le.mp hAbs
    simp [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs,
      hj, Rat.cast_div] at hBounds
    constructor
    · dsimp [
        primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower]
      simp [hj, Rat.cast_neg, Rat.cast_div]
      linarith [hBounds.1]
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs,
        hj, Rat.cast_div] using hBounds.2

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpSourceCenterJet18_signed_interval
    (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower
        j : Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper
          j : Real) := by
  by_cases hj : j.1 < 17
  · have hSigned :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval
        ⟨j.1, hj⟩
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetLower,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetUpper,
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
      hj] using hSigned
  · have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpSourceCenterJet_abs
        j
    rw [Real.norm_eq_abs] at hAbs
    have hBounds := abs_le.mp hAbs
    simp [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs,
      hj, Rat.cast_div] at hBounds
    constructor
    · dsimp [
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower]
      simp [hj, Rat.cast_neg, Rat.cast_div]
      linarith [hBounds.1]
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs,
        hj, Rat.cast_div] using hBounds.2

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceToLocal_uIcc_subset_segment
    (i : Fin 2) :
    ∀ eta ∈
        Set.uIcc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real),
      eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real) := by
  intro eta hEta
  fin_cases i <;>
    norm_num [
      Set.uIcc,
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] at hEta ⊢ <;>
    constructor <;> linarith

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_point_interval_generated
    (i : Fin 2) (k : Fin 18) :
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
        ((primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
            18 : Real) *
          ‖(primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) -
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real)‖ ^ (18 - k.1) /
            (Nat.factorial (18 - k.1) : Real)) <=
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) ∧
      iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) <=
        centeredTaylorDerivPointUpper18
          (fun j : Fin 18 =>
            (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower
              j : Real))
          (fun j : Fin 18 =>
            (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper
              j : Real))
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real)
          k
          ((primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
              18 : Real) *
            ‖(primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) -
              (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
                Real)‖ ^ (18 - k.1) /
              (Nat.factorial (18 - k.1) : Real)) := by
  refine
    iteratedDeriv_mem_Icc_of_centerJet18_point
      (f := primaryFiniteRow0Parent0Split100Sub0OmegaActual)
      (center :=
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real))
      (x := (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real))
      (order18Abs :=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
          18 : Real))
      (jetLower := fun j : Fin 18 =>
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetLower
          j : Real))
      (jetUpper := fun j : Fin 18 =>
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetUpper
          j : Real))
      k
      primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17Sharp
      ?_ ?_
  · exact
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpSourceCenterJet18_signed_interval
  · intro eta hEta
    exact
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_order18_on_rawD17Segment_sharp
        i eta
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceToLocal_uIcc_subset_segment
          i eta hEta)

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_point_interval_generated
    (i : Fin 2) (k : Fin 18) :
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
        ((primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
            18 : Real) *
          ‖(primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) -
            (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
              Real)‖ ^ (18 - k.1) /
            (Nat.factorial (18 - k.1) : Real)) <=
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) ∧
      iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) <=
        centeredTaylorDerivPointUpper18
          (fun j : Fin 18 =>
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower
              j : Real))
          (fun j : Fin 18 =>
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper
              j : Real))
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real)
          k
          ((primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
              18 : Real) *
            ‖(primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) -
              (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
                Real)‖ ^ (18 - k.1) /
              (Nat.factorial (18 - k.1) : Real)) := by
  refine
    iteratedDeriv_mem_Icc_of_centerJet18_point
      (f := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
      (center :=
        (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter : Real))
      (x := (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real))
      (order18Abs :=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
          18 : Real))
      (jetLower := fun j : Fin 18 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetLower
          j : Real))
      (jetUpper := fun j : Fin 18 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetUpper
          j : Real))
      k
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17Sharp
      ?_ ?_
  · exact
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpSourceCenterJet18_signed_interval
  · intro eta hEta
    exact
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_on_rawD17Segment_sharp
        i eta
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceToLocal_uIcc_subset_segment
          i eta hEta)

/-- Sharp local normalized `OmegaActual` center-jet absolute row. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
    (_i : Fin 2) (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
        18)
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius
      ⟨j.1, Nat.lt_trans j.2 (by norm_num)⟩ /
    (Nat.factorial j.1 : Rat)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetLower
    (i : Fin 2) (j : Fin 18) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs i j

def primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetUpper
    (i : Fin 2) (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs i j

/-- Sharp local normalized `ShapeSqActual` center-jet absolute row. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
    (_i : Fin 2) (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
        18)
      primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius
      ⟨j.1, Nat.lt_trans j.2 (by norm_num)⟩ /
    (Nat.factorial j.1 : Rat)

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetLower
    (i : Fin 2) (j : Fin 18) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs i j

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetUpper
    (i : Fin 2) (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs i j

private theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpLocalJet_abs
    (i : Fin 2) (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
        i j : Real) := by
  have hDeriv :
      ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
          primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
            18)
          primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius
          ⟨j.1, Nat.lt_trans j.2 (by norm_num)⟩ : Real) := by
    have hTaylor :=
      iteratedDeriv_norm_le_centeredTaylorDerivMajorant18
        (f := primaryFiniteRow0Parent0Split100Sub0OmegaActual)
        (a :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL
            i : Real))
        (b :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU
            i : Real))
        (center :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real))
        (radius :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius :
            Real))
        (order18Abs :=
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
            18 : Real))
        (eta :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real))
        (jetAbs := fun j : Fin 18 =>
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpSourceCenterJetAbs
            j : Real))
        ⟨j.1, Nat.lt_trans j.2 (by norm_num)⟩
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSource_mem_segment
          i)
        primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17Sharp
        primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpSourceCenterJet_abs
        (by
          intro eta heta
          have hCell :=
            primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_subset_cell
              i eta heta
          have hAbs :=
            primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18
              eta hCell 18 (by norm_num)
          simpa [
            primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast]
            using hAbs)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_radius
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_reflect_cell
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_sharpSourceSegment
          i)
    simpa [
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast]
      using hTaylor
  have hDiv :=
    primaryFiniteRow0Parent0Split100Sub0_norm_div_factorial_le
      (n := j.1) hDeriv
  simpa [
    primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs,
    Rat.cast_div] using hDiv

private theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpLocalJet_abs
    (i : Fin 2) (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
        i j : Real) := by
  have hDeriv :
      ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
            18)
          primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius
          ⟨j.1, Nat.lt_trans j.2 (by norm_num)⟩ : Real) := by
    have hTaylor :=
      iteratedDeriv_norm_le_centeredTaylorDerivMajorant18
        (f := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
        (a :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentL
            i : Real))
        (b :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceSegmentU
            i : Real))
        (center :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceCenter :
            Real))
        (radius :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17SharpSourceRadius :
            Real))
        (order18Abs :=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
            18 : Real))
        (eta :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real))
        (jetAbs := fun j : Fin 18 =>
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpSourceCenterJetAbs
            j : Real))
        ⟨j.1, Nat.lt_trans j.2 (by norm_num)⟩
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSource_mem_segment
          i)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17Sharp
        primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpSourceCenterJet_abs
        (by
          intro eta heta
          have hCell :=
            primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_subset_cell
              i eta heta
          have hAbs :=
            primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18
              eta hCell 18 (by norm_num)
          simpa [
            primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast]
            using hAbs)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_radius
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17SharpSourceSegment_reflect_cell
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_sharpSourceSegment
          i)
    simpa [
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast]
      using hTaylor
  have hDiv :=
    primaryFiniteRow0Parent0Split100Sub0_norm_div_factorial_le
      (n := j.1) hDeriv
  simpa [
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs,
    Rat.cast_div] using hDiv

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_sharp_interval_generated
    (i : Fin 2) (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetLower
        i j : Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
        (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetUpper
          i j : Real) := by
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpLocalJet_abs i j
  rw [Real.norm_eq_abs] at hAbs
  simpa [
    primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetUpper,
    Rat.cast_neg] using
    abs_le.mp hAbs

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_sharp_interval_generated
    (i : Fin 2) (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetLower
        i j : Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
        (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetUpper
          i j : Real) := by
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpLocalJet_abs i j
  rw [Real.norm_eq_abs] at hAbs
  simpa [
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetLower,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetUpper,
    Rat.cast_neg] using
    abs_le.mp hAbs

/-- Sharp two-segment absolute row for local `OmegaActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs
    (i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs i)
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
      18)
    primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius
    k

def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower
    (i : Fin 2) (k : Fin 19) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs
    i k

def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper
    (i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs
    i k

/-- Sharp two-segment absolute row for local `ShapeSqActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs
    (i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs i)
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
      18)
    primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius
    k

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower
    (i : Fin 2) (k : Fin 19) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs
    i k

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper
    (i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs
    i k

private theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpLocalJet_abs_for_derivative
    (i : Fin 2) (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
        i j : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpLocalJet_abs i j

private theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpLocalJet_abs_for_derivative
    (i : Fin 2) (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
        i j : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpLocalJet_abs i j

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_sharp_interval
    (i : Fin 2) (k : Fin 19) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower
        i k : Real) <=
          iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            eta ∧
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            eta <=
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper
            i k : Real) := by
  intro eta heta
  have hBound :
      ‖iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs
          i k : Real) := by
    have hTaylor :=
      iteratedDeriv_norm_le_centeredTaylorDerivMajorant18
        (f := primaryFiniteRow0Parent0Split100Sub0OmegaActual)
        (a := (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real))
        (b := (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real))
        (center :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real))
        (radius :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius : Real))
        (order18Abs :=
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
            18 : Real))
        (eta := eta)
        (jetAbs := fun j : Fin 18 =>
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
            i j : Real))
        k
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
          i)
        primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17Sharp
        (primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpLocalJet_abs_for_derivative
          i)
        (primaryFiniteRow0Parent0Split100Sub0_omegaActual_order18_on_rawD17Segment_sharp
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_radius i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_reflect_cell i)
        heta
    simpa [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs,
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast]
      using hTaylor
  rw [Real.norm_eq_abs] at hBound
  simpa [
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper,
    Rat.cast_neg] using abs_le.mp hBound

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_sharp_interval
    (i : Fin 2) (k : Fin 19) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower
        i k : Real) <=
          iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            eta ∧
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            eta <=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper
            i k : Real) := by
  intro eta heta
  have hBound :
      ‖iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs
          i k : Real) := by
    have hTaylor :=
      iteratedDeriv_norm_le_centeredTaylorDerivMajorant18
        (f := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
        (a := (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real))
        (b := (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real))
        (center :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real))
        (radius :=
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius : Real))
        (order18Abs :=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
            18 : Real))
        (eta := eta)
        (jetAbs := fun j : Fin 18 =>
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
            i j : Real))
        k
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
          i)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17Sharp
        (primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpLocalJet_abs_for_derivative
          i)
        (primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_on_rawD17Segment_sharp
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_radius i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_reflect_cell i)
        heta
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs,
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast]
      using hTaylor
  rw [Real.norm_eq_abs] at hBound
  simpa [
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper,
    Rat.cast_neg] using abs_le.mp hBound

private theorem primaryFiniteRow0Parent0Split100Sub0_const_mul_symmetric_corners_sharp
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

/-- `Nat` wrapper for sharp local `OmegaActual` derivative lower rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaLower
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower
      i ⟨k, hk⟩
  else
    0

/-- `Nat` wrapper for sharp local `OmegaActual` derivative upper rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaUpper
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper
      i ⟨k, hk⟩
  else
    0

/-- `Nat` wrapper for sharp local `ShapeSqActual` derivative lower rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqLower
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower
      i ⟨k, hk⟩
  else
    0

/-- `Nat` wrapper for sharp local `ShapeSqActual` derivative upper rows. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqUpper
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper
      i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs
      i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs
    (i : Fin 2) (k : Nat) : Rat :=
  if hk : k < 19 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs
      i ⟨k, hk⟩
  else
    0

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbs
    (i : Fin 2) (k : Nat) : Rat :=
  (Nat.choose 18 k : Rat) *
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs
      i (18 - k) *
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs
      i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermLower
    (i : Fin 2) (k : Nat) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbs
    i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermUpper
    (i : Fin 2) (k : Nat) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbs
    i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum
    (i : Fin 2) : Rat :=
  ∑ k ∈ Finset.range (18 + 1),
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbs
      i k

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum
      i

/-- Local sharp signed-factor segment certificate. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
    (i : Fin 2) :
    Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert where
  cellL := primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i
  cellU := primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i
  omegaLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaLower i
  omegaUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaUpper i
  shapeSqLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqLower i
  shapeSqUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqUpper i
  termLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermLower
      i
  termUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermUpper
      i
  rawLower :=
    -primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs i
  rawUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs i

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentSharpOmegaAbs_nonneg
    (i : Fin 2) (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs
        i k := by
  fin_cases i <;>
    interval_cases k <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentSharpShapeSqAbs_nonneg
    (i : Fin 2) (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs
        i k := by
  fin_cases i <;>
    interval_cases k <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentSharpTermAbsSum_nonneg
    (i : Fin 2) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum
        i := by
  fin_cases i <;>
    native_decide

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_termCorners
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
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
        (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs
          i (18 - k) : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentSharpOmegaAbs_nonneg
        i (18 - k) hkSubLe
  have hShapeNonneg :
      0 <=
        (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs
          i k : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentSharpShapeSqAbs_nonneg
        i k hkLe
  have hCorners :=
    primaryFiniteRow0Parent0Split100Sub0_const_mul_symmetric_corners_sharp
      hChooseNonneg hOmegaNonneg hShapeNonneg
  simpa [
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermLower,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermUpper,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbs,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs,
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper,
    hkLt,
    hkSubLt,
    Rat.cast_neg,
    Rat.cast_mul,
    mul_assoc] using hCorners

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_rawAssembly
    (i : Fin 2) :
    ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
        i).rawLower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
              i).termLower k : Real)) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
              i).termUpper k : Real)) <=
        ((primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
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
        (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum
          i : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_twoSegmentSharpTermAbsSum_nonneg
        i
  have hMulLe :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum
            i : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum
            i : Real) :=
    mul_le_mul_of_nonneg_right hScaleLe hTermSumNonneg
  have hMulLeSum :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbs
              i k : Real)) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) *
          (∑ k ∈ Finset.range (18 + 1),
            (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbs
              i k : Real)) := by
    simpa [
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum,
      Rat.cast_sum] using hMulLe
  constructor
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum]
    rw [Rat.cast_neg, Rat.cast_mul, Rat.cast_sum]
    norm_num
    nlinarith
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermUpper,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum]
    rw [Rat.cast_mul, Rat.cast_sum]
    exact hMulLeSum

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_valid
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
      i).Valid := by
  refine
    { cellSubset := ?_
      factorRows := ?_
      termCorners :=
        primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_termCorners
          i
      rawAssembly :=
        primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_rawAssembly
          i }
  · intro eta hEta
    simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp]
      using
        primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_subset_cell
          i eta hEta
  · intro eta hEta k hk
    have hkLt : k < 19 := Finset.mem_range.mp hk
    have hOmega :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_sharp_interval
        i ⟨k, hkLt⟩ eta
        (by
          simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp]
            using hEta)
    have hShapeSq :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_sharp_interval
        i ⟨k, hkLt⟩ eta
        (by
          simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp]
            using hEta)
    simpa [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaUpper,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqUpper,
      hkLt] using
      ⟨hOmega.1, hOmega.2, hShapeSq.1, hShapeSq.2⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_left_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
      ⟨0, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_valid
    ⟨0, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_right_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
      ⟨1, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_valid
    ⟨1, by decide⟩

def primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs i +
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat

def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
    (i : Fin 2) :
    Step33Sub0CollapsedDegree0RawPolySegmentCert :=
  (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
    i).toRawPolySegmentCert
    (-primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat)
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat
    (-primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs i)
    (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs i)

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_rawPoly_valid
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      i).Valid := by
  unfold primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
  refine
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment
      (primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_valid
        i)
      ?_ ?_ ?_
  · intro eta hEta
    have hFull :
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      exact
        primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_subset_cell
          i eta
          (by
            simpa [primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp]
              using hEta)
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_abs_le
        hFull
    simpa [Real.norm_eq_abs, abs_le] using hAbs
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs]
    simp [Rat.cast_neg, Rat.cast_add]
    ring_nf
    exact
      (le_rfl :
        -(primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
          Real) <=
        -(primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
          Real))
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs]
    simp [Rat.cast_neg, Rat.cast_add]

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_left_rawPoly_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      ⟨0, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_rawPoly_valid
    ⟨0, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_right_rawPoly_valid :
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      ⟨1, by decide⟩).Valid :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_rawPoly_valid
    ⟨1, by decide⟩

def primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs
      ⟨0, by decide⟩ +
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs
      ⟨1, by decide⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax /
          20 := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_not_spendable :
    ¬
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax :
            Real) *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) := by
  have h :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
            primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax /
              20 :
          Rat) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_fail_rat
  rw [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at h
  have hDiv :
      (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax :
          Real) /
          20 =
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax :
          Real) *
          ((1 : Real) / 20) := by
    ring
  rw [hDiv] at h
  exact not_le_of_gt h

end Step33
end PSDpd
end Q3
