import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18BudgetAudit
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant18

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-grade local center-jet rows for the Step33A.1-A sub0 raw-D17
two-segment route.

This payload is deliberately coarse: it bounds the normalized center jets at
the local centers `1 / 40` and `3 / 40` by the existing full-cell order-18
absolute derivative majorants.  It proves that the local center-jet row
interface is live, but it is not a sharp two-segment budget closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- The two local centers for the raw-D17 split of the sub0 cell `[0, 1/10]`. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter
    (i : Fin 2) : Rat :=
  if i.1 = 0 then (1 : Rat) / 40 else (3 : Rat) / 40

theorem primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_cell
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) ∈
      Set.Icc (0 : Real) ((1 : Real) / 10) := by
  fin_cases i <;>
    norm_num [primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter]

/-- Left endpoint of the two raw-D17 local segments. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL
    (i : Fin 2) : Rat :=
  if i.1 = 0 then 0 else (1 : Rat) / 20

/-- Right endpoint of the two raw-D17 local segments. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU
    (i : Fin 2) : Rat :=
  if i.1 = 0 then (1 : Rat) / 20 else (1 : Rat) / 10

/-- Common local radius for both raw-D17 split segments. -/
def primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius : Rat :=
  (1 : Rat) / 40

theorem primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real) ∈
      Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
        (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real) := by
  fin_cases i <;>
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU]

theorem primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_subset_cell
    (i : Fin 2) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
  intro eta heta
  fin_cases i <;>
    simp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] at heta ⊢ <;>
    constructor <;> linarith

theorem primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_radius
    (i : Fin 2) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      ‖eta -
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius : Real) := by
  intro eta heta
  rw [Real.norm_eq_abs]
  fin_cases i <;>
    simp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius] at heta ⊢ <;>
    rw [abs_le] <;>
    constructor <;> linarith

theorem primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_reflect_cell
    (i : Fin 2) :
    ∀ y ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      y <=
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) ->
        ∀ x ∈
            Set.Icc
              (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
                Real)
              (2 *
                  (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
                    Real) -
                y),
          2 *
              (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
                Real) -
            x ∈
              Set.Icc
                (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i :
                  Real)
                (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i :
                  Real) := by
  intro y hy hy_le x hx
  fin_cases i <;>
    simp [
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter] at hy hy_le hx ⊢ <;>
    constructor <;> linarith

/-- Coarse absolute row for normalized `OmegaActual` center jets. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs
    (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
      j.1 /
    (Nat.factorial j.1 : Rat)

/-- Coarse lower row for normalized `OmegaActual` center jets. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetLower
    (_i : Fin 2) (j : Fin 18) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs j

/-- Coarse upper row for normalized `OmegaActual` center jets. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetUpper
    (_i : Fin 2) (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs j

/-- Coarse absolute row for normalized `ShapeSqActual` center jets. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs
    (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
      j.1 /
    (Nat.factorial j.1 : Rat)

/-- Coarse lower row for normalized `ShapeSqActual` center jets. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetLower
    (_i : Fin 2) (j : Fin 18) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs j

/-- Coarse upper row for normalized `ShapeSqActual` center jets. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetUpper
    (_i : Fin 2) (j : Fin 18) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs j

private theorem primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_div_factorial
    {x m : Real} (n : Nat) (hAbs : ‖x‖ <= m) :
    -(m / (Nat.factorial n : Real)) <=
        x / (Nat.factorial n : Real) ∧
      x / (Nat.factorial n : Real) <=
        m / (Nat.factorial n : Real) := by
  have hfac_nonneg : 0 <= (Nat.factorial n : Real) := by
    positivity
  have hdiv :
      ‖x / (Nat.factorial n : Real)‖ <=
        m / (Nat.factorial n : Real) := by
    have hscaled :
        ‖x‖ / (Nat.factorial n : Real) <=
          m / (Nat.factorial n : Real) :=
      div_le_div_of_nonneg_right hAbs hfac_nonneg
    simpa [norm_div] using hscaled
  rw [Real.norm_eq_abs] at hdiv
  exact abs_le.mp hdiv

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet_interval_generated
    (i : Fin 2) (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetLower i j :
        Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetUpper i j :
          Real) := by
  have hj_le : j.1 <= 18 :=
    Nat.le_trans (Nat.le_of_lt j.2) (by norm_num)
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18
      (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
      (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_cell i)
      j.1 hj_le
  have hAbsRat :
      ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
          j.1 : Real) := by
    simpa [primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant18Rat_cast]
      using hAbs
  simpa [
    primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetUpper,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs,
    Rat.cast_neg,
    Rat.cast_div] using
    primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_div_factorial
      (n := j.1) hAbsRat

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet_interval_generated
    (i : Fin 2) (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetLower i j :
        Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetUpper i j :
          Real) := by
  have hj_le : j.1 <= 18 :=
    Nat.le_trans (Nat.le_of_lt j.2) (by norm_num)
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18
      (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
      (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_cell i)
      j.1 hj_le
  have hAbsRat :
      ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
          j.1 : Real) := by
    simpa [primaryFiniteRow0Parent0Split100Sub0_shapeSqActualSharpDerivativeMajorant18Rat_cast]
      using hAbs
  simpa [
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetLower,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetUpper,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs,
    Rat.cast_neg,
    Rat.cast_div] using
    primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_div_factorial
      (n := j.1) hAbsRat

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_twoSegment_interval
    (i : Fin 2) (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetLower i j :
        Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetUpper i j :
          Real) :=
  primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet_interval_generated
    i j

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_twoSegment_interval
    (i : Fin 2) (j : Fin 18) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetLower i j :
        Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) ∧
      iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) /
          (Nat.factorial j.1 : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetUpper i j :
          Real) :=
  primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet_interval_generated
    i j

/-- Exact rational mirror of `centeredTaylorDerivMajorant18`. -/
def primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
    (jetAbs : Fin 18 -> Rat) (order18Abs radius : Rat)
    (k : Fin 19) : Rat :=
  (∑ j : Fin 18,
      if k.1 <= j.1 then
        ((Nat.factorial j.1 : Rat) /
            (Nat.factorial (j.1 - k.1) : Rat)) *
          jetAbs j *
          radius ^ (j.1 - k.1)
      else
        0) +
    order18Abs * radius ^ (18 - k.1) /
      (Nat.factorial (18 - k.1) : Rat)

theorem
    primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast
    (jetAbs : Fin 18 -> Rat) (order18Abs radius : Rat)
    (k : Fin 19) :
    (primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
        jetAbs order18Abs radius k : Real) =
      centeredTaylorDerivMajorant18
        (fun j : Fin 18 => (jetAbs j : Real))
        (order18Abs : Real) (radius : Real) k := by
  unfold primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
  unfold centeredTaylorDerivMajorant18
  rw [Rat.cast_add]
  congr 1
  · rw [Rat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hle : k.1 <= j.1
    · simp [hle]
    · simp [hle]
  · simp

/-- Coarse two-segment absolute row for `OmegaActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentAbs
    (_i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
    primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs
    (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
      18)
    primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius
    k

/-- Coarse lower row for local `OmegaActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentLower
    (i : Fin 2) (k : Fin 19) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentAbs i k

/-- Coarse upper row for local `OmegaActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentUpper
    (i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentAbs i k

/-- Coarse two-segment absolute row for `ShapeSqActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentAbs
    (_i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
      18)
    primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius
    k

/-- Coarse lower row for local `ShapeSqActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentLower
    (i : Fin 2) (k : Fin 19) : Rat :=
  -primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentAbs i k

/-- Coarse upper row for local `ShapeSqActual` derivatives. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentUpper
    (i : Fin 2) (k : Fin 19) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentAbs i k

private theorem primaryFiniteRow0Parent0Split100Sub0_interval_of_norm_bound
    {x m : Real} (h : ‖x‖ <= m) :
    -m <= x ∧ x <= m := by
  rw [Real.norm_eq_abs] at h
  exact abs_le.mp h

private theorem step22OmegaArchWeight_contDiff18_rawD17LocalCenter :
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

private theorem
    primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17LocalCenter :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
  simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
    step22OmegaArchWeight_contDiff18_rawD17LocalCenter

private theorem
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17LocalCenter :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  fun_prop

private theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet_abs
    (i : Fin 2) (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs j :
        Real) := by
  rw [Real.norm_eq_abs, abs_le]
  simpa [
    primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetUpper,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs,
    Rat.cast_neg,
    Rat.cast_div] using
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet_interval_generated
      i j

private theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet_abs
    (i : Fin 2) (j : Fin 18) :
    ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) /
        (Nat.factorial j.1 : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs j :
        Real) := by
  rw [Real.norm_eq_abs, abs_le]
  simpa [
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetLower,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetUpper,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs,
    Rat.cast_neg,
    Rat.cast_div] using
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet_interval_generated
      i j

private theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_order18_on_rawD17Segment
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
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_on_rawD17Segment
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

theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_interval
    (i : Fin 2) (k : Fin 19) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentLower
        i k : Real) <=
          iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            eta ∧
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            eta <=
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentUpper
            i k : Real) := by
  intro eta heta
  have hBound :
      ‖iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentAbs
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
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetAbs j :
            Real))
        k
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
          i)
        primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17LocalCenter
        (primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet_abs
          i)
        (primaryFiniteRow0Parent0Split100Sub0_omegaActual_order18_on_rawD17Segment
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_radius i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_reflect_cell i)
        heta
    simpa [
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentAbs,
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast]
      using hTaylor
  simpa [
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentUpper,
    Rat.cast_neg] using
    primaryFiniteRow0Parent0Split100Sub0_interval_of_norm_bound hBound

theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_interval
    (i : Fin 2) (k : Fin 19) :
    ∀ eta ∈
        Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL i : Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU i : Real),
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentLower
        i k : Real) <=
          iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            eta ∧
        iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            eta <=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentUpper
            i k : Real) := by
  intro eta heta
  have hBound :
      ‖iteratedDeriv k.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentAbs
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
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetAbs j :
            Real))
        k
        (primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
          i)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17LocalCenter
        (primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet_abs
          i)
        (primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_on_rawD17Segment
          i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_radius i)
        (primaryFiniteRow0Parent0Split100Sub0_rawD17Segment_reflect_cell i)
        heta
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentAbs,
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast]
      using hTaylor
  simpa [
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentLower,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentUpper,
    Rat.cast_neg] using
    primaryFiniteRow0Parent0Split100Sub0_interval_of_norm_bound hBound

end Step33
end PSDpd
end Q3
