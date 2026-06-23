import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SourceIntervalCert
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorMajorant
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Signed Leibniz interval checker for one Step33A.1-A sub0 order-16 source
segment.

This file is fail-closed infrastructure only.  It does not emit signed factor
rows, does not instantiate a segment certificate, and does not claim
Step33A.1-A closure.  It proves the checker shape selected by route review:
generated signed factor/Leibniz term rows for one segment can be assembled into
the existing signed whole-source interval segment receiver.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_order16Signed_sum_interval
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    {x lower upper : ι -> Real}
    (hTerm : ∀ i ∈ s, lower i <= x i ∧ x i <= upper i) :
    (∑ i ∈ s, lower i) <= (∑ i ∈ s, x i) ∧
      (∑ i ∈ s, x i) <= (∑ i ∈ s, upper i) := by
  constructor
  · exact Finset.sum_le_sum (fun i hi => (hTerm i hi).1)
  · exact Finset.sum_le_sum (fun i hi => (hTerm i hi).2)

/-- Left Leibniz term for the actual product
`OmegaPrimeActual * ShapeSqActual`. -/
def primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm
    (k : Nat) (eta : Real) : Real :=
  (Nat.choose 16 k : Real) *
    (iteratedDeriv (16 - k)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta *
      iteratedDeriv k
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta)

/-- Right Leibniz term for the actual product
`OmegaActual * ShapeSqDerivActual`. -/
def primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm
    (k : Nat) (eta : Real) : Real :=
  (Nat.choose 16 k : Real) *
    (iteratedDeriv (16 - k)
        primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
      iteratedDeriv k
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta)

private theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_signedLeibniz
    (eta : Real) :
    iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
      (∑ k ∈ Finset.range (16 + 1),
        primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
      (∑ k ∈ Finset.range (16 + 1),
        primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) := by
  let omegaPrime :=
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
  let omega :=
    primaryFiniteRow0Parent0Split100Sub0OmegaActual
  let shapeSq :=
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  let shapeSqDeriv :=
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
  have hOmegaPrimeCont :
      ContDiff Real 16 omegaPrime := by
    simpa [omegaPrime, primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual]
      using step22OmegaArchWeightDerivClosedForm_contDiff16
  have hOmegaCont :
      ContDiff Real 16 omega := by
    simpa [omega, primaryFiniteRow0Parent0Split100Sub0OmegaActual]
      using step22OmegaArchWeight_contDiff16
  have hShapeSqCont :
      ContDiff Real 16 shapeSq := by
    have hShapeSq :
        ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
      unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
      fun_prop
    simpa [shapeSq] using hShapeSq
  have hShapeSqDerivCont :
      ContDiff Real 16 shapeSqDeriv := by
    simpa [shapeSqDeriv,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)
  have hProdLeft :
      iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta =
        ∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta := by
    have h :=
      congrFun
        (primaryFiniteRow0Parent0Split100Sub0_iterate_deriv_mul 16
          omegaPrime shapeSq hOmegaPrimeCont hShapeSqCont)
        eta
    simpa [
      iteratedDeriv_eq_iterate,
      primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm,
      omegaPrime,
      shapeSq,
      nsmul_eq_mul,
      Nat.cast_id] using h
  have hProdRight :
      iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta =
        ∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta := by
    have h :=
      congrFun
        (primaryFiniteRow0Parent0Split100Sub0_iterate_deriv_mul 16
          omega shapeSqDeriv hOmegaCont hShapeSqDerivCont)
        eta
    simpa [
      iteratedDeriv_eq_iterate,
      primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm,
      omega,
      shapeSqDeriv,
      nsmul_eq_mul,
      Nat.cast_id] using h
  have hAdd :
      iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
        iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta +
          iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta := by
    unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
    change
      iteratedDeriv 16
          ((fun t : Real => omegaPrime t * shapeSq t) +
            fun t : Real => omega t * shapeSqDeriv t) eta =
        iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta +
          iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta
    rw [iteratedDeriv_add
      (hOmegaPrimeCont.mul hShapeSqCont).contDiffAt
      (hOmegaCont.mul hShapeSqDerivCont).contDiffAt]
  rw [hAdd, hProdLeft, hProdRight]

/-- Data for one generated signed-factor segment.  The term rows are the
Leibniz products after exact interval multiplication; the final source rows are
the active-scale multiplication rows consumed by the existing source segment
certificate. -/
structure Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert where
  cellL : Rat
  cellU : Rat
  omegaPrimeLower : Nat -> Rat
  omegaPrimeUpper : Nat -> Rat
  omegaLower : Nat -> Rat
  omegaUpper : Nat -> Rat
  shapeSqLower : Nat -> Rat
  shapeSqUpper : Nat -> Rat
  shapeSqDerivLower : Nat -> Rat
  shapeSqDerivUpper : Nat -> Rat
  leftTermLower : Nat -> Rat
  leftTermUpper : Nat -> Rat
  rightTermLower : Nat -> Rat
  rightTermUpper : Nat -> Rat
  sourceLower : Rat
  sourceUpper : Rat

namespace Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert

/-- Corner arithmetic rows for the left Leibniz product terms. -/
def leftTermCornerRows
    (cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Prop :=
  ∀ k ∈ Finset.range (16 + 1),
    (cert.leftTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaPrimeLower (16 - k) : Real) *
          (cert.shapeSqLower k : Real) ∧
      (cert.leftTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaPrimeLower (16 - k) : Real) *
          (cert.shapeSqUpper k : Real) ∧
      (cert.leftTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaPrimeUpper (16 - k) : Real) *
          (cert.shapeSqLower k : Real) ∧
      (cert.leftTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaPrimeUpper (16 - k) : Real) *
          (cert.shapeSqUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaPrimeLower (16 - k) : Real) *
          (cert.shapeSqLower k : Real) <=
        (cert.leftTermUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaPrimeLower (16 - k) : Real) *
          (cert.shapeSqUpper k : Real) <=
        (cert.leftTermUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaPrimeUpper (16 - k) : Real) *
          (cert.shapeSqLower k : Real) <=
        (cert.leftTermUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaPrimeUpper (16 - k) : Real) *
          (cert.shapeSqUpper k : Real) <=
        (cert.leftTermUpper k : Real)

/-- Corner arithmetic rows for the right Leibniz product terms. -/
def rightTermCornerRows
    (cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Prop :=
  ∀ k ∈ Finset.range (16 + 1),
    (cert.rightTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaLower (16 - k) : Real) *
          (cert.shapeSqDerivLower k : Real) ∧
      (cert.rightTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaLower (16 - k) : Real) *
          (cert.shapeSqDerivUpper k : Real) ∧
      (cert.rightTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaUpper (16 - k) : Real) *
          (cert.shapeSqDerivLower k : Real) ∧
      (cert.rightTermLower k : Real) <=
        (Nat.choose 16 k : Real) *
          (cert.omegaUpper (16 - k) : Real) *
          (cert.shapeSqDerivUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaLower (16 - k) : Real) *
          (cert.shapeSqDerivLower k : Real) <=
        (cert.rightTermUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaLower (16 - k) : Real) *
          (cert.shapeSqDerivUpper k : Real) <=
        (cert.rightTermUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaUpper (16 - k) : Real) *
          (cert.shapeSqDerivLower k : Real) <=
        (cert.rightTermUpper k : Real) ∧
      (Nat.choose 16 k : Real) *
          (cert.omegaUpper (16 - k) : Real) *
          (cert.shapeSqDerivUpper k : Real) <=
        (cert.rightTermUpper k : Real)

/-- The existing whole-source segment row obtained from a signed-factor
segment. -/
def toSourceSegment
    (cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Step33Sub0CombinedCancellationOrder16SourceSegmentCert where
  cellL := cert.cellL
  cellU := cert.cellU
  sourceLower := cert.sourceLower
  sourceUpper := cert.sourceUpper

/-- Proof-bearing predicate for one signed-factor segment. -/
structure Valid
    (cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  factorRows :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (16 + 1),
        (cert.omegaPrimeLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta <=
            (cert.omegaPrimeUpper k : Real) ∧
          (cert.omegaLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta <=
            (cert.omegaUpper k : Real) ∧
          (cert.shapeSqLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta <=
            (cert.shapeSqUpper k : Real) ∧
          (cert.shapeSqDerivLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta <=
            (cert.shapeSqDerivUpper k : Real)
  leftTermCorners :
    cert.leftTermCornerRows
  rightTermCorners :
    cert.rightTermCornerRows
  sourceAssembly :
    (cert.sourceLower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          ((∑ k ∈ Finset.range (16 + 1),
              (cert.leftTermLower k : Real)) +
            ∑ k ∈ Finset.range (16 + 1),
              (cert.rightTermLower k : Real)) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          ((∑ k ∈ Finset.range (16 + 1),
              (cert.leftTermUpper k : Real)) +
            ∑ k ∈ Finset.range (16 + 1),
              (cert.rightTermUpper k : Real)) <=
        (cert.sourceUpper : Real)
  zeroModelBudget :
    -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
        Real) <=
        (cert.sourceLower : Real) ∧
      (cert.sourceUpper : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real)

/--
Source-only validity for one signed-factor segment.

This is the same signed-factor checker surface as `Valid`, but without the
old zero-model budget row.  It is the adapter target for routes that only need
the assembled source interval and spend a separate residual budget downstream.
-/
structure SourceIntervalValid
    (cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  factorRows :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (16 + 1),
        (cert.omegaPrimeLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta <=
            (cert.omegaPrimeUpper k : Real) ∧
          (cert.omegaLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta <=
            (cert.omegaUpper k : Real) ∧
          (cert.shapeSqLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta <=
            (cert.shapeSqUpper k : Real) ∧
          (cert.shapeSqDerivLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta <=
            (cert.shapeSqDerivUpper k : Real)
  leftTermCorners :
    cert.leftTermCornerRows
  rightTermCorners :
    cert.rightTermCornerRows
  sourceAssembly :
    (cert.sourceLower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          ((∑ k ∈ Finset.range (16 + 1),
              (cert.leftTermLower k : Real)) +
            ∑ k ∈ Finset.range (16 + 1),
              (cert.rightTermLower k : Real)) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          ((∑ k ∈ Finset.range (16 + 1),
              (cert.leftTermUpper k : Real)) +
            ∑ k ∈ Finset.range (16 + 1),
              (cert.rightTermUpper k : Real)) <=
        (cert.sourceUpper : Real)

namespace SourceIntervalValid

/-- The signed factor rows and left-term corner arithmetic imply the left
Leibniz term rows, without spending the old zero-model budget. -/
theorem to_leftTermRows
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.SourceIntervalValid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (16 + 1),
        (cert.leftTermLower k : Real) <=
            primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta ∧
          primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta <=
            (cert.leftTermUpper k : Real) := by
  intro eta hEta k hk
  have hk_sub_mem : 16 - k ∈ Finset.range (16 + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le 16 k))
  have hOmegaPrime := h.factorRows eta hEta (16 - k) hk_sub_mem
  have hShapeSq := h.factorRows eta hEta k hk
  have hCorners := h.leftTermCorners k hk
  have hMul :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := (Nat.choose 16 k : Real))
      (a := (cert.omegaPrimeLower (16 - k) : Real))
      (b := (cert.omegaPrimeUpper (16 - k) : Real))
      (c := (cert.shapeSqLower k : Real))
      (d := (cert.shapeSqUpper k : Real))
      (x :=
        iteratedDeriv (16 - k)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta)
      (y :=
        iteratedDeriv k
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta)
      (lower := (cert.leftTermLower k : Real))
      (upper := (cert.leftTermUpper k : Real))
      hOmegaPrime.1
      hOmegaPrime.2.1
      hShapeSq.2.2.2.2.1
      hShapeSq.2.2.2.2.2.1
      hCorners.1
      hCorners.2.1
      hCorners.2.2.1
      hCorners.2.2.2.1
      hCorners.2.2.2.2.1
      hCorners.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.2
  simpa [
    primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm,
    mul_assoc] using hMul

/-- The signed factor rows and right-term corner arithmetic imply the right
Leibniz term rows, without spending the old zero-model budget. -/
theorem to_rightTermRows
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.SourceIntervalValid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (16 + 1),
        (cert.rightTermLower k : Real) <=
            primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta ∧
          primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta <=
            (cert.rightTermUpper k : Real) := by
  intro eta hEta k hk
  have hk_sub_mem : 16 - k ∈ Finset.range (16 + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le 16 k))
  have hOmega := h.factorRows eta hEta (16 - k) hk_sub_mem
  have hShapeSqDeriv := h.factorRows eta hEta k hk
  have hCorners := h.rightTermCorners k hk
  have hMul :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := (Nat.choose 16 k : Real))
      (a := (cert.omegaLower (16 - k) : Real))
      (b := (cert.omegaUpper (16 - k) : Real))
      (c := (cert.shapeSqDerivLower k : Real))
      (d := (cert.shapeSqDerivUpper k : Real))
      (x :=
        iteratedDeriv (16 - k)
          primaryFiniteRow0Parent0Split100Sub0OmegaActual eta)
      (y :=
        iteratedDeriv k
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta)
      (lower := (cert.rightTermLower k : Real))
      (upper := (cert.rightTermUpper k : Real))
      hOmega.2.2.1
      hOmega.2.2.2.1
      hShapeSqDeriv.2.2.2.2.2.2.1
      hShapeSqDeriv.2.2.2.2.2.2.2
      hCorners.1
      hCorners.2.1
      hCorners.2.2.1
      hCorners.2.2.2.1
      hCorners.2.2.2.2.1
      hCorners.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.2
  simpa [
    primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm,
    mul_assoc] using hMul

/-- Source-only signed-factor rows imply the assembled source interval. -/
theorem to_sourceInterval
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.SourceIntervalValid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.sourceLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          (cert.sourceUpper : Real) := by
  intro eta hEta
  have hLeft :=
    primaryFiniteRow0Parent0Split100Sub0_order16Signed_sum_interval
      (Finset.range (16 + 1))
      (x := fun k =>
        primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta)
      (lower := fun k => (cert.leftTermLower k : Real))
      (upper := fun k => (cert.leftTermUpper k : Real))
      (fun k hk => h.to_leftTermRows eta hEta k hk)
  have hRight :=
    primaryFiniteRow0Parent0Split100Sub0_order16Signed_sum_interval
      (Finset.range (16 + 1))
      (x := fun k =>
        primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta)
      (lower := fun k => (cert.rightTermLower k : Real))
      (upper := fun k => (cert.rightTermUpper k : Real))
      (fun k hk => h.to_rightTermRows eta hEta k hk)
  have hTermLower :
      (∑ k ∈ Finset.range (16 + 1),
          (cert.leftTermLower k : Real)) +
        (∑ k ∈ Finset.range (16 + 1),
          (cert.rightTermLower k : Real)) <=
      (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
        (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) := by
    exact add_le_add hLeft.1 hRight.1
  have hTermUpper :
      (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
        (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) <=
      (∑ k ∈ Finset.range (16 + 1),
          (cert.leftTermUpper k : Real)) +
        (∑ k ∈ Finset.range (16 + 1),
          (cert.rightTermUpper k : Real)) := by
    exact add_le_add hLeft.2 hRight.2
  have hActiveScaleNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff := by
    unfold primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
    positivity
  have hScaledLower :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            (cert.leftTermLower k : Real)) +
          ∑ k ∈ Finset.range (16 + 1),
            (cert.rightTermLower k : Real)) <=
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
          ∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) :=
    mul_le_mul_of_nonneg_left hTermLower hActiveScaleNonneg
  have hScaledUpper :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
          ∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) <=
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            (cert.leftTermUpper k : Real)) +
          ∑ k ∈ Finset.range (16 + 1),
            (cert.rightTermUpper k : Real)) :=
    mul_le_mul_of_nonneg_left hTermUpper hActiveScaleNonneg
  have hSourceTerm :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          ((∑ k ∈ Finset.range (16 + 1),
              primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
            ∑ k ∈ Finset.range (16 + 1),
              primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) := by
    rw [
      primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual,
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_signedLeibniz]
  constructor
  · calc
      (cert.sourceLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                (cert.leftTermLower k : Real)) +
              ∑ k ∈ Finset.range (16 + 1),
                (cert.rightTermLower k : Real)) := h.sourceAssembly.1
      _ <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
              ∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) :=
          hScaledLower
      _ =
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta := by rw [hSourceTerm]
  · calc
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
              ∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) :=
          hSourceTerm
      _ <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                (cert.leftTermUpper k : Real)) +
              ∑ k ∈ Finset.range (16 + 1),
                (cert.rightTermUpper k : Real)) :=
          hScaledUpper
      _ <= (cert.sourceUpper : Real) := h.sourceAssembly.2

end SourceIntervalValid

namespace Valid

theorem to_sourceIntervalValid
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.Valid) :
    cert.SourceIntervalValid where
  cellSubset := h.cellSubset
  factorRows := h.factorRows
  leftTermCorners := h.leftTermCorners
  rightTermCorners := h.rightTermCorners
  sourceAssembly := h.sourceAssembly

/-- The signed factor rows and left-term corner arithmetic imply the left
Leibniz term rows. -/
theorem to_leftTermRows
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (16 + 1),
        (cert.leftTermLower k : Real) <=
            primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta ∧
          primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta <=
            (cert.leftTermUpper k : Real) := by
  intro eta hEta k hk
  have hk_sub_mem : 16 - k ∈ Finset.range (16 + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le 16 k))
  have hOmegaPrime := h.factorRows eta hEta (16 - k) hk_sub_mem
  have hShapeSq := h.factorRows eta hEta k hk
  have hCorners := h.leftTermCorners k hk
  have hMul :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := (Nat.choose 16 k : Real))
      (a := (cert.omegaPrimeLower (16 - k) : Real))
      (b := (cert.omegaPrimeUpper (16 - k) : Real))
      (c := (cert.shapeSqLower k : Real))
      (d := (cert.shapeSqUpper k : Real))
      (x :=
        iteratedDeriv (16 - k)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta)
      (y :=
        iteratedDeriv k
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta)
      (lower := (cert.leftTermLower k : Real))
      (upper := (cert.leftTermUpper k : Real))
      hOmegaPrime.1
      hOmegaPrime.2.1
      hShapeSq.2.2.2.2.1
      hShapeSq.2.2.2.2.2.1
      hCorners.1
      hCorners.2.1
      hCorners.2.2.1
      hCorners.2.2.2.1
      hCorners.2.2.2.2.1
      hCorners.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.2
  simpa [
    primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm,
    mul_assoc] using hMul

/-- The signed factor rows and right-term corner arithmetic imply the right
Leibniz term rows. -/
theorem to_rightTermRows
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (16 + 1),
        (cert.rightTermLower k : Real) <=
            primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta ∧
          primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta <=
            (cert.rightTermUpper k : Real) := by
  intro eta hEta k hk
  have hk_sub_mem : 16 - k ∈ Finset.range (16 + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le 16 k))
  have hOmega := h.factorRows eta hEta (16 - k) hk_sub_mem
  have hShapeSqDeriv := h.factorRows eta hEta k hk
  have hCorners := h.rightTermCorners k hk
  have hMul :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := (Nat.choose 16 k : Real))
      (a := (cert.omegaLower (16 - k) : Real))
      (b := (cert.omegaUpper (16 - k) : Real))
      (c := (cert.shapeSqDerivLower k : Real))
      (d := (cert.shapeSqDerivUpper k : Real))
      (x :=
        iteratedDeriv (16 - k)
          primaryFiniteRow0Parent0Split100Sub0OmegaActual eta)
      (y :=
        iteratedDeriv k
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta)
      (lower := (cert.rightTermLower k : Real))
      (upper := (cert.rightTermUpper k : Real))
      hOmega.2.2.1
      hOmega.2.2.2.1
      hShapeSqDeriv.2.2.2.2.2.2.1
      hShapeSqDeriv.2.2.2.2.2.2.2
      hCorners.1
      hCorners.2.1
      hCorners.2.2.1
      hCorners.2.2.2.1
      hCorners.2.2.2.2.1
      hCorners.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.2
  simpa [
    primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm,
    mul_assoc] using hMul

/-- A valid signed-factor segment gives the signed interval for the assembled
order-16 component source on that segment. -/
theorem to_sourceInterval
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.sourceLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          (cert.sourceUpper : Real) := by
  intro eta hEta
  have hLeft :=
    primaryFiniteRow0Parent0Split100Sub0_order16Signed_sum_interval
      (Finset.range (16 + 1))
      (x := fun k =>
        primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta)
      (lower := fun k => (cert.leftTermLower k : Real))
      (upper := fun k => (cert.leftTermUpper k : Real))
      (fun k hk => h.to_leftTermRows eta hEta k hk)
  have hRight :=
    primaryFiniteRow0Parent0Split100Sub0_order16Signed_sum_interval
      (Finset.range (16 + 1))
      (x := fun k =>
        primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta)
      (lower := fun k => (cert.rightTermLower k : Real))
      (upper := fun k => (cert.rightTermUpper k : Real))
      (fun k hk => h.to_rightTermRows eta hEta k hk)
  have hTermLower :
      (∑ k ∈ Finset.range (16 + 1),
          (cert.leftTermLower k : Real)) +
        (∑ k ∈ Finset.range (16 + 1),
          (cert.rightTermLower k : Real)) <=
      (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
        (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) := by
    exact add_le_add hLeft.1 hRight.1
  have hTermUpper :
      (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
        (∑ k ∈ Finset.range (16 + 1),
          primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) <=
      (∑ k ∈ Finset.range (16 + 1),
          (cert.leftTermUpper k : Real)) +
        (∑ k ∈ Finset.range (16 + 1),
          (cert.rightTermUpper k : Real)) := by
    exact add_le_add hLeft.2 hRight.2
  have hActiveScaleNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff := by
    unfold primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
    positivity
  have hScaledLower :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            (cert.leftTermLower k : Real)) +
          ∑ k ∈ Finset.range (16 + 1),
            (cert.rightTermLower k : Real)) <=
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
          ∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) :=
    mul_le_mul_of_nonneg_left hTermLower hActiveScaleNonneg
  have hScaledUpper :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
          ∑ k ∈ Finset.range (16 + 1),
            primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) <=
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        ((∑ k ∈ Finset.range (16 + 1),
            (cert.leftTermUpper k : Real)) +
          ∑ k ∈ Finset.range (16 + 1),
            (cert.rightTermUpper k : Real)) :=
    mul_le_mul_of_nonneg_left hTermUpper hActiveScaleNonneg
  have hSourceTerm :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          ((∑ k ∈ Finset.range (16 + 1),
              primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
            ∑ k ∈ Finset.range (16 + 1),
              primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) := by
    rw [
      primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual,
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_signedLeibniz]
  constructor
  · calc
      (cert.sourceLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                (cert.leftTermLower k : Real)) +
              ∑ k ∈ Finset.range (16 + 1),
                (cert.rightTermLower k : Real)) := h.sourceAssembly.1
      _ <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
              ∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) :=
          hScaledLower
      _ =
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta := by rw [hSourceTerm]
  · calc
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm k eta) +
              ∑ k ∈ Finset.range (16 + 1),
                primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm k eta) :=
          hSourceTerm
      _ <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            ((∑ k ∈ Finset.range (16 + 1),
                (cert.leftTermUpper k : Real)) +
              ∑ k ∈ Finset.range (16 + 1),
                (cert.rightTermUpper k : Real)) :=
          hScaledUpper
      _ <= (cert.sourceUpper : Real) := h.sourceAssembly.2

/-- A valid signed-factor segment instantiates the existing source segment
certificate interface. -/
theorem to_sourceSegmentValid
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (h : cert.Valid) :
    cert.toSourceSegment.Valid := by
  refine
    { cellSubset := ?_
      sourceInterval := ?_
      zeroModelBudget := ?_ }
  · intro eta hEta
    exact h.cellSubset eta hEta
  · intro eta hEta
    exact h.to_sourceInterval eta hEta
  · exact h.zeroModelBudget

end Valid
end Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert

/-- A signed-factor segment family covers the active cell when the corresponding
source-segment family covers it. -/
def Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCover
    (n : Nat)
    (seg :
      Fin n ->
        Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Prop :=
  Step33Sub0CombinedCancellationOrder16SourceSegmentCover n
    (fun i => (seg i).toSourceSegment)

/--
A proof-grade signed-factor segment certificate family feeds the existing
zero-model `hRemainder` bridge.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_signedFactor_segment_cover
    {n : Nat}
    {seg :
      Fin n ->
        Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (hValid : ∀ i : Fin n, (seg i).Valid)
    (hCover :
      Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCover n seg) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_segment_cover
      (n := n)
      (seg := fun i => (seg i).toSourceSegment)
      (fun i => (hValid i).to_sourceSegmentValid)
      hCover

/--
A proof-grade signed-factor segment certificate family also gives the full
zero-model direct interval data validity.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_signedFactor_segment_cover
    {n : Nat}
    {seg :
      Fin n ->
        Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (hValid : ∀ i : Fin n, (seg i).Valid)
    (hCover :
      Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCover n seg) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelIntervalData.Valid := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_remainder
      (primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_signedFactor_segment_cover
        hValid hCover)

end Step33
end PSDpd
end Q3
