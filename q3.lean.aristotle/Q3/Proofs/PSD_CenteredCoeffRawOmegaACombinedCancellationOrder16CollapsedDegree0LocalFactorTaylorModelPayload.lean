import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0LocalFactorTaylorModelBridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Concrete segment0 payload attempt for the local-factor Taylor-model bridge.

This file deliberately proves only the local bridge payload
`Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.Valid`.  It does not
claim the direct signed-source budget or Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open scoped BigOperators
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index :
    Fin 2 :=
  ⟨0, by decide⟩

private theorem
    step22OmegaArchWeight_contDiff18_localFactorTaylorPayload :
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
    primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_localFactorTaylorPayload :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
  simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
    step22OmegaArchWeight_contDiff18_localFactorTaylorPayload

private theorem
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_localFactorTaylorPayload :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  fun_prop

def primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0 :
    Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert where
  omegaCoeff := fun _ => 0
  omegaCoeffErrorAbs :=
    primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  omegaOrder18Abs :=
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat 18
  shapeSqCoeff := fun _ => 0
  shapeSqCoeffErrorAbs :=
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  shapeSqOrder18Abs :=
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
      18
  omegaLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaLower
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  omegaUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaUpper
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  shapeSqLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqLower
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  shapeSqUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqUpper
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  termLower :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermLower
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  termUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermUpper
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  rawLower :=
    -(primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index)
  rawUpper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
  polyLower := -primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat
  polyUpper := primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat
  lower :=
    -(primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index)
  upper :=
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index

private theorem
    primaryFiniteRow0Parent0Split100Sub0_segment0_as_rawD17_left
    {eta : Real}
    (hEta :
      eta ∈ Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
          Real)) :
    eta ∈ Set.Icc
      (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index :
        Real)
      (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index :
        Real) := by
  simpa [
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
    primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
    primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] using hEta

private theorem
    primaryFiniteRow0Parent0Split100Sub0_segment0_radius_as_rawD17_left
    {eta : Real}
    (hEta :
      eta ∈ Set.Icc
        ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
            Real) -
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
            Real))
        ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
            Real) +
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
            Real))) :
    eta ∈ Set.Icc
      (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index :
        Real)
          (primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index :
        Real) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
    primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
    primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] at hEta ⊢
  exact hEta

private theorem primaryFiniteRow0Parent0Split100Sub0_fin18_no_ge_18_sum
    (f : Fin 18 -> Real) :
    (∑ i : Fin 18, if 18 <= i.1 then f i else 0) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i _hi
  simp [Nat.not_le_of_gt i.2]

private theorem primaryFiniteRow0Parent0Split100Sub0_fin18_no_ge_18_ratCast_sum
    (f : Fin 18 -> Rat) :
    (∑ i : Fin 18, ((if 18 <= i.1 then f i else 0 : Rat) : Real)) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro i _hi
  simp [Nat.not_le_of_gt i.2]

private theorem centeredTaylorDerivError18_eq_majorant18Rat
    (jetAbs : Fin 18 -> Rat) (order18Abs radius : Rat) (k : Fin 18) :
    centeredTaylorDerivError18
        (fun j : Fin 18 => (jetAbs j : Real))
        (order18Abs : Real) (radius : Real) k =
      (primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat
        jetAbs order18Abs radius ⟨k.1, Nat.lt_trans k.2 (by norm_num)⟩ :
        Real) := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast,
    ← centeredTaylorDerivMajorant18Range_eq
        (fun j : Fin 18 => (jetAbs j : Real))
        (order18Abs : Real) (radius : Real)
        ⟨k.1, Nat.lt_trans k.2 (by norm_num)⟩]
  unfold centeredTaylorDerivError18 centeredTaylorDerivMajorant18Range
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _hm
  by_cases h : k.1 + m < 18
  · simp [h, mul_assoc]
  · simp [h]

private theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaSharpLocalTaylorError_eq_abs
    (k : Fin 18) :
    centeredTaylorDerivError18
        (fun j : Fin 18 =>
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
            j : Real))
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
          18 : Real)
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real)
        k =
      (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
        k.1 : Real) := by
  have hk19 : k.1 < 19 := Nat.lt_trans k.2 (by norm_num)
  rw [centeredTaylorDerivError18_eq_majorant18Rat]
  simp [
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs,
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius,
    primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
    hk19]

private theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSharpLocalTaylorError_eq_abs
    (k : Fin 18) :
    centeredTaylorDerivError18
        (fun j : Fin 18 =>
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
            j : Real))
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
          18 : Real)
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real)
        k =
      (primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
        k.1 : Real) := by
  have hk19 : k.1 < 19 := Nat.lt_trans k.2 (by norm_num)
  rw [centeredTaylorDerivError18_eq_majorant18Rat]
  simp [
    primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius,
    primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
    hk19]

private theorem primaryFiniteRow0Parent0Split100Sub0_zero_omegaPoly_segment0
    (k : Fin 18) (eta : Real) :
    (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.omegaPoly
        k eta) = 0 := by
  unfold Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaPoly
  unfold centeredTaylorDerivPolynomial18
  simp [
    primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
    Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaCoeffReal]

private theorem primaryFiniteRow0Parent0Split100Sub0_zero_shapeSqPoly_segment0
    (k : Fin 18) (eta : Real) :
    (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.shapeSqPoly
        k eta) = 0 := by
  unfold Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqPoly
  unfold centeredTaylorDerivPolynomial18
  simp [
    primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
    Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqCoeffReal]

private theorem
    primaryFiniteRow0Parent0Split100Sub0_localFactorTaylor18Segment0_valid :
    primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.Valid := by
  classical
  refine
    { omegaSmooth :=
        primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_localFactorTaylorPayload
      shapeSqSmooth :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_localFactorTaylorPayload
      omegaCoeffErrorNonneg := ?_
      shapeSqCoeffErrorNonneg := ?_
      omegaCenterJet := ?_
      shapeSqCenterJet := ?_
      omegaOrder18 := ?_
      shapeSqOrder18 := ?_
      omegaPolyRows := ?_
      shapeSqPolyRows := ?_
      omegaOrder18Rows := ?_
      shapeSqOrder18Rows := ?_
      termCorners := ?_
      rawAssembly := ?_
      polyInterval := ?_
      lowerFromRawPoly := ?_
      upperFromRawPoly := ?_ }
  · intro j
    have hRat :
        0 <=
          primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
            j := by
      fin_cases j <;>
        native_decide
    exact_mod_cast hRat
  · intro j
    have hRat :
        0 <=
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
            j := by
      fin_cases j <;>
        native_decide
    exact_mod_cast hRat
  · intro j
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_sharp_interval_generated
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index j
    rw [Real.norm_eq_abs]
    have h' :
        -((primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
            j : Rat) : Real) <=
            iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
              (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
                Real) /
              (Nat.factorial j.1 : Real) ∧
          iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
              (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
                Real) /
              (Nat.factorial j.1 : Real) <=
            (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
              primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
              j : Real) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center,
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
        primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetLower,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetUpper,
        Rat.cast_neg] using h
    simpa [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetLower,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetUpper,
      Rat.cast_neg,
      sub_zero] using abs_le.mpr h'
  · intro j
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_sharp_interval_generated
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index j
    rw [Real.norm_eq_abs]
    have h' :
        -((primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
            j : Rat) : Real) <=
            iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
                Real) /
              (Nat.factorial j.1 : Real) ∧
          iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
                Real) /
              (Nat.factorial j.1 : Real) <=
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
              primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
              j : Real) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center,
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
        primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetLower,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetUpper,
        Rat.cast_neg] using h
    simpa [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetLower,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetUpper,
      Rat.cast_neg,
      sub_zero] using abs_le.mpr h'
  · intro eta hEta
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_sharp_interval
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
        ⟨18, by decide⟩ eta
        (primaryFiniteRow0Parent0Split100Sub0_segment0_radius_as_rawD17_left
          hEta)
    rw [Real.norm_eq_abs]
    have h' :
        -(primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
            18 : Real) <=
            iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual
              eta ∧
          iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual eta <=
            (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
              18 : Real) := by
      have hsum :
          (∑ i : Fin 18,
              (if 18 <= i.1 then
                (Nat.factorial i.1 : Rat) *
                  primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                    i
              else
                0 : Rat) : Real) = 0 := by
        simpa using
          primaryFiniteRow0Parent0Split100Sub0_fin18_no_ge_18_ratCast_sum
            (fun i : Fin 18 =>
              (Nat.factorial i.1 : Rat) *
                primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                  primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                  i)
      have htmp :
          -(primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
              18 : Real) <=
              iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual
                eta +
                ∑ i : Fin 18,
                  ((if 18 <= i.1 then
                    (Nat.factorial i.1 : Rat) *
                      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                        i
                  else
                    0 : Rat) : Real) ∧
            iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual
                eta <=
              (∑ i : Fin 18,
                  ((if 18 <= i.1 then
                    (Nat.factorial i.1 : Rat) *
                      primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                        i
                  else
                    0 : Rat) : Real)) +
                (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
                  18 : Real) := by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
          primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower,
          primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper,
          primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs,
          primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat,
          primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
          Rat.cast_neg] using h
      constructor <;> linarith
    simpa [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs,
      primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
      Rat.cast_neg] using abs_le.mpr h'
  · intro eta hEta
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_sharp_interval
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
        ⟨18, by decide⟩ eta
        (primaryFiniteRow0Parent0Split100Sub0_segment0_radius_as_rawD17_left
          hEta)
    rw [Real.norm_eq_abs]
    have h' :
        -(primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
            18 : Real) <=
            iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              eta ∧
          iteratedDeriv 18
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta <=
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
              18 : Real) := by
      have hsum :
          (∑ i : Fin 18,
              (if 18 <= i.1 then
                (Nat.factorial i.1 : Rat) *
                  primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                    i
              else
                0 : Rat) : Real) = 0 := by
        simpa using
          primaryFiniteRow0Parent0Split100Sub0_fin18_no_ge_18_ratCast_sum
            (fun i : Fin 18 =>
              (Nat.factorial i.1 : Rat) *
                primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                  primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                  i)
      have htmp :
          -(primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
              18 : Real) <=
              iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
                eta +
                ∑ i : Fin 18,
                  ((if 18 <= i.1 then
                    (Nat.factorial i.1 : Rat) *
                      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                        i
                  else
                    0 : Rat) : Real) ∧
            iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
                eta <=
              (∑ i : Fin 18,
                  ((if 18 <= i.1 then
                    (Nat.factorial i.1 : Rat) *
                      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                        i
                  else
                    0 : Rat) : Real)) +
                (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
                  18 : Real) := by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs,
          primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat,
          primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
          Rat.cast_neg] using h
      constructor <;> linarith
    simpa [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs,
      primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
      Rat.cast_neg] using abs_le.mpr h'
  · intro eta _hEta k
    have hPoly :=
      primaryFiniteRow0Parent0Split100Sub0_zero_omegaPoly_segment0 k eta
    rw [hPoly]
    change
      (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.omegaLower
          k.1 : Real) <=
          0 - centeredTaylorDerivError18
            (fun j : Fin 18 =>
              (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                j : Real))
            (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
              18 : Real)
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
              Real)
            k ∧
        0 + centeredTaylorDerivError18
            (fun j : Fin 18 =>
              (primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                j : Real))
            (primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat
              18 : Real)
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
              Real)
            k <=
          (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.omegaUpper
            k.1 : Real)
    rw [primaryFiniteRow0Parent0Split100Sub0_omegaSharpLocalTaylorError_eq_abs]
    fin_cases k <;>
      simp [
        primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
        primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaLower,
        primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaUpper,
        primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaAbs,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs,
        primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
        sub_eq_add_neg]
  · intro eta _hEta k
    have hPoly :=
      primaryFiniteRow0Parent0Split100Sub0_zero_shapeSqPoly_segment0 k eta
    rw [hPoly]
    change
      (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.shapeSqLower
          k.1 : Real) <=
          0 - centeredTaylorDerivError18
            (fun j : Fin 18 =>
              (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                j : Real))
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
              18 : Real)
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
              Real)
            k ∧
        0 + centeredTaylorDerivError18
            (fun j : Fin 18 =>
              (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                j : Real))
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat
              18 : Real)
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
              Real)
            k <=
          (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.shapeSqUpper
            k.1 : Real)
    rw [primaryFiniteRow0Parent0Split100Sub0_shapeSharpLocalTaylorError_eq_abs]
    fin_cases k <;>
      simp [
        primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
        primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqLower,
        primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqUpper,
        primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqAbs,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs,
        primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius,
        sub_eq_add_neg]
  · have hsum :
        (∑ i : Fin 18,
            (if 18 <= i.1 then
              (Nat.factorial i.1 : Rat) *
                primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                  primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                  i
            else
              0 : Rat) : Real) = 0 := by
      simpa using
        primaryFiniteRow0Parent0Split100Sub0_fin18_no_ge_18_ratCast_sum
          (fun i : Fin 18 =>
            (Nat.factorial i.1 : Rat) *
              primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                i)
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpOmegaUpper,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpLower,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpUpper,
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeTwoSegmentSharpAbs,
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast,
      centeredTaylorDerivMajorant18_last,
      primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius]
    have hsum0 :
        (∑ i : Fin 18,
            (if 18 <= i.1 then
              (Nat.factorial i.1 : Rat) *
                primaryFiniteRow0Parent0Split100Sub0OmegaActualSharpLocalJetAbs
                  0 i
            else
              0 : Rat) : Real) = 0 := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index]
        using hsum
    rw [hsum0]
  · have hsum :
        (∑ i : Fin 18,
            (if 18 <= i.1 then
              (Nat.factorial i.1 : Rat) *
                primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                  primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                  i
            else
              0 : Rat) : Real) = 0 := by
      simpa using
        primaryFiniteRow0Parent0Split100Sub0_fin18_no_ge_18_ratCast_sum
          (fun i : Fin 18 =>
            (Nat.factorial i.1 : Rat) *
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index
                i)
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqLower,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpShapeSqUpper,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpLower,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpUpper,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeTwoSegmentSharpAbs,
      primaryFiniteRow0Parent0Split100Sub0_centeredTaylorDerivMajorant18Rat_cast,
      centeredTaylorDerivMajorant18_last,
      primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant18Rat,
      primaryFiniteRow0Parent0Split100Sub0RawD17LocalRadius]
    have hsum0 :
        (∑ i : Fin 18,
            (if 18 <= i.1 then
              (Nat.factorial i.1 : Rat) *
                primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpLocalJetAbs
                  0 i
            else
              0 : Rat) : Real) = 0 := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index]
        using hsum
    rw [hsum0]
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.toRawD17SignedFactorSegmentCert,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] using
      (primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_left_valid).termCorners
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.toRawD17SignedFactorSegmentCert,
      primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL,
      primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] using
      (primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_left_valid).rawAssembly
  · intro eta hEta
    have hFull :
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      constructor
      · simpa [
          primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL]
          using hEta.1
      · have h20 : eta <= (1 : Real) / 20 := by
          simpa [
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU]
            using hEta.2
        norm_num
        linarith
    have hFullSegment :
        eta ∈ Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellL
            ⟨0, by decide⟩ : Real)
          (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellU
            ⟨0, by decide⟩ : Real) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellL,
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellU]
        using hFull
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_interval_generated
        ⟨0, by decide⟩ eta hFullSegment
    simpa [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentLower,
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentUpper] using h
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum]
    ring_nf
    exact le_rfl
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Index,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawPolyAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpRawAbs,
      primaryFiniteRow0Parent0Split100Sub0RawD17TwoSegmentSharpSignedFactorTermAbsSum]

theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_localFactorTaylor18_segment0_valid :
    primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_localFactorTaylor18Segment0_valid

theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_of_localFactorTaylor18_payload :
    primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.toSignedSegmentCert.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_remainder_of_localFactorTaylor18
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_localFactorTaylor18_segment0_valid

end Step33
end PSDpd
end Q3
