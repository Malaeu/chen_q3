import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows01234567891011Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
First proof-grade bridge for the Step33A.1-A sub0 active-actual center rows.

This file deliberately does not emit the generated active-actual product rows.
It closes only the local crosswalk from an existing `singleAbs` proof object to
signed two-sided center-jet intervals for the `ShapeSqDerivActual` factor.  The
next generator must still assemble factor intervals through the Cauchy product
and active-scale/model subtraction before instantiating the source interval
certificate.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Elementary signed interval extraction from an absolute-error row. -/
theorem primaryFiniteRow0Parent0Split100Sub0_centerJet_interval_of_abs
    {x c e : Real} (h : ‖x - c‖ <= e) :
    c - e <= x ∧ x <= c + e := by
  rw [Real.norm_eq_abs] at h
  have hBounds := abs_le.mp h
  constructor <;> linarith

/--
Any proof-bearing `singleAbs` ShapeSqDeriv certificate provides signed
two-sided center-jet rows in the active combined-cancellation normalization.

This is the precise bridge needed before a generated active-actual product-row
payload can use coarse-but-proof-grade `singleAbs` rows as interval inputs.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_singleAbs_signed_centerJet_interval
    {coeff coeffErrorAbs : Fin 16 -> Rat}
    {order16Abs : Rat}
    (h :
      (ShapeSqDerivTaylorIntervalCert.singleAbs coeff coeffErrorAbs
        order16Abs).Valid)
    (j : Fin 16) :
    (coeff j : Real) - (coeffErrorAbs j : Real) <=
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual j.1 ∧
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual j.1 <=
        (coeff j : Real) + (coeffErrorAbs j : Real) := by
  have hrow := h.centerJetRows j
  simpa [
    ShapeSqDerivTaylorIntervalCert.singleAbs,
    ShapeSqDerivTaylorIntervalCert.single,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
  ] using hrow

/--
Concrete signed rows supplied by the current rows `0..11` partial-sharp
ShapeSqDeriv payload, stated in the active factor normalization.

Rows `12..15` are intentionally allowed to be coarse by the imported
`singleAbs` object.  This theorem is not a claim that the eventual active
product-row budget passes.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567891011_signed_centerJet_interval
    (j : Fin 16) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff j :
        Real) -
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
          j : Real) <=
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual j.1 ∧
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual j.1 <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff j :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
            j : Real) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_singleAbs_signed_centerJet_interval
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011_valid
      j

/-- Proof-grade signed center-jet rows for the OmegaPrime actual factor. -/
theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_signed_centerJet_interval
    (j : Fin 16) :
    (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff j : Real) -
        (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCoeffErrorAbs
          j : Real) <=
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual j.1 ∧
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual j.1 <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff j : Real) +
          (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCoeffErrorAbs
            j : Real) := by
  have hAbs :
      ‖primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual j.1 -
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff j : Real)‖ <=
        (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCoeffErrorAbs
          j : Real) := by
    simpa [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff,
      step33Sub0OmegaPrimeTaylorCenter]
      using
        Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCenterJet j
  exact primaryFiniteRow0Parent0Split100Sub0_centerJet_interval_of_abs hAbs

/-- Rowwise error budget for the integrated Omega actual center jets. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetErrorAbs
    (j : Fin 17) : Rat :=
  match j.1 with
  | 0 => primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs
  | k + 1 =>
      if hk : k < 16 then
        Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCoeffErrorAbs
            ⟨k, hk⟩ /
          ((k + 1 : Nat) : Rat)
      else
        0

/-- The Omega actual factor has OmegaPrime as derivative, row-by-row. -/
theorem primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv_succ_eq_omegaPrime
    (j : Nat) (eta : Real) :
    iteratedDeriv (j + 1) primaryFiniteRow0Parent0Split100Sub0OmegaActual
        eta =
      iteratedDeriv j primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
        eta := by
  induction j generalizing eta with
  | zero =>
      rw [iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]
      change
        deriv
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            eta =
          step22OmegaArchWeightDerivClosedForm eta
      exact step22OmegaArchWeight_deriv_eq_closedForm eta
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv (j + 1)
              primaryFiniteRow0Parent0Split100Sub0OmegaActual =
            iteratedDeriv j
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
        funext x
        exact ih x
      rw [hfun]
      rw [← iteratedDeriv_succ]

/-- Proof-grade absolute center-jet rows for the integrated Omega actual factor. -/
theorem primaryFiniteRow0Parent0Split100Sub0_omegaActual_centerJet_abs
    (j : Fin 17) :
    ‖primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaActual j.1 -
      (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff j : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetErrorAbs j :
        Real) := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
      have hAnchor :=
        primaryFiniteRow0Parent0Split100Sub0_omegaTaylor_center_anchor
      simpa [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
        primaryFiniteRow0Parent0Split100Sub0OmegaActual,
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetErrorAbs,
        Step33Sub0OmegaPrimeTaylorRemainderCert.integratedCoeff_zero,
        step33Sub0OmegaPrimeTaylorCenter,
        primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff,
        primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorAnchorCoeff,
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorAnchorErrorAbs]
        using hAnchor
  | succ k =>
      have hk : k < 16 := by omega
      let kFin : Fin 16 := ⟨k, hk⟩
      have hPrime :
          ‖primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual k -
            (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
              kFin : Real)‖ <=
            (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCoeffErrorAbs
              kFin : Real) := by
        simpa [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual,
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff,
          step33Sub0OmegaPrimeTaylorCenter, kFin]
          using
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCenterJet
              kFin
      have hCoeff :
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
              ⟨k + 1, Nat.succ_lt_succ hk⟩ =
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCoeff
                kFin /
              ((k + 1 : Nat) : Rat) := by
        simpa [primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff,
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff,
          Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert,
          kFin]
          using
            Step33Sub0OmegaPrimeTaylorRemainderCert.integratedCoeff_succ
              Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert
              primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff
              kFin
      have hEq :
          primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0OmegaActual (k + 1) -
            (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
              ⟨k + 1, Nat.succ_lt_succ hk⟩ : Real) =
          (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual k -
            (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
              kFin : Real)) /
            ((k + 1 : Nat) : Real) := by
        unfold primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        rw [
          primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv_succ_eq_omegaPrime,
          hCoeff]
        field_simp [Nat.cast_ne_zero]
        rw [Nat.factorial_succ]
        simp [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff,
          kFin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp [show (1 + (k : Real)) ≠ 0 by positivity]
      have hDenPos : 0 < ((k + 1 : Nat) : Real) := by positivity
      have hDenPosReal : 0 < ((k : Real) + 1) := by positivity
      have hScaled :=
        div_le_div_of_nonneg_right hPrime (le_of_lt hDenPos)
      simpa [hEq, norm_div, Real.norm_eq_abs,
        abs_of_pos hDenPosReal,
        primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetErrorAbs,
        kFin, hk, Nat.cast_add, Nat.cast_one] using hScaled

/-- Proof-grade signed center-jet rows for the integrated Omega actual factor. -/
theorem primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval
    (j : Fin 17) :
    (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff j : Real) -
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetErrorAbs
          j : Real) <=
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0OmegaActual j.1 ∧
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0OmegaActual j.1 <=
        (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff j : Real) +
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetErrorAbs
            j : Real) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_centerJet_interval_of_abs
      (primaryFiniteRow0Parent0Split100Sub0_omegaActual_centerJet_abs j)

/-- Rowwise error budget for the integrated ShapeSq actual center jets. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetErrorAbs
    (j : Fin 17) : Rat :=
  match j.1 with
  | 0 => primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated
  | k + 1 =>
      if hk : k < 16 then
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
            ⟨k, hk⟩ /
          ((k + 1 : Nat) : Rat)
      else
        0

/-- Proof-grade absolute center-jet rows for the integrated ShapeSq actual factor. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_centerJet_abs
    (j : Fin 17) :
    ‖primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual j.1 -
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff j : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetErrorAbs j :
        Real) := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
      have hLower :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hAnchorLower
      have hUpper :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hAnchorUpper
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · norm_num [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated,
          integratedTaylorCoeff_zero,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetErrorAbs,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated] at hLower hUpper ⊢
        linarith
      · norm_num [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated,
          integratedTaylorCoeff_zero,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetErrorAbs,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated] at hLower hUpper ⊢
        linarith
  | succ k =>
      have hk : k < 16 := by omega
      let kFin : Fin 16 := ⟨k, hk⟩
      have hDerivSigned :=
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567891011_signed_centerJet_interval
          kFin
      have hDerivAbs :
          ‖primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual k -
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
              kFin : Real)‖ <=
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
              kFin : Real) := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hDerivSigned.1, hDerivSigned.2]
      have hCoeff :
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff
              ⟨k + 1, Nat.succ_lt_succ hk⟩ =
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
                kFin /
              ((k + 1 : Nat) : Rat) := by
        simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
          kFin]
          using
            integratedTaylorCoeff_succ 15
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated
              primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated
              kFin
      have hEq :
          primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual (k + 1) -
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff
              ⟨k + 1, Nat.succ_lt_succ hk⟩ : Real) =
          (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual k -
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
              kFin : Real)) /
            ((k + 1 : Nat) : Real) := by
        unfold primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
        unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
        rw [← primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ,
          hCoeff]
        field_simp [Nat.cast_ne_zero]
        rw [Nat.factorial_succ]
        simp [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
          kFin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp [show (1 + (k : Real)) ≠ 0 by positivity]
      have hDenPos : 0 < ((k + 1 : Nat) : Real) := by positivity
      have hDenPosReal : 0 < ((k : Real) + 1) := by positivity
      have hScaled :=
        div_le_div_of_nonneg_right hDerivAbs (le_of_lt hDenPos)
      simpa [hEq, norm_div, Real.norm_eq_abs,
        abs_of_pos hDenPosReal,
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetErrorAbs,
        kFin, hk, Nat.cast_add, Nat.cast_one] using hScaled

/-- Proof-grade signed center-jet rows for the integrated ShapeSq actual factor. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval
    (j : Fin 17) :
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff j : Real) -
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetErrorAbs
          j : Real) <=
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual j.1 ∧
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual j.1 <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff j : Real) +
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetErrorAbs
            j : Real) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_centerJet_interval_of_abs
      (primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_centerJet_abs j)

/--
Finite-sum interval aggregation.  A generated payload can prove termwise
lower/upper rows, and this lemma folds them to the exact finite sum consumed by
the Cauchy center-jet convention.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_sum_interval_of_term_intervals
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    {x lower upper : ι -> Real}
    (hTerm : ∀ i ∈ s, lower i <= x i ∧ x i <= upper i) :
    (∑ i ∈ s, lower i) <= (∑ i ∈ s, x i) ∧
      (∑ i ∈ s, x i) <= (∑ i ∈ s, upper i) := by
  constructor
  · exact Finset.sum_le_sum (fun i hi => (hTerm i hi).1)
  · exact Finset.sum_le_sum (fun i hi => (hTerm i hi).2)

/--
Termwise product intervals imply a Cauchy-convolution interval in the normalized
center-jet convention used by the combined-cancellation source model.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_normalizedJetConvolution_interval_of_term_intervals
    (n : Nat) {a b termLower termUpper : Nat -> Real}
    (hTerm :
      ∀ k ∈ Finset.range (n + 1),
        termLower k <= a k * b (n - k) ∧
          a k * b (n - k) <= termUpper k) :
    (∑ k ∈ Finset.range (n + 1), termLower k) <=
        primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n a b ∧
      primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n a b <=
        (∑ k ∈ Finset.range (n + 1), termUpper k) := by
  unfold primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution
  exact
    primaryFiniteRow0Parent0Split100Sub0_sum_interval_of_term_intervals
      (Finset.range (n + 1)) hTerm

/--
Intervals for the two Cauchy products give an interval for the active actual
component-product Cauchy row.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActualCauchy_interval
    (n : Nat) {omegaPrimeShapeLower omegaPrimeShapeUpper
      omegaShapeDerivLower omegaShapeDerivUpper : Real}
    (hOmegaPrimeShape :
      omegaPrimeShapeLower <=
          primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual)
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual) ∧
        primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual)
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual) <=
          omegaPrimeShapeUpper)
    (hOmegaShapeDeriv :
      omegaShapeDerivLower <=
          primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0OmegaActual)
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual) ∧
        primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0OmegaActual)
            (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual) <=
          omegaShapeDerivUpper) :
    omegaPrimeShapeLower + omegaShapeDerivLower <=
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
          n ∧
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
          n <=
        omegaPrimeShapeUpper + omegaShapeDerivUpper := by
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
  constructor <;> linarith

theorem primaryFiniteRow0Parent0Split100Sub0_activeScale_nonneg :
    0 <= primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff := by
  unfold primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
  positivity

/--
Final row-level receiver for generated active-actual product rows.

Once the generator proves an interval for the actual Cauchy product row, this
lemma transports it through the positive active scale and subtracts the fixed
`ResidualDerivmodelCoeff` row.  The result is exactly the row premise consumed
by
`primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceIntervalValid_of_activeActual_interval`.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_of_product_interval
    (j : Fin 16) {productLower productUpper rowLower rowUpper : Real}
    (hProduct :
      productLower <=
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 ∧
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 <=
          productUpper)
    (hLower :
      rowLower <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * productLower -
          (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
            Real))
    (hUpper :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * productUpper -
          (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
            Real) <=
        rowUpper) :
    rowLower <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 -
          (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
            Real) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 -
          (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
            Real) <=
        rowUpper := by
  have hScaleNonneg :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_nonneg
  have hScaledLower :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * productLower <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 :=
    mul_le_mul_of_nonneg_left hProduct.1 hScaleNonneg
  have hScaledUpper :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * productUpper :=
    mul_le_mul_of_nonneg_left hProduct.2 hScaleNonneg
  constructor <;> linarith

end Step33
end PSDpd
end Q3
