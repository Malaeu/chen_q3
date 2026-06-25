import Q3.Proofs.PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Factor-derivative majorant bridge for the Step33A.1-A sub0 combined source.

This file is intentionally an adapter layer.  It does not emit the final
order-16 source interval payload.  It proves that two proof-bearing Taylor
certificates already present in the repository supply uniform derivative arrays
through the public centered Taylor majorant interface:

* `OmegaPrimeActual`
* `OmegaActual`
* `ShapeSqActual`
* `ShapeSqDerivActual`

The integrated factors use the checked derivative-shift identities: their
order-16 Taylor input is supplied by the derivative majorant for the
corresponding derivative factor at order 15.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_center_mem :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter ∈
      Set.Icc (0 : Real) ((1 : Real) / 10) := by
  norm_num [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter]

private theorem primaryFiniteRow0Parent0Split100Sub0_cell_radius
    {eta : Real}
    (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖eta - primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter‖ <=
      (1 : Real) / 20 := by
  rw [Real.norm_eq_abs, abs_le]
  rw [Set.mem_Icc] at heta
  constructor <;>
    norm_num [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter]
      at heta ⊢ <;>
    linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_reflect_cell
    {y : Real}
    (hy : y ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (_hyle : y <= primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter) :
    ∀ x ∈
        Set.Icc primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
          (2 * primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter - y),
      2 * primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter - x ∈
        Set.Icc (0 : Real) ((1 : Real) / 10) := by
  intro x hx
  rw [Set.mem_Icc] at hy hx ⊢
  constructor <;>
    norm_num [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter]
      at hy hx ⊢ <;>
    linarith

/-- Public derivative-majorant array for the `OmegaPrimeActual` factor. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
    (k : Nat) : Real :=
  if hk : k < 17 then
    centeredTaylorDerivMajorant16
      (fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs
          j.1 : Real))
      (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert.order16Abs :
        Real)
      ((1 : Real) / 20)
      ⟨k, hk⟩
  else
    0

/-- Public derivative-majorant array for the `ShapeSqDerivActual` factor. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
    (k : Nat) : Real :=
  if hk : k < 17 then
    centeredTaylorDerivMajorant16
      (fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
          j.1 : Real))
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs :
        Real)
      ((1 : Real) / 20)
      ⟨k, hk⟩
  else
    0

/-- Public derivative-majorant array for the integrated `OmegaActual` factor. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
    (k : Nat) : Real :=
  if hk : k < 17 then
    centeredTaylorDerivMajorant16
      (fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs
          j.1 : Real))
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant 15)
      ((1 : Real) / 20)
      ⟨k, hk⟩
  else
    0

/-- Public derivative-majorant array for the integrated `ShapeSqActual` factor. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
    (k : Nat) : Real :=
  if hk : k < 17 then
    centeredTaylorDerivMajorant16
      (fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
          j.1 : Real))
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
        15)
      ((1 : Real) / 20)
      ⟨k, hk⟩
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 16) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
        eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant k := by
  have hk17 : k < 17 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
  simp [hk17]
  let kFin : Fin 17 := ⟨k, hk17⟩
  have hSmooth :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16
  have hJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
            (Nat.factorial j.1 : Real)‖ <=
          (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs
            j.1 : Real) := by
    intro j
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_centerJet_abs_bound
        j.1 j.2
    rw [Real.norm_eq_abs]
    simpa [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet] using hAbs
  have hOrder16 :
      ∀ x ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
            x‖ <=
          (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert.order16Abs :
            Real) := by
    intro x hx
    have h :=
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert_valid.order16_bound
        x hx
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using h
  have h :=
    iteratedDeriv_norm_le_centeredTaylorDerivMajorant16
      (f := primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual)
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (center := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter)
      (radius := ((1 : Real) / 20))
      (order16Abs :=
        (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert.order16Abs :
          Real))
      (eta := eta)
      (jetAbs := fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs
          j.1 : Real))
      kFin
      primaryFiniteRow0Parent0Split100Sub0_center_mem
      hSmooth hJet hOrder16
      (fun x hx =>
        primaryFiniteRow0Parent0Split100Sub0_cell_radius hx)
      (fun y hy hyle =>
        primaryFiniteRow0Parent0Split100Sub0_reflect_cell hy hyle)
      heta
  simpa [kFin] using h

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_centeredTaylor
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 16) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
        eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant k := by
  have hk17 : k < 17 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
  simp [hk17]
  let kFin : Fin 17 := ⟨k, hk17⟩
  have hSmooth :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)
  have hJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
            (Nat.factorial j.1 : Real)‖ <=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
            j.1 : Real) := by
    intro j
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_centerJet_abs_bound
        j.1 j.2
    rw [Real.norm_eq_abs]
    simpa [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet] using hAbs
  have hOrder16 :
      ∀ x ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
            x‖ <=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs :
            Real) := by
    intro x hx
    have hValid :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011_valid
    obtain ⟨i, hi⟩ := hValid.cover x hx
    have hRows := hValid.order16Rows i x hi
    have hRowsActual :
        (ShapeSqDerivTaylorIntervalCert.singleAbs
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs).order16Lower
            i <=
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual x ∧
        iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual x <=
          (ShapeSqDerivTaylorIntervalCert.singleAbs
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs).order16Upper
            i := by
      simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual] using
        hRows
    have hBudget := hValid.order16Budget i
    have hBudgetActual :
        -(primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs :
            Real) <=
          (ShapeSqDerivTaylorIntervalCert.singleAbs
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs).order16Lower
              i ∧
          (ShapeSqDerivTaylorIntervalCert.singleAbs
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs).order16Upper
              i <=
            (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs :
              Real) := by
      simpa [ShapeSqDerivTaylorIntervalCert.singleAbs] using hBudget
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [hRowsActual.1, hBudgetActual.1]
    · linarith [hRowsActual.2, hBudgetActual.2]
  have h :=
    iteratedDeriv_norm_le_centeredTaylorDerivMajorant16
      (f := primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual)
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (center := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter)
      (radius := ((1 : Real) / 20))
      (order16Abs :=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs :
          Real))
      (eta := eta)
      (jetAbs := fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
          j.1 : Real))
      kFin
      primaryFiniteRow0Parent0Split100Sub0_center_mem
      hSmooth hJet hOrder16
      (fun x hx =>
        primaryFiniteRow0Parent0Split100Sub0_cell_radius hx)
      (fun y hy hyle =>
        primaryFiniteRow0Parent0Split100Sub0_reflect_cell hy hyle)
      heta
  simpa [kFin] using h

theorem primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 16) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual
        eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant k := by
  have hk17 : k < 17 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
  simp [hk17]
  let kFin : Fin 17 := ⟨k, hk17⟩
  have hSmooth :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16
  have hJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
            (Nat.factorial j.1 : Real)‖ <=
          (primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs
            j.1 : Real) := by
    intro j
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_centerJet_abs_bound
        j.1 (lt_trans j.2 (by norm_num))
    rw [Real.norm_eq_abs]
    simpa [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet] using hAbs
  have hOrder16 :
      ∀ x ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0OmegaActual
            x‖ <=
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
            15 := by
    intro x hx
    have hBase :=
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
        x hx 15 (by norm_num)
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv_succ_eq_omegaPrime
        15 x
    rw [show 16 = 15 + 1 by norm_num, hShift]
    exact hBase
  have h :=
    iteratedDeriv_norm_le_centeredTaylorDerivMajorant16
      (f := primaryFiniteRow0Parent0Split100Sub0OmegaActual)
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (center := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter)
      (radius := ((1 : Real) / 20))
      (order16Abs :=
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
          15)
      (eta := eta)
      (jetAbs := fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs
          j.1 : Real))
      kFin
      primaryFiniteRow0Parent0Split100Sub0_center_mem
      hSmooth hJet hOrder16
      (fun x hx =>
        primaryFiniteRow0Parent0Split100Sub0_cell_radius hx)
      (fun y hy hyle =>
        primaryFiniteRow0Parent0Split100Sub0_reflect_cell hy hyle)
      heta
  simpa [kFin] using h

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_centeredTaylor
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 16) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
        eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant k := by
  have hk17 : k < 17 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
  simp [hk17]
  let kFin : Fin 17 := ⟨k, hk17⟩
  have hSmooth :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
            (Nat.factorial j.1 : Real)‖ <=
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
            j.1 : Real) := by
    intro j
    have hAbs :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_centerJet_abs_bound
        j.1 (lt_trans j.2 (by norm_num))
    rw [Real.norm_eq_abs]
    simpa [primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet] using hAbs
  have hOrder16 :
      ∀ x ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
            x‖ <=
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
            15 := by
    intro x hx
    have hBase :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_centeredTaylor
        x hx 15 (by norm_num)
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ
        15 x
    change
      ‖iteratedDeriv 15 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv x‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
          15 at hBase
    rw [hShift] at hBase
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqActual] using hBase
  have h :=
    iteratedDeriv_norm_le_centeredTaylorDerivMajorant16
      (f := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (center := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter)
      (radius := ((1 : Real) / 20))
      (order16Abs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
          15)
      (eta := eta)
      (jetAbs := fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
          j.1 : Real))
      kFin
      primaryFiniteRow0Parent0Split100Sub0_center_mem
      hSmooth hJet hOrder16
      (fun x hx =>
        primaryFiniteRow0Parent0Split100Sub0_cell_radius hx)
      (fun y hy hyle =>
        primaryFiniteRow0Parent0Split100Sub0_reflect_cell hy hyle)
      heta
  simpa [kFin] using h

private theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActualDerivativeMajorant_nonneg
    (k : Nat) (hk : k <= 16) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
        k := by
  have hBound :=
    primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
      primaryFiniteRow0Parent0Split100Sub0_center_mem k hk
  exact (norm_nonneg _).trans hBound

private theorem primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant_nonneg
    (k : Nat) (hk : k <= 16) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant k := by
  have hBound :=
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
      primaryFiniteRow0Parent0Split100Sub0_center_mem k hk
  exact (norm_nonneg _).trans hBound

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_centeredTaylor_factor_majorants :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
          primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_factor_derivative_abs
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActualDerivativeMajorant_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_centeredTaylor

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_centeredTaylor_factor_majorants
    {activeScaleAbs order16Abs : Real}
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        activeScaleAbs)
    (hBudget :
      activeScaleAbs *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
            primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
            primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
            primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant <=
        order16Abs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      -order16Abs <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <= order16Abs := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_factor_derivative_abs
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActualDerivativeMajorant_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_centeredTaylor
      hActiveScaleAbs hBudget

end Step33
end PSDpd
end Q3
