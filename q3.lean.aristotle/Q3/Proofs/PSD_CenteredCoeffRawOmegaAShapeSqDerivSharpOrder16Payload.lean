import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge
import Q3.Proofs.PSD_PowDerivMajorantRat

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Fail-closed target ledger for the active ShapeSqDeriv sharp order-16 payload.

Proshka route review after the centered-Taylor budget kill chose the narrow
repair: keep the factor-majorant route and sharpen only the
`ShapeSqDerivActual` order-16 bound before returning to rows `12..15`, cell
splitting, or direct combined-source certificates.

This file deliberately contains definitions and exact propositions only.  A
first proof attempt with the generic `powDerivMajorant` closed form made Lean
hang in arithmetic normalization, so no proof theorem is claimed here.
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

/-- Sharp scaled-sinc derivative target preserving the affine factor
`realSinc (eta / 40)`. -/
def primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs
    (k : Nat) : Real :=
  (2 : Real) * ((1 : Real) / 40) ^ k

/-- Rationalized target for active shape derivatives after preserving the
`1/40` scaling through the twelfth power. -/
def primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs
    (k : Nat) : Rat :=
  (2 : Rat) ^ (12 : Nat) * ((3 : Rat) / 10) ^ k

def primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs
    (k : Nat) : Real :=
  (primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs k : Real)

/-- Target ShapeSqDeriv order-16 bound, equivalent to a shape-square
order-17 bound with shape derivative budget `2^12 * (3/10)^k`. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs :
    Rat :=
  (2 : Rat) ^ (24 : Nat) * ((3 : Rat) / 5) ^ (17 : Nat)

def primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs
    (k : Nat) : Rat :=
  (2 : Rat) * ((1 : Rat) / 40) ^ k

theorem primaryFiniteRow0Parent0Split100Sub0_powDerivMajorantRat_cast
    (p n : Nat) (M : Nat -> Rat) :
    ((powDerivMajorantRat p n M : Rat) : Real) =
      powDerivMajorant p n (fun k : Nat => (M k : Real)) := by
  induction p generalizing n with
  | zero =>
      simp [powDerivMajorantRat, powDerivMajorant]
  | succ p ih =>
      simp [powDerivMajorantRat, powDerivMajorant, ih]

theorem primaryFiniteRow0Parent0Split100Sub0_powDerivMajorant11_sharp_rat_table :
    ∀ n : Fin 18,
      powDerivMajorantRat 11 n.1
          primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs =
        primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs n.1 := by
  intro n
  exact powDerivMajorantRat_sharpScaledSinc_11 n.1

theorem primaryFiniteRow0Parent0Split100Sub0_powDerivMajorant11_sharp_table :
    ∀ n : Fin 18,
      powDerivMajorant 11 n.1
          primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs =
        primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs n.1 := by
  intro n
  have hCast :=
    primaryFiniteRow0Parent0Split100Sub0_powDerivMajorantRat_cast
      11 n.1 primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs
  have hScaledFun :
      (fun k : Nat =>
          (primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs k :
            Real)) =
        primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs := by
    funext k
    norm_num [primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs,
      primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs]
  rw [hScaledFun] at hCast
  rw [← hCast]
  have hRat :=
    primaryFiniteRow0Parent0Split100Sub0_powDerivMajorant11_sharp_rat_table n
  have hRatReal :
      ((powDerivMajorantRat 11 n.1
          primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs :
          Rat) : Real) =
        (primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs n.1 :
          Real) := by
    exact_mod_cast hRat
  simpa [primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs] using hRatReal

theorem primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_sharp :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 17 ->
        ‖iteratedDeriv k
            primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs k := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_realSinc_abs
      (baseAbs := fun _ => (2 : Real))
      (scaledAbs := primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs)
      ?hBase ?hBudget
  · intro u hu k hk
    have hk18 : k < 18 := by omega
    have h :=
      Step33Sub0RealSincDerivativeMajorantCert.coarseTwoBaseAbs_providesAnalyticMajorant
        u hu ⟨k, hk18⟩
    simpa [Step33Sub0RealSincDerivativeMajorantCert.coarseTwoBaseAbs] using h
  · intro k hk
    rw [primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs]
    have hpow_nonneg : 0 <= ((1 : Real) / 40) ^ k := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    rw [mul_comm (((1 : Real) / 40) ^ k) (2 : Real)]

theorem primaryFiniteRow0Parent0Split100Sub0_sharpShapeSqProductSum_eq
    (n : Nat) :
    (∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) *
          primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs i *
          primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs (n - i)) =
      (2 : Real) ^ (24 : Nat) * ((3 : Real) / 5) ^ n := by
  have hRat :
      powDerivMajorantRat 1 n
          primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs =
        (2 : Rat) ^ (24 : Nat) * ((3 : Rat) / 5) ^ n := by
    exact powDerivMajorantRat_sharpShapeSq_1 n
  have hRatReal :
      ((powDerivMajorantRat 1 n
          primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs : Rat) :
          Real) =
        ((2 : Rat) ^ (24 : Nat) * ((3 : Rat) / 5) ^ n : Rat) := by
    exact_mod_cast hRat
  have hCast :=
    primaryFiniteRow0Parent0Split100Sub0_powDerivMajorantRat_cast
      1 n primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs
  have hShapeFun :
      (fun k : Nat =>
          (primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs k :
            Real)) =
        primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs := by
    funext k
    rfl
  rw [hShapeFun] at hCast
  rw [hCast] at hRatReal
  simpa [powDerivMajorant,
    primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs] using hRatReal

theorem primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_sharp :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 17 ->
        ‖iteratedDeriv k
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t)
            eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs k := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_scaledSinc_abs
      (baseAbs := primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs)
      (shapeAbs := primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs)
      ?hBaseAbsNonneg ?hBaseAbs ?hBudget
  · intro k hk
    unfold primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs
    positivity
  · exact primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_sharp
  · intro k hk
    have hD_abs_le_one :
        ‖primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer‖ <=
          (1 : Real) := by
      have hprod_pos :
          0 < bsplineScale 11 * bsplineAutocorrNorm 11 :=
        mul_pos (bsplineScale_pos 11) (bsplineAutocorrNorm_pos 11)
      have hprod_ge_one :
          (1 : Real) <= bsplineScale 11 * bsplineAutocorrNorm 11 := by
        rw [bsplineAutocorrNorm_11_exact]
        norm_num [bsplineScale]
      have hsqrt_ge_one :
          (1 : Real) <=
            Real.sqrt (bsplineScale 11 * bsplineAutocorrNorm 11) := by
        rw [Real.le_sqrt (by norm_num) (le_of_lt hprod_pos)]
        simpa using hprod_ge_one
      have hD_pos :
          0 < primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer := by
        simpa [primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer] using
          inv_pos.mpr (Real.sqrt_pos.mpr hprod_pos)
      rw [Real.norm_eq_abs]
      rw [abs_of_pos hD_pos]
      simpa [primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer] using
        inv_le_one_of_one_le₀ hsqrt_ge_one
    have hPow_nonneg :
        0 <=
          powDerivMajorant 11 k
            primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs :=
      powDerivMajorant_nonneg
        (p := 11) (n := k)
        (M := primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs)
        (by
          intro m hm
          unfold primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs
          positivity)
    have hTable :=
      primaryFiniteRow0Parent0Split100Sub0_powDerivMajorant11_sharp_table
        ⟨k, by omega⟩
    calc
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer‖ *
          powDerivMajorant 11 k
            primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs
          <=
        (1 : Real) *
          powDerivMajorant 11 k
            primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs := by
          exact mul_le_mul_of_nonneg_right hD_abs_le_one hPow_nonneg
      _ <= primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs k := by
          rw [one_mul]
          exact le_of_eq hTable

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSq_order17_abs_of_sharp :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 17
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm
              11 ((3 : Real) / 10) t) ^ 2)
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs :
          Real) := by
  intro eta heta
  have hProduct :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs
      (n := 17)
      (M := primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs)
      (eta := eta)
      (by
        intro k hk
        unfold primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs
        unfold primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs
        positivity)
      (fun k hk =>
        primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_sharp
          eta heta k hk)
  have hSum :
      (∑ i ∈ Finset.range (17 + 1),
          ((17 : Nat).choose i : Real) *
            primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs i *
            primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs (17 - i)) =
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs :
          Real) := by
    rw [primaryFiniteRow0Parent0Split100Sub0_sharpShapeSqProductSum_eq]
    norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs]
  exact le_trans hProduct (le_of_eq hSum)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_order16_abs_sharp :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs :
          Real) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_order16_abs_of_shapeSq_order17_abs
      primaryFiniteRow0Parent0Split100Sub0_shapeSq_order17_abs_of_sharp

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
    (k : Nat) : Real :=
  if hk : k < 17 then
    centeredTaylorDerivMajorant16
      (fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
          j.1 : Real))
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs :
        Real)
      ((1 : Real) / 20)
      ⟨k, hk⟩
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_sharp_centeredTaylor
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 16) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
        eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
        k := by
  have hk17 : k < 17 := Nat.lt_succ_of_le hk
  unfold
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
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
          (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs :
            Real) := by
    intro x hx
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual] using
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_order16_abs_sharp
        x hx
  have h :=
    iteratedDeriv_norm_le_centeredTaylorDerivMajorant16
      (f := primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual)
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (center := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter)
      (radius := ((1 : Real) / 20))
      (order16Abs :=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs :
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

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant
    (k : Nat) : Real :=
  if hk : k < 17 then
    centeredTaylorDerivMajorant16
      (fun j : Fin 16 =>
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
          j.1 : Real))
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
        15)
      ((1 : Real) / 20)
      ⟨k, hk⟩
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp_centeredTaylor
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 16) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
        eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant
        k := by
  have hk17 : k < 17 := Nat.lt_succ_of_le hk
  unfold
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant
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
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
            15 := by
    intro x hx
    have hBase :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_sharp_centeredTaylor
        x hx 15 (by norm_num)
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ
        15 x
    change
      ‖iteratedDeriv 15 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv x‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
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
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant
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

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_sharp_shapeSqDeriv :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
          primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_factor_derivative_abs
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActualDerivativeMajorant_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaActualDerivativeMajorant_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_sharp_centeredTaylor

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_sharp_shapeSqDeriv
    {activeScaleAbs order16Abs : Real}
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        activeScaleAbs)
    (hBudget :
      activeScaleAbs *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
            primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
            primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
            primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorant <=
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
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp_centeredTaylor
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_sharp_centeredTaylor
      hActiveScaleAbs hBudget

private def primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
    (jetAbs : Nat -> Rat) (order16Abs radius : Rat) (k : Nat) : Rat :=
  (∑ j ∈ Finset.range 16,
      if k <= j then
        ((Nat.factorial j : Rat) / (Nat.factorial (j - k) : Rat)) *
          jetAbs j * radius ^ (j - k)
      else
        0) +
    order16Abs * radius ^ (16 - k) / (Nat.factorial (16 - k) : Rat)

private def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualCenterJetAbs
      Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedOrder16Abs
      ((1 : Rat) / 20) k
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualCenterJetAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs
      ((1 : Rat) / 20) k
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorantRat
    (k : Nat) : Rat :=
  if k < 17 then
    primaryFiniteRow0Parent0Split100Sub0CenteredTaylorDerivMajorant16Rat
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetAbs
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorantRat
        15)
      ((1 : Rat) / 20) k
  else
    0

def primaryFiniteRow0Parent0Split100Sub0ComponentProductActualSharpShapeSqDerivOrder16MajorantRat :
    Rat :=
  (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Rat) *
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorantRat i *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorantRat
          (16 - i)) +
    (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Rat) *
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorantRat i *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualSharpDerivativeMajorantRat
          (16 - i))

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActualSharpShapeSqDerivOrder16MajorantRat

/-- Exact next arithmetic target after the proof-grade sharp order-16 bridge is
available.  This is a proposition, not a proved theorem. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetPass : Prop :=
  primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetRat *
      ((1 : Rat) / 20) ^ 16 / (Nat.factorial 16 : Rat) <=
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sharpShapeSqDeriv_order16Budget_remainder_width_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth <
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetRat *
        ((1 : Rat) / 20) ^ 16 / (Nat.factorial 16 : Rat) := by
  native_decide

end Step33
end PSDpd
end Q3
