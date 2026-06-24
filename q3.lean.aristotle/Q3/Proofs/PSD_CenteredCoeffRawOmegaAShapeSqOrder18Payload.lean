import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivSharpOrder16Payload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincDerivativeOrder18Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-grade ShapeSq order-18 source for the RawProduct18 receiver.

This file extends the existing sharp ShapeSq route by one derivative row.  It
does not claim the RawProduct18 source is closed: the Omega/OmegaPrime order-17
source remains a separate live gap.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Target ShapeSq order-18 bound with the same sharp shape derivative budget
used by the order-17 ShapeSqDeriv source. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqSharpOrder18Abs : Rat :=
  (2 : Rat) ^ (24 : Nat) * ((3 : Rat) / 5) ^ (18 : Nat)

theorem primaryFiniteRow0Parent0Split100Sub0_powDerivMajorant11_sharp_table_nat
    (n : Nat) :
    powDerivMajorant 11 n
        primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs =
      primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs n := by
  have hCast :=
    primaryFiniteRow0Parent0Split100Sub0_powDerivMajorantRat_cast
      11 n primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs
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
  have hRat :
      powDerivMajorantRat 11 n
          primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs =
        primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs n := by
    exact powDerivMajorantRat_sharpScaledSinc_11 n
  have hRatReal :
      ((powDerivMajorantRat 11 n
          primaryFiniteRow0Parent0Split100Sub0SharpScaledSincRatAbs :
          Rat) : Real) =
        (primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs n :
          Real) := by
    exact_mod_cast hRat
  simpa [primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs] using hRatReal

private theorem primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_realSinc_abs18
    {baseAbs scaledAbs : Nat -> Real}
    (hBaseAbs :
      ∀ u ∈ Set.Icc (0 : Real) ((1 : Real) / 400),
        ∀ k : Nat, k <= 18 ->
          ‖iteratedDeriv k realSinc u‖ <= baseAbs k)
    (hBudget :
      ∀ k : Nat, k <= 18 ->
        ‖((1 : Real) / 40) ^ k‖ * baseAbs k <= scaledAbs k) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 18 ->
        ‖iteratedDeriv k
            primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc eta‖ <=
          scaledAbs k := by
  intro eta heta k hk
  have hArg :
      ((1 : Real) / 40) * eta ∈ Set.Icc (0 : Real) ((1 : Real) / 400) := by
    constructor <;> nlinarith [heta.1, heta.2]
  have hScaledFun :
      primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc =
        fun x : Real => realSinc (((1 : Real) / 40) * x) := by
    funext x
    apply congrArg realSinc
    norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc,
      bsplineScale]
    ring
  have hScaledEq :
      iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc eta =
        iteratedDeriv k realSinc (((1 : Real) / 40) * eta) *
          ((1 : Real) / 40) ^ k := by
    have h :=
      congrFun
        (iteratedDeriv_comp_const_mul
          (n := k) (f := realSinc)
          (realSinc_contDiff (k : WithTop ENat))
          ((1 : Real) / 40))
        eta
    rw [hScaledFun]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  rw [hScaledEq, norm_mul]
  have hBase := hBaseAbs (((1 : Real) / 40) * eta) hArg k hk
  have hScaledBase :
      ‖iteratedDeriv k realSinc (((1 : Real) / 40) * eta)‖ *
          ‖((1 : Real) / 40) ^ k‖ <=
        baseAbs k * ‖((1 : Real) / 40) ^ k‖ :=
    mul_le_mul_of_nonneg_right hBase (norm_nonneg _)
  have hBudget_k :
      baseAbs k * ‖((1 : Real) / 40) ^ k‖ <= scaledAbs k := by
    simpa [mul_comm] using hBudget k hk
  exact le_trans hScaledBase hBudget_k

private theorem primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_scaledSinc_abs18
    {baseAbs shapeAbs : Nat -> Real}
    (hBaseAbsNonneg :
      ∀ k : Nat, k <= 18 -> 0 <= baseAbs k)
    (hBaseAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 18 ->
          ‖iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc eta‖ <=
            baseAbs k)
    (hBudget :
      ∀ k : Nat, k <= 18 ->
        ‖primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer‖ *
            powDerivMajorant 11 k baseAbs <=
          shapeAbs k) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 18 ->
        ‖iteratedDeriv k
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t)
            eta‖ <=
          shapeAbs k := by
  intro eta heta k hk
  let base : Real -> Real :=
    primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc
  let D : Real := primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer
  have hBaseCont : ∀ m : Nat, ContDiff Real (m : WithTop ENat) base := by
    intro m
    simpa [base, primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc] using
      (realSinc_contDiff (m : WithTop ENat)).comp (by fun_prop)
  have hPow :
      ‖iteratedDeriv k (fun t : Real => base t ^ (11 + 1)) eta‖ <=
        powDerivMajorant 11 k baseAbs := by
    exact
      pow_succ_derivative_abs_of_base_derivative_abs
        (p := 11) (n := k) (base := base) (M := baseAbs) (eta := eta)
        hBaseCont
        (fun m hm => hBaseAbsNonneg m (le_trans hm hk))
        (fun m hm => hBaseAbs eta heta m (le_trans hm hk))
  have hPowContAt :
      ContDiffAt Real k (fun t : Real => base t ^ (11 + 1)) eta := by
    exact ((hBaseCont k).pow (11 + 1)).contDiffAt
  have hConst :
      iteratedDeriv k (fun t : Real => D * base t ^ (11 + 1)) eta =
        D * iteratedDeriv k (fun t : Real => base t ^ (11 + 1)) eta := by
    simpa [smul_eq_mul] using
      (iteratedDeriv_const_mul
        (n := k) (f := fun t : Real => base t ^ (11 + 1))
        (x := eta) hPowContAt D)
  have hScaled :
      ‖iteratedDeriv k (fun t : Real => D * base t ^ (11 + 1)) eta‖ <=
        ‖D‖ * powDerivMajorant 11 k baseAbs := by
    rw [hConst, norm_mul]
    exact mul_le_mul_of_nonneg_left hPow (norm_nonneg D)
  have hShapeEq :
      (fun t : Real =>
        centeredBSplineImagTransformRealClosedForm
          11 ((3 : Real) / 10) t) =
        fun t : Real => D * base t ^ (11 + 1) := by
    funext t
    simp [D, base, primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer,
      primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc,
      centeredBSplineImagTransformRealClosedForm]
  have hBudget_k : ‖D‖ * powDerivMajorant 11 k baseAbs <= shapeAbs k := by
    simpa [D, primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer] using
      hBudget k hk
  rw [hShapeEq]
  exact le_trans hScaled hBudget_k

theorem primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_sharp18 :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 18 ->
        ‖iteratedDeriv k
            primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs k := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_realSinc_abs18
      (baseAbs := fun _ => (2 : Real))
      (scaledAbs := primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs)
      ?hBase ?hBudget
  · intro u hu k hk
    have hk19 : k < 19 := by omega
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_realSinc_derivative_abs_through18
        u hu ⟨k, hk19⟩
    exact h
  · intro k hk
    rw [primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs]
    have hpow_nonneg : 0 <= ((1 : Real) / 40) ^ k := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    rw [mul_comm (((1 : Real) / 40) ^ k) (2 : Real)]

theorem primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_sharp18 :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 18 ->
        ‖iteratedDeriv k
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t)
            eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs k := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_scaledSinc_abs18
      (baseAbs := primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs)
      (shapeAbs := primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs)
      ?hBaseAbsNonneg ?hBaseAbs ?hBudget
  · intro k hk
    unfold primaryFiniteRow0Parent0Split100Sub0SharpScaledSincAbs
    positivity
  · exact primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_sharp18
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
      primaryFiniteRow0Parent0Split100Sub0_powDerivMajorant11_sharp_table_nat
        k
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

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSq_order18_abs_of_sharp :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 18
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm
              11 ((3 : Real) / 10) t) ^ 2)
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqSharpOrder18Abs :
          Real) := by
  intro eta heta
  have hProduct :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs
      (n := 18)
      (M := primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs)
      (eta := eta)
      (by
        intro k hk
        unfold primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs
        unfold primaryFiniteRow0Parent0Split100Sub0SharpShapeRatAbs
        positivity)
      (fun k hk =>
        primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_sharp18
          eta heta k hk)
  have hSum :
      (∑ i ∈ Finset.range (18 + 1),
          ((18 : Nat).choose i : Real) *
            primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs i *
            primaryFiniteRow0Parent0Split100Sub0SharpShapeAbs (18 - i)) =
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqSharpOrder18Abs :
          Real) := by
    rw [primaryFiniteRow0Parent0Split100Sub0_sharpShapeSqProductSum_eq]
    norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqSharpOrder18Abs]
  exact le_trans hProduct (le_of_eq hSum)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_abs_of_sharp :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqSharpOrder18Abs :
          Real) := by
  intro eta heta
  simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqActual] using
    primaryFiniteRow0Parent0Split100Sub0_shapeSq_order18_abs_of_sharp eta heta

/-- ShapeSqActual derivative majorant through the rows needed by the
RawProduct18 Leibniz receiver. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18
    (k : Nat) : Real :=
  if _ : k < 17 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant k
  else if k = 17 then
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivSharpOrder16Abs : Real)
  else if k = 18 then
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqSharpOrder18Abs : Real)
  else
    0

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 18) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
        eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18
        k := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18
  by_cases hk17 : k < 17
  · simp [hk17]
    exact
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp_centeredTaylor
        eta heta k (Nat.le_of_lt_succ hk17)
  · simp [hk17]
    have hk_cases : k = 17 ∨ k = 18 := by omega
    rcases hk_cases with hk_eq | hk_eq
    · subst k
      simp
      simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqActual] using
        primaryFiniteRow0Parent0Split100Sub0_shapeSq_order17_abs_of_sharp eta heta
    · subst k
      simp
      exact primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_abs_of_sharp
        eta heta

end Step33
end PSDpd
end Q3
