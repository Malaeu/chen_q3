import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincDerivativePayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Scaled-sinc feed for the coarse Step33A.1-A `realSinc` derivative payload.

The theorem in this file closes only the affine normalization
`realSinc u -> realSinc (eta / 40)`.  It deliberately does not claim the later
shape-derivative budget through `powDerivMajorant`.
-/

namespace Q3
namespace PSDpd
namespace Step33

/-- Coarse scaled-sinc derivative budget inherited from the unscaled `2`
realSinc payload. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs : Nat -> Real :=
  fun _ => 2

/-- Coarse scaled-sinc derivative bound obtained from the exact unscaled
`realSinc` payload and the affine factor `(1 / 40)^k`. -/
theorem primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_coarseTwo :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 17 ->
        ‖iteratedDeriv k
            primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs k := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_realSinc_abs
      (baseAbs := fun _ => (2 : Real))
      (scaledAbs := primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs)
      ?hBase ?hBudget
  · intro u hu k hk
    have hk18 : k < 18 := by omega
    have h :=
      Step33Sub0RealSincDerivativeMajorantCert.coarseTwoBaseAbs_providesAnalyticMajorant
        u hu ⟨k, hk18⟩
    simpa [Step33Sub0RealSincDerivativeMajorantCert.coarseTwoBaseAbs] using h
  · intro k hk
    have hpow_abs_le_one : ‖((1 : Real) / 40) ^ k‖ <= (1 : Real) := by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (n := k) (abs_nonneg ((1 : Real) / 40)) (by norm_num)
    calc
      ‖((1 : Real) / 40) ^ k‖ * (2 : Real)
          <= (1 : Real) * (2 : Real) := by
            exact mul_le_mul_of_nonneg_right hpow_abs_le_one (by norm_num)
      _ <= primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs k := by
            norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs]

/-- Exact symbolic shape-derivative budget induced by the coarse scaled-sinc
budget.  This is intentionally not a rationalized generator payload. -/
noncomputable def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeAbs
    (k : Nat) : Real :=
  ‖primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer‖ *
    powDerivMajorant 11 k
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs

/-- Shape derivative bound obtained from the coarse realSinc payload through
the affine-scale and Leibniz shape receivers.

The right-hand side is exact but symbolic.  A later generator-facing patch must
still compare this expression against a rational shape-derivative budget if the
Taylor payload requires rational fields. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 17 ->
        ‖iteratedDeriv k
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t)
            eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeAbs k := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_scaledSinc_abs
      (baseAbs := primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs)
      (shapeAbs := primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeAbs)
      ?hBaseAbsNonneg ?hBaseAbs ?hBudget
  · intro k hk
    norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs]
  · exact primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_coarseTwo
  · intro k hk
    rfl

/-- Closed form for the recursive Leibniz majorant when every derivative of
the base is bounded by `2`. -/
theorem powDerivMajorant_const_two (p n : Nat) :
    powDerivMajorant p n (fun _ => (2 : Real)) =
      (2 : Real) ^ (p + 1) * ((p + 1 : Nat) : Real) ^ n := by
  induction p generalizing n with
  | zero =>
      simp [powDerivMajorant]
  | succ p ih =>
      simp only [powDerivMajorant]
      calc
        (∑ i ∈ Finset.range (n + 1),
            (n.choose i : Real) * powDerivMajorant p i (fun _ => (2 : Real)) *
              (fun _ => (2 : Real)) (n - i)) =
            ∑ i ∈ Finset.range (n + 1),
              (2 : Real) ^ (p + 2) * ((p + 1 : Nat) : Real) ^ i *
                (1 : Real) ^ (n - i) * (n.choose i : Real) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [ih i]
          ring
        _ = (2 : Real) ^ (p + 2) *
            (((p + 1 : Nat) : Real) + 1) ^ n := by
          rw [add_pow]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        _ = (2 : Real) ^ ((p + 1) + 1) *
            (((p + 1) + 1 : Nat) : Real) ^ n := by
          norm_num

/-- Rational shape-derivative budget induced by the coarse `2` realSinc
payload. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs
    (k : Nat) : Rat :=
  (2 : Rat) ^ (12 : Nat) * (12 : Rat) ^ k

/-- Real view of the rational coarse shape-derivative budget. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
    (k : Nat) : Real :=
  (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs k : Real)

/-- The symbolic shape budget is majorized by the rational coarse budget. -/
theorem primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeAbs_le_rationalAbs
    (k : Nat) :
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeAbs k <=
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs k := by
  have hD_abs_le_one :
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer‖ <= (1 : Real) := by
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
      0 <= powDerivMajorant 11 k
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs := by
    have hPow_eq :
        powDerivMajorant 11 k
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs =
          (2 : Real) ^ (11 + 1) * ((11 + 1 : Nat) : Real) ^ k := by
      simpa [primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs] using
        powDerivMajorant_const_two 11 k
    rw [hPow_eq]
    positivity
  calc
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeAbs k =
        ‖primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer‖ *
          powDerivMajorant 11 k
            primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs := by
      rfl
    _ <= (1 : Real) *
        powDerivMajorant 11 k
          primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs := by
      exact mul_le_mul_of_nonneg_right hD_abs_le_one hPow_nonneg
    _ <= primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs k := by
      have hPow_eq :
          powDerivMajorant 11 k
              primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs =
            (2 : Real) ^ (11 + 1) * ((11 + 1 : Nat) : Real) ^ k := by
        simpa [primaryFiniteRow0Parent0Split100Sub0CoarseTwoScaledAbs] using
          powDerivMajorant_const_two 11 k
      rw [hPow_eq]
      norm_num [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs,
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs]

/-- Fully rationalized coarse shape-derivative receiver. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 17 ->
        ‖iteratedDeriv k
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t)
            eta‖ <=
          primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs k := by
  intro eta heta k hk
  exact
    le_trans
      (primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo
        eta heta k hk)
      (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeAbs_le_rationalAbs k)

end Step33
end PSDpd
end Q3
