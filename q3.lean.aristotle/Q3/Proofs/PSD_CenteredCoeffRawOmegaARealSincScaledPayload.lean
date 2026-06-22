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

end Step33
end PSDpd
end Q3
