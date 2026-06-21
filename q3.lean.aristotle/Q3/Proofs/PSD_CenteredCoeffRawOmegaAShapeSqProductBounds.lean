import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Product-bound bridge for the active Step33A.1-A ShapeSqDeriv layer.

This isolated file keeps the heavy endpoint support module unchanged while
exposing a checked receiver from proof-grade derivative bounds on the active
shape function to derivative bounds for its square.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Product-bound receiver for the active shape-square derivative layer.

This is the checked Mathlib bridge from bounds on derivatives of the active
`k=11`, `ell=3/10` shape function to a bound on the corresponding derivative
of its square.  It closes only the product-Leibniz/bilinear norm-transfer
interface; the proof-grade numerical/rational derivative bounds `M` remain a
separate payload obligation. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs
    {n : Nat} {M : Nat -> Real} {eta : Real}
    (hMnonneg : forall k, k <= n -> 0 <= M k)
    (hShapeDerivAbs :
      forall k, k <= n ->
        ‖iteratedDeriv k
            (fun t : Real =>
              centeredBSplineImagTransformRealClosedForm
                11 ((3 : Real) / 10) t)
            eta‖ <= M k) :
    ‖iteratedDeriv n
        (fun t : Real =>
          (centeredBSplineImagTransformRealClosedForm
            11 ((3 : Real) / 10) t) ^ 2)
        eta‖ <=
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) * M i * M (n - i) := by
  let shape : Real -> Real :=
    fun t : Real =>
      centeredBSplineImagTransformRealClosedForm
        11 ((3 : Real) / 10) t
  have hcont : ContDiff Real (n : WithTop ENat) shape := by
    simpa [shape] using
      centeredBSplineImagTransformRealClosedForm_contDiff
        11 ((3 : Real) / 10) (n : WithTop ENat)
  have hmulF :
      ‖iteratedFDeriv Real n (fun y : Real => shape y * shape y) eta‖ <=
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : Real) *
            ‖iteratedFDeriv Real i shape eta‖ *
            ‖iteratedFDeriv Real (n - i) shape eta‖ := by
    exact norm_iteratedFDeriv_mul_le
      (𝕜 := Real) (f := shape) (g := shape) hcont hcont eta
      (n := n) (by simp)
  have hmulD :
      ‖iteratedDeriv n (fun y : Real => shape y * shape y) eta‖ <=
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : Real) *
            ‖iteratedDeriv i shape eta‖ *
            ‖iteratedDeriv (n - i) shape eta‖ := by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hmulF
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
          (n.choose i : Real) *
            ‖iteratedDeriv i shape eta‖ *
            ‖iteratedDeriv (n - i) shape eta‖) <=
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : Real) * M i * M (n - i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i <= n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hni_le : n - i <= n := Nat.sub_le n i
    have hchoose_nonneg : 0 <= (n.choose i : Real) := by positivity
    have hprod :
        ‖iteratedDeriv i shape eta‖ *
            ‖iteratedDeriv (n - i) shape eta‖ <=
          M i * M (n - i) := by
      exact mul_le_mul
        (hShapeDerivAbs i hi_le)
        (hShapeDerivAbs (n - i) hni_le)
        (norm_nonneg _)
        (hMnonneg i hi_le)
    calc
      (n.choose i : Real) *
            ‖iteratedDeriv i shape eta‖ *
            ‖iteratedDeriv (n - i) shape eta‖ =
          (n.choose i : Real) *
            (‖iteratedDeriv i shape eta‖ *
              ‖iteratedDeriv (n - i) shape eta‖) := by ring
      _ <= (n.choose i : Real) * (M i * M (n - i)) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nonneg
      _ = (n.choose i : Real) * M i * M (n - i) := by ring
  have hmain := le_trans hmulD hsum
  simpa [shape, pow_two] using hmain

end Step33
end PSDpd
end Q3
