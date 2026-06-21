import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivMajorantReceiver

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Majorant receiver for the active Step33A.1-A shape derivative layer.

This file is intentionally numerical-data free.  It checks the reusable
Leibniz receiver that turns proof-grade bounds for the derivatives of the
scaled `realSinc` factor into proof-grade bounds for the active
`k=11`, `ell=3/10` B-spline shape.  The later payload must still supply the
scaled-sinc derivative bounds themselves.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Recursive Leibniz majorant for derivatives of `base^(p+1)`.

The index `p` counts one less than the power, so
`powDerivMajorant 0 n M = M n` majorizes `base`, and
`powDerivMajorant 11 n M` majorizes the active twelfth power. -/
def powDerivMajorant : Nat -> Nat -> (Nat -> Real) -> Real
  | 0, n, M => M n
  | p + 1, n, M =>
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) * powDerivMajorant p i M * M (n - i)

theorem powDerivMajorant_nonneg
    {p n : Nat} {M : Nat -> Real}
    (hMnonneg : ∀ k : Nat, k <= n -> 0 <= M k) :
    0 <= powDerivMajorant p n M := by
  induction p generalizing n with
  | zero =>
      simpa [powDerivMajorant] using hMnonneg n le_rfl
  | succ p ih =>
      simp only [powDerivMajorant]
      refine Finset.sum_nonneg ?_
      intro i hi
      have hi_le : i <= n :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hni_le : n - i <= n := Nat.sub_le n i
      exact mul_nonneg
        (mul_nonneg (by positivity)
          (ih (n := i) (fun k hk => hMnonneg k (le_trans hk hi_le))))
        (hMnonneg (n - i) hni_le)

/-- Checked power receiver: derivative bounds for a smooth base imply derivative
bounds for `base^(p+1)` with the recursive Leibniz majorant above. -/
theorem pow_succ_derivative_abs_of_base_derivative_abs
    {p n : Nat} {base : Real -> Real} {M : Nat -> Real} {eta : Real}
    (hBaseCont : ∀ m : Nat, ContDiff Real (m : WithTop ENat) base)
    (hMnonneg : ∀ k : Nat, k <= n -> 0 <= M k)
    (hBaseDerivAbs :
      ∀ k : Nat, k <= n -> ‖iteratedDeriv k base eta‖ <= M k) :
    ‖iteratedDeriv n (fun t : Real => base t ^ (p + 1)) eta‖ <=
      powDerivMajorant p n M := by
  induction p generalizing n eta with
  | zero =>
      simpa [powDerivMajorant] using hBaseDerivAbs n le_rfl
  | succ p ih =>
      let powBase : Real -> Real := fun t : Real => base t ^ (p + 1)
      have hPowCont : ContDiff Real (n : WithTop ENat) powBase := by
        simpa [powBase] using (hBaseCont n).pow (p + 1)
      have hMulF :
          ‖iteratedFDeriv Real n (fun y : Real => powBase y * base y) eta‖ <=
            ∑ i ∈ Finset.range (n + 1),
              (n.choose i : Real) *
                ‖iteratedFDeriv Real i powBase eta‖ *
                ‖iteratedFDeriv Real (n - i) base eta‖ := by
        exact norm_iteratedFDeriv_mul_le
          (𝕜 := Real) (f := powBase) (g := base)
          hPowCont (hBaseCont n) eta (n := n) (by simp)
      have hMulD :
          ‖iteratedDeriv n (fun y : Real => powBase y * base y) eta‖ <=
            ∑ i ∈ Finset.range (n + 1),
              (n.choose i : Real) *
                ‖iteratedDeriv i powBase eta‖ *
                ‖iteratedDeriv (n - i) base eta‖ := by
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hMulF
      have hSum :
          (∑ i ∈ Finset.range (n + 1),
              (n.choose i : Real) *
                ‖iteratedDeriv i powBase eta‖ *
                ‖iteratedDeriv (n - i) base eta‖) <=
            ∑ i ∈ Finset.range (n + 1),
              (n.choose i : Real) * powDerivMajorant p i M * M (n - i) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi_le : i <= n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hni_le : n - i <= n := Nat.sub_le n i
        have hchoose_nonneg : 0 <= (n.choose i : Real) := by positivity
        have hPow_i :
            ‖iteratedDeriv i powBase eta‖ <= powDerivMajorant p i M := by
          simpa [powBase] using
            ih (n := i) (eta := eta)
              (fun k hk => hMnonneg k (le_trans hk hi_le))
              (fun k hk => hBaseDerivAbs k (le_trans hk hi_le))
        have hPow_nonneg : 0 <= powDerivMajorant p i M :=
          powDerivMajorant_nonneg
            (p := p) (n := i) (M := M)
            (fun k hk => hMnonneg k (le_trans hk hi_le))
        have hprod :
            ‖iteratedDeriv i powBase eta‖ *
                ‖iteratedDeriv (n - i) base eta‖ <=
              powDerivMajorant p i M * M (n - i) := by
          exact mul_le_mul
            hPow_i
            (hBaseDerivAbs (n - i) hni_le)
            (norm_nonneg _)
            hPow_nonneg
        calc
          (n.choose i : Real) *
                ‖iteratedDeriv i powBase eta‖ *
                ‖iteratedDeriv (n - i) base eta‖ =
              (n.choose i : Real) *
                (‖iteratedDeriv i powBase eta‖ *
                  ‖iteratedDeriv (n - i) base eta‖) := by ring
          _ <= (n.choose i : Real) *
                (powDerivMajorant p i M * M (n - i)) :=
              mul_le_mul_of_nonneg_left hprod hchoose_nonneg
          _ = (n.choose i : Real) * powDerivMajorant p i M * M (n - i) := by
              ring
      have hMain := le_trans hMulD hSum
      simpa [powBase, pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc,
        powDerivMajorant] using hMain

/-- Active scaled-sinc base in the repository's local normalization. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc (eta : Real) : Real :=
  realSinc (((3 : Real) / 10) * eta / (2 * bsplineScale 11))

/-- Active B-spline shape normalizer in the repository's local normalization. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer : Real :=
  (Real.sqrt (bsplineScale 11 * bsplineAutocorrNorm 11))⁻¹

/-- Receiver from proof-grade scaled-sinc derivative bounds to proof-grade
active shape derivative bounds through order `17`.

This is still only a checker surface: `baseAbs` must be supplied by a later
interval/rational payload in the exact `realSinc (((3/10) * eta) /
(2 * bsplineScale 11))` normalization. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_scaledSinc_abs
    {baseAbs shapeAbs : Nat -> Real}
    (hBaseAbsNonneg :
      ∀ k : Nat, k <= 17 -> 0 <= baseAbs k)
    (hBaseAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 17 ->
          ‖iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeScaledSinc eta‖ <=
            baseAbs k)
    (hBudget :
      ∀ k : Nat, k <= 17 ->
        ‖primaryFiniteRow0Parent0Split100Sub0ShapeNormalizer‖ *
            powDerivMajorant 11 k baseAbs <=
          shapeAbs k) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∀ k : Nat, k <= 17 ->
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

end Step33
end PSDpd
end Q3
