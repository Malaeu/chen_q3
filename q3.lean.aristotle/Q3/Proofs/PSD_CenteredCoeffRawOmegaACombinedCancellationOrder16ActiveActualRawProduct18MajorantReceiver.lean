import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Conditional RawProduct18 Leibniz receiver for the Step33A.1-A degree-0 gate.

The previous bridge reduces the missing D17 bound for `ComponentProductActual`
to a D18 bound for `RawProductActual = OmegaActual * ShapeSqActual`.  This file
adds only the product-rule receiver.  It deliberately keeps the factor bounds
as hypotheses: the live sources still needed are proof-grade derivative bounds
for `OmegaActual` and `ShapeSqActual` through order 18.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Leibniz majorant for the order-18 derivative of the raw product. -/
def primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant
    (omegaAbs shapeSqAbs : Nat -> Real) : Real :=
  ∑ i ∈ Finset.range (18 + 1),
    (Nat.choose 18 i : Real) * omegaAbs i * shapeSqAbs (18 - i)

private theorem primaryFiniteRow0Parent0Split100Sub0_product_order18_abs_of_factor_bounds
    {f g : Real -> Real} {fAbs gAbs : Nat -> Real} {eta : Real}
    (hf : ContDiff Real 18 f)
    (hg : ContDiff Real 18 g)
    (hfAbsNonneg : ∀ k : Nat, k <= 18 -> 0 <= fAbs k)
    (hfAbs :
      ∀ k : Nat, k <= 18 -> ‖iteratedDeriv k f eta‖ <= fAbs k)
    (hgAbs :
      ∀ k : Nat, k <= 18 -> ‖iteratedDeriv k g eta‖ <= gAbs k) :
    ‖iteratedDeriv 18 (fun t : Real => f t * g t) eta‖ <=
      ∑ i ∈ Finset.range (18 + 1),
        (Nat.choose 18 i : Real) * fAbs i * gAbs (18 - i) := by
  have hmulF :
      ‖iteratedFDeriv Real 18 (fun y : Real => f y * g y) eta‖ <=
        ∑ i ∈ Finset.range (18 + 1),
          (Nat.choose 18 i : Real) *
            ‖iteratedFDeriv Real i f eta‖ *
            ‖iteratedFDeriv Real (18 - i) g eta‖ := by
    exact norm_iteratedFDeriv_mul_le
      (𝕜 := Real) (f := f) (g := g) hf hg eta (n := 18) (by simp)
  have hmulD :
      ‖iteratedDeriv 18 (fun y : Real => f y * g y) eta‖ <=
        ∑ i ∈ Finset.range (18 + 1),
          (Nat.choose 18 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (18 - i) g eta‖ := by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hmulF
  have hsum :
      (∑ i ∈ Finset.range (18 + 1),
          (Nat.choose 18 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (18 - i) g eta‖) <=
        ∑ i ∈ Finset.range (18 + 1),
          (Nat.choose 18 i : Real) * fAbs i * gAbs (18 - i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i <= 18 :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hni_le : 18 - i <= 18 := Nat.sub_le 18 i
    have hchoose_nonneg : 0 <= (Nat.choose 18 i : Real) := by positivity
    have hprod :
        ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (18 - i) g eta‖ <=
          fAbs i * gAbs (18 - i) := by
      exact mul_le_mul
        (hfAbs i hi_le)
        (hgAbs (18 - i) hni_le)
        (norm_nonneg _)
        (hfAbsNonneg i hi_le)
    calc
      (Nat.choose 18 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (18 - i) g eta‖ =
          (Nat.choose 18 i : Real) *
            (‖iteratedDeriv i f eta‖ *
              ‖iteratedDeriv (18 - i) g eta‖) := by ring
      _ <= (Nat.choose 18 i : Real) * (fAbs i * gAbs (18 - i)) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nonneg
      _ = (Nat.choose 18 i : Real) * fAbs i * gAbs (18 - i) := by ring
  exact le_trans hmulD hsum

theorem primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs
    {omegaAbs shapeSqAbs : Nat -> Real}
    (hOmegaCont :
      ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual)
    (hShapeSqCont :
      ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
    (hOmegaAbsNonneg :
      ∀ k : Nat, k <= 18 -> 0 <= omegaAbs k)
    (hOmegaAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 18 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual
              eta‖ <= omegaAbs k)
    (hShapeSqAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 18 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              eta‖ <= shapeSqAbs k) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 18
          primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant
          omegaAbs shapeSqAbs := by
  intro eta hEta
  exact
    primaryFiniteRow0Parent0Split100Sub0_product_order18_abs_of_factor_bounds
      (f := primaryFiniteRow0Parent0Split100Sub0OmegaActual)
      (g := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
      (fAbs := omegaAbs)
      (gAbs := shapeSqAbs)
      (eta := eta)
      hOmegaCont
      hShapeSqCont
      hOmegaAbsNonneg
      (fun k hk => hOmegaAbs eta hEta k hk)
      (fun k hk => hShapeSqAbs eta hEta k hk)

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_factor_derivative_abs
    {omegaAbs shapeSqAbs : Nat -> Real}
    (hOmegaCont :
      ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual)
    (hShapeSqCont :
      ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
    (hOmegaAbsNonneg :
      ∀ k : Nat, k <= 18 -> 0 <= omegaAbs k)
    (hOmegaAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 18 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual
              eta‖ <= omegaAbs k)
    (hShapeSqAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 18 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              eta‖ <= shapeSqAbs k) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant
          omegaAbs shapeSqAbs := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs
      (primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant
        omegaAbs shapeSqAbs)
      (primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs
        hOmegaCont hShapeSqCont hOmegaAbsNonneg hOmegaAbs hShapeSqAbs)

end Step33
end PSDpd
end Q3
