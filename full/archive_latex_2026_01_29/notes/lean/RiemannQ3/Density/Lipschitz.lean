import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Real BigOperators
-- (no explicit measure annotations; use default volume)

namespace RiemannQ3
namespace Density

noncomputable section

/-!
# RiemannQ3.Density.Lipschitz

Abstract Lipschitz control for the functional `Q` on a compact interval `[-K,K]` plus a
finite set of point evaluations (prime part). We work in a lightweight, parameterized
setting sufficient for Q3 accounting.
-/

structure QSpec (α : Type*) where
  K : ℝ
  archC : ℝ
  nodes : Finset α
  ξ : α → ℝ
  w : α → ℝ
  nodes_in : ∀ i ∈ nodes, |ξ i| ≤ K

def Q {α} (S : QSpec α) (Φ : ℝ → ℝ) : ℝ :=
  S.archC * (∫ x in (-S.K)..S.K, Φ x) + S.nodes.sum (fun i => S.w i * Φ (S.ξ i))

/-! A clean Lipschitz bound in terms of a uniform bound `B` on `|Φ₁-Φ₂|` over `[-K,K]`
and at all active nodes. -/

theorem lipschitz_bound {α} (S : QSpec α) {Φ₁ Φ₂ : ℝ → ℝ} {B : ℝ}
    (hB_int : ∀ x ∈ Set.uIoc (-S.K) (S.K), ‖Φ₁ x - Φ₂ x‖ ≤ B)
    (hB_nodes : ∀ i ∈ S.nodes, ‖Φ₁ (S.ξ i) - Φ₂ (S.ξ i)‖ ≤ B)
    (hInt₁ : IntervalIntegrable Φ₁ MeasureTheory.volume (-S.K) (S.K))
    (hInt₂ : IntervalIntegrable Φ₂ MeasureTheory.volume (-S.K) (S.K)) :
    |Q S Φ₁ - Q S Φ₂|
      ≤ (|S.archC| * (2 * |S.K|)) * B + (S.nodes.sum (fun i => |S.w i|)) * B := by
  classical
  -- Triangle bound on the difference: split into integral part and prime-sum part
  set IΔ := (∫ x in (-S.K)..S.K, Φ₁ x) - (∫ x in (-S.K)..S.K, Φ₂ x) with hIΔ
  set SΔ := S.nodes.sum (fun i => S.w i * Φ₁ (S.ξ i))
              - S.nodes.sum (fun i => S.w i * Φ₂ (S.ξ i)) with hSΔ
  have h_eq : Q S Φ₁ - Q S Φ₂ = S.archC * IΔ + SΔ := by
    simp [Q, IΔ, SΔ, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
  have h_split : |Q S Φ₁ - Q S Φ₂| ≤ |S.archC * IΔ| + |SΔ| := by
    have := abs_add_le (S.archC * IΔ) SΔ
    simpa [h_eq] using this
  -- Rewrite integral/sum differences in terms of the pointwise difference.
  have hIntDeltaEq : IΔ = ∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x) := by
    simpa [IΔ] using (intervalIntegral.integral_sub (a := (-S.K)) (b := S.K)
      (f := Φ₁) (g := Φ₂) hInt₁ hInt₂).symm
  have h_sum_diff :
      |S.nodes.sum (fun i => S.w i * Φ₁ (S.ξ i))
          - S.nodes.sum (fun i => S.w i * Φ₂ (S.ξ i))|
        = |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))| := by
    simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
      using congrArg abs
        ((Finset.sum_sub_distrib (s := S.nodes)
          (f := fun i => S.w i * Φ₁ (S.ξ i))
          (g := fun i => S.w i * Φ₂ (S.ξ i))).symm)
  -- Bound the integral term by `B * |2K|` and sum by `(∑ |w_i|) * B`.
  have h_int_bound :
      ‖∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x)‖ ≤ B * |S.K - (-S.K)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (-S.K)) (b := S.K)
      (f := fun x => Φ₁ x - Φ₂ x) (C := B) (by simpa using hB_int)
  have h_len : |S.K - (-S.K)| = (2 : ℝ) * |S.K| := by
    have : S.K - (-S.K) = 2 * S.K := by simp [sub_eq_add_neg, two_mul]
    simp [this, abs_mul]
  have h_len_add : |S.K + S.K| = (2 : ℝ) * |S.K| := by
    simpa [sub_eq_add_neg] using h_len
  -- Sum term bound: `|∑ a| ≤ ∑ |a|` then bound each summand by `|w_i| * B`.
  have hsum_abs :
      |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))|
        ≤ S.nodes.sum (fun i => |S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs (s := S.nodes)
        (f := fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))))
  have hsum_step :
      S.nodes.sum (fun i => |S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))|)
        ≤ S.nodes.sum (fun i => B * |S.w i|) := by
    refine Finset.sum_le_sum ?_ 
    intro i hi
    have hb : |Φ₁ (S.ξ i) - Φ₂ (S.ξ i)| ≤ B := by
      simpa [Real.norm_eq_abs] using hB_nodes i hi
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc]
      using (mul_le_mul_of_nonneg_left hb (abs_nonneg (S.w i)))
  have hsum' :
      |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))|
        ≤ (S.nodes.sum fun i => B * |S.w i|) := hsum_abs.trans hsum_step
  have hsumFactor :
      S.nodes.sum (fun i => B * |S.w i|)
        = B * (S.nodes.sum fun i => |S.w i|) := by
    classical
    change (∑ i ∈ S.nodes, B * |S.w i|)
        = B * (∑ i ∈ S.nodes, |S.w i|)
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using
        (Finset.mul_sum (s := S.nodes)
          (f := fun i => |S.w i|) (a := B)).symm
  have hsum'' :
      |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))|
        ≤ (S.nodes.sum fun i => |S.w i|) * B := by
    -- factor `B` out of the sum on the right
    have :
        |S.nodes.sum fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i))|
          ≤ B * (S.nodes.sum fun i => |S.w i|) := by
      simpa [hsumFactor] using hsum'
    simpa [mul_comm] using this
  -- Combine by triangle inequality via parts; integral part:
  have hIntAbs : |∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x)| ≤ B * (2 * |S.K|) := by
    have :
        |∫ x in (-S.K)..S.K, (Φ₁ x - Φ₂ x)| ≤ B * |S.K + S.K| := by
      simpa [Real.norm_eq_abs, sub_eq_add_neg] using h_int_bound
    simpa [h_len_add] using this
  have hIntPart : |S.archC * IΔ| ≤ (|S.archC| * (2 * |S.K|)) * B := by
    have hI : |IΔ| ≤ B * (2 * |S.K|) := by simpa [hIntDeltaEq] using hIntAbs
    have := mul_le_mul_of_nonneg_left hI (abs_nonneg S.archC)
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hSumEq : |SΔ| = |S.nodes.sum (fun i => S.w i * (Φ₁ (S.ξ i) - Φ₂ (S.ξ i)))| := by
    simpa [hSΔ, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
      using congrArg abs
        ((Finset.sum_sub_distrib (s := S.nodes)
          (f := fun i => S.w i * Φ₁ (S.ξ i))
          (g := fun i => S.w i * Φ₂ (S.ξ i))).symm)
  have hSumPart : |SΔ| ≤ (S.nodes.sum fun i => |S.w i|) * B := by
    -- use previous `hsum''`
    simpa [hSumEq] using hsum''
  exact (le_trans h_split (add_le_add hIntPart hSumPart))

end -- section

end Density
end RiemannQ3
