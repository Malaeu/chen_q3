import Mathlib.Analysis.InnerProductSpace.l2Space

set_option linter.mathlibStandardSet false

open Complex
open scoped ENNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Generic Hilbert-basis weighted tail

This module proves only the abstract complement Parseval identity and its
weighted finite-tail receiver.  It has no project imports and makes no claim
that a project-specific orthonormal family is complete or has controlled
weighted energy.
-/

/-- The representation coordinate of a finite Hilbert-basis residual is zero
on the retained set and unchanged off it. -/
private theorem hilbertBasis_repr_sub_basisPartialSum_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : HilbertBasis ℤ ℂ E)
    (s : Finset ℤ)
    (f : E)
    (n : ℤ) :
    b.repr
        (f - ∑ j ∈ s, inner ℂ (b j) f • b j) n =
      if n ∈ s then 0 else inner ℂ (b n) f := by
  classical
  rw [b.repr_apply_apply]
  by_cases hn : n ∈ s
  · rw [inner_sub_right]
    rw [show inner ℂ (b n)
          (∑ j ∈ s, inner ℂ (b j) f • b j) =
        inner ℂ (b n) f by
      exact b.orthonormal.inner_right_sum
        (fun j => inner ℂ (b j) f) hn]
    simp [hn]
  · have hsum :
        inner ℂ (b n)
          (∑ j ∈ s, inner ℂ (b j) f • b j) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [inner_smul_right]
      have hne : n ≠ j := by
        intro h
        subst j
        exact hn hj
      rw [b.orthonormal.inner_eq_zero hne, mul_zero]
    rw [inner_sub_right, hsum]
    simp [hn]

/-- Exact Parseval identity for the residual outside an arbitrary finite
subset of a complex Hilbert basis. -/
theorem norm_sub_basisPartialSum_sq_eq_tsum
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : HilbertBasis ℤ ℂ E)
    (s : Finset ℤ)
    (f : E) :
    ‖f - ∑ n ∈ s, inner ℂ (b n) f • b n‖ ^ 2 =
      ∑' n : ℤ,
        if n ∈ s then 0 else ‖inner ℂ (b n) f‖ ^ 2 := by
  classical
  let r : E := f - ∑ n ∈ s, inner ℂ (b n) f • b n
  have hsum := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num)
    (b.repr r)
  have hparseval :
      ‖b.repr r‖ ^ 2 = ∑' n : ℤ, ‖((b.repr r : ℤ → ℂ) n)‖ ^ 2 := by
    simpa using hsum.tsum_eq.symm
  calc
    ‖f - ∑ n ∈ s, inner ℂ (b n) f • b n‖ ^ 2 =
        ‖b.repr r‖ ^ 2 := by
      rw [b.repr.norm_map]
    _ = ∑' n : ℤ, ‖((b.repr r : ℤ → ℂ) n)‖ ^ 2 := hparseval
    _ = ∑' n : ℤ,
        if n ∈ s then 0 else ‖inner ℂ (b n) f‖ ^ 2 := by
      apply tsum_congr
      intro n
      rw [show r = f - ∑ j ∈ s, inner ℂ (b j) f • b j by rfl]
      rw [hilbertBasis_repr_sub_basisPartialSum_apply]
      split <;> simp_all

/-- A nonnegative summable weighted coefficient energy controls the finite
Hilbert-basis residual whenever the weight dominates one off the retained
set. -/
theorem norm_sub_basisPartialSum_sq_le_weightedEnergy
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : HilbertBasis ℤ ℂ E)
    (s : Finset ℤ)
    (f : E)
    (a : ℝ)
    (w : ℤ → ℝ)
    (ha : 0 ≤ a)
    (hw : ∀ n, 0 ≤ w n)
    (hband : ∀ n, n ∉ s → 1 ≤ a * w n)
    (hsum : Summable (fun n : ℤ =>
      w n * ‖inner ℂ (b n) f‖ ^ 2)) :
    ‖f - ∑ n ∈ s, inner ℂ (b n) f • b n‖ ^ 2 ≤
      a * ∑' n : ℤ, w n * ‖inner ℂ (b n) f‖ ^ 2 := by
  classical
  rw [norm_sub_basisPartialSum_sq_eq_tsum]
  rw [← tsum_mul_left]
  let lhs : ℤ → ℝ := fun n =>
    if n ∈ s then 0 else ‖inner ℂ (b n) f‖ ^ 2
  let rhs : ℤ → ℝ := fun n =>
    a * (w n * ‖inner ℂ (b n) f‖ ^ 2)
  have hlhs_nonneg : ∀ n, 0 ≤ lhs n := by
    intro n
    dsimp [lhs]
    split <;> positivity
  have hrhs_nonneg : ∀ n, 0 ≤ rhs n := by
    intro n
    exact mul_nonneg ha (mul_nonneg (hw n) (sq_nonneg _))
  have hpoint : ∀ n, lhs n ≤ rhs n := by
    intro n
    by_cases hn : n ∈ s
    · simp [lhs, rhs, hn, hrhs_nonneg n]
    · simp only [lhs, rhs, hn, if_false]
      have h := mul_le_mul_of_nonneg_right (hband n hn)
        (sq_nonneg ‖inner ℂ (b n) f‖)
      simpa [mul_assoc] using h
  have hrhs_sum : Summable rhs := hsum.mul_left a
  have hlhs_sum : Summable lhs :=
    Summable.of_nonneg_of_le hlhs_nonneg hpoint hrhs_sum
  exact Summable.tsum_le_tsum hpoint hlhs_sum hrhs_sum

#print axioms norm_sub_basisPartialSum_sq_eq_tsum
#print axioms norm_sub_basisPartialSum_sq_le_weightedEnergy

end Q3.RouteB.D0Pstar
