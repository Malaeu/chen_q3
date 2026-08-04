import Q3.Proofs.RouteB.RankOneCorrectionLagrangeIdentity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option linter.mathlibStandardSet false

noncomputable section
namespace Q3.RouteB

open Matrix Polynomial
open scoped BigOperators

noncomputable def sourceLagrangePolynomial
    {n : Type*} [Fintype n] [DecidableEq n]
    (lam xi : n → ℝ) : ℝ[X] :=
  ∑ k, Polynomial.C (xi k) *
    ∏ j ∈ Finset.univ.erase k, (Polynomial.C (lam j) - Polynomial.X)

@[simp] theorem sourceLagrangePolynomial_eval
    {n : Type*} [Fintype n] [DecidableEq n]
    (lam xi : n → ℝ) (s : ℝ) :
    (sourceLagrangePolynomial lam xi).eval s =
      ∑ k, xi k * ∏ j ∈ Finset.univ.erase k, (lam j - s) := by
  classical
  rw [sourceLagrangePolynomial, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp

theorem det_sub_smul_one_eq_negOnePow_mul_charpoly_eval
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (s : ℝ) :
    (M - s • (1 : Matrix n n ℝ)).det =
      (-1 : ℝ) ^ Fintype.card n * M.charpoly.eval s := by
  calc
    (M - s • (1 : Matrix n n ℝ)).det =
        (-(s • (1 : Matrix n n ℝ) - M)).det := by
          congr 1
          abel
    _ = (-1 : ℝ) ^ Fintype.card n *
        (s • (1 : Matrix n n ℝ) - M).det := by
          rw [Matrix.det_neg]
    _ = (-1 : ℝ) ^ Fintype.card n * M.charpoly.eval s := by
          rw [Matrix.eval_charpoly, Matrix.smul_one_eq_diagonal,
            Matrix.scalar_apply]

theorem sourceLagrangePolynomial_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (lam xi : n → ℝ)
    (hnormalized : (1 : n → ℝ) ⬝ᵥ xi = 1) :
    Polynomial.C ((-1 : ℝ) ^ Fintype.card n) *
        (rankOneCorrection (Matrix.diagonal lam) xi
          (1 : n → ℝ)).charpoly =
      -Polynomial.X * sourceLagrangePolynomial lam xi := by
  apply Polynomial.funext
  intro s
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_X]
  rw [sourceLagrangePolynomial_eval]
  rw [← det_sub_smul_one_eq_negOnePow_mul_charpoly_eval]
  exact det_rankOneCorrection_diagonal_eq_neg_s_mul_lagrange
    lam xi hnormalized s

#print axioms sourceLagrangePolynomial_eval
#print axioms sourceLagrangePolynomial_charpoly_factor

end Q3.RouteB
