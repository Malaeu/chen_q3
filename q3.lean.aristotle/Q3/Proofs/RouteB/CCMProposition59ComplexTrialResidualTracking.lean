import Mathlib

set_option linter.mathlibStandardSet false

/-!
# Finite complex residual-to-projective tracking

This file proves a generic finite-dimensional receiver.  A positive Rayleigh
floor for `K` on the orthogonal complement of a chosen unit eigenvector turns
the residual of a unit trial vector into a quantitative projective-distance
bound.  No source arithmetic, cofinal estimate, or Route B promotion is used.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped ComplexOrder BigOperators

private theorem euclidean_inner_toLp_eq_star_dotProduct
    {ι : Type*} [Fintype ι]
    (u v : ι → ℂ) :
    inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = star u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

private theorem euclidean_norm_sq_toLp_eq_star_dotProduct_re
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ) :
    ‖WithLp.toLp 2 u‖ ^ 2 = (star u ⬝ᵥ u).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),
    euclidean_inner_toLp_eq_star_dotProduct]
  rfl

/-- Let `xi` be a unit eigenvector of a finite Hermitian matrix `K`.  If the
Rayleigh form of `K` is at least `a + beta` on `xi⊥`, then the residual of any
unit trial vector `q` at the real center `a` controls its squared projective
defect from the line spanned by `xi`.

The floor is deliberately stated directly on `xi⊥`; this theorem neither
constructs the eigenvector nor supplies the floor. -/
theorem hermitian_unit_eigen_projective_defect_le_residual_sq_div_beta_sq_of_orthogonal_floor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ)
    (xi q r : ι → ℂ)
    (epsilon a beta : ℝ)
    (hK : K.IsHermitian)
    (hxi_unit : star xi ⬝ᵥ xi = 1)
    (hxi_eig : K *ᵥ xi = (epsilon : ℂ) • xi)
    (hq_unit : star q ⬝ᵥ q = 1)
    (hr : r = K *ᵥ q - (a : ℂ) • q)
    (hbeta : 0 < beta)
    (hfloor : ∀ x : ι → ℂ,
      star xi ⬝ᵥ x = 0 →
      (a + beta) * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (K *ᵥ x)).re) :
    1 - Complex.normSq (star xi ⬝ᵥ q) ≤
      (star r ⬝ᵥ r).re / beta ^ 2 := by
  let c : ℂ := star xi ⬝ᵥ q
  let x : ι → ℂ := q - c • xi
  let y : ι → ℂ := K *ᵥ x - (a : ℂ) • x

  have hxi_x : star xi ⬝ᵥ x = 0 := by
    simp [x, c, dotProduct_sub, dotProduct_smul, hxi_unit]

  have hKadj (u v : ι → ℂ) :
      star u ⬝ᵥ (K *ᵥ v) = star (K *ᵥ u) ⬝ᵥ v := by
    simp +decide [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm]
    rw [Finset.sum_comm]
    congr
    ext
    congr
    ext
    rw [← hK.apply]
    simp +decide [mul_comm, mul_left_comm]

  have hxi_y : star xi ⬝ᵥ y = 0 := by
    calc
      star xi ⬝ᵥ y =
          star xi ⬝ᵥ (K *ᵥ x) -
            star xi ⬝ᵥ ((a : ℂ) • x) := by
              simp only [y, dotProduct_sub]
      _ = star (K *ᵥ xi) ⬝ᵥ x -
            star xi ⬝ᵥ ((a : ℂ) • x) := by rw [hKadj xi x]
      _ = 0 := by simp [hxi_eig, hxi_x]

  have hshift :
      (star x ⬝ᵥ y).re =
        (star x ⬝ᵥ (K *ᵥ x)).re -
          a * (star x ⬝ᵥ x).re := by
    simp [y, dotProduct_sub, dotProduct_smul, Complex.mul_re]

  have hcoercive :
      beta * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ y).re := by
    have hx_floor := hfloor x hxi_x
    rw [hshift]
    nlinarith

  let x₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  let y₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 y
  let r₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 r

  have hx_norm_sq : ‖x₂‖ ^ 2 = (star x ⬝ᵥ x).re := by
    simpa [x₂] using euclidean_norm_sq_toLp_eq_star_dotProduct_re x

  have hcauchy : (star x ⬝ᵥ y).re ≤ ‖x₂‖ * ‖y₂‖ := by
    change (star x ⬝ᵥ y).re ≤
      ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖
    rw [← euclidean_inner_toLp_eq_star_dotProduct]
    change RCLike.re
        (inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y)) ≤
      ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖
    exact re_inner_le_norm _ _

  have hbeta_norm_sq_le : beta * ‖x₂‖ ^ 2 ≤ ‖x₂‖ * ‖y₂‖ := by
    rw [hx_norm_sq]
    exact hcoercive.trans hcauchy

  have hbeta_norm_le : beta * ‖x₂‖ ≤ ‖y₂‖ := by
    rcases eq_or_lt_of_le (norm_nonneg x₂) with hx_zero | hx_pos
    · rw [← hx_zero]
      simp
    · apply le_of_mul_le_mul_left _ hx_pos
      nlinarith [hbeta_norm_sq_le]

  have hbeta_sq_norm_sq_le : beta ^ 2 * ‖x₂‖ ^ 2 ≤ ‖y₂‖ ^ 2 := by
    have hsquare : (beta * ‖x₂‖) ^ 2 ≤ ‖y₂‖ ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg hbeta.le (norm_nonneg x₂))
        (norm_nonneg y₂)).2 hbeta_norm_le
    simpa [mul_pow] using hsquare

  have hq_decomp : c • xi + x = q := by
    simp [x]

  have hcxi_orth_x :
      inner ℂ (WithLp.toLp 2 (c • xi)) (WithLp.toLp 2 x) = 0 := by
    rw [euclidean_inner_toLp_eq_star_dotProduct]
    simp [hxi_x]

  have hq_pythagoras :
      ‖WithLp.toLp 2 q‖ ^ 2 =
        ‖WithLp.toLp 2 (c • xi)‖ ^ 2 + ‖x₂‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (WithLp.toLp 2 (c • xi)) (WithLp.toLp 2 x) hcxi_orth_x
    have hq_decomp₂ :
        WithLp.toLp 2 q =
          WithLp.toLp 2 (c • xi) + WithLp.toLp 2 x := by
      ext j
      exact congrFun hq_decomp.symm j
    rw [← hq_decomp₂] at h
    simpa [x₂, pow_two] using h

  have hq_norm_sq : ‖WithLp.toLp 2 q‖ ^ 2 = 1 := by
    rw [euclidean_norm_sq_toLp_eq_star_dotProduct_re]
    simpa using congrArg Complex.re hq_unit

  have hxi_norm_sq : ‖WithLp.toLp 2 xi‖ ^ 2 = 1 := by
    rw [euclidean_norm_sq_toLp_eq_star_dotProduct_re]
    simpa using congrArg Complex.re hxi_unit

  have hcxi_norm_sq :
      ‖WithLp.toLp 2 (c • xi)‖ ^ 2 = Complex.normSq c := by
    change ‖c • (WithLp.toLp 2 xi)‖ ^ 2 = Complex.normSq c
    rw [norm_smul, mul_pow, hxi_norm_sq, mul_one, Complex.sq_norm]

  have hdefect :
      1 - Complex.normSq c = ‖x₂‖ ^ 2 := by
    rw [hq_norm_sq, hcxi_norm_sq] at hq_pythagoras
    linarith

  let d : ℂ := ((epsilon - a : ℝ) : ℂ) * c
  have hr_decomp : r = d • xi + y := by
    rw [hr]
    ext j
    simp [d, x, y, Matrix.mulVec_sub, Matrix.mulVec_smul, hxi_eig]
    ring

  have hdxi_orth_y :
      inner ℂ (WithLp.toLp 2 (d • xi)) (WithLp.toLp 2 y) = 0 := by
    rw [euclidean_inner_toLp_eq_star_dotProduct]
    simp [hxi_y]

  have hr_pythagoras :
      ‖r₂‖ ^ 2 =
        ‖WithLp.toLp 2 (d • xi)‖ ^ 2 + ‖y₂‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (WithLp.toLp 2 (d • xi)) (WithLp.toLp 2 y) hdxi_orth_y
    have hr_decomp₂ :
        WithLp.toLp 2 r =
          WithLp.toLp 2 (d • xi) + WithLp.toLp 2 y := by
      ext j
      exact congrFun hr_decomp j
    rw [← hr_decomp₂] at h
    simpa [r₂, y₂, pow_two] using h

  have hy_norm_sq_le : ‖y₂‖ ^ 2 ≤ ‖r₂‖ ^ 2 := by
    rw [hr_pythagoras]
    nlinarith [sq_nonneg ‖WithLp.toLp 2 (d • xi)‖]

  have hr_norm_sq : ‖r₂‖ ^ 2 = (star r ⬝ᵥ r).re := by
    simpa [r₂] using euclidean_norm_sq_toLp_eq_star_dotProduct_re r

  apply (le_div_iff₀ (sq_pos_of_pos hbeta)).2
  rw [show star xi ⬝ᵥ q = c by rfl, hdefect, ← hr_norm_sq]
  nlinarith [hbeta_sq_norm_sq_le, hy_norm_sq_le]

#print axioms
  hermitian_unit_eigen_projective_defect_le_residual_sq_div_beta_sq_of_orthogonal_floor

end Q3.RouteB
