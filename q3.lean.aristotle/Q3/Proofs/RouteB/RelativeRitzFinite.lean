import Mathlib

set_option linter.mathlibStandardSet false

/-!
# Finite relative Ritz bound

This file proves only the standalone finite-dimensional Hermitian-matrix
interface selected for Goal 058. It does not modify or consume the existing
trial-complement floor predicate and makes no cofinal or asymptotic claim.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped ComplexOrder BigOperators

private theorem euclidean_inner_toLp_eq_star_dotProduct
    {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = star u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

private theorem euclidean_norm_sq_toLp_eq_star_dotProduct_re
    {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    ‖WithLp.toLp 2 u‖ ^ 2 = (star u ⬝ᵥ u).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), euclidean_inner_toLp_eq_star_dotProduct]
  rfl

private theorem hermitian_star_dotProduct_mulVec
    {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (u v : ι → ℂ) :
    star u ⬝ᵥ (K *ᵥ v) = star (K *ᵥ u) ⬝ᵥ v := by
  simp +decide [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm]
  rw [Finset.sum_comm]
  congr
  ext i
  congr
  ext j
  rw [← hK.apply]
  simp +decide [mul_comm, mul_left_comm]

/-- For a unit eigenvector at the bottom eigenvalue, an orthogonal Rayleigh
floor at the next level bounds the projective defect of every unit trial
vector by its relative Rayleigh excess. -/
theorem hermitian_relative_ritz_projective_defect_le_rayleigh_excess_div_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (xi q : ι → ℂ) (lambda1 lambda2 : ℝ)
    (hK : K.IsHermitian)
    (hxi_eig : K *ᵥ xi = (lambda1 : ℂ) • xi)
    (hxi_unit : star xi ⬝ᵥ xi = 1)
    (_hlambda1 : 0 < lambda1)
    (hgap : lambda1 < lambda2)
    (horthogonal_floor : ∀ u : ι → ℂ,
      star xi ⬝ᵥ u = 0 →
      lambda2 * (star u ⬝ᵥ u).re ≤ (star u ⬝ᵥ (K *ᵥ u)).re)
    (hq_unit : star q ⬝ᵥ q = 1) :
    1 - ‖star xi ⬝ᵥ q‖ ^ 2 ≤
      ((star q ⬝ᵥ (K *ᵥ q)).re - lambda1) / (lambda2 - lambda1) := by
  let c : ℂ := star xi ⬝ᵥ q
  let u : ι → ℂ := q - c • xi
  have hxi_u : star xi ⬝ᵥ u = 0 := by
    simp [u, c, dotProduct_sub, dotProduct_smul, hxi_unit]
  let u2 : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  have hq_decomp : c • xi + u = q := by simp [u]
  have hcxi_orth_u :
      inner ℂ (WithLp.toLp 2 (c • xi)) u2 = 0 := by
    rw [euclidean_inner_toLp_eq_star_dotProduct]
    simp [hxi_u]
  have hq_pythagoras :
      ‖WithLp.toLp 2 q‖ ^ 2 =
        ‖WithLp.toLp 2 (c • xi)‖ ^ 2 + ‖u2‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (WithLp.toLp 2 (c • xi)) u2 hcxi_orth_u
    have hdecomp : WithLp.toLp 2 q =
        WithLp.toLp 2 (c • xi) + u2 := by
      ext j
      exact congrFun hq_decomp.symm j
    rw [← hdecomp] at h
    simpa [pow_two] using h
  have hq_norm_sq : ‖WithLp.toLp 2 q‖ ^ 2 = 1 := by
    rw [euclidean_norm_sq_toLp_eq_star_dotProduct_re]
    simpa using congrArg Complex.re hq_unit
  have hxi_norm_sq : ‖WithLp.toLp 2 xi‖ ^ 2 = 1 := by
    rw [euclidean_norm_sq_toLp_eq_star_dotProduct_re]
    simpa using congrArg Complex.re hxi_unit
  have hcxi_norm_sq :
      ‖WithLp.toLp 2 (c • xi)‖ ^ 2 = ‖c‖ ^ 2 := by
    change ‖c • (WithLp.toLp 2 xi)‖ ^ 2 = ‖c‖ ^ 2
    rw [norm_smul, mul_pow, hxi_norm_sq, mul_one]
  have hdefect : 1 - ‖c‖ ^ 2 = ‖u2‖ ^ 2 := by
    rw [hq_norm_sq, hcxi_norm_sq] at hq_pythagoras
    linarith
  have hKu_cross : star xi ⬝ᵥ (K *ᵥ u) = 0 := by
    rw [hermitian_star_dotProduct_mulVec K hK xi u, hxi_eig]
    simp [hxi_u]
  have huKxi : star u ⬝ᵥ (K *ᵥ xi) = 0 := by
    rw [hxi_eig]
    have hui : star u ⬝ᵥ xi = 0 := by
      rw [Matrix.star_dotProduct] at hxi_u
      exact star_eq_zero.mp hxi_u
    simp [hui]
  have henergy_decomp :
      (star q ⬝ᵥ (K *ᵥ q)).re =
        lambda1 * ‖c‖ ^ 2 + (star u ⬝ᵥ (K *ᵥ u)).re := by
    have hmain : star (c • xi) ⬝ᵥ (K *ᵥ (c • xi)) =
        (lambda1 : ℂ) * (Complex.normSq c : ℂ) := by
      rw [Matrix.mulVec_smul, hxi_eig]
      simp [dotProduct_smul, hxi_unit, smul_eq_mul,
        Complex.normSq_eq_conj_mul_self]
      ring
    have hcross1 : star (c • xi) ⬝ᵥ (K *ᵥ u) = 0 := by
      simp [hKu_cross]
    have hcross2 : star u ⬝ᵥ (K *ᵥ (c • xi)) = 0 := by
      rw [Matrix.mulVec_smul]
      simp [huKxi]
    rw [← hq_decomp]
    rw [Matrix.mulVec_add, star_add, add_dotProduct, dotProduct_add,
      hmain, hcross1]
    rw [dotProduct_add, hcross2]
    simp [Complex.sq_norm, Complex.mul_re]
  have hu_norm : (star u ⬝ᵥ u).re = ‖u2‖ ^ 2 := by
    exact (euclidean_norm_sq_toLp_eq_star_dotProduct_re u).symm
  have hfloor := horthogonal_floor u hxi_u
  rw [hu_norm] at hfloor
  apply (le_div_iff₀ (sub_pos.mpr hgap)).2
  rw [show star xi ⬝ᵥ q = c by rfl, hdefect, henergy_decomp]
  nlinarith

#print axioms
  hermitian_relative_ritz_projective_defect_le_rayleigh_excess_div_gap

end Q3.RouteB
