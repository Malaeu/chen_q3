import Q3.Proofs.RouteB.H2aPenaltyCoercivity

set_option linter.mathlibStandardSet false

/-!
# Unit minimum eigenpair for a finite complex Hermitian matrix

This file exposes the unit normalization already present in Mathlib's
orthonormal Hermitian eigenbasis together with the variational minimum proved
by `H2aPenalty.hermitian_min_eig`.  It is a generic finite-dimensional lemma;
it supplies no project-specific spectral floor or source estimate.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped ComplexOrder BigOperators

/-- A finite complex Hermitian matrix has a unit eigenvector at its lowest
eigenvalue, and that eigenvalue is a global Rayleigh lower bound. -/
theorem hermitian_exists_unit_minimum_eigenpair
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Matrix ι ι ℂ)
    (hK : K.IsHermitian) :
    ∃ (epsilon : ℝ) (xi : ι → ℂ),
      star xi ⬝ᵥ xi = 1 ∧
      K *ᵥ xi = (epsilon : ℂ) • xi ∧
      ∀ x : ι → ℂ,
        epsilon * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ (K *ᵥ x)).re := by
  obtain ⟨mu, hmu⟩ :
      ∃ mu ∈ Set.range (fun j => hK.eigenvalues j),
        ∀ nu ∈ Set.range (fun j => hK.eigenvalues j), mu ≤ nu := by
    exact
      ⟨Finset.min'
          (Set.toFinset (Set.range fun j => hK.eigenvalues j))
          ⟨_, Set.mem_toFinset.mpr
            (Set.mem_range_self (Classical.arbitrary ι))⟩,
        Set.mem_toFinset.mp (Finset.min'_mem _ _),
        fun nu hnu =>
          Finset.min'_le _ _ (Set.mem_toFinset.mpr hnu)⟩
  obtain ⟨j, rfl⟩ := hmu.1
  let xi : ι → ℂ := hK.eigenvectorBasis j
  have hxi_unit : star xi ⬝ᵥ xi = 1 := by
    have hnorm : ‖WithLp.toLp 2 xi‖ = 1 := by
      simpa [xi] using hK.eigenvectorBasis.orthonormal.norm_eq_one j
    have hnorm_sq :
        ‖WithLp.toLp 2 xi‖ ^ 2 = (star xi ⬝ᵥ xi).re := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ),
        EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
      rfl
    have hre : (star xi ⬝ᵥ xi).re = 1 := by
      rw [hnorm] at hnorm_sq
      simpa using hnorm_sq.symm
    have him : (star xi ⬝ᵥ xi).im = 0 :=
      (Complex.le_def.mp (dotProduct_star_self_nonneg xi)).2.symm
    apply Complex.ext
    · simpa using hre
    · simpa using him
  refine ⟨hK.eigenvalues j, xi, hxi_unit, ?_, ?_⟩
  · simpa [xi] using hK.mulVec_eigenvectorBasis j
  · intro x
    set y :=
      (hK.eigenvectorUnitary : Matrix ι ι ℂ).conjTranspose.mulVec x
    have hy_norm :
        (star x ⬝ᵥ x).re = ∑ i, ‖y i‖ ^ 2 := by
      have hxy : star x ⬝ᵥ x = star y ⬝ᵥ y := by
        simp +zetaDelta at *
        simp +decide [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
          Matrix.star_mulVec, Matrix.IsHermitian.eigenvectorUnitary]
      simp_all +decide [Complex.normSq, Complex.sq_norm, dotProduct]
    have hy_energy :
        (star x ⬝ᵥ (K *ᵥ x)).re =
          ∑ i, hK.eigenvalues i * ‖y i‖ ^ 2 := by
      have hcomplex :
          star x ⬝ᵥ (K *ᵥ x) =
            ∑ i, hK.eigenvalues i * (star (y i) * y i) := by
        have hspectral :
            star x ⬝ᵥ (K *ᵥ x) =
              star y ⬝ᵥ
                (Matrix.diagonal
                  (fun i => (hK.eigenvalues i : ℂ)) *ᵥ y) := by
          have hKspec :
              K =
                (hK.eigenvectorUnitary : Matrix ι ι ℂ) *
                    Matrix.diagonal
                      (fun i => (hK.eigenvalues i : ℂ)) *
                  (hK.eigenvectorUnitary : Matrix ι ι ℂ).conjTranspose := by
            convert hK.spectral_theorem using 1
          simp +zetaDelta at *
          conv_lhs => rw [hKspec]
          simp +decide [Matrix.mul_assoc, Matrix.dotProduct_mulVec,
            Matrix.vecMul_mulVec, Matrix.star_mulVec]
        simp_all +decide [Matrix.mulVec, dotProduct, Finset.mul_sum,
          mul_assoc, mul_comm, mul_left_comm]
        simp +decide [Matrix.diagonal, mul_assoc, mul_comm, mul_left_comm,
          Finset.mul_sum]
      simp_all +decide [Complex.normSq, Complex.sq_norm]
    rw [hy_norm, hy_energy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right
        (hmu.2 _ (Set.mem_range_self i)) (sq_nonneg _)

#print axioms hermitian_exists_unit_minimum_eigenpair

end Q3.RouteB
