import Q3.Proofs.RouteB.RankOneCorrectionAllSpectralPoints

set_option linter.mathlibStandardSet false

noncomputable section
namespace Q3.RouteB

open Matrix
open scoped BigOperators

theorem diagonal_adjugate_mulVec_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (a u : n → ℝ) (k : n) :
    Matrix.mulVec (Matrix.diagonal a).adjugate u k =
      u k * ∏ j ∈ Finset.univ.erase k, a j := by
  classical
  rw [Matrix.adjugate_diagonal, Matrix.mulVec_diagonal]
  ring

theorem det_rankOneCorrection_diagonal_eq_neg_s_mul_lagrange
    {n : Type*} [Fintype n] [DecidableEq n]
    (lam xi : n → ℝ)
    (hnormalized : (1 : n → ℝ) ⬝ᵥ xi = 1)
    (s : ℝ) :
    (rankOneCorrection (Matrix.diagonal lam) xi (1 : n → ℝ) -
      s • (1 : Matrix n n ℝ)).det =
      (-s) * ∑ k, xi k *
        ∏ j ∈ Finset.univ.erase k, (lam j - s) := by
  classical
  have hdiag :
      Matrix.diagonal lam - s • (1 : Matrix n n ℝ) =
        Matrix.diagonal (fun k => lam k - s) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  have hmul :
      Matrix.mulVec (Matrix.diagonal lam) xi = fun k => lam k * xi k := by
    ext k
    exact Matrix.mulVec_diagonal lam xi k
  rw [det_rankOneCorrection_sub_smul_one_all, hdiag, hmul,
    Matrix.det_diagonal]
  simp only [dotProduct, Pi.one_apply, one_mul]
  simp_rw [diagonal_adjugate_mulVec_apply]
  have hprod (k : n) :
      (∏ j, (lam j - s)) =
        (lam k - s) * ∏ j ∈ Finset.univ.erase k, (lam j - s) := by
    symm
    exact Finset.mul_prod_erase Finset.univ (fun j => lam j - s)
      (Finset.mem_univ k)
  have hsum : ∑ k, xi k = 1 := by
    simpa [dotProduct] using hnormalized
  have hP :
      (∏ j, (lam j - s)) =
        ∑ k, xi k * ((lam k - s) *
          ∏ j ∈ Finset.univ.erase k, (lam j - s)) := by
    calc
      (∏ j, (lam j - s)) = 1 * ∏ j, (lam j - s) := by rw [one_mul]
      _ = (∑ k, xi k) * ∏ j, (lam j - s) := by rw [hsum]
      _ = ∑ k, xi k * ∏ j, (lam j - s) := by rw [Finset.sum_mul]
      _ = ∑ k, xi k * ((lam k - s) *
            ∏ j ∈ Finset.univ.erase k, (lam j - s)) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hprod k]
  calc
    (∏ j, (lam j - s)) -
        ∑ k, lam k * xi k * ∏ j ∈ Finset.univ.erase k, (lam j - s) =
      ∑ k, xi k * ((lam k - s) *
          ∏ j ∈ Finset.univ.erase k, (lam j - s)) -
        ∑ k, lam k * xi k *
          ∏ j ∈ Finset.univ.erase k, (lam j - s) := by
            rw [hP]
    _ = (-s) * ∑ k, xi k *
          ∏ j ∈ Finset.univ.erase k, (lam j - s) := by
            rw [← Finset.sum_sub_distrib, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

#print axioms diagonal_adjugate_mulVec_apply
#print axioms det_rankOneCorrection_diagonal_eq_neg_s_mul_lagrange

end Q3.RouteB
