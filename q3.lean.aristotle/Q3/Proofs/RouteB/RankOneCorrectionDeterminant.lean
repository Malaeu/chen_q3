import Q3.Proofs.RouteB.RankOneCorrectionWeightedSymmetry

set_option linter.mathlibStandardSet false

noncomputable section
namespace Q3.RouteB

/-- Off the spectrum of `D`, the matrix determinant lemma factors the
determinant of the source rank-one correction.  Lattice/spectral points, where
the resolvent matrix is singular, remain a separate exact obligation. -/
theorem det_rankOneCorrection_sub_smul_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℝ) (xi eta : n → ℝ) (s : ℝ)
    (hA : IsUnit (D - s • (1 : Matrix n n ℝ)).det) :
    (rankOneCorrection D xi eta - s • (1 : Matrix n n ℝ)).det =
      (D - s • (1 : Matrix n n ℝ)).det *
        (1 +
          Matrix.replicateRow Unit eta *
            (D - s • (1 : Matrix n n ℝ))⁻¹ *
              Matrix.replicateCol Unit (-(Matrix.mulVec D xi))).det := by
  let A : Matrix n n ℝ := D - s • (1 : Matrix n n ℝ)
  let u : n → ℝ := Matrix.mulVec D xi
  have hmatrix :
      rankOneCorrection D xi eta - s • (1 : Matrix n n ℝ) =
        A + Matrix.replicateCol Unit (-u) *
          Matrix.replicateRow Unit eta := by
    rw [← Matrix.vecMulVec_eq (ι := Unit)]
    ext i j
    simp [rankOneCorrection, A, u, Matrix.vecMulVec_apply]
    ring
  rw [hmatrix]
  exact Matrix.det_add_replicateCol_mul_replicateRow hA (-u) eta

#print axioms det_rankOneCorrection_sub_smul_one

end Q3.RouteB
