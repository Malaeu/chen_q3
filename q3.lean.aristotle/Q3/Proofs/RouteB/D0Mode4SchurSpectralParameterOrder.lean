import Q3.Proofs.RouteB.D0Mode4JacobiRightTailMonotonicity
import Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization
import Mathlib.Analysis.Matrix.PosDef

/-!
# Spectral-parameter order of the exact mode-four Schur matrix

The finite left Jacobi block drops by exactly `Delta * I` when the shifted
spectral parameter grows by `Delta`.  The exact infinite-tail Schur correction
drops in the same direction because the right-tail ratio is monotone.  Hence
the full Hermitian Schur matrix at `Lambda_1` minus the matrix at `Lambda_2`
dominates `(Lambda_2 - Lambda_1) * I` in positive-semidefinite order.

This supplies the order mechanism needed by an inertia/root ladder.  It does
not supply endpoint inertia counts, root existence, PSWF index selection, a
finite-Fourier relation, or a CCM rate.
-/

open Set

noncomputable section

/-- The reversed finite left block depends affinely on `Lambda`, with slope
exactly `-I`. -/
theorem mode4HermitianLeftContinuantMatrix_sub_eq_smul_one
    (G Λ₁ Λ₂ : ℝ) (K : ℕ) :
    mode4HermitianLeftContinuantMatrix G Λ₁ K -
        mode4HermitianLeftContinuantMatrix G Λ₂ K =
      (Λ₂ - Λ₁) • (1 : Matrix (Fin K) (Fin K) ℝ) := by
  induction K with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simp [mode4HermitianLeftContinuantMatrix, mode4JacobiCenter]
      · have hj : (0 : Fin (n + 1)) ≠ j'.succ :=
          (Fin.succ_ne_zero j').symm
        simp [mode4HermitianLeftContinuantMatrix, hj]
      · have hi : i'.succ ≠ (0 : Fin (n + 1)) :=
          Fin.succ_ne_zero i'
        simp [mode4HermitianLeftContinuantMatrix, hi]
      · simpa [mode4HermitianLeftContinuantMatrix, Matrix.one_apply] using
          congrFun (congrFun ih i') j'

/-- Exact decomposition of the spectral-parameter drop: a scalar identity
plus one nonnegative correction on the newest Schur coordinate. -/
theorem mode4HermitianSchurMatrix_sub_eq_smul_one_add_diagonal
    (mProject K : ℕ) (Λ₁ Λ₂ : ℝ)
    (hK : 1 ≤ K) :
    mode4HermitianSchurMatrix mProject Λ₁ K -
        mode4HermitianSchurMatrix mProject Λ₂ K =
      (Λ₂ - Λ₁) • (1 : Matrix (Fin K) (Fin K) ℝ) +
        Matrix.diagonal (fun i : Fin K =>
          if i.val = 0 then
            mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
              (mode4RightTailLimit mProject Λ₂ K -
                mode4RightTailLimit mProject Λ₁ K)
          else 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;>
    refine Fin.cases ?_ (fun j' => ?_) j
  · simp [mode4HermitianSchurMatrix, mode4JacobiCenter]
    ring
  · have hj : (0 : Fin (n + 1)) ≠ j'.succ :=
      (Fin.succ_ne_zero j').symm
    simp [mode4HermitianSchurMatrix, hj]
  · have hi : i'.succ ≠ (0 : Fin (n + 1)) :=
      Fin.succ_ne_zero i'
    simp [mode4HermitianSchurMatrix, hi]
  · have hleft :=
      mode4HermitianLeftContinuantMatrix_sub_eq_smul_one
        (mode4JacobiG mProject) Λ₁ Λ₂ n
    simpa [mode4HermitianSchurMatrix, Matrix.one_apply,
      Matrix.diagonal_apply] using
      congrFun (congrFun hleft i') j'

/-- Growing `Lambda` lowers the exact Hermitian Schur matrix by at least the
same scalar multiple of the identity, in positive-semidefinite order. -/
theorem mode4HermitianSchurMatrix_spectralParameter_drop_posSemidef
    (mProject K : ℕ) (Λ₁ Λ₂ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ₁ : Λ₁ ≤ 20)
    (hΛ₂ : Λ₂ ≤ 20)
    (hΛ : Λ₁ ≤ Λ₂) :
    (mode4HermitianSchurMatrix mProject Λ₁ K -
        mode4HermitianSchurMatrix mProject Λ₂ K -
          (Λ₂ - Λ₁) • (1 : Matrix (Fin K) (Fin K) ℝ)).PosSemidef := by
  rw [mode4HermitianSchurMatrix_sub_eq_smul_one_add_diagonal
    mProject K Λ₁ Λ₂ (le_trans (by decide : 1 ≤ 3) hK)]
  simp only [add_sub_cancel_left]
  apply Matrix.PosSemidef.diagonal
  intro i
  change 0 ≤ if i.val = 0 then
    mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
      (mode4RightTailLimit mProject Λ₂ K -
        mode4RightTailLimit mProject Λ₁ K)
    else 0
  split_ifs
  · have hG : 0 < mode4JacobiG mProject := by
      unfold mode4JacobiG
      positivity
    have hU :
        0 ≤ mode4JacobiUpper
          (mode4JacobiG mProject) (K - 1) :=
      (mode4JacobiUpper_pos
        (mode4JacobiG mProject) (K - 1) hG).le
    have htail := mode4RightTailLimit_monotoneOn_lambda
      mProject K hm hK hsep hΛ₁ hΛ₂ hΛ
    exact mul_nonneg hU (sub_nonneg.mpr htail)
  · exact le_rfl

#print axioms mode4HermitianLeftContinuantMatrix_sub_eq_smul_one
#print axioms mode4HermitianSchurMatrix_sub_eq_smul_one_add_diagonal
#print axioms mode4HermitianSchurMatrix_spectralParameter_drop_posSemidef
