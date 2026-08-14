import Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Simple kernel at an exact mode-four Schur root

Consecutive finite-left Jacobi continuants cannot vanish simultaneously,
because their three-term recurrence has a strictly positive coupling.  At a
zero of the exact Schur/root function, this makes the `(K-1)` principal minor
invertible.  The full `K` by `K` Hermitian Schur matrix therefore has rank at
least `K-1`, so its kernel has dimension at most one.

This proves nullity simplicity of an already-supplied exact matching root.  It
does not construct a root, identify its PSWF index, or prove a Fourier or CCM
rate statement.
-/

noncomputable section

private theorem mode4JacobiLower_pos_of_one_le
    (G : ℝ) (q : ℕ) (hG : 0 < G) (hq : 1 ≤ q) :
    0 < mode4JacobiLower G q := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  unfold mode4JacobiLower mode4JacobiIndex
  apply div_pos
  · exact mul_pos (mul_pos hG (by linarith)) (by linarith)
  · exact mul_pos (by linarith) (by linarith)

/-- Two consecutive finite-left continuants cannot both vanish. -/
theorem mode4ScaledLeftContinuant_succ_ne_zero_of_eq_zero
    (mProject q : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hqzero :
      mode4ScaledLeftContinuant
        (mode4JacobiG mProject) Λ q = 0) :
    mode4ScaledLeftContinuant
        (mode4JacobiG mProject) Λ (q + 1) ≠ 0 := by
  induction q with
  | zero =>
      rw [mode4ScaledLeftContinuant_zero] at hqzero
      norm_num at hqzero
  | succ q ih =>
      have hprev :
          mode4ScaledLeftContinuant
            (mode4JacobiG mProject) Λ q ≠ 0 := by
        intro hqPrevZero
        exact (ih hqPrevZero) hqzero
      have hG : 0 < mode4JacobiG mProject := by
        unfold mode4JacobiG
        positivity
      have hL :
          mode4JacobiLower (mode4JacobiG mProject) (q + 1) ≠ 0 :=
        (mode4JacobiLower_pos_of_one_le
          (mode4JacobiG mProject) (q + 1) hG (by omega)).ne'
      have hU :
          mode4JacobiUpper (mode4JacobiG mProject) q ≠ 0 :=
        (mode4JacobiUpper_pos
          (mode4JacobiG mProject) q hG).ne'
      intro hnextZero
      have hrec := mode4ScaledLeftContinuant_succ_succ
        mProject q Λ hm
      dsimp only at hrec
      rw [hqzero] at hrec
      rw [hnextZero] at hrec
      have hprod :
          mode4JacobiLower (mode4JacobiG mProject) (q + 1) *
              mode4JacobiUpper (mode4JacobiG mProject) q *
                mode4ScaledLeftContinuant
                  (mode4JacobiG mProject) Λ q = 0 := by
        linarith
      rcases mul_eq_zero.mp hprod with hLU | hprevZero
      · exact (mul_ne_zero hL hU) hLU
      · exact hprev hprevZero

/-- At an exact Schur root, the penultimate finite-left continuant is nonzero.
This is the determinant of the principal minor obtained by deleting the
newest Schur coordinate. -/
theorem mode4ScaledLeftContinuant_pred_ne_zero_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    mode4ScaledLeftContinuant
        (mode4JacobiG mProject) Λ (K - 1) ≠ 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  have hschur : mode4SchurContinuant mProject (q + 1) Λ = 0 := by
    rw [mode4SchurContinuant_eq_upperProd_mul_rootFunction
      mProject (q + 1) Λ (by omega)]
    rw [hroot]
    ring
  intro hprev
  have hprevq :
      mode4ScaledLeftContinuant
        (mode4JacobiG mProject) Λ q = 0 := by
    simpa using hprev
  have hnext := mode4ScaledLeftContinuant_succ_ne_zero_of_eq_zero
    mProject q Λ hm hprevq
  unfold mode4SchurContinuant at hschur
  have hschur' := hschur
  simp only [Nat.succ_sub_one] at hschur'
  rw [hprevq, mul_zero, sub_zero] at hschur'
  exact hnext hschur'

/-- The principal minor deleting the newest Schur coordinate is exactly the
finite-left Hermitian continuant matrix. -/
theorem mode4HermitianSchurMatrix_succ_principalMinor
    (mProject n : ℕ) (Λ : ℝ) :
    Matrix.submatrix
        (mode4HermitianSchurMatrix mProject Λ (n + 1))
        Fin.succ Fin.succ =
      mode4HermitianLeftContinuantMatrix
        (mode4JacobiG mProject) Λ n := by
  ext i j
  simp [mode4HermitianSchurMatrix]

/-- An exact root of the scalar matching function gives a Schur kernel of
dimension at most one. -/
theorem mode4HermitianSchurMatrix_root_ker_finrank_le_one
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    Module.finrank ℝ
        (LinearMap.ker
          (mode4HermitianSchurMatrix mProject Λ K).mulVecLin) ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  let A := mode4HermitianSchurMatrix mProject Λ (n + 1)
  let B := mode4HermitianLeftContinuantMatrix
    (mode4JacobiG mProject) Λ n
  have hBdet : B.det ≠ 0 := by
    rw [show B.det =
        mode4ScaledLeftContinuant
          (mode4JacobiG mProject) Λ n by
      simpa [B] using
        mode4HermitianLeftContinuantMatrix_det_eq_scaledLeftContinuant
          mProject n Λ hm]
    simpa using mode4ScaledLeftContinuant_pred_ne_zero_of_root
      mProject (n + 1) Λ hm (by omega) hroot
  have hBrank : B.rank = n := by
    have hBunit : IsUnit B :=
      B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hBdet)
    simpa [B] using Matrix.rank_of_isUnit B hBunit
  have hminor : Matrix.submatrix A Fin.succ Fin.succ = B := by
    simpa [A, B] using
      mode4HermitianSchurMatrix_succ_principalMinor mProject n Λ
  have hcrank : (Matrix.submatrix A Fin.succ Fin.succ).cRank ≤ A.cRank :=
    Matrix.cRank_submatrix_le A Fin.succ Fin.succ
  have hAfinite : A.cRank < Cardinal.aleph0 :=
    lt_of_le_of_lt A.cRank_le_card_width
      (by simpa using Cardinal.nat_lt_aleph0 (n + 1))
  have hrank : n ≤ A.rank := by
    have hnat := Cardinal.toNat_le_toNat hcrank hAfinite
    rw [Matrix.cRank_toNat_eq_rank, Matrix.cRank_toNat_eq_rank,
      hminor, hBrank] at hnat
    exact hnat
  have hrankNullity := A.mulVecLin.finrank_range_add_finrank_ker
  have hrankNullity' :
      A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = n + 1 := by
    simpa [Matrix.rank, A] using hrankNullity
  change Module.finrank ℝ (LinearMap.ker A.mulVecLin) ≤ 1
  omega

/-- The exact Schur kernel at a matching root is genuinely one-dimensional:
the root makes the full determinant singular, while the preceding theorem
bounds the nullity by one. -/
theorem mode4HermitianSchurMatrix_root_ker_finrank_eq_one
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    Module.finrank ℝ
        (LinearMap.ker
          (mode4HermitianSchurMatrix mProject Λ K).mulVecLin) = 1 := by
  let A := mode4HermitianSchurMatrix mProject Λ K
  have hle :
      Module.finrank ℝ (LinearMap.ker A.mulVecLin) ≤ 1 := by
    simpa [A] using mode4HermitianSchurMatrix_root_ker_finrank_le_one
      mProject K Λ hm hK hroot
  have hdet : A.det = 0 := by
    rw [show A.det = mode4SchurContinuant mProject K Λ by
      simpa [A] using det_mode4HermitianSchurMatrix_eq_schurContinuant
        mProject K Λ hm hK]
    rw [mode4SchurContinuant_eq_upperProd_mul_rootFunction
      mProject K Λ hK, hroot, mul_zero]
  obtain ⟨v, hv, hAv⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hvker : v ∈ LinearMap.ker A.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hAv
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨v, hvker, hv⟩
  have hone : 1 ≤ Module.finrank ℝ (LinearMap.ker A.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hker
  change Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 1
  omega

#print axioms mode4ScaledLeftContinuant_succ_ne_zero_of_eq_zero
#print axioms mode4ScaledLeftContinuant_pred_ne_zero_of_root
#print axioms mode4HermitianSchurMatrix_succ_principalMinor
#print axioms mode4HermitianSchurMatrix_root_ker_finrank_le_one
#print axioms mode4HermitianSchurMatrix_root_ker_finrank_eq_one
