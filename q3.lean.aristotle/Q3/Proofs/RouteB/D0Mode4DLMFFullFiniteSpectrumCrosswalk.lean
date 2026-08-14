import Q3.Proofs.RouteB.D0Mode4DLMFEvenFiniteMatrix
import Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteSchurCrosswalk

/-!
# Full finite DLMF spectrum crosswalk

The literal DLMF matrix is stored in forward source order, whereas the actual
finite Jacobi truncation used by the Schur/inertia chain reverses only its
retained block.  This file supplies the missing full-carrier permutation and
proves that the two finite objects have the same characteristic polynomial.

It also exposes the exact scalar shift and a constructed ascending finite
eigenvalue family.  No classical spheroidal spectral carrier, DLMF 30.16.3
limit, endpoint count, or degree-four identification is imported here.
-/

noncomputable section

open Matrix

/-- Reverses the retained block and leaves the forward tail in source order. -/
def mode4ActualFiniteForwardEquiv (K d : ℕ) :
    (Fin K ⊕ Fin d) ≃ Fin (K + d) :=
  (Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin d))).trans finSumFinEquiv

/-- The explicit full-carrier equivalence sends a retained coordinate to its
reversed source coordinate. -/
@[simp] theorem mode4ActualFiniteForwardEquiv_inl
    (K d : ℕ) (i : Fin K) :
    mode4ActualFiniteForwardEquiv K d (Sum.inl i) =
      Fin.castAdd d i.rev := by
  rfl

/-- The explicit full-carrier equivalence leaves a tail coordinate in forward
source order after the first `K` coordinates. -/
@[simp] theorem mode4ActualFiniteForwardEquiv_inr
    (K d : ℕ) (j : Fin d) :
    mode4ActualFiniteForwardEquiv K d (Sum.inr j) =
      Fin.natAdd K j := by
  rfl

private theorem mode4ActualFiniteJacobiTruncation_tail_entry
    (mProject : ℕ) (Λ : ℝ) (K d : ℕ) (i j : Fin d) :
    mode4ActualFiniteJacobiTruncation mProject Λ K d (Sum.inr i) (Sum.inr j) =
      mode4ForwardHermitianFiniteMatrix (mode4JacobiG mProject) Λ (K + d)
        (Fin.natAdd K i) (Fin.natAdd K j) := by
  induction d generalizing K with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · change mode4JacobiCenter (mode4JacobiG mProject) Λ K = _
        simp [mode4ForwardHermitianFiniteMatrix]
      · change (if j'.val = 0 then
          -mode4JacobiSymmetricOff (mode4JacobiG mProject) K else 0) = _
        simp only [mode4ForwardHermitianFiniteMatrix, Fin.val_zero,
          Fin.val_succ, Fin.ext_iff, Fin.coe_natAdd]
        split_ifs
        all_goals try omega
        all_goals simp
      · change (if i'.val = 0 then
          -mode4JacobiSymmetricOff (mode4JacobiG mProject) K else 0) = _
        simp only [mode4ForwardHermitianFiniteMatrix, Fin.val_zero,
          Fin.val_succ, Fin.ext_iff, Fin.coe_natAdd]
        split_ifs
        all_goals try omega
        all_goals simp
      · change mode4ActualFiniteJacobiTruncation
          mProject Λ (K + 1) n (Sum.inr i') (Sum.inr j') = _
        simpa [mode4ForwardHermitianFiniteMatrix, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using ih (K + 1) i' j'

/-- The Schur-chain actual truncation is exactly the source-ordered forward
Hermitian matrix after reversing only the retained block. -/
theorem mode4ActualFiniteJacobiTruncation_eq_reindex_forwardHermitianFiniteMatrix
    (mProject : ℕ) (Λ : ℝ) (K d : ℕ) :
    mode4ActualFiniteJacobiTruncation mProject Λ K d =
      Matrix.reindex (mode4ActualFiniteForwardEquiv K d).symm
        (mode4ActualFiniteForwardEquiv K d).symm
        (mode4ForwardHermitianFiniteMatrix
          (mode4JacobiG mProject) Λ (K + d)) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j
  · simp only [Matrix.reindex_apply, Equiv.symm_symm,
      Matrix.submatrix_apply,
      mode4ActualFiniteForwardEquiv_inl]
    change mode4HermitianLeftContinuantMatrix
      (mode4JacobiG mProject) Λ K i j = _
    have h := congrFun (congrFun
      (mode4ForwardHermitianFiniteMatrix_submatrix_rev_eq_leftContinuant
        (mode4JacobiG mProject) Λ K) i) j
    simpa [Matrix.submatrix_apply, mode4ForwardHermitianFiniteMatrix] using h.symm
  · simp only [Matrix.reindex_apply, Equiv.symm_symm,
      Matrix.submatrix_apply,
      mode4ActualFiniteForwardEquiv_inl,
      mode4ActualFiniteForwardEquiv_inr]
    change (if i.val = 0 ∧ j.val = 0 then
      -mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1) else 0) = _
    have hiK := i.isLt
    have hjd := j.isLt
    have hsubi : K - (i.val + 1) + (i.val + 1) = K :=
      Nat.sub_add_cancel (by omega)
    by_cases hboth : i.val = 0 ∧ j.val = 0
    · rcases hboth with ⟨hi, hj⟩
      rw [if_pos ⟨hi, hj⟩]
      simp only [mode4ForwardHermitianFiniteMatrix, Fin.ext_iff,
        Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_rev, hi, hj]
      split_ifs
      all_goals try omega
      all_goals simp
    · rw [if_neg hboth]
      simp only [mode4ForwardHermitianFiniteMatrix, Fin.ext_iff,
        Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_rev]
      split_ifs
      all_goals try omega
      all_goals simp
  · simp only [Matrix.reindex_apply, Equiv.symm_symm,
      Matrix.submatrix_apply,
      mode4ActualFiniteForwardEquiv_inl,
      mode4ActualFiniteForwardEquiv_inr]
    change (if j.val = 0 ∧ i.val = 0 then
      -mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1) else 0) = _
    have hiK := j.isLt
    have hjd := i.isLt
    have hsubj : K - (j.val + 1) + (j.val + 1) = K :=
      Nat.sub_add_cancel (by omega)
    by_cases hboth : j.val = 0 ∧ i.val = 0
    · rcases hboth with ⟨hj, hi⟩
      rw [if_pos ⟨hj, hi⟩]
      simp only [mode4ForwardHermitianFiniteMatrix, Fin.ext_iff,
        Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_rev, hi, hj]
      split_ifs
      all_goals try omega
      all_goals simp
    · rw [if_neg hboth]
      simp only [mode4ForwardHermitianFiniteMatrix, Fin.ext_iff,
        Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_rev]
      split_ifs
      all_goals try omega
      all_goals rfl
  · simp only [Matrix.reindex_apply, Equiv.symm_symm,
      Matrix.submatrix_apply,
      mode4ActualFiniteForwardEquiv_inr]
    exact mode4ActualFiniteJacobiTruncation_tail_entry
      mProject Λ K d i j

/-- Reindexing the full actual truncation into forward source order preserves
its characteristic polynomial. -/
theorem mode4ActualFiniteJacobiTruncation_charpoly_eq_forwardHermitianFiniteMatrix
    (mProject : ℕ) (Λ : ℝ) (K d : ℕ) :
    (mode4ActualFiniteJacobiTruncation mProject Λ K d).charpoly =
      (mode4ForwardHermitianFiniteMatrix
        (mode4JacobiG mProject) Λ (K + d)).charpoly := by
  rw [mode4ActualFiniteJacobiTruncation_eq_reindex_forwardHermitianFiniteMatrix]
  exact Matrix.charpoly_reindex
    (mode4ActualFiniteForwardEquiv K d).symm
    (mode4ForwardHermitianFiniteMatrix
      (mode4JacobiG mProject) Λ (K + d))

/-- The source-ordered forward finite matrix is real Hermitian. -/
theorem mode4ForwardHermitianFiniteMatrix_isHermitian
    (G Λ : ℝ) (d : ℕ) :
    (mode4ForwardHermitianFiniteMatrix G Λ d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change mode4ForwardHermitianFiniteMatrix G Λ d j i =
    mode4ForwardHermitianFiniteMatrix G Λ d i j
  unfold mode4ForwardHermitianFiniteMatrix
  split_ifs <;> try rfl
  all_goals try omega
  all_goals (congr 1; omega)

/-- The project parameter `Lambda` is a literal scalar shift of the unshifted
finite Hermitian DLMF matrix. -/
theorem mode4ForwardHermitianFiniteMatrix_eq_unshifted_sub_scalar
    (G Λ : ℝ) (d : ℕ) :
    mode4ForwardHermitianFiniteMatrix G Λ d =
      mode4ForwardHermitianFiniteMatrix G 0 d - Matrix.scalar (Fin d) Λ := by
  ext i j
  by_cases hdiag : i = j
  · subst j
    simp [mode4ForwardHermitianFiniteMatrix, Matrix.scalar,
      mode4JacobiCenter]
  · simp [mode4ForwardHermitianFiniteMatrix, Matrix.scalar, hdiag]

/-- The `p`-th finite even DLMF eigenvalue in ascending value order, with
zero-based Lean index `p`; DLMF's published selector is `p + 1`. -/
noncomputable def mode4DLMFEvenFiniteEigenvalue
    (G : ℝ) (d : ℕ) (p : Fin d) : ℝ :=
  (mode4ForwardHermitianFiniteMatrix_isHermitian G 0 d).eigenvalues₀
    (Fin.cast (Fintype.card_fin d).symm p.rev)

/-- The constructed finite DLMF eigenvalues are ordered increasingly by their
zero-based Lean index. -/
theorem mode4DLMFEvenFiniteEigenvalue_monotone
    (G : ℝ) (d : ℕ) :
    Monotone (mode4DLMFEvenFiniteEigenvalue G d) := by
  intro p q hpq
  unfold mode4DLMFEvenFiniteEigenvalue
  have hrev : Fin.cast (Fintype.card_fin d).symm q.rev ≤
      Fin.cast (Fintype.card_fin d).symm p.rev := by
    simpa using (Fin.rev_le_rev.mpr hpq)
  exact (mode4ForwardHermitianFiniteMatrix_isHermitian G 0 d).eigenvalues₀_antitone
    hrev

/-- Positive diagonal similarity transports the characteristic polynomial of
the literal nonsymmetric DLMF matrix to the forward Hermitian matrix. -/
theorem mode4DLMFEvenFiniteMatrix_charpoly_eq_forwardHermitianFiniteMatrix
    (G Λ : ℝ) (d : ℕ) (hG : 0 < G) :
    (mode4DLMFEvenFiniteMatrix G Λ d).charpoly =
      (mode4ForwardHermitianFiniteMatrix G Λ d).charpoly := by
  let v : Fin d → ℝ := fun i => mode4DLMFEvenSimilarityScale G i.val
  let D : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal v
  have hv : IsUnit v := Pi.isUnit_iff.mpr fun i =>
    isUnit_iff_ne_zero.mpr (mode4DLMFEvenSimilarityScale_pos G i.val hG).ne'
  have hD : IsUnit D := Matrix.isUnit_diagonal.mpr hv
  let U : (Matrix (Fin d) (Fin d) ℝ)ˣ := hD.unit
  have hU : (U : Matrix (Fin d) (Fin d) ℝ) = D := hD.unit_spec
  have hAD : mode4DLMFEvenFiniteMatrix G Λ d * D =
      D * mode4ForwardHermitianFiniteMatrix G Λ d := by
    simpa [D, v] using
      mode4DLMFEvenFiniteMatrix_mul_diagonal_eq_diagonal_mul_forwardHermitian
        G Λ d hG
  have hADU : mode4DLMFEvenFiniteMatrix G Λ d *
        (U : Matrix (Fin d) (Fin d) ℝ) =
      (U : Matrix (Fin d) (Fin d) ℝ) *
        mode4ForwardHermitianFiniteMatrix G Λ d := by
    simpa [hU] using hAD
  have hconj : mode4DLMFEvenFiniteMatrix G Λ d =
      (U : Matrix (Fin d) (Fin d) ℝ) *
        mode4ForwardHermitianFiniteMatrix G Λ d *
          (↑(U⁻¹) : Matrix (Fin d) (Fin d) ℝ) := by
    calc
      mode4DLMFEvenFiniteMatrix G Λ d =
          mode4DLMFEvenFiniteMatrix G Λ d *
            ((U : Matrix (Fin d) (Fin d) ℝ) *
              (↑(U⁻¹) : Matrix (Fin d) (Fin d) ℝ)) := by simp
      _ = (mode4DLMFEvenFiniteMatrix G Λ d *
            (U : Matrix (Fin d) (Fin d) ℝ)) *
              (↑(U⁻¹) : Matrix (Fin d) (Fin d) ℝ) := by rw [mul_assoc]
      _ = ((U : Matrix (Fin d) (Fin d) ℝ) *
            mode4ForwardHermitianFiniteMatrix G Λ d) *
              (↑(U⁻¹) : Matrix (Fin d) (Fin d) ℝ) := by rw [hADU]
  rw [hconj]
  exact Matrix.charpoly_units_conj U
    (mode4ForwardHermitianFiniteMatrix G Λ d)

/-- The literal DLMF matrix and the Schur-chain actual truncation have exactly
the same characteristic polynomial on the full `K + d` finite carrier. -/
theorem mode4ActualFiniteJacobiTruncation_charpoly_eq_DLMFEvenFiniteMatrix
    (mProject : ℕ) (Λ : ℝ) (K d : ℕ)
    (hG : 0 < mode4JacobiG mProject) :
    (mode4ActualFiniteJacobiTruncation mProject Λ K d).charpoly =
      (mode4DLMFEvenFiniteMatrix
        (mode4JacobiG mProject) Λ (K + d)).charpoly := by
  rw [mode4ActualFiniteJacobiTruncation_charpoly_eq_forwardHermitianFiniteMatrix]
  exact (mode4DLMFEvenFiniteMatrix_charpoly_eq_forwardHermitianFiniteMatrix
    (mode4JacobiG mProject) Λ (K + d) hG).symm

#print axioms mode4ActualFiniteJacobiTruncation_eq_reindex_forwardHermitianFiniteMatrix
#print axioms mode4ActualFiniteJacobiTruncation_charpoly_eq_forwardHermitianFiniteMatrix
#print axioms mode4ForwardHermitianFiniteMatrix_isHermitian
#print axioms mode4ForwardHermitianFiniteMatrix_eq_unshifted_sub_scalar
#print axioms mode4DLMFEvenFiniteEigenvalue_monotone
#print axioms mode4DLMFEvenFiniteMatrix_charpoly_eq_forwardHermitianFiniteMatrix
#print axioms mode4ActualFiniteJacobiTruncation_charpoly_eq_DLMFEvenFiniteMatrix
