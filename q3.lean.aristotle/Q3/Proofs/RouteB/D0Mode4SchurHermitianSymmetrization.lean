import Q3.Proofs.RouteB.D0Mode4SchurInertiaOrientation

/-!
# Hermitian symmetrization of the mode-four Schur matrix

The nonsymmetric Jacobi recurrence has positive lower/upper coefficient products.  Replacing
each off-diagonal pair by the common real value
`-sqrt (mode4JacobiLower G (q + 1) * mode4JacobiUpper G q)` therefore gives a real Hermitian
matrix.  Its determinant recurrence is literally the already-committed Schur continuant
recurrence because the square of that off-diagonal is the original lower/upper product.

This closes the same-determinant Hermitian supplier required by the inertia receiver.  Concrete
endpoint nonsingularity and negative-eigenvalue counts remain separate suppliers.
-/

noncomputable section

/-- Every lower Jacobi coefficient is nonnegative when `G` is positive.  The zero-index
coefficient vanishes; subsequent coefficients are positive, although only nonnegativity is
needed for the square-root construction. -/
theorem mode4JacobiLower_nonneg
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    0 ≤ mode4JacobiLower G q := by
  cases q with
  | zero => simp [mode4JacobiLower, mode4JacobiIndex]
  | succ q =>
      have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
      unfold mode4JacobiLower mode4JacobiIndex
      norm_num [Nat.cast_succ]
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg hG.le (by linarith)) (by linarith)
      · exact mul_nonneg (by linarith) (by linarith)

/-- Common off-diagonal coefficient for the symmetric Jacobi realization. -/
noncomputable def mode4JacobiSymmetricOff
    (G : ℝ) (q : ℕ) : ℝ :=
  Real.sqrt (mode4JacobiLower G (q + 1) * mode4JacobiUpper G q)

/-- Reversed-index symmetric matrix realizing the cleared left continuant. -/
noncomputable def mode4HermitianLeftContinuantMatrix
    (G Λ : ℝ) : (K : ℕ) → Matrix (Fin K) (Fin K) ℝ
  | 0 => fun i => Fin.elim0 i
  | n + 1 => fun i j =>
      Fin.cases
        (Fin.cases
          (mode4JacobiCenter G Λ n)
          (fun j' => if j'.val = 0 then -mode4JacobiSymmetricOff G (n - 1) else 0)
          j)
        (fun i' =>
          Fin.cases
            (if i'.val = 0 then -mode4JacobiSymmetricOff G (n - 1) else 0)
            (fun j' => mode4HermitianLeftContinuantMatrix G Λ n i' j')
            j)
        i

theorem mode4HermitianLeftContinuantMatrix_isHermitian
    (G Λ : ℝ) (K : ℕ) :
    (mode4HermitianLeftContinuantMatrix G Λ K).IsHermitian := by
  induction K with
  | zero =>
      apply Matrix.IsHermitian.ext
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      apply Matrix.IsHermitian.ext
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simp [mode4HermitianLeftContinuantMatrix]
      · simp [mode4HermitianLeftContinuantMatrix]
      · simp [mode4HermitianLeftContinuantMatrix]
      · simpa [mode4HermitianLeftContinuantMatrix] using ih.apply i' j'

/-- Squaring the symmetric off-diagonal recovers the original Jacobi lower/upper product. -/
theorem mode4JacobiSymmetricOff_sq
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    mode4JacobiSymmetricOff G q ^ 2 =
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q := by
  unfold mode4JacobiSymmetricOff
  rw [Real.sq_sqrt]
  exact mul_nonneg
    (mode4JacobiLower_nonneg G (q + 1) hG)
    (mode4JacobiUpper_pos G q hG).le

private theorem mode4HermitianLeftContinuantMatrix_minor_zero
    (G Λ : ℝ) (n : ℕ) :
    Matrix.submatrix (mode4HermitianLeftContinuantMatrix G Λ (n + 1))
        Fin.succ (Fin.succAbove 0) =
      mode4HermitianLeftContinuantMatrix G Λ n := by
  ext i j
  simp [mode4HermitianLeftContinuantMatrix]

private theorem mode4HermitianLeftContinuantMatrix_minor_one_det
    (G Λ : ℝ) (n : ℕ) :
    (Matrix.submatrix (mode4HermitianLeftContinuantMatrix G Λ (n + 2))
        Fin.succ (Fin.succ 0).succAbove).det =
      -mode4JacobiSymmetricOff G n *
        (mode4HermitianLeftContinuantMatrix G Λ n).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.submatrix (mode4HermitianLeftContinuantMatrix G Λ (n + 2))
      Fin.succ (Fin.succ 0).succAbove
  have hB00 : B 0 0 = -mode4JacobiSymmetricOff G n := by
    simp only [B, Matrix.submatrix_apply, mode4HermitianLeftContinuantMatrix,
      Fin.succ_zero_eq_one]
    change (if (0 : ℕ) = 0 then -mode4JacobiSymmetricOff G n else 0) = _
    simp
  have hBsucc0 (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, mode4HermitianLeftContinuantMatrix]
  have hBtail :
      Matrix.submatrix B (Fin.succAbove 0) Fin.succ =
        mode4HermitianLeftContinuantMatrix G Λ n := by
    ext i j
    simp [B, mode4HermitianLeftContinuantMatrix]
  change B.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hB00]
  rw [hBtail]
  have hrest :
      (∑ i : Fin n,
        (-1 : ℝ) ^ (i.succ : Fin (n + 1)).val *
          B i.succ 0 *
          (Matrix.submatrix B (Fin.succAbove i.succ) Fin.succ).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hBsucc0]
    ring
  rw [hrest, add_zero]

private theorem mode4HermitianLeftContinuantMatrix_det_succ_succ
    (G Λ : ℝ) (n : ℕ) (hG : 0 < G) :
    (mode4HermitianLeftContinuantMatrix G Λ (n + 2)).det =
      mode4JacobiCenter G Λ (n + 1) *
          (mode4HermitianLeftContinuantMatrix G Λ (n + 1)).det -
        mode4JacobiLower G (n + 1) * mode4JacobiUpper G n *
          (mode4HermitianLeftContinuantMatrix G Λ n).det := by
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    mode4HermitianLeftContinuantMatrix G Λ (n + 2)
  have hA00 : A 0 0 = mode4JacobiCenter G Λ (n + 1) := by
    simp [A, mode4HermitianLeftContinuantMatrix]
  have hA0succ : A 0 (Fin.succ 0) = -mode4JacobiSymmetricOff G n := by
    simp only [A, mode4HermitianLeftContinuantMatrix, Fin.cases_zero]
    change (if (0 : ℕ) = 0 then -mode4JacobiSymmetricOff G n else 0) = _
    simp
  have hA0ss (j : Fin n) : A 0 j.succ.succ = 0 := by
    simp [A, mode4HermitianLeftContinuantMatrix]
  have hminor0 :
      (Matrix.submatrix A Fin.succ (Fin.succAbove 0)).det =
        (mode4HermitianLeftContinuantMatrix G Λ (n + 1)).det := by
    rw [show A = mode4HermitianLeftContinuantMatrix G Λ (n + 2) from rfl]
    exact congrArg Matrix.det
      (mode4HermitianLeftContinuantMatrix_minor_zero G Λ (n + 1))
  have hminor1 :
      (Matrix.submatrix A Fin.succ ((Fin.succ 0).succAbove)).det =
        -mode4JacobiSymmetricOff G n *
          (mode4HermitianLeftContinuantMatrix G Λ n).det := by
    rw [show A = mode4HermitianLeftContinuantMatrix G Λ (n + 2) from rfl]
    exact mode4HermitianLeftContinuantMatrix_minor_one_det G Λ n
  change A.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hA00, hminor0]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_succ, hA0succ, hminor1]
  have hrest :
      (∑ j : Fin n,
        (-1 : ℝ) ^ (j.val + 1 + 1) *
          A 0 j.succ.succ *
          (Matrix.submatrix A Fin.succ
            (Fin.succAbove j.succ.succ)).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hA0ss]
    ring
  rw [hrest, add_zero]
  norm_num
  calc
    _ = mode4JacobiCenter G Λ (n + 1) *
          (mode4HermitianLeftContinuantMatrix G Λ (n + 1)).det -
        mode4JacobiSymmetricOff G n ^ 2 *
          (mode4HermitianLeftContinuantMatrix G Λ n).det := by ring
    _ = _ := by rw [mode4JacobiSymmetricOff_sq G n hG]

theorem mode4HermitianLeftContinuantMatrix_det_eq_scaledLeftContinuant
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    (mode4HermitianLeftContinuantMatrix (mode4JacobiG mProject) Λ K).det =
      mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ K := by
  have hG : 0 < mode4JacobiG mProject := by
    have hmR : (0 : ℝ) < (mProject : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    unfold mode4JacobiG
    positivity
  induction K using Nat.twoStepInduction with
  | zero =>
      simpa [mode4HermitianLeftContinuantMatrix] using
        (mode4ScaledLeftContinuant_zero (mode4JacobiG mProject) Λ).symm
  | one =>
      rw [mode4ScaledLeftContinuant_one mProject Λ hm]
      simp [mode4HermitianLeftContinuantMatrix]
  | more n ih0 ih1 =>
      rw [mode4HermitianLeftContinuantMatrix_det_succ_succ _ _ n hG,
        mode4ScaledLeftContinuant_succ_succ mProject n Λ hm,
        ih1, ih0]

/-- Hermitian Schur matrix: the symmetric left block with the exact infinite right-tail
correction inserted in its newest diagonal entry. -/
noncomputable def mode4HermitianSchurMatrix
    (mProject : ℕ) (Λ : ℝ) : (K : ℕ) → Matrix (Fin K) (Fin K) ℝ
  | 0 => fun i => Fin.elim0 i
  | n + 1 => fun i j =>
      let G := mode4JacobiG mProject
      Fin.cases
        (Fin.cases
          (mode4JacobiCenter G Λ n -
            mode4JacobiUpper G n * mode4RightTailLimit mProject Λ (n + 1))
          (fun j' => if j'.val = 0 then -mode4JacobiSymmetricOff G (n - 1) else 0)
          j)
        (fun i' =>
          Fin.cases
            (if i'.val = 0 then -mode4JacobiSymmetricOff G (n - 1) else 0)
            (fun j' => mode4HermitianLeftContinuantMatrix G Λ n i' j')
            j)
        i

theorem mode4HermitianSchurMatrix_isHermitian
    (mProject K : ℕ) (Λ : ℝ) :
    (mode4HermitianSchurMatrix mProject Λ K).IsHermitian := by
  cases K with
  | zero =>
      apply Matrix.IsHermitian.ext
      intro i
      exact Fin.elim0 i
  | succ n =>
      apply Matrix.IsHermitian.ext
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simp [mode4HermitianSchurMatrix]
      · simp [mode4HermitianSchurMatrix]
      · simp [mode4HermitianSchurMatrix]
      · simpa [mode4HermitianSchurMatrix] using
          (mode4HermitianLeftContinuantMatrix_isHermitian
            (mode4JacobiG mProject) Λ n).apply i' j'

private theorem mode4HermitianSchurMatrix_det_one
    (mProject : ℕ) (Λ : ℝ) :
    (mode4HermitianSchurMatrix mProject Λ 1).det =
      mode4JacobiCenter (mode4JacobiG mProject) Λ 0 -
        mode4JacobiUpper (mode4JacobiG mProject) 0 *
          mode4RightTailLimit mProject Λ 1 := by
  simp [mode4HermitianSchurMatrix]

private theorem mode4HermitianSchurMatrix_minor_zero
    (mProject : ℕ) (Λ : ℝ) (n : ℕ) :
    Matrix.submatrix (mode4HermitianSchurMatrix mProject Λ (n + 1))
        Fin.succ (Fin.succAbove 0) =
      mode4HermitianLeftContinuantMatrix (mode4JacobiG mProject) Λ n := by
  ext i j
  simp [mode4HermitianSchurMatrix]

private theorem mode4HermitianSchurMatrix_minor_one_det
    (mProject : ℕ) (Λ : ℝ) (n : ℕ) :
    (Matrix.submatrix (mode4HermitianSchurMatrix mProject Λ (n + 2))
        Fin.succ (Fin.succ 0).succAbove).det =
      -mode4JacobiSymmetricOff (mode4JacobiG mProject) n *
        (mode4HermitianLeftContinuantMatrix
          (mode4JacobiG mProject) Λ n).det := by
  let G := mode4JacobiG mProject
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.submatrix (mode4HermitianSchurMatrix mProject Λ (n + 2))
      Fin.succ (Fin.succ 0).succAbove
  have hB00 : B 0 0 = -mode4JacobiSymmetricOff G n := by
    simp only [B, Matrix.submatrix_apply, mode4HermitianSchurMatrix,
      Fin.succ_zero_eq_one]
    change (if (0 : ℕ) = 0 then -mode4JacobiSymmetricOff G n else 0) = _
    simp
  have hBsucc0 (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, mode4HermitianSchurMatrix]
  have hBtail :
      Matrix.submatrix B (Fin.succAbove 0) Fin.succ =
        mode4HermitianLeftContinuantMatrix G Λ n := by
    ext i j
    simp only [B, Matrix.submatrix_apply, mode4HermitianSchurMatrix]
    change mode4HermitianLeftContinuantMatrix (mode4JacobiG mProject) Λ (n + 1)
        i.succ j.succ = mode4HermitianLeftContinuantMatrix G Λ n i j
    simp [G, mode4HermitianLeftContinuantMatrix]
  change B.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hB00]
  rw [hBtail]
  have hrest :
      (∑ i : Fin n,
        (-1 : ℝ) ^ (i.succ : Fin (n + 1)).val *
          B i.succ 0 *
          (Matrix.submatrix B (Fin.succAbove i.succ) Fin.succ).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hBsucc0]
    ring
  rw [hrest, add_zero]

private theorem mode4HermitianSchurMatrix_det_succ_succ
    (mProject n : ℕ) (Λ : ℝ) (hm : 2 ≤ mProject) :
    let G := mode4JacobiG mProject
    (mode4HermitianSchurMatrix mProject Λ (n + 2)).det =
      (mode4JacobiCenter G Λ (n + 1) -
          mode4JacobiUpper G (n + 1) *
            mode4RightTailLimit mProject Λ (n + 2)) *
          (mode4HermitianLeftContinuantMatrix G Λ (n + 1)).det -
        mode4JacobiLower G (n + 1) * mode4JacobiUpper G n *
          (mode4HermitianLeftContinuantMatrix G Λ n).det := by
  let G := mode4JacobiG mProject
  have hG : 0 < G := by
    have hmR : (0 : ℝ) < (mProject : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    unfold G mode4JacobiG
    positivity
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    mode4HermitianSchurMatrix mProject Λ (n + 2)
  have hA00 : A 0 0 =
      mode4JacobiCenter G Λ (n + 1) -
        mode4JacobiUpper G (n + 1) *
          mode4RightTailLimit mProject Λ (n + 2) := by
    simp [A, G, mode4HermitianSchurMatrix]
  have hA0succ : A 0 (Fin.succ 0) = -mode4JacobiSymmetricOff G n := by
    dsimp only [G]
    simp only [A, mode4HermitianSchurMatrix, Fin.cases_zero]
    change (if (0 : ℕ) = 0 then -mode4JacobiSymmetricOff G n else 0) = _
    simp [G]
  have hA0ss (j : Fin n) : A 0 j.succ.succ = 0 := by
    simp [A, mode4HermitianSchurMatrix]
  have hminor0 :
      (Matrix.submatrix A Fin.succ (Fin.succAbove 0)).det =
        (mode4HermitianLeftContinuantMatrix G Λ (n + 1)).det := by
    rw [show A = mode4HermitianSchurMatrix mProject Λ (n + 2) from rfl]
    exact congrArg Matrix.det
      (mode4HermitianSchurMatrix_minor_zero mProject Λ (n + 1))
  have hminor1 :
      (Matrix.submatrix A Fin.succ ((Fin.succ 0).succAbove)).det =
        -mode4JacobiSymmetricOff G n *
          (mode4HermitianLeftContinuantMatrix G Λ n).det := by
    rw [show A = mode4HermitianSchurMatrix mProject Λ (n + 2) from rfl]
    exact mode4HermitianSchurMatrix_minor_one_det mProject Λ n
  dsimp only
  change A.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hA00, hminor0]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_succ, hA0succ, hminor1]
  have hrest :
      (∑ j : Fin n,
        (-1 : ℝ) ^ (j.val + 1 + 1) *
          A 0 j.succ.succ *
          (Matrix.submatrix A Fin.succ
            (Fin.succAbove j.succ.succ)).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hA0ss]
    ring
  rw [hrest, add_zero]
  norm_num
  calc
    _ = (mode4JacobiCenter G Λ (n + 1) -
          mode4JacobiUpper G (n + 1) *
            mode4RightTailLimit mProject Λ (n + 2)) *
          (mode4HermitianLeftContinuantMatrix G Λ (n + 1)).det -
        mode4JacobiSymmetricOff G n ^ 2 *
          (mode4HermitianLeftContinuantMatrix G Λ n).det := by ring
    _ = _ := by rw [mode4JacobiSymmetricOff_sq G n hG]

theorem det_mode4HermitianSchurMatrix_eq_schurContinuant
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K) :
    (mode4HermitianSchurMatrix mProject Λ K).det =
      mode4SchurContinuant mProject K Λ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  cases n with
  | zero =>
      rw [mode4HermitianSchurMatrix_det_one]
      rw [mode4SchurContinuant]
      rw [mode4ScaledLeftContinuant_one mProject Λ hm,
        mode4ScaledLeftContinuant_zero]
      simp only [Nat.succ_eq_add_one, Nat.zero_add, Nat.reduceSubDiff]
      ring
  | succ n =>
      rw [mode4HermitianSchurMatrix_det_succ_succ _ _ _ hm]
      rw [mode4HermitianLeftContinuantMatrix_det_eq_scaledLeftContinuant
          mProject (n + 1) Λ hm,
        mode4HermitianLeftContinuantMatrix_det_eq_scaledLeftContinuant mProject n Λ hm]
      change
        (mode4JacobiCenter (mode4JacobiG mProject) Λ (n + 1) -
            mode4JacobiUpper (mode4JacobiG mProject) (n + 1) *
              mode4RightTailLimit mProject Λ (n + 2)) *
            mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ (n + 1) -
          mode4JacobiLower (mode4JacobiG mProject) (n + 1) *
            mode4JacobiUpper (mode4JacobiG mProject) n *
              mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ n =
        mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ (n + 2) -
          mode4RightTailLimit mProject Λ (n + 2) *
            mode4JacobiUpper (mode4JacobiG mProject) (n + 1) *
              mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ (n + 1)
      rw [mode4ScaledLeftContinuant_succ_succ mProject n Λ hm]
      ring

theorem det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K) :
    (mode4HermitianSchurMatrix mProject Λ K).det =
      (mode4SchurMatrix mProject Λ K).det := by
  rw [det_mode4HermitianSchurMatrix_eq_schurContinuant
      mProject K Λ hm hK,
    det_mode4SchurMatrix_eq_schurContinuant mProject K Λ hm hK]

/-! ## Direct determinant-sign receivers -/

/-- Strict positivity of the explicit Hermitian Schur determinant has exactly the same
orientation as strict positivity of the scalar root function. -/
theorem mode4RootFunction_pos_of_hermitianSchur_det_pos
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet : 0 < (mode4HermitianSchurMatrix mProject Λ K).det) :
    0 < mode4RootFunction mProject K Λ := by
  apply sign_eq_one_iff.mp
  rw [← mode4SchurMatrix_det_sign_eq_rootFunction_sign mProject K Λ hm hK]
  rw [← det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
    mProject K Λ hm hK]
  exact sign_eq_one_iff.mpr hdet

/-- Strict negativity of the explicit Hermitian Schur determinant has exactly the same
orientation as strict negativity of the scalar root function. -/
theorem mode4RootFunction_neg_of_hermitianSchur_det_neg
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet : (mode4HermitianSchurMatrix mProject Λ K).det < 0) :
    mode4RootFunction mProject K Λ < 0 := by
  apply sign_eq_neg_one_iff.mp
  rw [← mode4SchurMatrix_det_sign_eq_rootFunction_sign mProject K Λ hm hK]
  rw [← det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
    mProject K Λ hm hK]
  exact sign_eq_neg_one_iff.mpr hdet

/-- Minimal conditional endpoint receiver.  The matrix construction, Hermitianity,
determinant crosswalk, sign orientation, and continuity are internal; only the two strict
endpoint determinant inequalities remain concrete. -/
theorem exists_mode4RootFunction_eq_zero_of_hermitianSchur_det_pos_neg
    (mProject K : ℕ) (ΛLower ΛUpper : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hLowerUpper : ΛLower ≤ ΛUpper)
    (hUpper20 : ΛUpper ≤ 20)
    (hLowerPos :
      0 < (mode4HermitianSchurMatrix mProject ΛLower K).det)
    (hUpperNeg :
      (mode4HermitianSchurMatrix mProject ΛUpper K).det < 0) :
    ∃ Λ ∈ Set.Icc ΛLower ΛUpper,
      mode4RootFunction mProject K Λ = 0 := by
  have hK1 : 1 ≤ K := le_trans (by decide : 1 ≤ 3) hK
  have hpos : 0 < mode4RootFunction mProject K ΛLower :=
    mode4RootFunction_pos_of_hermitianSchur_det_pos
      mProject K ΛLower hm hK1 hLowerPos
  have hneg : mode4RootFunction mProject K ΛUpper < 0 :=
    mode4RootFunction_neg_of_hermitianSchur_det_neg
      mProject K ΛUpper hm hK1 hUpperNeg
  have hcont : ContinuousOn (mode4RootFunction mProject K)
      (Set.Icc ΛLower ΛUpper) :=
    (mode4RootFunction_continuousOn_lambda mProject K hm hK hsep).mono
      (fun x hx => hx.2.trans hUpper20)
  have hz : (0 : ℝ) ∈ Set.Icc
      (mode4RootFunction mProject K ΛUpper)
      (mode4RootFunction mProject K ΛLower) :=
    ⟨hneg.le, hpos.le⟩
  obtain ⟨Λ, hΛ, hroot⟩ :=
    intermediate_value_Icc' hLowerUpper hcont hz
  exact ⟨Λ, hΛ, hroot⟩

/-! ## Specialized inertia receivers -/

theorem mode4RootFunction_pos_of_hermitianSchur_count_two
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet_ne : (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject Λ K)
        (mode4HermitianSchurMatrix_isHermitian mProject K Λ) = 2) :
    0 < mode4RootFunction mProject K Λ :=
  mode4RootFunction_pos_of_hermitian_count_two
    (mode4HermitianSchurMatrix mProject Λ K)
    (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
    mProject K Λ hm hK
    (det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
      mProject K Λ hm hK)
    hdet_ne hcount

theorem mode4RootFunction_neg_of_hermitianSchur_count_three
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet_ne : (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject Λ K)
        (mode4HermitianSchurMatrix_isHermitian mProject K Λ) = 3) :
    mode4RootFunction mProject K Λ < 0 :=
  mode4RootFunction_neg_of_hermitian_count_three
    (mode4HermitianSchurMatrix mProject Λ K)
    (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
    mProject K Λ hm hK
    (det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
      mProject K Λ hm hK)
    hdet_ne hcount

/-- Conditional root bracket with the same-determinant Hermitian supplier discharged.  Only
the two concrete endpoint nonsingularity and inertia-count facts remain. -/
theorem exists_mode4RootFunction_eq_zero_of_hermitianSchur_counts_two_three
    (mProject K : ℕ) (ΛLower ΛUpper : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hLowerUpper : ΛLower ≤ ΛUpper)
    (hUpper20 : ΛUpper ≤ 20)
    (hLower_ne :
      (mode4HermitianSchurMatrix mProject ΛLower K).det ≠ 0)
    (hUpper_ne :
      (mode4HermitianSchurMatrix mProject ΛUpper K).det ≠ 0)
    (hcountLower : mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject ΛLower K)
        (mode4HermitianSchurMatrix_isHermitian mProject K ΛLower) = 2)
    (hcountUpper : mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject ΛUpper K)
        (mode4HermitianSchurMatrix_isHermitian mProject K ΛUpper) = 3) :
    ∃ Λ ∈ Set.Icc ΛLower ΛUpper,
      mode4RootFunction mProject K Λ = 0 := by
  have hK1 : 1 ≤ K := le_trans (by decide : 1 ≤ 3) hK
  exact exists_mode4RootFunction_eq_zero_of_hermitian_counts_two_three
    (mode4HermitianSchurMatrix mProject ΛLower K)
    (mode4HermitianSchurMatrix_isHermitian mProject K ΛLower)
    (mode4HermitianSchurMatrix mProject ΛUpper K)
    (mode4HermitianSchurMatrix_isHermitian mProject K ΛUpper)
    mProject K ΛLower ΛUpper hm hK hsep hLowerUpper hUpper20
    (det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
      mProject K ΛLower hm hK1)
    (det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
      mProject K ΛUpper hm hK1)
    hLower_ne hUpper_ne hcountLower hcountUpper

#print axioms mode4JacobiLower_nonneg
#print axioms mode4HermitianLeftContinuantMatrix_isHermitian
#print axioms mode4HermitianLeftContinuantMatrix_det_eq_scaledLeftContinuant
#print axioms mode4HermitianSchurMatrix_isHermitian
#print axioms det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
#print axioms mode4RootFunction_pos_of_hermitianSchur_det_pos
#print axioms mode4RootFunction_neg_of_hermitianSchur_det_neg
#print axioms exists_mode4RootFunction_eq_zero_of_hermitianSchur_det_pos_neg
#print axioms mode4RootFunction_pos_of_hermitianSchur_count_two
#print axioms mode4RootFunction_neg_of_hermitianSchur_count_three
#print axioms exists_mode4RootFunction_eq_zero_of_hermitianSchur_counts_two_three
