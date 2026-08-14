import Q3.Proofs.RouteB.D0Mode4PSWFLegendreRecurrenceCrosswalk

/-!
# Literal DLMF 30.16.1 even finite matrix

For DLMF spheroidal order `m = 0`, row `j = q + 1` corresponds to the even
Legendre degree `2q`.  The three scalar definitions below are the literal
30.16.1 entries in the project's `G = gamma^2` and `Lambda = lambda` units.

The finite matrix is kept in the source order `q = 0, ..., d - 1`.  Its raw
off-diagonal entries are nonsymmetric.  The positive recursive scale proves
the exact diagonal-similarity identity with the forward Hermitian Jacobi
matrix.  This file does not import ordered eigenvalues, a limiting classical
spectrum, endpoint counts, a negative-count value, or an indexed PSWF.
-/

noncomputable section

/-- Literal diagonal entry of DLMF 30.16.1 for `m = 0`, `j = q + 1`, shifted
by the project spectral parameter `Lambda` in DLMF `lambda`-units. -/
noncomputable def mode4DLMFEvenDiagonal
    (G Λ : ℝ) (q : ℕ) : ℝ :=
  let N : ℝ := 2 * q
  N * (N + 1) -
    2 * G * (N * (N + 1) - 1) /
      ((2 * N - 1) * (2 * N + 3)) -
    Λ

/-- Literal upper entry of DLMF 30.16.1 for `m = 0`, `j = q + 1`. -/
noncomputable def mode4DLMFEvenUpper
    (G : ℝ) (q : ℕ) : ℝ :=
  let N : ℝ := 2 * q;
  (-G * (N + 1) * (N + 2)) / ((2 * N + 3) * (2 * N + 5))

/-- Literal lower entry of DLMF 30.16.1 for `m = 0`, `j = q + 1`.
At `q = 0` its numerator vanishes, so the source matrix starts at degree zero
without a hidden lower coordinate. -/
noncomputable def mode4DLMFEvenLower
    (G : ℝ) (q : ℕ) : ℝ :=
  let N : ℝ := 2 * q;
  (-G * (N - 1) * N) / ((2 * N - 3) * (2 * N - 1))

theorem mode4DLMFEvenDiagonal_eq_jacobiCenter
    (G Λ : ℝ) (q : ℕ) :
    mode4DLMFEvenDiagonal G Λ q = mode4JacobiCenter G Λ q := by
  rfl

theorem mode4DLMFEvenUpper_eq_neg_jacobiUpper
    (G : ℝ) (q : ℕ) :
    mode4DLMFEvenUpper G q = -mode4JacobiUpper G q := by
  unfold mode4DLMFEvenUpper mode4JacobiUpper
  unfold mode4JacobiIndex
  ring

theorem mode4DLMFEvenLower_eq_neg_jacobiLower
    (G : ℝ) (q : ℕ) :
    mode4DLMFEvenLower G q = -mode4JacobiLower G q := by
  unfold mode4DLMFEvenLower mode4JacobiLower
  unfold mode4JacobiIndex
  ring

/-- Literal source-ordered finite matrix from DLMF 30.16.1, already shifted
by `-Lambda I` in DLMF `lambda`-units. -/
noncomputable def mode4DLMFEvenFiniteMatrix
    (G Λ : ℝ) (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    if i = j then mode4DLMFEvenDiagonal G Λ i.val
    else if j.val = i.val + 1 then mode4DLMFEvenUpper G i.val
    else if i.val = j.val + 1 then mode4DLMFEvenLower G i.val
    else 0

/-- The same finite Jacobi matrix in forward Hermitian coordinates. -/
noncomputable def mode4ForwardHermitianFiniteMatrix
    (G Λ : ℝ) (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    if i = j then mode4JacobiCenter G Λ i.val
    else if j.val = i.val + 1 then -mode4JacobiSymmetricOff G i.val
    else if i.val = j.val + 1 then -mode4JacobiSymmetricOff G j.val
    else 0

/-- Positive diagonal scale for the source-to-Hermitian similarity.  The
recurrence is exactly the source ratio
`D_(q+1)/D_q = sqrt (lower_(q+1)/upper_q)`, expressed through the already
kernel-checked positive Jacobi coefficients. -/
noncomputable def mode4DLMFEvenSimilarityScale
    (G : ℝ) : ℕ → ℝ
  | 0 => 1
  | q + 1 =>
      mode4DLMFEvenSimilarityScale G q * mode4JacobiSymmetricOff G q /
        mode4JacobiUpper G q

private theorem mode4JacobiLower_succ_pos
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    0 < mode4JacobiLower G (q + 1) := by
  have hq : (0 : ℝ) ≤ q := by positivity
  unfold mode4JacobiLower mode4JacobiIndex
  apply div_pos
  · exact mul_pos (mul_pos hG (by norm_num; linarith)) (by positivity)
  · exact mul_pos (by norm_num; linarith) (by norm_num; linarith)

private theorem mode4JacobiSymmetricOff_pos
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    0 < mode4JacobiSymmetricOff G q := by
  unfold mode4JacobiSymmetricOff
  exact Real.sqrt_pos.2 (mul_pos
    (mode4JacobiLower_succ_pos G q hG)
    (mode4JacobiUpper_pos G q hG))

theorem mode4DLMFEvenSimilarityScale_pos
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    0 < mode4DLMFEvenSimilarityScale G q := by
  induction q with
  | zero => simp [mode4DLMFEvenSimilarityScale]
  | succ q ih =>
      rw [mode4DLMFEvenSimilarityScale]
      exact div_pos
        (mul_pos ih (mode4JacobiSymmetricOff_pos G q hG))
        (mode4JacobiUpper_pos G q hG)

private theorem mode4DLMFEvenSimilarityScale_upper_balance
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    mode4JacobiUpper G q * mode4DLMFEvenSimilarityScale G (q + 1) =
      mode4DLMFEvenSimilarityScale G q * mode4JacobiSymmetricOff G q := by
  rw [mode4DLMFEvenSimilarityScale]
  field_simp [(mode4JacobiUpper_pos G q hG).ne']

private theorem mode4DLMFEvenSimilarityScale_lower_balance
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    mode4JacobiLower G (q + 1) * mode4DLMFEvenSimilarityScale G q =
      mode4DLMFEvenSimilarityScale G (q + 1) *
        mode4JacobiSymmetricOff G q := by
  rw [mode4DLMFEvenSimilarityScale]
  field_simp [(mode4JacobiUpper_pos G q hG).ne']
  rw [mode4JacobiSymmetricOff_sq G q hG]
  ring

/-- Entrywise diagonal-similarity equation `A D = D H` between the literal
DLMF source matrix `A` and the forward Hermitian Jacobi matrix `H`. -/
theorem mode4DLMFEvenFiniteMatrix_mul_scale_eq_scale_mul_forwardHermitian
    (G Λ : ℝ) (d : ℕ) (hG : 0 < G) (i j : Fin d) :
    mode4DLMFEvenFiniteMatrix G Λ d i j *
        mode4DLMFEvenSimilarityScale G j.val =
      mode4DLMFEvenSimilarityScale G i.val *
        mode4ForwardHermitianFiniteMatrix G Λ d i j := by
  by_cases hdiag : i = j
  · subst j
    simp [mode4DLMFEvenFiniteMatrix, mode4ForwardHermitianFiniteMatrix,
      mode4DLMFEvenDiagonal_eq_jacobiCenter]
    ring
  by_cases hu : j.val = i.val + 1
  · unfold mode4DLMFEvenFiniteMatrix mode4ForwardHermitianFiniteMatrix
    rw [if_neg hdiag, if_neg hdiag, if_pos hu, if_pos hu,
      mode4DLMFEvenUpper_eq_neg_jacobiUpper, hu]
    have hbalance := mode4DLMFEvenSimilarityScale_upper_balance G i.val hG
    calc
      -mode4JacobiUpper G i.val *
          mode4DLMFEvenSimilarityScale G (i.val + 1) =
        -(mode4JacobiUpper G i.val *
          mode4DLMFEvenSimilarityScale G (i.val + 1)) := by ring
      _ = -(mode4DLMFEvenSimilarityScale G i.val *
          mode4JacobiSymmetricOff G i.val) := by rw [hbalance]
      _ = mode4DLMFEvenSimilarityScale G i.val *
          -mode4JacobiSymmetricOff G i.val := by ring
  by_cases hl : i.val = j.val + 1
  · unfold mode4DLMFEvenFiniteMatrix mode4ForwardHermitianFiniteMatrix
    rw [if_neg hdiag, if_neg hdiag, if_neg hu, if_neg hu,
      if_pos hl, if_pos hl, mode4DLMFEvenLower_eq_neg_jacobiLower]
    have hbalance := mode4DLMFEvenSimilarityScale_lower_balance G j.val hG
    rw [hl]
    calc
      -mode4JacobiLower G (j.val + 1) *
          mode4DLMFEvenSimilarityScale G j.val =
        -(mode4JacobiLower G (j.val + 1) *
          mode4DLMFEvenSimilarityScale G j.val) := by ring
      _ = -(mode4DLMFEvenSimilarityScale G (j.val + 1) *
          mode4JacobiSymmetricOff G j.val) := by rw [hbalance]
      _ = mode4DLMFEvenSimilarityScale G (j.val + 1) *
          -mode4JacobiSymmetricOff G j.val := by ring
  · unfold mode4DLMFEvenFiniteMatrix mode4ForwardHermitianFiniteMatrix
    rw [if_neg hdiag, if_neg hdiag, if_neg hu, if_neg hu,
      if_neg hl, if_neg hl]
    ring

/-- Matrix spelling of the exact positive diagonal similarity. -/
theorem mode4DLMFEvenFiniteMatrix_mul_diagonal_eq_diagonal_mul_forwardHermitian
    (G Λ : ℝ) (d : ℕ) (hG : 0 < G) :
    mode4DLMFEvenFiniteMatrix G Λ d *
        Matrix.diagonal (fun i : Fin d =>
          mode4DLMFEvenSimilarityScale G i.val) =
      Matrix.diagonal (fun i : Fin d =>
          mode4DLMFEvenSimilarityScale G i.val) *
        mode4ForwardHermitianFiniteMatrix G Λ d := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mode4DLMFEvenFiniteMatrix_mul_scale_eq_scale_mul_forwardHermitian
    G Λ d hG i j

/-- Reversing the source-ordered Hermitian matrix gives exactly the existing
left-continuant matrix.  This is the explicit finite permutation step; it is
separate from the positive diagonal similarity above. -/
theorem mode4ForwardHermitianFiniteMatrix_submatrix_rev_eq_leftContinuant
    (G Λ : ℝ) (d : ℕ) :
    Matrix.submatrix (mode4ForwardHermitianFiniteMatrix G Λ d)
        Fin.rev Fin.rev =
      mode4HermitianLeftContinuantMatrix G Λ d := by
  induction d with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simp [mode4ForwardHermitianFiniteMatrix,
          mode4HermitianLeftContinuantMatrix, Matrix.submatrix, Fin.rev]
      · by_cases hj : j'.val = 0
        · simp [mode4ForwardHermitianFiniteMatrix,
            mode4HermitianLeftContinuantMatrix, Matrix.submatrix, Fin.rev, hj]
          have hjlt := j'.isLt
          have hn : 0 < n := by omega
          have hne : n ≠ n - 1 := by omega
          have heq : n - 1 + 1 = n := by omega
          simp [hne, heq]
        · simp [mode4ForwardHermitianFiniteMatrix,
            mode4HermitianLeftContinuantMatrix, Matrix.submatrix, Fin.rev, hj]
          have hjlt := j'.isLt
          have hle : j'.val + 1 ≤ n := by omega
          have hsub := Nat.sub_add_cancel hle
          have hne1 : n ≠ n - (j'.val + 1) := by omega
          have hne2 : n - (j'.val + 1) ≠ n + 1 := by omega
          have hne3 : n ≠ n - (j'.val + 1) + 1 := by omega
          simp [hne1, hne2, hne3]
      · by_cases hi : i'.val = 0
        · simp [mode4ForwardHermitianFiniteMatrix,
            mode4HermitianLeftContinuantMatrix, Matrix.submatrix, Fin.rev, hi]
          have hilt := i'.isLt
          have hn : 0 < n := by omega
          have hne : n - 1 ≠ n := by omega
          have heq : n - 1 + 1 = n := by omega
          simp [hne, heq]
        · simp [mode4ForwardHermitianFiniteMatrix,
            mode4HermitianLeftContinuantMatrix, Matrix.submatrix, Fin.rev, hi]
          have hilt := i'.isLt
          have hle : i'.val + 1 ≤ n := by omega
          have hsub := Nat.sub_add_cancel hle
          have hne1 : n - (i'.val + 1) ≠ n := by omega
          have hne2 : n ≠ n - (i'.val + 1) + 1 := by omega
          have hne3 : n - (i'.val + 1) ≠ n + 1 := by omega
          simp [hne1, hne2, hne3]
      · have h := congrFun (congrFun ih i') j'
        simpa [mode4ForwardHermitianFiniteMatrix,
          mode4HermitianLeftContinuantMatrix, Matrix.submatrix, Fin.rev] using h

/-- Consumer-sized source crosswalk: the literal DLMF 30.16.1 even matrix is
positively diagonally similar to a forward Hermitian matrix, and the explicit
reversal permutation is exactly the existing project left-continuant matrix.

This statement imports no ordered-eigenvalue limit and no endpoint count. -/
theorem mode4DLMFEvenFiniteMatrix_similar_hermitianLeftContinuantMatrix
    (G Λ : ℝ) (d : ℕ) (hG : 0 < G) :
    (mode4DLMFEvenFiniteMatrix G Λ d *
          Matrix.diagonal (fun i : Fin d =>
            mode4DLMFEvenSimilarityScale G i.val) =
        Matrix.diagonal (fun i : Fin d =>
            mode4DLMFEvenSimilarityScale G i.val) *
          mode4ForwardHermitianFiniteMatrix G Λ d) ∧
      (Matrix.submatrix (mode4ForwardHermitianFiniteMatrix G Λ d)
          Fin.rev Fin.rev =
        mode4HermitianLeftContinuantMatrix G Λ d) ∧
      (∀ i : Fin d, 0 < mode4DLMFEvenSimilarityScale G i.val) := by
  exact ⟨
    mode4DLMFEvenFiniteMatrix_mul_diagonal_eq_diagonal_mul_forwardHermitian
      G Λ d hG,
    mode4ForwardHermitianFiniteMatrix_submatrix_rev_eq_leftContinuant G Λ d,
    fun i => mode4DLMFEvenSimilarityScale_pos G i.val hG⟩

#print axioms mode4DLMFEvenDiagonal_eq_jacobiCenter
#print axioms mode4DLMFEvenSimilarityScale_pos
#print axioms mode4DLMFEvenFiniteMatrix_mul_scale_eq_scale_mul_forwardHermitian
#print axioms mode4DLMFEvenFiniteMatrix_mul_diagonal_eq_diagonal_mul_forwardHermitian
#print axioms mode4ForwardHermitianFiniteMatrix_submatrix_rev_eq_leftContinuant
#print axioms mode4DLMFEvenFiniteMatrix_similar_hermitianLeftContinuantMatrix
