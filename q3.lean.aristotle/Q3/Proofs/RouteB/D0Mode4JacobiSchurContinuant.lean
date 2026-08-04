import Q3.Proofs.RouteB.D0Mode4JacobiRootFunction

/-!
# The mode-four Schur continuant orientation

This file constructs the finite Jacobi/Schur matrix in reversed index order, proves its
determinant recurrence, identifies the determinant with the scalar Schur continuant, and then
proves the exact positive-factor identity with `mode4RootFunction`.  No finite-truncation
eigenvalue or endpoint sign is assumed.
-/

open scoped BigOperators

noncomputable section

/-- Product of the positive upper Jacobi coefficients through index `K - 1`. -/
noncomputable def mode4JacobiUpperProd
    (G : ℝ) (K : ℕ) : ℝ :=
  ∏ q ∈ Finset.range K, mode4JacobiUpper G q

/-- The left solution after clearing every upper-coefficient denominator. -/
noncomputable def mode4ScaledLeftContinuant
    (G Λ : ℝ) (K : ℕ) : ℝ :=
  mode4JacobiUpperProd G K * (mode4LeftPair G Λ K).2

/-- Scalar Schur continuant at the matching index.  The final term is the exact infinite
right-tail boundary correction, not a finite terminal truncation. -/
noncomputable def mode4SchurContinuant
    (mProject K : ℕ) (Λ : ℝ) : ℝ :=
  let G := mode4JacobiG mProject
  mode4ScaledLeftContinuant G Λ K -
    mode4RightTailLimit mProject Λ K *
      mode4JacobiUpper G (K - 1) *
        mode4ScaledLeftContinuant G Λ (K - 1)

private theorem mode4JacobiG_pos_for_upperProd
    (mProject : ℕ) (hm : 2 ≤ mProject) :
    0 < mode4JacobiG mProject := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  unfold mode4JacobiG
  positivity

theorem mode4JacobiUpperProd_pos
    (mProject K : ℕ)
    (hm : 2 ≤ mProject) :
    0 < mode4JacobiUpperProd (mode4JacobiG mProject) K := by
  have hG : 0 < mode4JacobiG mProject :=
    mode4JacobiG_pos_for_upperProd mProject hm
  unfold mode4JacobiUpperProd
  exact Finset.prod_pos fun q _ => mode4JacobiUpper_pos _ q hG

theorem mode4ScaledLeftContinuant_zero
    (G Λ : ℝ) :
    mode4ScaledLeftContinuant G Λ 0 = 1 := by
  simp [mode4ScaledLeftContinuant, mode4JacobiUpperProd, mode4LeftPair]

theorem mode4ScaledLeftContinuant_one
    (mProject : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ 1 =
      mode4JacobiCenter (mode4JacobiG mProject) Λ 0 := by
  have hG : 0 < mode4JacobiG mProject :=
    mode4JacobiG_pos_for_upperProd mProject hm
  have hU : mode4JacobiUpper (mode4JacobiG mProject) 0 ≠ 0 :=
    (mode4JacobiUpper_pos _ 0 hG).ne'
  simp only [mode4ScaledLeftContinuant, mode4JacobiUpperProd,
    Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    mode4LeftPair]
  rw [mul_one, mul_zero, sub_zero]
  exact mul_div_cancel₀ _ hU

/-- Clearing the positive upper factors turns the normalized left solution into the ordinary
three-term continuant recurrence. -/
theorem mode4ScaledLeftContinuant_succ_succ
    (mProject q : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    let G := mode4JacobiG mProject
    mode4ScaledLeftContinuant G Λ (q + 2) =
      mode4JacobiCenter G Λ (q + 1) *
          mode4ScaledLeftContinuant G Λ (q + 1) -
        mode4JacobiLower G (q + 1) *
          mode4JacobiUpper G q *
            mode4ScaledLeftContinuant G Λ q := by
  let G := mode4JacobiG mProject
  have htransfer := mode4LeftPair_succ_transfer mProject (q + 1) Λ hm
  dsimp only at htransfer ⊢
  rw [mode4ScaledLeftContinuant, mode4ScaledLeftContinuant,
    mode4ScaledLeftContinuant]
  rw [mode4JacobiUpperProd, mode4JacobiUpperProd,
    mode4JacobiUpperProd]
  rw [Finset.prod_range_succ, Finset.prod_range_succ]
  rcases htransfer with ⟨hfst, hrec⟩
  have hrec' :
      mode4JacobiUpper (mode4JacobiG mProject) (q + 1) *
          (mode4LeftPair (mode4JacobiG mProject) Λ (q + 2)).2 =
        mode4JacobiCenter (mode4JacobiG mProject) Λ (q + 1) *
            (mode4LeftPair (mode4JacobiG mProject) Λ (q + 1)).2 -
          mode4JacobiLower (mode4JacobiG mProject) (q + 1) *
            (mode4LeftPair (mode4JacobiG mProject) Λ (q + 1)).1 := by
    simpa [Nat.add_assoc] using hrec
  have hprev :
      (mode4LeftPair (mode4JacobiG mProject) Λ (q + 1)).1 =
        (mode4LeftPair (mode4JacobiG mProject) Λ q).2 := by
    simp [mode4LeftPair]
  rw [hprev] at hrec'
  linear_combination
    ((∏ x ∈ Finset.range q,
        mode4JacobiUpper (mode4JacobiG mProject) x) *
      mode4JacobiUpper (mode4JacobiG mProject) q) * hrec'

/-- Exact positive-factor orientation between the scalar Schur continuant and the committed
division-free root residual. -/
theorem mode4SchurContinuant_eq_upperProd_mul_rootFunction
    (mProject K : ℕ)
    (Λ : ℝ)
    (hK : 1 ≤ K) :
    mode4SchurContinuant mProject K Λ =
      mode4JacobiUpperProd (mode4JacobiG mProject) K *
        mode4RootFunction mProject K Λ := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  simp only [mode4SchurContinuant, mode4ScaledLeftContinuant,
    mode4JacobiUpperProd, mode4RootFunction, Nat.succ_sub_one,
    Finset.prod_range_succ, mode4LeftPair]
  ring

theorem mode4SchurContinuant_sign_eq_rootFunction_sign
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K) :
    SignType.sign (mode4SchurContinuant mProject K Λ) =
      SignType.sign (mode4RootFunction mProject K Λ) := by
  rw [mode4SchurContinuant_eq_upperProd_mul_rootFunction mProject K Λ hK,
    sign_mul, sign_pos (mode4JacobiUpperProd_pos mProject K hm), one_mul]

/-- Requested spelling of the upper-factor positivity theorem. -/
theorem mode4JacobiUpper_prod_pos
    (mProject K : ℕ)
    (hm : 2 ≤ mProject) :
    0 < mode4JacobiUpperProd (mode4JacobiG mProject) K :=
  mode4JacobiUpperProd_pos mProject K hm

/-! ## Literal matrix receiver -/

/-- Reversed-index tridiagonal Jacobi block.  Reversing the finite index order puts the newest
Jacobi coefficient in row zero, so Laplace expansion realizes the left continuant recurrence
without any permutation-sign correction. -/
noncomputable def mode4LeftContinuantMatrix
    (G Λ : ℝ) : (K : ℕ) → Matrix (Fin K) (Fin K) ℝ
  | 0 => fun i => Fin.elim0 i
  | n + 1 => fun i j =>
      Fin.cases
        (Fin.cases
          (mode4JacobiCenter G Λ n)
          (fun j' => if j'.val = 0 then -mode4JacobiLower G n else 0)
          j)
        (fun i' =>
          Fin.cases
            (if i'.val = 0 then -mode4JacobiUpper G (n - 1) else 0)
            (fun j' => mode4LeftContinuantMatrix G Λ n i' j')
            j)
        i

private theorem mode4LeftContinuantMatrix_minor_zero
    (G Λ : ℝ) (n : ℕ) :
    Matrix.submatrix (mode4LeftContinuantMatrix G Λ (n + 1))
        Fin.succ (Fin.succAbove 0) =
      mode4LeftContinuantMatrix G Λ n := by
  ext i j
  simp [mode4LeftContinuantMatrix]

private theorem mode4LeftContinuantMatrix_minor_one_det
    (G Λ : ℝ) (n : ℕ) :
    (Matrix.submatrix (mode4LeftContinuantMatrix G Λ (n + 2))
        Fin.succ (Fin.succ 0).succAbove).det =
      -mode4JacobiUpper G n *
        (mode4LeftContinuantMatrix G Λ n).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.submatrix (mode4LeftContinuantMatrix G Λ (n + 2))
      Fin.succ (Fin.succ 0).succAbove
  have hB00 : B 0 0 = -mode4JacobiUpper G n := by
    simp only [B, Matrix.submatrix_apply, mode4LeftContinuantMatrix,
      Fin.succ_zero_eq_one]
    change (if (0 : ℕ) = 0 then -mode4JacobiUpper G n else 0) = _
    simp
  have hBsucc0 (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, mode4LeftContinuantMatrix]
  have hBtail :
      Matrix.submatrix B (Fin.succAbove 0) Fin.succ =
        mode4LeftContinuantMatrix G Λ n := by
    ext i j
    simp [B, mode4LeftContinuantMatrix]
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

private theorem mode4LeftContinuantMatrix_det_succ_succ
    (G Λ : ℝ) (n : ℕ) :
    (mode4LeftContinuantMatrix G Λ (n + 2)).det =
      mode4JacobiCenter G Λ (n + 1) *
          (mode4LeftContinuantMatrix G Λ (n + 1)).det -
        mode4JacobiLower G (n + 1) * mode4JacobiUpper G n *
          (mode4LeftContinuantMatrix G Λ n).det := by
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    mode4LeftContinuantMatrix G Λ (n + 2)
  have hA00 : A 0 0 = mode4JacobiCenter G Λ (n + 1) := by
    simp [A, mode4LeftContinuantMatrix]
  have hA01 : A 0 1 = -mode4JacobiLower G (n + 1) := by
    simp only [A, mode4LeftContinuantMatrix, Fin.cases_zero]
    change (if (0 : ℕ) = 0 then -mode4JacobiLower G (n + 1) else 0) = _
    simp
  have hA0succ : A 0 (Fin.succ 0) = -mode4JacobiLower G (n + 1) := by
    simpa only [Fin.succ_zero_eq_one] using hA01
  have hA0ss (j : Fin n) : A 0 j.succ.succ = 0 := by
    simp [A, mode4LeftContinuantMatrix]
  have hminor0 :
      (Matrix.submatrix A Fin.succ (Fin.succAbove 0)).det =
        (mode4LeftContinuantMatrix G Λ (n + 1)).det := by
    rw [show A = mode4LeftContinuantMatrix G Λ (n + 2) from rfl]
    exact congrArg Matrix.det
      (mode4LeftContinuantMatrix_minor_zero G Λ (n + 1))
  have hminor1 :
      (Matrix.submatrix A Fin.succ ((Fin.succ 0).succAbove)).det =
        -mode4JacobiUpper G n *
          (mode4LeftContinuantMatrix G Λ n).det := by
    rw [show A = mode4LeftContinuantMatrix G Λ (n + 2) from rfl]
    exact mode4LeftContinuantMatrix_minor_one_det G Λ n
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
  ring

theorem mode4LeftContinuantMatrix_det_eq_scaledLeftContinuant
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    (mode4LeftContinuantMatrix (mode4JacobiG mProject) Λ K).det =
      mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ K := by
  induction K using Nat.twoStepInduction with
  | zero =>
      simpa [mode4LeftContinuantMatrix] using
        (mode4ScaledLeftContinuant_zero (mode4JacobiG mProject) Λ).symm
  | one =>
      rw [mode4ScaledLeftContinuant_one mProject Λ hm]
      simp [mode4LeftContinuantMatrix]
  | more n ih0 ih1 =>
      rw [mode4LeftContinuantMatrix_det_succ_succ,
        mode4ScaledLeftContinuant_succ_succ mProject n Λ hm,
        ih1, ih0]

/-- The reversed finite Jacobi block with the exact infinite right-tail Schur correction
inserted in its newest diagonal entry. -/
noncomputable def mode4SchurMatrix
    (mProject : ℕ) (Λ : ℝ) : (K : ℕ) → Matrix (Fin K) (Fin K) ℝ
  | 0 => fun i => Fin.elim0 i
  | n + 1 => fun i j =>
      let G := mode4JacobiG mProject
      Fin.cases
        (Fin.cases
          (mode4JacobiCenter G Λ n -
            mode4JacobiUpper G n * mode4RightTailLimit mProject Λ (n + 1))
          (fun j' => if j'.val = 0 then -mode4JacobiLower G n else 0)
          j)
        (fun i' =>
          Fin.cases
            (if i'.val = 0 then -mode4JacobiUpper G (n - 1) else 0)
            (fun j' => mode4LeftContinuantMatrix G Λ n i' j')
            j)
        i

private theorem mode4SchurMatrix_det_one
    (mProject : ℕ) (Λ : ℝ) :
    (mode4SchurMatrix mProject Λ 1).det =
      mode4JacobiCenter (mode4JacobiG mProject) Λ 0 -
        mode4JacobiUpper (mode4JacobiG mProject) 0 *
          mode4RightTailLimit mProject Λ 1 := by
  simp [mode4SchurMatrix]

private theorem mode4SchurMatrix_minor_zero
    (mProject : ℕ) (Λ : ℝ) (n : ℕ) :
    Matrix.submatrix (mode4SchurMatrix mProject Λ (n + 1))
        Fin.succ (Fin.succAbove 0) =
      mode4LeftContinuantMatrix (mode4JacobiG mProject) Λ n := by
  ext i j
  simp [mode4SchurMatrix]

private theorem mode4SchurMatrix_minor_one_det
    (mProject : ℕ) (Λ : ℝ) (n : ℕ) :
    (Matrix.submatrix (mode4SchurMatrix mProject Λ (n + 2))
        Fin.succ (Fin.succ 0).succAbove).det =
      -mode4JacobiUpper (mode4JacobiG mProject) n *
        (mode4LeftContinuantMatrix (mode4JacobiG mProject) Λ n).det := by
  let G := mode4JacobiG mProject
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.submatrix (mode4SchurMatrix mProject Λ (n + 2))
      Fin.succ (Fin.succ 0).succAbove
  have hB00 : B 0 0 = -mode4JacobiUpper G n := by
    simp only [B, Matrix.submatrix_apply, mode4SchurMatrix,
      Fin.succ_zero_eq_one]
    change (if (0 : ℕ) = 0 then -mode4JacobiUpper G n else 0) = _
    simp
  have hBsucc0 (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, mode4SchurMatrix]
  have hBtail :
      Matrix.submatrix B (Fin.succAbove 0) Fin.succ =
        mode4LeftContinuantMatrix G Λ n := by
    ext i j
    simp only [B, Matrix.submatrix_apply, mode4SchurMatrix]
    change mode4LeftContinuantMatrix (mode4JacobiG mProject) Λ (n + 1)
        i.succ j.succ = mode4LeftContinuantMatrix G Λ n i j
    simp [G, mode4LeftContinuantMatrix]
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

private theorem mode4SchurMatrix_det_succ_succ
    (mProject n : ℕ) (Λ : ℝ) :
    let G := mode4JacobiG mProject
    (mode4SchurMatrix mProject Λ (n + 2)).det =
      (mode4JacobiCenter G Λ (n + 1) -
          mode4JacobiUpper G (n + 1) *
            mode4RightTailLimit mProject Λ (n + 2)) *
          (mode4LeftContinuantMatrix G Λ (n + 1)).det -
        mode4JacobiLower G (n + 1) * mode4JacobiUpper G n *
          (mode4LeftContinuantMatrix G Λ n).det := by
  let G := mode4JacobiG mProject
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    mode4SchurMatrix mProject Λ (n + 2)
  have hA00 : A 0 0 =
      mode4JacobiCenter G Λ (n + 1) -
        mode4JacobiUpper G (n + 1) *
          mode4RightTailLimit mProject Λ (n + 2) := by
    simp [A, G, mode4SchurMatrix]
  have hA0succ : A 0 (Fin.succ 0) = -mode4JacobiLower G (n + 1) := by
    dsimp only [G]
    simp only [A, mode4SchurMatrix, Fin.cases_zero]
    change (if (0 : ℕ) = 0 then -mode4JacobiLower G (n + 1) else 0) = _
    simp [G]
  have hA0ss (j : Fin n) : A 0 j.succ.succ = 0 := by
    simp [A, mode4SchurMatrix]
  have hminor0 :
      (Matrix.submatrix A Fin.succ (Fin.succAbove 0)).det =
        (mode4LeftContinuantMatrix G Λ (n + 1)).det := by
    rw [show A = mode4SchurMatrix mProject Λ (n + 2) from rfl]
    exact congrArg Matrix.det
      (mode4SchurMatrix_minor_zero mProject Λ (n + 1))
  have hminor1 :
      (Matrix.submatrix A Fin.succ ((Fin.succ 0).succAbove)).det =
        -mode4JacobiUpper G n *
          (mode4LeftContinuantMatrix G Λ n).det := by
    rw [show A = mode4SchurMatrix mProject Λ (n + 2) from rfl]
    exact mode4SchurMatrix_minor_one_det mProject Λ n
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
  ring

theorem det_mode4SchurMatrix_eq_schurContinuant
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K) :
    (mode4SchurMatrix mProject Λ K).det =
      mode4SchurContinuant mProject K Λ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  cases n with
  | zero =>
      rw [mode4SchurMatrix_det_one]
      rw [mode4SchurContinuant]
      rw [mode4ScaledLeftContinuant_one mProject Λ hm,
        mode4ScaledLeftContinuant_zero]
      simp only [Nat.succ_eq_add_one, Nat.zero_add, Nat.reduceSubDiff]
      ring
  | succ n =>
      rw [mode4SchurMatrix_det_succ_succ]
      rw [mode4LeftContinuantMatrix_det_eq_scaledLeftContinuant
          mProject (n + 1) Λ hm,
        mode4LeftContinuantMatrix_det_eq_scaledLeftContinuant mProject n Λ hm]
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

theorem det_mode4SchurMatrix_eq_upperProd_mul_rootFunction
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K) :
    (mode4SchurMatrix mProject Λ K).det =
      mode4JacobiUpperProd (mode4JacobiG mProject) K *
        mode4RootFunction mProject K Λ := by
  rw [det_mode4SchurMatrix_eq_schurContinuant mProject K Λ hm hK,
    mode4SchurContinuant_eq_upperProd_mul_rootFunction mProject K Λ hK]

theorem mode4SchurMatrix_det_sign_eq_rootFunction_sign
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 1 ≤ K) :
    SignType.sign (mode4SchurMatrix mProject Λ K).det =
      SignType.sign (mode4RootFunction mProject K Λ) := by
  rw [det_mode4SchurMatrix_eq_schurContinuant mProject K Λ hm hK,
    mode4SchurContinuant_sign_eq_rootFunction_sign mProject K Λ hm hK]

#print axioms mode4JacobiUpperProd_pos
#print axioms mode4ScaledLeftContinuant_succ_succ
#print axioms mode4SchurContinuant_eq_upperProd_mul_rootFunction
#print axioms mode4SchurContinuant_sign_eq_rootFunction_sign
#print axioms mode4LeftContinuantMatrix_det_eq_scaledLeftContinuant
#print axioms det_mode4SchurMatrix_eq_schurContinuant
#print axioms det_mode4SchurMatrix_eq_upperProd_mul_rootFunction
#print axioms mode4SchurMatrix_det_sign_eq_rootFunction_sign
