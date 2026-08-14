import Q3.Proofs.RouteB.D0Mode4BackwardTailSchurConvergence

/-!
# Actual finite mode-four Jacobi truncation and Schur crosswalk

This file realizes the finite backward tail used by
`mode4BackwardTailSchurApprox` as the literal Schur correction of a finite
source Jacobi truncation.  The retained coordinates are kept in the existing
reversed order (`q = K - 1` first), while the eliminated coordinates run
forward through `q = K, ..., K + d - 1`.  The last finite row has no outgoing
coefficient: this is exactly the terminal-zero convention in
`mode4BackwardTail mProject Λ K d 0`.

The source lock is DLMF 30.16.1 together with the already proved coefficient
crosswalk and Hermitian diagonal similarity.  No positivity or inertia claim
is made here.
-/

noncomputable section

private noncomputable def mode4ForwardFiniteTailMatrix
    (G Λ : ℝ) (K : ℕ) : (d : ℕ) → Matrix (Fin d) (Fin d) ℝ
  | 0 => fun i => Fin.elim0 i
  | n + 1 => fun i j =>
      Fin.cases
        (Fin.cases
          (mode4JacobiCenter G Λ K)
          (fun j' => if j'.val = 0 then -mode4JacobiSymmetricOff G K else 0)
          j)
        (fun i' =>
          Fin.cases
            (if i'.val = 0 then -mode4JacobiSymmetricOff G K else 0)
            (fun j' => mode4ForwardFiniteTailMatrix G Λ (K + 1) n i' j')
            j)
        i

private noncomputable def mode4RetainedTailCoupling
    (G : ℝ) (K d : ℕ) : Matrix (Fin K) (Fin d) ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then -mode4JacobiSymmetricOff G (K - 1) else 0

private theorem mode4RetainedTailCoupling_eq_single
    (G : ℝ) (n e : ℕ) :
    mode4RetainedTailCoupling G (n + 1) (e + 1) =
      Matrix.single (0 : Fin (n + 1)) (0 : Fin (e + 1))
        (-mode4JacobiSymmetricOff G n) := by
  ext i j
  simp [mode4RetainedTailCoupling, Matrix.single, eq_comm]

/-- The actual finite Hermitian Jacobi truncation split after the first `K`
source coordinates.  The retained block is reversed, the finite tail is
forward, and the only cross-block edge is `q = K - 1 ↔ q = K`. -/
noncomputable def mode4ActualFiniteJacobiTruncation
    (mProject : ℕ) (Λ : ℝ) (K d : ℕ) :
    Matrix (Fin K ⊕ Fin d) (Fin K ⊕ Fin d) ℝ :=
  let G := mode4JacobiG mProject
  let B := mode4RetainedTailCoupling G K d
  Matrix.fromBlocks
    (mode4HermitianLeftContinuantMatrix G Λ K)
    B B.conjTranspose
    (mode4ForwardFiniteTailMatrix G Λ K d)

private theorem mode4ForwardFiniteTailMatrix_isHermitian
    (G Λ : ℝ) (K d : ℕ) :
    (mode4ForwardFiniteTailMatrix G Λ K d).IsHermitian := by
  induction d generalizing K with
  | zero =>
      apply Matrix.IsHermitian.ext
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      apply Matrix.IsHermitian.ext
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simp [mode4ForwardFiniteTailMatrix]
      · simp [mode4ForwardFiniteTailMatrix]
      · simp [mode4ForwardFiniteTailMatrix]
      · simpa [mode4ForwardFiniteTailMatrix] using (ih (K + 1)).apply i' j'

/-- The literal finite source truncation is Hermitian. -/
theorem mode4ActualFiniteJacobiTruncation_isHermitian
    (mProject : ℕ) (Λ : ℝ) (K d : ℕ) :
    (mode4ActualFiniteJacobiTruncation mProject Λ K d).IsHermitian := by
  unfold mode4ActualFiniteJacobiTruncation
  exact Matrix.IsHermitian.fromBlocks
    (mode4HermitianLeftContinuantMatrix_isHermitian
      (mode4JacobiG mProject) Λ K)
    rfl
    (mode4ForwardFiniteTailMatrix_isHermitian
      (mode4JacobiG mProject) Λ K d)

private theorem mode4ForwardFiniteTailMatrix_minor_zero
    (G Λ : ℝ) (K n : ℕ) :
    Matrix.submatrix (mode4ForwardFiniteTailMatrix G Λ K (n + 1))
        Fin.succ (Fin.succAbove 0) =
      mode4ForwardFiniteTailMatrix G Λ (K + 1) n := by
  ext i j
  simp [mode4ForwardFiniteTailMatrix]

private theorem mode4ForwardFiniteTailMatrix_minor_one_det
    (G Λ : ℝ) (K n : ℕ) :
    (Matrix.submatrix (mode4ForwardFiniteTailMatrix G Λ K (n + 2))
        Fin.succ (Fin.succ 0).succAbove).det =
      -mode4JacobiSymmetricOff G K *
        (mode4ForwardFiniteTailMatrix G Λ (K + 2) n).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.submatrix (mode4ForwardFiniteTailMatrix G Λ K (n + 2))
      Fin.succ (Fin.succ 0).succAbove
  have hB00 : B 0 0 = -mode4JacobiSymmetricOff G K := by
    simp only [B, Matrix.submatrix_apply, mode4ForwardFiniteTailMatrix,
      Fin.succ_zero_eq_one]
    change (if (0 : ℕ) = 0 then -mode4JacobiSymmetricOff G K else 0) = _
    simp
  have hBsucc0 (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, mode4ForwardFiniteTailMatrix]
  have hBtail :
      Matrix.submatrix B (Fin.succAbove 0) Fin.succ =
        mode4ForwardFiniteTailMatrix G Λ (K + 2) n := by
    ext i j
    simp [B, mode4ForwardFiniteTailMatrix]
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

private theorem mode4ForwardFiniteTailMatrix_det_succ_succ
    (G Λ : ℝ) (K n : ℕ) (hG : 0 < G) :
    (mode4ForwardFiniteTailMatrix G Λ K (n + 2)).det =
      mode4JacobiCenter G Λ K *
          (mode4ForwardFiniteTailMatrix G Λ (K + 1) (n + 1)).det -
        mode4JacobiLower G (K + 1) * mode4JacobiUpper G K *
          (mode4ForwardFiniteTailMatrix G Λ (K + 2) n).det := by
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    mode4ForwardFiniteTailMatrix G Λ K (n + 2)
  have hA00 : A 0 0 = mode4JacobiCenter G Λ K := by
    simp [A, mode4ForwardFiniteTailMatrix]
  have hA0succ : A 0 (Fin.succ 0) = -mode4JacobiSymmetricOff G K := by
    simp only [A, mode4ForwardFiniteTailMatrix, Fin.cases_zero]
    change (if (0 : ℕ) = 0 then -mode4JacobiSymmetricOff G K else 0) = _
    simp
  have hA0ss (j : Fin n) : A 0 j.succ.succ = 0 := by
    simp [A, mode4ForwardFiniteTailMatrix]
  have hminor0 :
      (Matrix.submatrix A Fin.succ (Fin.succAbove 0)).det =
        (mode4ForwardFiniteTailMatrix G Λ (K + 1) (n + 1)).det := by
    rw [show A = mode4ForwardFiniteTailMatrix G Λ K (n + 2) from rfl]
    exact congrArg Matrix.det
      (mode4ForwardFiniteTailMatrix_minor_zero G Λ K (n + 1))
  have hminor1 :
      (Matrix.submatrix A Fin.succ ((Fin.succ 0).succAbove)).det =
        -mode4JacobiSymmetricOff G K *
          (mode4ForwardFiniteTailMatrix G Λ (K + 2) n).det := by
    rw [show A = mode4ForwardFiniteTailMatrix G Λ K (n + 2) from rfl]
    exact mode4ForwardFiniteTailMatrix_minor_one_det G Λ K n
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
    _ = mode4JacobiCenter G Λ K *
          (mode4ForwardFiniteTailMatrix G Λ (K + 1) (n + 1)).det -
        mode4JacobiSymmetricOff G K ^ 2 *
          (mode4ForwardFiniteTailMatrix G Λ (K + 2) n).det := by ring
    _ = _ := by rw [mode4JacobiSymmetricOff_sq G K hG]

private def mode4FiniteTailPivotsNonzero
    (mProject : ℕ) (Λ : ℝ) : (K d : ℕ) → Prop
  | _, 0 => True
  | K, n + 1 =>
      mode4JacobiCenter (mode4JacobiG mProject) Λ K -
          mode4JacobiUpper (mode4JacobiG mProject) K *
            mode4BackwardTail mProject Λ (K + 1) n 0 ≠ 0 ∧
        mode4FiniteTailPivotsNonzero mProject Λ (K + 1) n

private theorem mode4ForwardFiniteTailMatrix_det_ne_zero_and_backwardTail_eq
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hpiv : mode4FiniteTailPivotsNonzero mProject Λ K (d + 1)) :
    (mode4ForwardFiniteTailMatrix
        (mode4JacobiG mProject) Λ K (d + 1)).det ≠ 0 ∧
      mode4BackwardTail mProject Λ K (d + 1) 0 =
        mode4JacobiLower (mode4JacobiG mProject) K *
          (mode4ForwardFiniteTailMatrix
            (mode4JacobiG mProject) Λ (K + 1) d).det /
          (mode4ForwardFiniteTailMatrix
            (mode4JacobiG mProject) Λ K (d + 1)).det := by
  have hG : 0 < mode4JacobiG mProject := by
    have hmR : (0 : ℝ) < (mProject : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    unfold mode4JacobiG
    positivity
  induction d generalizing K with
  | zero =>
      simpa [mode4FiniteTailPivotsNonzero, mode4BackwardTail,
        mode4TailMap, mode4ForwardFiniteTailMatrix] using
        And.intro hpiv.1 hpiv.1
  | succ n ih =>
      rcases hpiv with ⟨houter, hpivSuffix⟩
      rcases ih (K := K + 1) hpivSuffix with ⟨hdetSuffix, htailSuffix⟩
      have hfactor :
          (mode4ForwardFiniteTailMatrix
              (mode4JacobiG mProject) Λ K (n + 2)).det =
            (mode4JacobiCenter (mode4JacobiG mProject) Λ K -
                mode4JacobiUpper (mode4JacobiG mProject) K *
                  mode4BackwardTail mProject Λ (K + 1) (n + 1) 0) *
              (mode4ForwardFiniteTailMatrix
                (mode4JacobiG mProject) Λ (K + 1) (n + 1)).det := by
        rw [mode4ForwardFiniteTailMatrix_det_succ_succ
          (mode4JacobiG mProject) Λ K n hG]
        rw [htailSuffix]
        field_simp [hdetSuffix]
      constructor
      · rw [hfactor]
        exact mul_ne_zero houter hdetSuffix
      · change
          mode4TailMap (mode4JacobiG mProject) Λ K
              (mode4BackwardTail mProject Λ (K + 1) (n + 1) 0) = _
        unfold mode4TailMap
        rw [hfactor]
        field_simp [houter, hdetSuffix]

private theorem mode4BackwardTail_eq_lower_mul_det_div_det
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hpiv : mode4FiniteTailPivotsNonzero mProject Λ K (d + 1)) :
    mode4BackwardTail mProject Λ K (d + 1) 0 =
      mode4JacobiLower (mode4JacobiG mProject) K *
        (mode4ForwardFiniteTailMatrix
          (mode4JacobiG mProject) Λ (K + 1) d).det /
        (mode4ForwardFiniteTailMatrix
          (mode4JacobiG mProject) Λ K (d + 1)).det := by
  exact (mode4ForwardFiniteTailMatrix_det_ne_zero_and_backwardTail_eq
    mProject K d Λ hm hpiv).2

private theorem mode4ForwardFiniteTailMatrix_inv_zero_zero
    (mProject K d : ℕ) (Λ : ℝ) :
    (mode4ForwardFiniteTailMatrix
        (mode4JacobiG mProject) Λ K (d + 1))⁻¹ 0 0 =
      (mode4ForwardFiniteTailMatrix
        (mode4JacobiG mProject) Λ (K + 1) d).det /
      (mode4ForwardFiniteTailMatrix
        (mode4JacobiG mProject) Λ K (d + 1)).det := by
  let D := mode4ForwardFiniteTailMatrix
    (mode4JacobiG mProject) Λ K (d + 1)
  have hminor :
      Matrix.submatrix D
          ((0 : Fin (d + 1)).succAbove)
          ((0 : Fin (d + 1)).succAbove) =
        mode4ForwardFiniteTailMatrix
          (mode4JacobiG mProject) Λ (K + 1) d := by
    simpa [D] using
      (mode4ForwardFiniteTailMatrix_minor_zero
        (mode4JacobiG mProject) Λ K d)
  change D⁻¹ 0 0 = _
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [hminor]
  norm_num
  change
    D.det⁻¹ *
        (mode4ForwardFiniteTailMatrix
          (mode4JacobiG mProject) Λ (K + 1) d).det =
      (mode4ForwardFiniteTailMatrix
          (mode4JacobiG mProject) Λ (K + 1) d).det / D.det
  rw [div_eq_mul_inv]
  ring

/-- Under the explicit nonvanishing of the finite elimination pivots, the
Schur complement of the actual finite source truncation onto the retained
`Fin K` block is exactly the previously defined terminal-zero approximation. -/
theorem mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hpiv : mode4FiniteTailPivotsNonzero mProject Λ K d) :
    let M := mode4ActualFiniteJacobiTruncation mProject Λ K d
    M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁ =
      mode4BackwardTailSchurApprox mProject Λ K d := by
  cases d with
  | zero =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
      simp only [mode4ActualFiniteJacobiTruncation,
        Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
        Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j <;>
        simp [mode4BackwardTailSchurApprox, mode4BackwardTail,
          mode4HermitianLeftContinuantMatrix]
  | succ e =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
      have htail := mode4BackwardTail_eq_lower_mul_det_div_det
        mProject (n + 1) e Λ hm hpiv
      have hinv := mode4ForwardFiniteTailMatrix_inv_zero_zero
        mProject (n + 1) e Λ
      have hG : 0 < mode4JacobiG mProject := by
        have hmR : (0 : ℝ) < (mProject : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
        unfold mode4JacobiG
        positivity
      rw [show
        mode4ActualFiniteJacobiTruncation mProject Λ (n + 1) (e + 1) =
          Matrix.fromBlocks
            (mode4HermitianLeftContinuantMatrix
              (mode4JacobiG mProject) Λ (n + 1))
            (mode4RetainedTailCoupling
              (mode4JacobiG mProject) (n + 1) (e + 1))
            (mode4RetainedTailCoupling
              (mode4JacobiG mProject) (n + 1) (e + 1)).conjTranspose
            (mode4ForwardFiniteTailMatrix
              (mode4JacobiG mProject) Λ (n + 1) (e + 1)) from rfl]
      simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
        Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
      rw [mode4RetainedTailCoupling_eq_single]
      simp only [Matrix.conjTranspose_single, star_trivial,
        Matrix.single_mul_mul_single]
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simp [Matrix.sub_apply, Matrix.single,
          mode4BackwardTailSchurApprox,
          mode4HermitianLeftContinuantMatrix]
        rw [hinv, htail]
        calc
          _ = mode4JacobiSymmetricOff (mode4JacobiG mProject) n ^ 2 *
                ((mode4ForwardFiniteTailMatrix
                    (mode4JacobiG mProject) Λ (n + 1 + 1) e).det /
                  (mode4ForwardFiniteTailMatrix
                    (mode4JacobiG mProject) Λ (n + 1) (e + 1)).det) := by ring
          _ = (mode4JacobiLower (mode4JacobiG mProject) (n + 1) *
                  mode4JacobiUpper (mode4JacobiG mProject) n) *
                ((mode4ForwardFiniteTailMatrix
                    (mode4JacobiG mProject) Λ (n + 1 + 1) e).det /
                  (mode4ForwardFiniteTailMatrix
                    (mode4JacobiG mProject) Λ (n + 1) (e + 1)).det) := by
              rw [mode4JacobiSymmetricOff_sq
                (mode4JacobiG mProject) n hG]
          _ = _ := by ring
      · have hjne : (0 : Fin (n + 1)) ≠ j'.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        simp [Matrix.sub_apply, Matrix.single, hjne,
          mode4BackwardTailSchurApprox,
          mode4HermitianLeftContinuantMatrix]
      · have hine : (0 : Fin (n + 1)) ≠ i'.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        simp [Matrix.sub_apply, Matrix.single, hine,
          mode4BackwardTailSchurApprox,
          mode4HermitianLeftContinuantMatrix]
      · have hine : (0 : Fin (n + 1)) ≠ i'.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        have hjne : (0 : Fin (n + 1)) ≠ j'.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        simp [Matrix.sub_apply, Matrix.single, hine, hjne,
          mode4BackwardTailSchurApprox,
          mode4HermitianLeftContinuantMatrix]

#print axioms mode4ActualFiniteJacobiTruncation_isHermitian
#print axioms mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx
