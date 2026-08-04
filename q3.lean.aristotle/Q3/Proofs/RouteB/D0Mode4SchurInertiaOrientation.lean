import Q3.Proofs.RouteB.D0Mode4JacobiSchurContinuant
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hermitian inertia orientation for the mode-four Schur residual

This file packages the finite-dimensional sign bridge needed after a Sturm count.  For a
Hermitian matrix it proves that the determinant sign is `(-1)` to the number of negative
eigenvalues.  Counts two and three then give the two strict signs of `mode4RootFunction`,
provided a supplier proves that its Hermitian matrix has the same determinant as the committed
`mode4SchurMatrix` and that the endpoint is nonsingular.

The same-determinant Hermitian symmetrization and the concrete source/Sturm counts are deliberately
not supplied here.
-/

open scoped BigOperators

noncomputable section

/-- Number of strictly negative eigenvalues of a finite real Hermitian matrix, counted with the
Mathlib spectral-theorem indexing and hence with multiplicity. -/
noncomputable def mode4HermitianNegativeEigenvalueCount
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues i < 0).card

private theorem mode4Sign_finset_prod
    {n : Type*} [DecidableEq n]
    (s : Finset n) (f : n → ℝ) :
    SignType.sign (∏ i ∈ s, f i) =
      ∏ i ∈ s, SignType.sign (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, sign_mul, ih]

/-- A nonsingular Hermitian determinant has one negative sign for each negative eigenvalue. -/
theorem mode4IsHermitian_sign_det_eq_neg_one_pow_negative_count
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hzero : ∀ i, hA.eigenvalues i ≠ 0) :
    SignType.sign A.det =
      (-1 : SignType) ^ mode4HermitianNegativeEigenvalueCount A hA := by
  rw [hA.det_eq_prod_eigenvalues]
  rw [mode4Sign_finset_prod]
  unfold mode4HermitianNegativeEigenvalueCount
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hsign : ∀ i,
      SignType.sign (hA.eigenvalues i) =
        if hA.eigenvalues i < 0 then -1 else 1 := by
    intro i
    split_ifs with hneg
    · exact sign_neg hneg
    · apply sign_pos
      exact lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm (hzero i))
  simp_rw [hsign]
  rw [Finset.prod_ite]
  simp

theorem mode4IsHermitian_eigenvalues_ne_zero_of_det_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hdet : A.det ≠ 0) :
    ∀ i, hA.eigenvalues i ≠ 0 := by
  have hprod : (∏ i, (↑(hA.eigenvalues i) : ℝ)) ≠ 0 := by
    have heq : A.det = ∏ i, hA.eigenvalues i := by
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using
        hA.det_eq_prod_eigenvalues
    rwa [← heq]
  rw [Finset.prod_ne_zero_iff] at hprod
  intro i
  exact RCLike.ofReal_ne_zero.mp (hprod i (Finset.mem_univ i))

theorem mode4IsHermitian_sign_det_eq_neg_one_pow_negative_count_of_det_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hdet : A.det ≠ 0) :
    SignType.sign A.det =
      (-1 : SignType) ^ mode4HermitianNegativeEigenvalueCount A hA :=
  mode4IsHermitian_sign_det_eq_neg_one_pow_negative_count hA
    (mode4IsHermitian_eigenvalues_ne_zero_of_det_ne_zero hA hdet)

theorem mode4IsHermitian_sign_det_eq_one_of_negative_count_two
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hzero : ∀ i, hA.eigenvalues i ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount A hA = 2) :
    SignType.sign A.det = 1 := by
  rw [mode4IsHermitian_sign_det_eq_neg_one_pow_negative_count hA hzero, hcount]
  decide

theorem mode4IsHermitian_sign_det_eq_neg_one_of_negative_count_three
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hzero : ∀ i, hA.eigenvalues i ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount A hA = 3) :
    SignType.sign A.det = -1 := by
  rw [mode4IsHermitian_sign_det_eq_neg_one_pow_negative_count hA hzero, hcount]
  decide

/-- A Hermitian same-determinant supplier with two negative eigenvalues forces the positive
mode-four residual sign. -/
theorem mode4RootFunction_sign_eq_one_of_hermitian_count_two
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet : A.det = (mode4SchurMatrix mProject Λ K).det)
    (hA_det_ne : A.det ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount A hA = 2) :
    SignType.sign (mode4RootFunction mProject K Λ) = 1 := by
  rw [← mode4SchurMatrix_det_sign_eq_rootFunction_sign mProject K Λ hm hK]
  rw [← hdet]
  exact mode4IsHermitian_sign_det_eq_one_of_negative_count_two hA
    (mode4IsHermitian_eigenvalues_ne_zero_of_det_ne_zero hA hA_det_ne) hcount

/-- A Hermitian same-determinant supplier with three negative eigenvalues forces the negative
mode-four residual sign. -/
theorem mode4RootFunction_sign_eq_neg_one_of_hermitian_count_three
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet : A.det = (mode4SchurMatrix mProject Λ K).det)
    (hA_det_ne : A.det ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount A hA = 3) :
    SignType.sign (mode4RootFunction mProject K Λ) = -1 := by
  rw [← mode4SchurMatrix_det_sign_eq_rootFunction_sign mProject K Λ hm hK]
  rw [← hdet]
  exact mode4IsHermitian_sign_det_eq_neg_one_of_negative_count_three hA
    (mode4IsHermitian_eigenvalues_ne_zero_of_det_ne_zero hA hA_det_ne) hcount

theorem mode4RootFunction_pos_of_hermitian_count_two
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet : A.det = (mode4SchurMatrix mProject Λ K).det)
    (hA_det_ne : A.det ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount A hA = 2) :
    0 < mode4RootFunction mProject K Λ :=
  sign_eq_one_iff.mp
    (mode4RootFunction_sign_eq_one_of_hermitian_count_two
      A hA mProject K Λ hm hK hdet hA_det_ne hcount)

theorem mode4RootFunction_neg_of_hermitian_count_three
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 1 ≤ K)
    (hdet : A.det = (mode4SchurMatrix mProject Λ K).det)
    (hA_det_ne : A.det ≠ 0)
    (hcount : mode4HermitianNegativeEigenvalueCount A hA = 3) :
    mode4RootFunction mProject K Λ < 0 :=
  sign_eq_neg_one_iff.mp
    (mode4RootFunction_sign_eq_neg_one_of_hermitian_count_three
      A hA mProject K Λ hm hK hdet hA_det_ne hcount)

/-- Complete conditional root-bracket receiver.  The concrete suppliers still have to provide
the same-determinant Hermitian matrices and their endpoint counts. -/
theorem exists_mode4RootFunction_eq_zero_of_hermitian_counts_two_three
    {nLower nUpper : Type*}
    [Fintype nLower] [DecidableEq nLower]
    [Fintype nUpper] [DecidableEq nUpper]
    (ALower : Matrix nLower nLower ℝ) (hALower : ALower.IsHermitian)
    (AUpper : Matrix nUpper nUpper ℝ) (hAUpper : AUpper.IsHermitian)
    (mProject K : ℕ) (ΛLower ΛUpper : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hLowerUpper : ΛLower ≤ ΛUpper)
    (hUpper20 : ΛUpper ≤ 20)
    (hdetLower :
      ALower.det = (mode4SchurMatrix mProject ΛLower K).det)
    (hdetUpper :
      AUpper.det = (mode4SchurMatrix mProject ΛUpper K).det)
    (hLower_ne : ALower.det ≠ 0)
    (hUpper_ne : AUpper.det ≠ 0)
    (hcountLower :
      mode4HermitianNegativeEigenvalueCount ALower hALower = 2)
    (hcountUpper :
      mode4HermitianNegativeEigenvalueCount AUpper hAUpper = 3) :
    ∃ Λ ∈ Set.Icc ΛLower ΛUpper,
      mode4RootFunction mProject K Λ = 0 := by
  have hK1 : 1 ≤ K := le_trans (by decide : 1 ≤ 3) hK
  have hpos : 0 < mode4RootFunction mProject K ΛLower :=
    mode4RootFunction_pos_of_hermitian_count_two
      ALower hALower mProject K ΛLower hm hK1
      hdetLower hLower_ne hcountLower
  have hneg : mode4RootFunction mProject K ΛUpper < 0 :=
    mode4RootFunction_neg_of_hermitian_count_three
      AUpper hAUpper mProject K ΛUpper hm hK1
      hdetUpper hUpper_ne hcountUpper
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

#print axioms mode4IsHermitian_sign_det_eq_neg_one_pow_negative_count
#print axioms mode4IsHermitian_eigenvalues_ne_zero_of_det_ne_zero
#print axioms mode4IsHermitian_sign_det_eq_neg_one_pow_negative_count_of_det_ne_zero
#print axioms mode4IsHermitian_sign_det_eq_one_of_negative_count_two
#print axioms mode4IsHermitian_sign_det_eq_neg_one_of_negative_count_three
#print axioms mode4RootFunction_sign_eq_one_of_hermitian_count_two
#print axioms mode4RootFunction_sign_eq_neg_one_of_hermitian_count_three
#print axioms mode4RootFunction_pos_of_hermitian_count_two
#print axioms mode4RootFunction_neg_of_hermitian_count_three
#print axioms exists_mode4RootFunction_eq_zero_of_hermitian_counts_two_three
