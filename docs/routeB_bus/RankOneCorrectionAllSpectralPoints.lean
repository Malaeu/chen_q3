import Q3.Proofs.RouteB.RankOneCorrectionWeightedSymmetry
import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option linter.mathlibStandardSet false

noncomputable section
namespace Q3.RouteB

private theorem det_eq_of_forall_col_eq_smul_add_const
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} (c : n → R) (k : n) (hk : c k = 0)
    (hAB : ∀ i j, A i j = B i j + c j * B i k) :
    A.det = B.det := by
  rw [← Matrix.det_transpose A, ← Matrix.det_transpose B]
  exact Matrix.det_eq_of_forall_row_eq_smul_add_const c k hk fun i j => hAB j i

private def addVecMulVecOn
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (u v : n → R) (s : Finset n) : Matrix n n R :=
  fun i j => A i j + if j ∈ s then u i * v j else 0

private theorem det_addVecMulVecOn
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (u v : n → R) (s : Finset n) :
    (addVecMulVecOn A u v s).det =
      A.det + ∑ j ∈ s, v j * (A.updateCol j u).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : addVecMulVecOn A u v ∅ = A := by
        ext i j
        simp [addVecMulVecOn]
      rw [hzero]
      simp
  | @insert k s hk ih =>
      have hmatrix :
          addVecMulVecOn A u v (insert k s) =
            (addVecMulVecOn A u v s).updateCol k
              (fun i => A i k + v k * u i) := by
        ext i j
        by_cases hjk : j = k
        · subst j
          simp [addVecMulVecOn, hk, mul_comm]
        · simp [addVecMulVecOn, hjk]
      have hremove :
          (addVecMulVecOn A u v s).updateCol k (fun i => A i k) =
            addVecMulVecOn A u v s := by
        ext i j
        by_cases hjk : j = k
        · subst j
          simp [addVecMulVecOn, hk]
        · simp [addVecMulVecOn, hjk]
      have hscaled :
          (addVecMulVecOn A u v s).updateCol k (fun i => v k * u i) =
            (addVecMulVecOn A u v s).updateCol k (v k • u) := by
        congr
      have haux :
          ((addVecMulVecOn A u v s).updateCol k u).det =
            (A.updateCol k u).det := by
        apply det_eq_of_forall_col_eq_smul_add_const
          (B := A.updateCol k u) (fun j => if j ∈ s then v j else 0) k
        · simp [hk]
        · intro i j
          by_cases hjk : j = k
          · subst j
            simp [hk]
          · by_cases hjs : j ∈ s
            · simp [addVecMulVecOn, hjk, hjs, mul_comm]
            · simp [addVecMulVecOn, hjk, hjs]
      rw [hmatrix]
      have hcol :
          (fun i => A i k + v k * u i) =
            (fun i => A i k) + (fun i => v k * u i) := by
        ext i
        simp
      rw [hcol, Matrix.det_updateCol_add, hremove, hscaled,
        Matrix.det_updateCol_smul, haux, ih]
      simp [Finset.sum_insert hk, add_assoc, add_left_comm, add_comm]

/-- The adjugate form of the rank-one determinant lemma.  Unlike the
resolvent form, it is valid also when `A` is singular. -/
theorem det_add_vecMulVec_adjugate
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (u v : n → R) :
    (A + Matrix.vecMulVec u v).det =
      A.det + v ⬝ᵥ Matrix.mulVec A.adjugate u := by
  classical
  have hmatrix : A + Matrix.vecMulVec u v =
      addVecMulVecOn A u v Finset.univ := by
    ext i j
    simp [addVecMulVecOn, Matrix.vecMulVec_apply]
  rw [hmatrix, det_addVecMulVecOn]
  rw [← Matrix.cramer_eq_adjugate_mulVec A u]
  rfl

/-- The determinant identity for the Route B rank-one correction at every
spectral parameter, including points where `D - sI` is singular. -/
theorem det_rankOneCorrection_sub_smul_one_all
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℝ) (xi eta : n → ℝ) (s : ℝ) :
    (rankOneCorrection D xi eta - s • (1 : Matrix n n ℝ)).det =
      (D - s • (1 : Matrix n n ℝ)).det -
        eta ⬝ᵥ
          Matrix.mulVec (D - s • (1 : Matrix n n ℝ)).adjugate
            (Matrix.mulVec D xi) := by
  let A : Matrix n n ℝ := D - s • (1 : Matrix n n ℝ)
  let u : n → ℝ := Matrix.mulVec D xi
  have hmatrix :
      rankOneCorrection D xi eta - s • (1 : Matrix n n ℝ) =
        A + Matrix.vecMulVec (-u) eta := by
    ext i j
    simp [rankOneCorrection, A, u, Matrix.vecMulVec_apply]
    ring
  rw [hmatrix, det_add_vecMulVec_adjugate]
  change A.det + eta ⬝ᵥ Matrix.mulVec A.adjugate (-u) =
    A.det - eta ⬝ᵥ Matrix.mulVec A.adjugate u
  rw [Matrix.mulVec_neg]
  rw [sub_eq_add_neg]
  simp [dotProduct]

/-- Two continuous complex-valued functions that agree away from a finite
exceptional set agree everywhere. -/
theorem continuous_eq_of_eq_off_finite
    (f g : ℂ → ℂ) (S : Set ℂ) (hS : S.Finite)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, z ∉ S → f z = g z) :
    f = g := by
  apply Continuous.ext_on (hS.countable.dense_compl ℂ) hf hg
  intro z hz
  exact hfg z hz

#print axioms det_add_vecMulVec_adjugate
#print axioms det_rankOneCorrection_sub_smul_one_all
#print axioms continuous_eq_of_eq_off_finite

end Q3.RouteB
