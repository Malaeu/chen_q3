import Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteTailPosDef
import Q3.Proofs.RouteB.D0Mode4HermitianNegativeCountStability

/-!
# Finite block inertia for the mode-four Schur truncation

This file proves the exact finite-dimensional Haynsworth/Sylvester step left
open by the finite Schur crosswalk.  A Hermitian block matrix with positive
definite eliminated block is congruent to the direct sum of that block and its
Schur complement.  The positive block contributes no negative direction.

The subspace proof is an independent Mathlib realization.  Its architecture
was cross-checked against `Zeta23/LinAlg/Inertia.lean` (Apache-2.0); no source
code is copied.  The final theorem is finite-cell only: it proves no endpoint
count, stabilization, index-four identification, or cofinal statement.
-/

noncomputable section

open Matrix Finset Submodule

private theorem mode4NegativeCount_eq_of_matrix_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) :
    mode4HermitianNegativeEigenvalueCount A hA =
      mode4HermitianNegativeEigenvalueCount B hB := by
  subst B
  rfl

private theorem mode4Block_form_conj
    {m n : Type*} [Fintype m] [Fintype n]
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((Bᴴ * Q * B) *ᵥ x) =
      star (B *ᵥ x) ⬝ᵥ (Q *ᵥ (B *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) Bᴴ, ← star_mulVec]

private theorem mode4HermitianNegativeEigenvalueCount_conj_le
    {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {Q : Matrix m m ℝ} (hQ : Q.IsHermitian) (B : Matrix m n ℝ) :
    mode4HermitianNegativeEigenvalueCount
        (Bᴴ * Q * B) (isHermitian_conjTranspose_mul_mul B hQ) ≤
      mode4HermitianNegativeEigenvalueCount Q hQ := by
  let M : Matrix n n ℝ := Bᴴ * Q * B
  let hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul B hQ
  obtain ⟨W, hWneg, hWdim⟩ :=
    mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount hM
  let LB : (n → ℝ) →ₗ[ℝ] (m → ℝ) := B.mulVecLin
  have hinj : Function.Injective (LB.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : B *ᵥ x = 0 := hxL
    simp only [Submodule.mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hneg := hWneg x hxW hne'
    change star x ⬝ᵥ ((Bᴴ * Q * B) *ᵥ x) < 0 at hneg
    rw [mode4Block_form_conj Q B x, hxL'] at hneg
    simp at hneg
  have hnegImage :
      ∀ y ∈ LinearMap.range (LB.domRestrict W), y ≠ 0 →
        star y ⬝ᵥ (Q *ᵥ y) < 0 := by
    rintro _ ⟨⟨x, hxW⟩, rfl⟩ hne
    simp only [LinearMap.domRestrict_apply, LB, mulVecLin_apply] at *
    have hxne : x ≠ 0 := by
      rintro rfl
      apply hne
      simp
    rw [← mode4Block_form_conj Q B x]
    exact hWneg x hxW hxne
  calc
    mode4HermitianNegativeEigenvalueCount
        (Bᴴ * Q * B) (isHermitian_conjTranspose_mul_mul B hQ) =
        Module.finrank ℝ W := by simpa [M, hM] using hWdim.symm
    _ = Module.finrank ℝ (LinearMap.range (LB.domRestrict W)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ mode4HermitianNegativeEigenvalueCount Q hQ :=
      mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn hQ hnegImage

private theorem mode4HermitianNegativeEigenvalueCount_congr_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℝ} (hQ : Q.IsHermitian)
    (B : Matrix n n ℝ) [Invertible B] :
    mode4HermitianNegativeEigenvalueCount
        (Bᴴ * Q * B) (isHermitian_conjTranspose_mul_mul B hQ) =
      mode4HermitianNegativeEigenvalueCount Q hQ := by
  apply Nat.le_antisymm
  · exact mode4HermitianNegativeEigenvalueCount_conj_le hQ B
  · let M : Matrix n n ℝ := Bᴴ * Q * B
    let hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul B hQ
    have hback := mode4HermitianNegativeEigenvalueCount_conj_le hM (⅟B)
    have hrecover : (⅟B)ᴴ * M * ⅟B = Q := by
      dsimp [M]
      calc
        (⅟B)ᴴ * (Bᴴ * Q * B) * ⅟B =
            ((⅟B)ᴴ * Bᴴ) * Q * (B * ⅟B) := by
              simp only [Matrix.mul_assoc]
        _ = (B * ⅟B)ᴴ * Q * (B * ⅟B) := by
              rw [Matrix.conjTranspose_mul]
        _ = Q := by rw [mul_invOf_self]; simp
    have hrecoverHerm : ((⅟B)ᴴ * M * ⅟B).IsHermitian :=
      isHermitian_conjTranspose_mul_mul (⅟B) hM
    have htransport := mode4NegativeCount_eq_of_matrix_eq
      hrecoverHerm hQ hrecover
    exact htransport.symm.trans_le hback

private def mode4SumFst
    {m n : Type*} : ((m ⊕ n) → ℝ) →ₗ[ℝ] (m → ℝ) where
  toFun x := x ∘ Sum.inl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def mode4SumSnd
    {m n : Type*} : ((m ⊕ n) → ℝ) →ₗ[ℝ] (n → ℝ) where
  toFun x := x ∘ Sum.inr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def mode4SumInl
    {m n : Type*} : (m → ℝ) →ₗ[ℝ] ((m ⊕ n) → ℝ) where
  toFun x := Sum.elim x 0
  map_add' x y := by
    ext i
    cases i <;> simp
  map_smul' c x := by
    ext i
    cases i <;> simp

@[simp] private theorem mode4SumFst_apply
    {m n : Type*} (x : (m ⊕ n) → ℝ) :
    mode4SumFst x = x ∘ Sum.inl := rfl

@[simp] private theorem mode4SumSnd_apply
    {m n : Type*} (x : (m ⊕ n) → ℝ) :
    mode4SumSnd x = x ∘ Sum.inr := rfl

@[simp] private theorem mode4SumInl_inl
    {m n : Type*} (x : m → ℝ) (i : m) :
    mode4SumInl (n := n) x (Sum.inl i) = x i := rfl

@[simp] private theorem mode4SumInl_inr
    {m n : Type*} (x : m → ℝ) (j : n) :
    mode4SumInl (n := n) x (Sum.inr j) = 0 := rfl

private theorem mode4BlockDiagonal_form
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) (x : (m ⊕ n) → ℝ) :
    star x ⬝ᵥ ((Matrix.fromBlocks A 0 0 D) *ᵥ x) =
      star (mode4SumFst x) ⬝ᵥ (A *ᵥ mode4SumFst x) +
        star (mode4SumSnd x) ⬝ᵥ (D *ᵥ mode4SumSnd x) := by
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    dotProduct, Fintype.sum_sum_type, Pi.star_apply, Sum.elim_inl,
    Sum.elim_inr, mode4SumFst_apply, mode4SumSnd_apply]
  rfl

private theorem mode4HermitianNegativeEigenvalueCount_fromBlocks_posDef₂₂
    {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℝ} (hA : A.IsHermitian)
    {D : Matrix n n ℝ} (hD : D.PosDef) :
    mode4HermitianNegativeEigenvalueCount
        (Matrix.fromBlocks A 0 0 D)
        (Matrix.IsHermitian.fromBlocks hA rfl hD.isHermitian) =
      mode4HermitianNegativeEigenvalueCount A hA := by
  let H : Matrix (m ⊕ n) (m ⊕ n) ℝ := Matrix.fromBlocks A 0 0 D
  let hH : H.IsHermitian := Matrix.IsHermitian.fromBlocks hA rfl hD.isHermitian
  apply Nat.le_antisymm
  · obtain ⟨W, hWneg, hWdim⟩ :=
      mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount hH
    let L : ((m ⊕ n) → ℝ) →ₗ[ℝ] (m → ℝ) := mode4SumFst
    have hinj : Function.Injective (L.domRestrict W) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      rintro ⟨x, hxW⟩ hxL
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
      have hfst : mode4SumFst x = 0 := hxL
      simp only [Submodule.mem_bot]
      by_contra hne
      have hxne : x ≠ 0 := fun h => hne (Subtype.ext h)
      have hsndne : mode4SumSnd x ≠ 0 := by
        intro hsnd
        apply hxne
        funext i
        cases i with
        | inl i => simpa [mode4SumFst] using congrFun hfst i
        | inr j => simpa [mode4SumSnd] using congrFun hsnd j
      have hposD := hD.dotProduct_mulVec_pos hsndne
      have hneg := hWneg x hxW hxne
      change star x ⬝ᵥ (H *ᵥ x) < 0 at hneg
      rw [show H = Matrix.fromBlocks A 0 0 D from rfl,
        mode4BlockDiagonal_form, hfst] at hneg
      simp at hneg
      exact (not_lt_of_ge hposD.le) hneg
    have hnegImage :
        ∀ y ∈ LinearMap.range (L.domRestrict W), y ≠ 0 →
          star y ⬝ᵥ (A *ᵥ y) < 0 := by
      rintro _ ⟨⟨x, hxW⟩, rfl⟩ hne
      simp only [LinearMap.domRestrict_apply, L] at *
      have hxne : x ≠ 0 := by
        rintro rfl
        apply hne
        simp
      have hneg := hWneg x hxW hxne
      change star x ⬝ᵥ (H *ᵥ x) < 0 at hneg
      rw [show H = Matrix.fromBlocks A 0 0 D from rfl,
        mode4BlockDiagonal_form] at hneg
      have hDnonneg := hD.posSemidef.dotProduct_mulVec_nonneg (mode4SumSnd x)
      linarith
    calc
      mode4HermitianNegativeEigenvalueCount
          (Matrix.fromBlocks A 0 0 D)
          (Matrix.IsHermitian.fromBlocks hA rfl hD.isHermitian) =
          Module.finrank ℝ W := by simpa [H, hH] using hWdim.symm
      _ = Module.finrank ℝ (LinearMap.range (L.domRestrict W)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ mode4HermitianNegativeEigenvalueCount A hA :=
        mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn hA hnegImage
  · obtain ⟨W, hWneg, hWdim⟩ :=
      mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount hA
    let E : (m → ℝ) →ₗ[ℝ] ((m ⊕ n) → ℝ) := mode4SumInl
    have hinj : Function.Injective (E.domRestrict W) := by
      intro x y hxy
      apply Subtype.ext
      funext i
      have hi := congrFun hxy (Sum.inl i)
      simpa [E] using hi
    have hnegImage :
        ∀ y ∈ LinearMap.range (E.domRestrict W), y ≠ 0 →
          star y ⬝ᵥ (H *ᵥ y) < 0 := by
      rintro _ ⟨⟨x, hxW⟩, rfl⟩ hne
      simp only [LinearMap.domRestrict_apply, E] at *
      have hxne : x ≠ 0 := by
        rintro rfl
        apply hne
        simp [mode4SumInl]
      rw [show H = Matrix.fromBlocks A 0 0 D from rfl,
        mode4BlockDiagonal_form]
      simpa [mode4SumInl, mode4SumFst, mode4SumSnd] using hWneg x hxW hxne
    calc
      mode4HermitianNegativeEigenvalueCount A hA = Module.finrank ℝ W := hWdim.symm
      _ = Module.finrank ℝ (LinearMap.range (E.domRestrict W)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ mode4HermitianNegativeEigenvalueCount H hH :=
        mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn hH hnegImage

private theorem mode4HermitianBlock_negativeCount_eq_schur_of_posDef₂₂
    {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : A.IsHermitian) (hD : D.PosDef) :
    let M := Matrix.fromBlocks A B Bᴴ D
    let S := A - B * D⁻¹ * Bᴴ
    mode4HermitianNegativeEigenvalueCount M
        (Matrix.IsHermitian.fromBlocks hA rfl hD.isHermitian) =
      mode4HermitianNegativeEigenvalueCount S
        (hA.sub (isHermitian_mul_mul_conjTranspose B hD.inv.isHermitian)) := by
  dsimp only
  letI : Invertible D := hD.isUnit.invertible
  have hDinv : (⅟D).IsHermitian := by
    rw [invOf_eq_nonsing_inv]
    exact hD.inv.isHermitian
  let P : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    Matrix.fromBlocks (1 : Matrix m m ℝ) (B * ⅟D) 0 1
  letI : Invertible (1 : Matrix m m ℝ) := invertibleOne
  letI : Invertible (1 : Matrix n n ℝ) := invertibleOne
  letI : Invertible P := Matrix.fromBlocksZero₂₁Invertible 1 (B * ⅟D) 1
  let S : Matrix m m ℝ := A - B * D⁻¹ * Bᴴ
  let hS : S.IsHermitian :=
    hA.sub (isHermitian_mul_mul_conjTranspose B hD.inv.isHermitian)
  let H : Matrix (m ⊕ n) (m ⊕ n) ℝ := Matrix.fromBlocks S 0 0 D
  let hH : H.IsHermitian := Matrix.IsHermitian.fromBlocks hS rfl hD.isHermitian
  have hfactor : Matrix.fromBlocks A B Bᴴ D = P * H * Pᴴ := by
    rw [Matrix.fromBlocks_eq_of_invertible₂₂]
    simp only [invOf_eq_nonsing_inv]
    have hPstar :
        Pᴴ = Matrix.fromBlocks (1 : Matrix m m ℝ) 0 (D⁻¹ * Bᴴ) 1 := by
      calc
        Pᴴ = Matrix.fromBlocks (1 : Matrix m m ℝ) 0 ((⅟D)ᴴ * Bᴴ) 1 := by
          rw [show P = Matrix.fromBlocks (1 : Matrix m m ℝ) (B * ⅟D) 0 1 from rfl]
          rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul]
          simp
        _ = Matrix.fromBlocks (1 : Matrix m m ℝ) 0 (D⁻¹ * Bᴴ) 1 := by
          rw [hDinv.eq, invOf_eq_nonsing_inv]
    rw [hPstar]
    simp only [P, H, S, invOf_eq_nonsing_inv]
  have hcongr := mode4HermitianNegativeEigenvalueCount_congr_eq hH Pᴴ
  have hdiag := mode4HermitianNegativeEigenvalueCount_fromBlocks_posDef₂₂ hS hD
  let hM : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hA rfl hD.isHermitian
  let hPH : (P * H * Pᴴ).IsHermitian := by
    rw [← hfactor]
    exact hM
  have hfactorCount := mode4NegativeCount_eq_of_matrix_eq hM hPH hfactor
  let hCong : ((Pᴴ)ᴴ * H * Pᴴ).IsHermitian :=
    isHermitian_conjTranspose_mul_mul Pᴴ hH
  have hdouble : (Pᴴ)ᴴ * H * Pᴴ = P * H * Pᴴ := by simp
  have hdoubleCount := mode4NegativeCount_eq_of_matrix_eq hCong hPH hdouble
  have hPHtoH :
      mode4HermitianNegativeEigenvalueCount (P * H * Pᴴ) hPH =
        mode4HermitianNegativeEigenvalueCount H hH :=
    hdoubleCount.symm.trans hcongr
  have hHtoS :
      mode4HermitianNegativeEigenvalueCount H hH =
        mode4HermitianNegativeEigenvalueCount S hS := by
    simpa [H, hH] using hdiag
  exact hfactorCount.trans (hPHtoH.trans hHtoS)

/-- The literal actual finite Jacobi truncation and its terminal-zero Schur
approximation have exactly the same number of negative eigenvalues on the
production separation range. -/
theorem mode4ActualFiniteJacobiTruncation_negativeCount_eq_schurApprox
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4HermitianNegativeEigenvalueCount
        (mode4ActualFiniteJacobiTruncation mProject Λ K d)
        (mode4ActualFiniteJacobiTruncation_isHermitian mProject Λ K d) =
      mode4HermitianNegativeEigenvalueCount
        (mode4BackwardTailSchurApprox mProject Λ K d)
        (mode4BackwardTailSchurApprox_isHermitian mProject K d Λ) := by
  let M := mode4ActualFiniteJacobiTruncation mProject Λ K d
  let A := M.toBlocks₁₁
  let B := M.toBlocks₁₂
  let D := M.toBlocks₂₂
  have hM : M.IsHermitian :=
    mode4ActualFiniteJacobiTruncation_isHermitian mProject Λ K d
  have hblocks : A.IsHermitian ∧ Bᴴ = M.toBlocks₂₁ ∧
      M.toBlocks₂₁ᴴ = B ∧ D.IsHermitian := by
    apply Matrix.isHermitian_fromBlocks_iff.mp
    simpa [A, B, D, M] using hM
  have hD : D.PosDef := by
    simpa [D, M] using
      mode4ActualFiniteJacobiTruncation_tailBlock_posDef
        mProject K d Λ hm hK hsep hΛ
  have hsource : Matrix.fromBlocks A B Bᴴ D = M := by
    rw [hblocks.2.1]
    exact Matrix.fromBlocks_toBlocks M
  have hschur : A - B * D⁻¹ * Bᴴ =
      mode4BackwardTailSchurApprox mProject Λ K d := by
    rw [hblocks.2.1]
    simpa [A, B, D, M] using
      mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation
        mProject K d Λ hm hK hsep hΛ
  have hgeneric := mode4HermitianBlock_negativeCount_eq_schur_of_posDef₂₂
    A B D hblocks.1 hD
  let hFrom : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hblocks.1 rfl hD.isHermitian
  let S : Matrix (Fin K) (Fin K) ℝ := A - B * D⁻¹ * Bᴴ
  let hS : S.IsHermitian :=
    hblocks.1.sub (isHermitian_mul_mul_conjTranspose B hD.inv.isHermitian)
  have hgeneric' :
      mode4HermitianNegativeEigenvalueCount (Matrix.fromBlocks A B Bᴴ D) hFrom =
        mode4HermitianNegativeEigenvalueCount S hS := by
    simpa [hFrom, S, hS] using hgeneric
  have hleft := mode4NegativeCount_eq_of_matrix_eq hFrom hM hsource
  have hright := mode4NegativeCount_eq_of_matrix_eq hS
    (mode4BackwardTailSchurApprox_isHermitian mProject K d Λ) hschur
  exact hleft.symm.trans (hgeneric'.trans hright)

#print axioms mode4ActualFiniteJacobiTruncation_negativeCount_eq_schurApprox

end
