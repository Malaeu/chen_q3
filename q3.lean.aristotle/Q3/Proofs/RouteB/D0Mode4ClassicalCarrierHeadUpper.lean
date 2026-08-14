import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierFromFiniteLimit
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite head upper bounds for the classical carrier

The first nontrivial endpoint bound is proved from the literal three-by-three
even head.  The positive defect `20 I - A₃(G)` is completed into three
squares plus the nonnegative unperturbed head.  This is finite algebra only;
it supplies no lower separator and no semiclassical estimate.
-/

noncomputable section

open Matrix Finset

private theorem mode4HeadThree_twenty_sub_posDef
    (G : ℝ) (hG : 0 < G) :
    (Matrix.scalar (Fin 3) 20 -
      mode4ForwardHermitianFiniteMatrix G 0 3).PosDef := by
  let b₀ := mode4JacobiSymmetricOff G 0
  let b₁ := mode4JacobiSymmetricOff G 1
  have hb₀sq : b₀ ^ 2 = (4 / 45 : ℝ) * G ^ 2 := by
    dsimp [b₀]
    rw [mode4JacobiSymmetricOff_sq G 0 hG]
    norm_num [mode4JacobiLower, mode4JacobiUpper, mode4JacobiIndex]
    ring
  have hb₁sq : b₁ ^ 2 = (16 / 245 : ℝ) * G ^ 2 := by
    dsimp [b₁]
    rw [mode4JacobiSymmetricOff_sq G 1 hG]
    norm_num [mode4JacobiLower, mode4JacobiUpper, mode4JacobiIndex]
    ring
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (isHermitian_diagonal_of_self_adjoint _
      (funext fun _ => star_trivial (20 : ℝ))).sub
      (mode4ForwardHermitianFiniteMatrix_isHermitian G 0 3)
  · intro x hx
    let x₀ := x (0 : Fin 3)
    let x₁ := x (1 : Fin 3)
    let x₂ := x (2 : Fin 3)
    have hquad :
        star x ⬝ᵥ ((Matrix.scalar (Fin 3) 20 -
            mode4ForwardHermitianFiniteMatrix G 0 3) *ᵥ x) =
          20 * x₀ ^ 2 + 14 * x₁ ^ 2 +
          (2 * G / 3) * (x₀ + (3 * b₀ / (2 * G)) * x₁) ^ 2 +
          (12 * G / 35) * (x₁ + (35 * b₁ / (12 * G)) * x₂) ^ 2 +
          (10 * G / 33) * x₂ ^ 2 := by
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Matrix.scalar,
        Matrix.diagonal, mode4ForwardHermitianFiniteMatrix,
        mode4JacobiCenter, mode4JacobiIndex, x₀, x₁, x₂, b₀, b₁]
      field_simp [hG.ne']
      nlinarith [hb₀sq, hb₁sq]
    rw [hquad]
    have ha : 0 < 2 * G / 3 := by positivity
    have hc : 0 < 12 * G / 35 := by positivity
    have he : 0 < 10 * G / 33 := by positivity
    have hnonneg :
        0 ≤ 20 * x₀ ^ 2 + 14 * x₁ ^ 2 +
          (2 * G / 3) * (x₀ + (3 * b₀ / (2 * G)) * x₁) ^ 2 +
          (12 * G / 35) * (x₁ + (35 * b₁ / (12 * G)) * x₂) ^ 2 +
          (10 * G / 33) * x₂ ^ 2 := by positivity
    by_cases hx₂ : x₂ = 0
    · by_cases hx₁ : x₁ = 0
      · have hx₀ : x₀ ≠ 0 := by
          intro hx₀
          apply hx
          funext i
          fin_cases i
          · exact hx₀
          · exact hx₁
          · exact hx₂
        have hx₀sq : 0 < x₀ ^ 2 := sq_pos_of_ne_zero hx₀
        nlinarith [sq_nonneg
          (x₀ + (3 * b₀ / (2 * G)) * x₁),
          sq_nonneg (x₁ + (35 * b₁ / (12 * G)) * x₂)]
      · have hx₁sq : 0 < x₁ ^ 2 := sq_pos_of_ne_zero hx₁
        nlinarith [sq_nonneg x₀,
          sq_nonneg (x₀ + (3 * b₀ / (2 * G)) * x₁),
          sq_nonneg (x₁ + (35 * b₁ / (12 * G)) * x₂)]
    · have hx₂sq : 0 < x₂ ^ 2 := sq_pos_of_ne_zero hx₂
      nlinarith [sq_nonneg x₀, sq_nonneg x₁,
        sq_nonneg (x₀ + (3 * b₀ / (2 * G)) * x₁),
        sq_nonneg (x₁ + (35 * b₁ / (12 * G)) * x₂)]

private theorem mode4DLMFEvenFiniteEigenvalue_two_three_lt_twenty
    (G : ℝ) (hG : 0 < G) :
    mode4DLMFEvenFiniteEigenvalue G 3 ⟨2, by omega⟩ < 20 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    mode4ForwardHermitianFiniteMatrix G 0 3
  let hA : A.IsHermitian :=
    mode4ForwardHermitianFiniteMatrix_isHermitian G 0 3
  let p : Fin 3 := ⟨2, by omega⟩
  let k : Fin (Fintype.card (Fin 3)) :=
    Fin.cast (Fintype.card_fin 3).symm p.rev
  let j : Fin 3 :=
    (Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin 3)))) k
  have hmu :
      hA.eigenvalues j = mode4DLMFEvenFiniteEigenvalue G 3 p := by
    simp [j, k, p, mode4DLMFEvenFiniteEigenvalue,
      Matrix.IsHermitian.eigenvalues, A]
  let v : Fin 3 → ℝ := hA.eigenvectorBasis j
  have hv_ne : v ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2
      (hA.eigenvectorBasis.orthonormal.ne_zero j)
  have hMv :
      (Matrix.scalar (Fin 3) 20 - A) *ᵥ v =
        (20 - mode4DLMFEvenFiniteEigenvalue G 3 p) • v := by
    rw [sub_mulVec, hA.mulVec_eigenvectorBasis j, hmu]
    ext i
    change
      (Matrix.diagonal (fun _ : Fin 3 => (20 : ℝ)) *ᵥ v) i -
          mode4DLMFEvenFiniteEigenvalue G 3 p * v i =
        (20 - mode4DLMFEvenFiniteEigenvalue G 3 p) * v i
    rw [mulVec_diagonal]
    ring
  have hpos :=
    (mode4HeadThree_twenty_sub_posDef G hG).dotProduct_mulVec_pos hv_ne
  change 0 < star v ⬝ᵥ ((Matrix.scalar (Fin 3) 20 - A) *ᵥ v) at hpos
  rw [hMv, dotProduct_smul] at hpos
  have hvnorm : star v ⬝ᵥ v = 1 := by
    change star ⇑(hA.eigenvectorBasis j) ⬝ᵥ
      ⇑(hA.eigenvectorBasis j) = 1
    rw [dotProduct_comm]
    rw [← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K,
      hA.eigenvectorBasis.orthonormal.1 j]
    norm_num
  rw [hvnorm] at hpos
  simpa [p] using hpos

/-- The third zero-based even carrier (degree four) lies strictly below the
unperturbed value `20` for every positive `G`.  This closes the finite-head
upper endpoint only; the lower/cofinal separator remains analytic. -/
theorem mode4ClassicalEvenEigenvalue_two_lt_twenty
    (G : ℝ) (hG : 0 < G) :
    mode4ClassicalEvenEigenvalue G 2 < 20 := by
  have hfinite :=
    mode4DLMFEvenFiniteEigenvalue_two_three_lt_twenty G hG
  have hcarrier :
      mode4ClassicalEvenEigenvalue G 2 ≤
        mode4DLMFEvenFiniteEigenvalue G 3 ⟨2, by omega⟩ := by
    unfold mode4ClassicalEvenEigenvalue
    exact ciInf_le
      (mode4DLMFEvenFiniteEigenvalue_bddBelow G 2 hG)
      (⟨3, by omega⟩ : {d : ℕ // 2 < d})
  exact lt_of_le_of_lt hcarrier hfinite

/-- All three carrier levels indexed below `3` lie strictly below `20`.
This is the exact upper-head input needed by the eventual-count bridge. -/
theorem mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three
    (G : ℝ) (hG : 0 < G) (p : ℕ) (hp : p < 3) :
    mode4ClassicalEvenEigenvalue G p < 20 := by
  have hp2 : p ≤ 2 := by omega
  exact lt_of_le_of_lt
    (mode4ClassicalEvenEigenvalue_monotone G hG hp2)
    (mode4ClassicalEvenEigenvalue_two_lt_twenty G hG)

#print axioms mode4HeadThree_twenty_sub_posDef
#print axioms mode4ClassicalEvenEigenvalue_two_lt_twenty
#print axioms mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three

end
