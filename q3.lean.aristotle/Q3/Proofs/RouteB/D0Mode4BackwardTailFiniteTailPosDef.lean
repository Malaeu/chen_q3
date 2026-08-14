import Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteSchurCrosswalk

/-!
# Positive definiteness of the actual finite mode-four tail

This bounded finite-dimensional leaf proves positivity of the literal forward
tail block under the production separation inequality and seals the accepted
finite Schur crosswalk's private pivot premise.  The `d = 0` block is handled
explicitly.  No claim beyond these two finite consequences is made.

Knowledge preflight receipt: `./ask.sh "D0Mode4BackwardTailFiniteTailPosDef
actual finite Jacobi tail block positive definite separation"` exited `0` and
returned only broad unrelated metadata names; the exact `kb.py ask` exited `1`
with no hits; `kb.py flags D0_MODE4_BACKWARD_TAIL_FINITE_TAIL_POSDEF` exited `1`
because the territory had not previously been searched.  Semantic queries
identified `D0Mode4JacobiTailContraction.lean` (notably
`mode4JacobiCenter_sub_upper_mul_lower_bound` and
`mode4TailMap_mapsTo_and_contracts`), the accepted finite-Schur report/verdict,
and the existing Jacobi sources, but no ready positive-definiteness theorem.
-/

noncomputable section

open Matrix

private noncomputable def mode4ForwardFiniteTailMatrixPD
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
            (fun j' => mode4ForwardFiniteTailMatrixPD G Λ (K + 1) n i' j')
            j)
        i

private theorem mode4ActualFiniteJacobiTruncation_tailBlock_eq_forwardPD
    (mProject K d : ℕ) (Λ : ℝ) :
    (mode4ActualFiniteJacobiTruncation mProject Λ K d).toBlocks₂₂ =
      mode4ForwardFiniteTailMatrixPD (mode4JacobiG mProject) Λ K d := by
  simp only [mode4ActualFiniteJacobiTruncation,
    Matrix.toBlocks_fromBlocks₂₂]
  induction d generalizing K with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · rfl
      · rfl
      · rfl
      · simpa [mode4ForwardFiniteTailMatrixPD] using
          congrFun (congrFun (ih (K := K + 1)) i') j'

private theorem mode4ForwardFiniteTailMatrixPD_quadratic_succ_succ
    (G Λ : ℝ) (K n : ℕ) (x : Fin (n + 2) → ℝ) :
    star x ⬝ᵥ
        (mode4ForwardFiniteTailMatrixPD G Λ K (n + 2) *ᵥ x) =
      mode4JacobiCenter G Λ K * x 0 ^ 2 -
        2 * mode4JacobiSymmetricOff G K * x 0 * x 1 +
        star (fun i : Fin (n + 1) => x i.succ) ⬝ᵥ
          (mode4ForwardFiniteTailMatrixPD G Λ (K + 1) (n + 1) *ᵥ
            (fun i : Fin (n + 1) => x i.succ)) := by
  simp [mode4ForwardFiniteTailMatrixPD, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

private theorem mode4JacobiSymmetricOff_young
    (G : ℝ) (q : ℕ) (hG : 0 < G) (x y : ℝ) :
    2 * mode4JacobiSymmetricOff G q * x * y ≤
      mode4JacobiUpper G q * x ^ 2 +
        mode4JacobiLower G (q + 1) * y ^ 2 := by
  have hU : 0 < mode4JacobiUpper G q :=
    mode4JacobiUpper_pos G q hG
  have hsq := mode4JacobiSymmetricOff_sq G q hG
  have hfactor :
      (mode4JacobiUpper G q * x -
          mode4JacobiSymmetricOff G q * y) ^ 2 =
        mode4JacobiUpper G q *
          (mode4JacobiUpper G q * x ^ 2 -
            2 * mode4JacobiSymmetricOff G q * x * y +
            mode4JacobiLower G (q + 1) * y ^ 2) := by
    calc
      (mode4JacobiUpper G q * x -
          mode4JacobiSymmetricOff G q * y) ^ 2 =
          mode4JacobiUpper G q ^ 2 * x ^ 2 -
            2 * mode4JacobiUpper G q *
              mode4JacobiSymmetricOff G q * x * y +
            mode4JacobiSymmetricOff G q ^ 2 * y ^ 2 := by ring
      _ = mode4JacobiUpper G q *
          (mode4JacobiUpper G q * x ^ 2 -
            2 * mode4JacobiSymmetricOff G q * x * y +
            mode4JacobiLower G (q + 1) * y ^ 2) := by
        rw [hsq]
        ring
  have hnonneg := sq_nonneg
    (mode4JacobiUpper G q * x - mode4JacobiSymmetricOff G q * y)
  rw [hfactor] at hnonneg
  have := nonneg_of_mul_nonneg_right hnonneg hU
  linarith

private theorem mode4ForwardFiniteTailMatrixPD_quadratic_lower
    (mProject K n : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (x : Fin (n + 1) → ℝ) :
    mode4JacobiLower (mode4JacobiG mProject) K * x 0 ^ 2 +
        (1 / 12 : ℝ) * mode4JacobiG mProject * ∑ i, x i ^ 2 ≤
      star x ⬝ᵥ
        (mode4ForwardFiniteTailMatrixPD
          (mode4JacobiG mProject) Λ K (n + 1) *ᵥ x) := by
  have hG : 0 < mode4JacobiG mProject := by
    have hmR : (0 : ℝ) < (mProject : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    unfold mode4JacobiG
    positivity
  induction n generalizing K with
  | zero =>
      have hcenter := mode4JacobiCenter_sub_upper_mul_lower_bound
        (mode4JacobiG mProject) Λ 0 K hG hK (hsep K le_rfl) hΛ
          (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 (1 / 2))
      have hL := mode4JacobiLower_le_one_third_mul_G
        (mode4JacobiG mProject) K hG hK
      simp [mode4ForwardFiniteTailMatrixPD, Matrix.mulVec, dotProduct] at ⊢
      nlinarith [sq_nonneg (x 0)]
  | succ n ih =>
      let y : Fin (n + 1) → ℝ := fun i => x i.succ
      have hK' : 3 ≤ K + 1 := by omega
      have hsep' :
          ∀ q ≥ K + 1,
            (31 / 24 : ℝ) * mode4JacobiG mProject ≤
              mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
        intro q hq
        exact hsep q (le_trans (Nat.le_add_right K 1) hq)
      have htail := ih (K := K + 1) hK' hsep' y
      have hcenter := mode4JacobiCenter_sub_upper_mul_lower_bound
        (mode4JacobiG mProject) Λ 0 K hG hK (hsep K le_rfl) hΛ
          (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 (1 / 2))
      have hL := mode4JacobiLower_le_one_third_mul_G
        (mode4JacobiG mProject) K hG hK
      have hU := mode4JacobiUpper_le_one_quarter_mul_G
        (mode4JacobiG mProject) K hG
      have hbudget :
          mode4JacobiLower (mode4JacobiG mProject) K +
              (1 / 12 : ℝ) * mode4JacobiG mProject +
              mode4JacobiUpper (mode4JacobiG mProject) K ≤
            mode4JacobiCenter (mode4JacobiG mProject) Λ K := by
        linarith
      have hbudget_x := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (x 0))
      have hedge := mode4JacobiSymmetricOff_young
        (mode4JacobiG mProject) K hG (x 0) (x 1)
      rw [mode4ForwardFiniteTailMatrixPD_quadratic_succ_succ,
        Fin.sum_univ_succ]
      change
        mode4JacobiLower (mode4JacobiG mProject) (K + 1) * x 1 ^ 2 +
            (1 / 12 : ℝ) * mode4JacobiG mProject *
              ∑ i : Fin (n + 1), y i ^ 2 ≤
          star y ⬝ᵥ
            (mode4ForwardFiniteTailMatrixPD
              (mode4JacobiG mProject) Λ (K + 1) (n + 1) *ᵥ y) at htail
      change
        mode4JacobiLower (mode4JacobiG mProject) K * x 0 ^ 2 +
            (1 / 12 : ℝ) * mode4JacobiG mProject *
              (x 0 ^ 2 + ∑ i : Fin (n + 1), y i ^ 2) ≤ _
      linarith

private theorem mode4ForwardFiniteTailMatrixPD_isHermitian
    (G Λ : ℝ) (K d : ℕ) :
    (mode4ForwardFiniteTailMatrixPD G Λ K d).IsHermitian := by
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
      · simp [mode4ForwardFiniteTailMatrixPD]
      · simp [mode4ForwardFiniteTailMatrixPD]
      · simp [mode4ForwardFiniteTailMatrixPD]
      · simpa [mode4ForwardFiniteTailMatrixPD] using
          (ih (K + 1)).apply i' j'

private theorem mode4ForwardFiniteTailMatrixPD_posDef
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    (mode4ForwardFiniteTailMatrixPD
      (mode4JacobiG mProject) Λ K d).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (mode4ForwardFiniteTailMatrixPD_isHermitian
      (mode4JacobiG mProject) Λ K d)
  intro x hx
  cases d with
  | zero =>
      exfalso
      apply hx
      funext i
      exact Fin.elim0 i
  | succ n =>
      have hG : 0 < mode4JacobiG mProject := by
        have hmR : (0 : ℝ) < (mProject : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
        unfold mode4JacobiG
        positivity
      have hsum : 0 < ∑ i, x i ^ 2 := by
        apply Finset.sum_pos'
        · exact fun i _ => sq_nonneg (x i)
        · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
          exact ⟨i, Finset.mem_univ i, pow_two_pos_of_ne_zero hi⟩
      have hL : 0 ≤ mode4JacobiLower (mode4JacobiG mProject) K :=
        (mode4JacobiLower_pos (mode4JacobiG mProject) K hG hK).le
      have hlower := mode4ForwardFiniteTailMatrixPD_quadratic_lower
        mProject K n Λ hm hK hsep hΛ x
      have hstrict :
          0 < mode4JacobiLower (mode4JacobiG mProject) K * x 0 ^ 2 +
            (1 / 12 : ℝ) * mode4JacobiG mProject * ∑ i, x i ^ 2 := by
        have hfirst :
            0 ≤ mode4JacobiLower (mode4JacobiG mProject) K * x 0 ^ 2 :=
          mul_nonneg hL (sq_nonneg (x 0))
        have hdelta : 0 < (1 / 12 : ℝ) * mode4JacobiG mProject := by
          positivity
        exact add_pos_of_nonneg_of_pos hfirst (mul_pos hdelta hsum)
      exact lt_of_lt_of_le hstrict hlower

/-- Under the production separation inequality, the literal eliminated tail
block of the actual finite Jacobi truncation is positive definite. -/
theorem mode4ActualFiniteJacobiTruncation_tailBlock_posDef
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    (mode4ActualFiniteJacobiTruncation mProject Λ K d).toBlocks₂₂.PosDef := by
  rw [mode4ActualFiniteJacobiTruncation_tailBlock_eq_forwardPD]
  exact mode4ForwardFiniteTailMatrixPD_posDef
    mProject K d Λ hm hK hsep hΛ

private theorem mode4BackwardTail_zero_mem_Icc
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4BackwardTail mProject Λ K d 0 ∈ Set.Icc 0 (1 / 2) := by
  exact (mode4BackwardTail_mapsTo_and_lipschitz
    mProject K d Λ hm hK hsep hΛ).1 (by constructor <;> norm_num)

/-- Separation makes every internal finite-elimination pivot nonzero, so the
accepted finite Schur crosswalk becomes unconditional on this source range. -/
theorem mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    let M := mode4ActualFiniteJacobiTruncation mProject Λ K d
    M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁ =
      mode4BackwardTailSchurApprox mProject Λ K d := by
  apply mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx
    mProject K d Λ hm hK
  induction d generalizing K with
  | zero =>
      change True
      trivial
  | succ n ih =>
      change
        mode4JacobiCenter (mode4JacobiG mProject) Λ K -
              mode4JacobiUpper (mode4JacobiG mProject) K *
                mode4BackwardTail mProject Λ (K + 1) n 0 ≠ 0 ∧ _
      have hG : 0 < mode4JacobiG mProject := by
        have hmR : (0 : ℝ) < (mProject : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
        unfold mode4JacobiG
        positivity
      have hK' : 3 ≤ K + 1 := by omega
      have hsep' :
          ∀ q ≥ K + 1,
            (31 / 24 : ℝ) * mode4JacobiG mProject ≤
              mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
        intro q hq
        exact hsep q (le_trans (Nat.le_add_right K 1) hq)
      have htail := mode4BackwardTail_zero_mem_Icc
        mProject (K + 1) n Λ hm hK' hsep' hΛ
      have hpivot := mode4JacobiCenter_sub_upper_mul_lower_bound
        (mode4JacobiG mProject) Λ
        (mode4BackwardTail mProject Λ (K + 1) n 0) K
        hG hK (hsep K le_rfl) hΛ htail
      constructor
      · nlinarith
      · exact ih (K + 1) hK' hsep'

#print axioms mode4ActualFiniteJacobiTruncation_tailBlock_posDef
#print axioms mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation

end
