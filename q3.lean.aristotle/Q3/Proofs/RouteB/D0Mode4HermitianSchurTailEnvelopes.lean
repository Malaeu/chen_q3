import Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization

/-!
# Source-neutral finite-left envelopes for the mode-four Hermitian Schur determinant

The exact Schur determinant is a finite left continuant corrected by the infinite right-tail
ratio.  On the contraction domain the latter lies in `[0, 1 / 2]`.  Splitting only on the sign
of the penultimate finite continuant gives sharp lower and upper determinant envelopes.

No endpoint formula, determinant sign, spectral count, finite threshold, or PSWF crosswalk is
asserted here.
-/

noncomputable section

/-- The exact Hermitian Schur determinant is bounded below by the finite-left envelope obtained
from the worst admissible tail when the penultimate continuant is nonnegative. -/
theorem mode4HermitianSchur_det_ge_finiteLeft_lowerEnvelope
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ K -
          (1 / 2 : ℝ) * mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
            max (mode4ScaledLeftContinuant
              (mode4JacobiG mProject) Λ (K - 1)) 0 ≤
      (mode4HermitianSchurMatrix mProject Λ K).det := by
  have hK1 : 1 ≤ K := le_trans (by decide : 1 ≤ 3) hK
  have htail := mode4RightTailLimit_mem_Icc
    mProject K Λ hm hK hsep hΛ
  have hmR : (0 : ℝ) < (mProject : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have hU : 0 < mode4JacobiUpper (mode4JacobiG mProject) (K - 1) :=
    mode4JacobiUpper_pos _ _ hG
  rw [det_mode4HermitianSchurMatrix_eq_schurContinuant
    mProject K Λ hm hK1]
  unfold mode4SchurContinuant
  by_cases hP : 0 ≤ mode4ScaledLeftContinuant
      (mode4JacobiG mProject) Λ (K - 1)
  · rw [max_eq_left hP]
    have hmul := mul_le_mul_of_nonneg_right htail.2
      (mul_nonneg hU.le hP)
    nlinarith
  · have hP' : mode4ScaledLeftContinuant
        (mode4JacobiG mProject) Λ (K - 1) ≤ 0 := le_of_not_ge hP
    rw [max_eq_right hP']
    have hprod :
        mode4RightTailLimit mProject Λ K *
            mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
              mode4ScaledLeftContinuant
                (mode4JacobiG mProject) Λ (K - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg htail.1 hU.le) hP'
    nlinarith

/-- The exact Hermitian Schur determinant is bounded above by the finite-left envelope obtained
from the worst admissible tail when the penultimate continuant is nonpositive. -/
theorem mode4HermitianSchur_det_le_finiteLeft_upperEnvelope
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    (mode4HermitianSchurMatrix mProject Λ K).det ≤
      mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ K +
        (1 / 2 : ℝ) * mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
          max (-mode4ScaledLeftContinuant
            (mode4JacobiG mProject) Λ (K - 1)) 0 := by
  have hK1 : 1 ≤ K := le_trans (by decide : 1 ≤ 3) hK
  have htail := mode4RightTailLimit_mem_Icc
    mProject K Λ hm hK hsep hΛ
  have hmR : (0 : ℝ) < (mProject : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have hU : 0 < mode4JacobiUpper (mode4JacobiG mProject) (K - 1) :=
    mode4JacobiUpper_pos _ _ hG
  rw [det_mode4HermitianSchurMatrix_eq_schurContinuant
    mProject K Λ hm hK1]
  unfold mode4SchurContinuant
  by_cases hP : 0 ≤ mode4ScaledLeftContinuant
      (mode4JacobiG mProject) Λ (K - 1)
  · rw [max_eq_right (neg_nonpos.mpr hP)]
    have hprod : 0 ≤
        mode4RightTailLimit mProject Λ K *
            mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
              mode4ScaledLeftContinuant
                (mode4JacobiG mProject) Λ (K - 1) :=
      mul_nonneg (mul_nonneg htail.1 hU.le) hP
    nlinarith
  · have hP' : mode4ScaledLeftContinuant
        (mode4JacobiG mProject) Λ (K - 1) ≤ 0 := le_of_not_ge hP
    rw [max_eq_left (neg_nonneg.mpr hP')]
    have hmul := mul_le_mul_of_nonneg_right htail.2
      (mul_nonneg hU.le (neg_nonneg.mpr hP'))
    nlinarith

/-- A positive finite-left lower envelope supplies the positive determinant input required by
the direct root-bracket receiver. -/
theorem mode4HermitianSchur_det_pos_of_finiteLeft_lowerEnvelope_pos
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (henv : 0 <
      mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ K -
        (1 / 2 : ℝ) * mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
          max (mode4ScaledLeftContinuant
            (mode4JacobiG mProject) Λ (K - 1)) 0) :
    0 < (mode4HermitianSchurMatrix mProject Λ K).det :=
  lt_of_lt_of_le henv
    (mode4HermitianSchur_det_ge_finiteLeft_lowerEnvelope
      mProject K Λ hm hK hsep hΛ)

/-- A negative finite-left upper envelope supplies the negative determinant input required by
the direct root-bracket receiver. -/
theorem mode4HermitianSchur_det_neg_of_finiteLeft_upperEnvelope_neg
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (henv :
      mode4ScaledLeftContinuant (mode4JacobiG mProject) Λ K +
          (1 / 2 : ℝ) * mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
            max (-mode4ScaledLeftContinuant
              (mode4JacobiG mProject) Λ (K - 1)) 0 < 0) :
    (mode4HermitianSchurMatrix mProject Λ K).det < 0 :=
  lt_of_le_of_lt
    (mode4HermitianSchur_det_le_finiteLeft_upperEnvelope
      mProject K Λ hm hK hsep hΛ) henv

/-- Canonical `K = 4m` assembly.  The infinite tail, determinant signs, continuity, and split
separation are all discharged internally; only the two strict finite-left envelope inequalities
at the chosen endpoints remain. -/
theorem exists_mode4RootFunction_eq_zero_at_four_mul_of_finiteLeft_envelopes
    (mProject : ℕ) (ΛLower ΛUpper : ℝ)
    (hm : 2 ≤ mProject)
    (hLowerUpper : ΛLower ≤ ΛUpper)
    (hUpper20 : ΛUpper ≤ 20)
    (hLowerEnvelope : 0 <
      mode4ScaledLeftContinuant (mode4JacobiG mProject) ΛLower (4 * mProject) -
        (1 / 2 : ℝ) *
            mode4JacobiUpper (mode4JacobiG mProject) (4 * mProject - 1) *
          max (mode4ScaledLeftContinuant
            (mode4JacobiG mProject) ΛLower (4 * mProject - 1)) 0)
    (hUpperEnvelope :
      mode4ScaledLeftContinuant (mode4JacobiG mProject) ΛUpper (4 * mProject) +
          (1 / 2 : ℝ) *
              mode4JacobiUpper (mode4JacobiG mProject) (4 * mProject - 1) *
            max (-mode4ScaledLeftContinuant
              (mode4JacobiG mProject) ΛUpper (4 * mProject - 1)) 0 < 0) :
    ∃ Λ ∈ Set.Icc ΛLower ΛUpper,
      mode4RootFunction mProject (4 * mProject) Λ = 0 := by
  have hK : 3 ≤ 4 * mProject := by omega
  have hsep :
      ∀ q ≥ 4 * mProject,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 :=
    fun q hq => mode4Jacobi_tail_separated_at_four_mul mProject q hm hq
  have hLower20 : ΛLower ≤ 20 := hLowerUpper.trans hUpper20
  have hLowerDet :
      0 < (mode4HermitianSchurMatrix
        mProject ΛLower (4 * mProject)).det :=
    mode4HermitianSchur_det_pos_of_finiteLeft_lowerEnvelope_pos
      mProject (4 * mProject) ΛLower hm hK hsep hLower20 hLowerEnvelope
  have hUpperDet :
      (mode4HermitianSchurMatrix
        mProject ΛUpper (4 * mProject)).det < 0 :=
    mode4HermitianSchur_det_neg_of_finiteLeft_upperEnvelope_neg
      mProject (4 * mProject) ΛUpper hm hK hsep hUpper20 hUpperEnvelope
  exact exists_mode4RootFunction_eq_zero_at_four_mul_of_hermitianSchur_det_pos_neg
    mProject ΛLower ΛUpper hm hLowerUpper hUpper20 hLowerDet hUpperDet

#print axioms mode4HermitianSchur_det_ge_finiteLeft_lowerEnvelope
#print axioms mode4HermitianSchur_det_le_finiteLeft_upperEnvelope
#print axioms mode4HermitianSchur_det_pos_of_finiteLeft_lowerEnvelope_pos
#print axioms mode4HermitianSchur_det_neg_of_finiteLeft_upperEnvelope_neg
#print axioms exists_mode4RootFunction_eq_zero_at_four_mul_of_finiteLeft_envelopes
