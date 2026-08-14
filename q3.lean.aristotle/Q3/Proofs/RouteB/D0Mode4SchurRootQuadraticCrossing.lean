import Q3.Proofs.RouteB.D0Mode4SchurSpectralParameterOrder
import Q3.Proofs.RouteB.D0Mode4SchurSimpleKernel
import Q3.Proofs.RouteB.D0HermitianNegativeIndexDrop

/-!
# Quantitative quadratic crossing at an exact mode-four Schur root

Knowledge preflight for `Goal058.G3.Mode4SchurRootQuadraticCrossing` used the
exact shelf queries
`Goal058 mode4 Schur endpoint inertia index4 selection`,
`mode4RootFunction inertia crossing continuant Sturm count`,
`Hermitian Schur matrix principal minors inertia simple kernel`, and
`psi4 indexed Ferrers DLMF 30.8.4 root selection`, followed by three semantic
queries for the same endpoint-inertia, principal-minor, and indexed-source
interfaces.  The search found the existing Hermitian count receiver,
spectral-parameter matrix order, simple-root kernel, and DLMF coefficient
crosswalk, but no theorem giving the literal crossing direction or a concrete
endpoint count.

This file closes the first of those two gaps.  If `v` lies in the kernel at an
exact root `Lambda`, the Loewner drop proves a quantitative positive quadratic
margin below the root and a quantitative negative margin above it.  The
existence wrapper uses the literal root determinant and returns one nonzero
kernel vector witnessing both signs.

This is not an endpoint-inertia count, root-existence theorem, ordered PSWF
selection, finite-Fourier relation, or CCM rate theorem.
-/

noncomputable section

open Matrix

/-- A root-kernel vector has a quantitative positive quadratic margin at every
smaller spectral parameter in the pole-free domain. -/
theorem mode4HermitianSchurMatrix_rootKernel_quadratic_ge_below
    (mProject K : ℕ) (Λlo Λ : ℝ) (v : Fin K → ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛlo20 : Λlo ≤ 20)
    (hΛ20 : Λ ≤ 20)
    (hlo : Λlo ≤ Λ)
    (hAv : mode4HermitianSchurMatrix mProject Λ K *ᵥ v = 0) :
    (Λ - Λlo) * (star v ⬝ᵥ v) ≤
      star v ⬝ᵥ
        (mode4HermitianSchurMatrix mProject Λlo K *ᵥ v) := by
  have hpsd :=
    mode4HermitianSchurMatrix_spectralParameter_drop_posSemidef
      mProject K Λlo Λ hm hK hsep hΛlo20 hΛ20 hlo
  have hq := hpsd.dotProduct_mulVec_nonneg v
  have hq' :
      0 ≤ star v ⬝ᵥ
          (mode4HermitianSchurMatrix mProject Λlo K *ᵥ v) -
        (Λ - Λlo) * (star v ⬝ᵥ v) := by
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hAv, dotProduct_sub, dotProduct_smul, smul_eq_mul] using hq
  exact sub_nonneg.mp hq'

/-- A root-kernel vector has a quantitative negative quadratic margin at every
larger spectral parameter in the pole-free domain. -/
theorem mode4HermitianSchurMatrix_rootKernel_quadratic_le_above
    (mProject K : ℕ) (Λ Λhi : ℝ) (v : Fin K → ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ20 : Λ ≤ 20)
    (hΛhi20 : Λhi ≤ 20)
    (hhi : Λ ≤ Λhi)
    (hAv : mode4HermitianSchurMatrix mProject Λ K *ᵥ v = 0) :
    star v ⬝ᵥ
        (mode4HermitianSchurMatrix mProject Λhi K *ᵥ v) ≤
      -(Λhi - Λ) * (star v ⬝ᵥ v) := by
  have hpsd :=
    mode4HermitianSchurMatrix_spectralParameter_drop_posSemidef
      mProject K Λ Λhi hm hK hsep hΛ20 hΛhi20 hhi
  have hq := hpsd.dotProduct_mulVec_nonneg v
  have hq' :
      0 ≤ -(star v ⬝ᵥ
          (mode4HermitianSchurMatrix mProject Λhi K *ᵥ v)) -
        (Λhi - Λ) * (star v ⬝ᵥ v) := by
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hAv, dotProduct_sub, dotProduct_smul, smul_eq_mul] using hq
  linarith

/-- Every exact matching root supplies a nonzero kernel vector whose quadratic
form is strictly positive below the root and strictly negative above it.  The
same vector is used on both sides; no eigenvector reindexing is involved. -/
theorem exists_mode4HermitianSchurMatrix_root_crossingVector
    (mProject K : ℕ) (Λlo Λ Λhi : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hlo : Λlo < Λ)
    (hhi : Λ < Λhi)
    (hΛhi20 : Λhi ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    ∃ v : Fin K → ℝ,
      v ≠ 0 ∧
      mode4HermitianSchurMatrix mProject Λ K *ᵥ v = 0 ∧
      0 < star v ⬝ᵥ
        (mode4HermitianSchurMatrix mProject Λlo K *ᵥ v) ∧
      star v ⬝ᵥ
        (mode4HermitianSchurMatrix mProject Λhi K *ᵥ v) < 0 := by
  let A := mode4HermitianSchurMatrix mProject Λ K
  have hdet : A.det = 0 := by
    rw [show A.det = mode4SchurContinuant mProject K Λ by
      simpa [A] using det_mode4HermitianSchurMatrix_eq_schurContinuant
        mProject K Λ hm (le_trans (by decide : 1 ≤ 3) hK)]
    rw [mode4SchurContinuant_eq_upperProd_mul_rootFunction
      mProject K Λ (le_trans (by decide : 1 ≤ 3) hK), hroot, mul_zero]
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv' : mode4HermitianSchurMatrix mProject Λ K *ᵥ v = 0 := by
    simpa [A] using hAv
  have hΛ20 : Λ ≤ 20 := le_trans hhi.le hΛhi20
  have hΛlo20 : Λlo ≤ 20 := le_trans hlo.le hΛ20
  have hvnorm : 0 < star v ⬝ᵥ v :=
    Matrix.dotProduct_star_self_pos_iff.mpr hv
  have hbelow :=
    mode4HermitianSchurMatrix_rootKernel_quadratic_ge_below
      mProject K Λlo Λ v hm hK hsep hΛlo20 hΛ20 hlo.le hAv'
  have habove :=
    mode4HermitianSchurMatrix_rootKernel_quadratic_le_above
      mProject K Λ Λhi v hm hK hsep hΛ20 hΛhi20 hhi.le hAv'
  have hpositive :
      0 < star v ⬝ᵥ
        (mode4HermitianSchurMatrix mProject Λlo K *ᵥ v) := by
    have hmargin : 0 < (Λ - Λlo) * (star v ⬝ᵥ v) :=
      mul_pos (sub_pos.mpr hlo) hvnorm
    exact lt_of_lt_of_le hmargin hbelow
  have hnegative :
      star v ⬝ᵥ
        (mode4HermitianSchurMatrix mProject Λhi K *ᵥ v) < 0 := by
    have hmargin : -(Λhi - Λ) * (star v ⬝ᵥ v) < 0 := by
      have : 0 < (Λhi - Λ) * (star v ⬝ᵥ v) :=
        mul_pos (sub_pos.mpr hhi) hvnorm
      linarith
    exact lt_of_le_of_lt habove hmargin
  exact ⟨v, hv, hAv', hpositive, hnegative⟩

/-- Strictly increasing the spectral parameter grows the negative index by at
least the nullity at the starting parameter.  This is the exact one-step
inertia ladder supplied by the Schur-family Loewner drop. -/
theorem mode4HermitianSchurMatrix_negativeCount_add_nullity_le_of_lt
    (mProject K : ℕ) (Λ Λhi : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hhi : Λ < Λhi)
    (hΛhi20 : Λhi ≤ 20) :
    mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ) +
        Module.finrank ℝ
          (LinearMap.ker
            (mode4HermitianSchurMatrix mProject Λ K).mulVecLin) ≤
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λhi K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λhi) := by
  let A := mode4HermitianSchurMatrix mProject Λ K
  let B := mode4HermitianSchurMatrix mProject Λhi K
  let hA : A.IsHermitian :=
    mode4HermitianSchurMatrix_isHermitian mProject K Λ
  let hB : B.IsHermitian :=
    mode4HermitianSchurMatrix_isHermitian mProject K Λhi
  have hΛ20 : Λ ≤ 20 := le_trans hhi.le hΛhi20
  have hdrop :
      (A - B - (Λhi - Λ) • (1 : Matrix (Fin K) (Fin K) ℝ)).PosSemidef := by
    simpa [A, B] using
      mode4HermitianSchurMatrix_spectralParameter_drop_posSemidef
        mProject K Λ Λhi hm hK hsep hΛ20 hΛhi20 hhi.le
  simpa [A, B, hA, hB] using
    hermitian_negativeCount_add_nullity_le_of_strict_drop
      hA hB (Λhi - Λ) (sub_pos.mpr hhi) hdrop

/-- Crossing a simple exact root in the increasing-`Lambda` direction raises
the negative eigenvalue count by at least one.  This is a one-sided inertia
jump; it does not identify the count on either endpoint or select which
ordered PSWF root has been crossed. -/
theorem mode4HermitianSchurMatrix_negativeCount_succ_le_above_root
    (mProject K : ℕ) (Λ Λhi : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hhi : Λ < Λhi)
    (hΛhi20 : Λhi ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ) + 1 ≤
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λhi K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λhi) := by
  let A := mode4HermitianSchurMatrix mProject Λ K
  have hnullity :
      Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 1 := by
    simpa [A] using
      mode4HermitianSchurMatrix_root_ker_finrank_eq_one
        mProject K Λ hm (le_trans (by decide : 1 ≤ 3) hK) hroot
  have hjump :=
    mode4HermitianSchurMatrix_negativeCount_add_nullity_le_of_lt
      mProject K Λ Λhi hm hK hsep hhi hΛhi20
  simpa [A, hnullity] using hjump

#print axioms mode4HermitianSchurMatrix_rootKernel_quadratic_ge_below
#print axioms mode4HermitianSchurMatrix_rootKernel_quadratic_le_above
#print axioms exists_mode4HermitianSchurMatrix_root_crossingVector
#print axioms mode4HermitianSchurMatrix_negativeCount_add_nullity_le_of_lt
#print axioms mode4HermitianSchurMatrix_negativeCount_succ_le_above_root
