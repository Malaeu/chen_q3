import Q3.Proofs.RouteB.D0PstarSourceWeilClosedForm
import Q3.Proofs.RouteB.D0PstarShiftedArchFiniteModeDomain
import Q3.Proofs.RouteB.D0PstarCCMFiniteRieszOperator

noncomputable section

open Complex Matrix
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-!
# Exact normalized odd source-Weil form pullback at `m = 13`

This file embeds the literal positive odd coefficients into the ordered CCM
carrier by the normalized antisymmetric pairs
`(V_r - V_{-r}) / sqrt 2`, synthesizes them in the exact finite source span,
and pulls the already-proved source-Weil form identity back to that carrier.

It is only a form-level finite pullback.  It does not define an associated
operator or graph, prove a form core or tail estimate, run a numerical probe,
close `H4a1b`, decrement a coarse checkpoint, or promote Route B.
-/

private def ccmOddPositiveFinite (N : ℕ) (r : Fin N) : CCMModeFinite N :=
  ⟨N + r.1 + 1, by omega⟩

private theorem ccmOddPositiveFinite_inj
    (N : ℕ) (r s : Fin N) :
    ccmOddPositiveFinite N r = ccmOddPositiveFinite N s ↔ r = s := by
  constructor
  · intro h
    apply Fin.ext
    simpa [ccmOddPositiveFinite] using congrArg Fin.val h
  · intro h
    subst s
    rfl

private theorem ccmOddPositiveFinite_ne_neg
    (N : ℕ) (r s : Fin N) :
    ccmOddPositiveFinite N r ≠
      ccmNegFinite N (ccmOddPositiveFinite N s) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ccmOddPositiveFinite, ccmNegFinite] at hv
  omega

private theorem ccmOddNegativeFinite_inj
    (N : ℕ) (r s : Fin N) :
    ccmNegFinite N (ccmOddPositiveFinite N r) =
        ccmNegFinite N (ccmOddPositiveFinite N s) ↔ r = s := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [ccmOddPositiveFinite, ccmNegFinite] at hv
    apply Fin.ext
    omega
  · intro h
    subst s
    rfl

private theorem ccmOddNegativeFinite_ne_pos
    (N : ℕ) (r s : Fin N) :
    ccmNegFinite N (ccmOddPositiveFinite N r) ≠
      ccmOddPositiveFinite N s := by
  exact fun h => ccmOddPositiveFinite_ne_neg N s r h.symm

private noncomputable def ccmOddBasisVector
    (N : ℕ) (r : Fin N) : EuclideanSpace ℂ (CCMModeFinite N) :=
  EuclideanSpace.single (ccmOddPositiveFinite N r)
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) -
    EuclideanSpace.single
      (ccmNegFinite N (ccmOddPositiveFinite N r))
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)

private theorem ccmInvSqrtTwo_pair_norm :
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) +
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 := by
  have hsR : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsC : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hsR
  field_simp [hsC]
  norm_cast
  norm_num [Real.sq_sqrt]

private theorem ccmOddBasisVector_orthonormal (N : ℕ) :
    Orthonormal ℂ (ccmOddBasisVector N) := by
  classical
  rw [orthonormal_iff_ite]
  intro r s
  simp only [ccmOddBasisVector, inner_sub_left, inner_sub_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
    ccmOddPositiveFinite_inj, ccmOddPositiveFinite_ne_neg,
    ccmOddNegativeFinite_ne_pos, ccmOddNegativeFinite_inj]
  by_cases hrs : r = s
  · subst s
    simpa using ccmInvSqrtTwo_pair_norm
  · simp [hrs]

private noncomputable def ccmOddCoefficientMatrix (N : ℕ) :
    Matrix (CCMModeFinite N) (Fin N) ℂ :=
  fun j r => ccmOddBasisVector N r j

/-- The exact normalized antisymmetric coefficient embedding into the literal
CCM order `-N, ..., 0, ..., N`. -/
noncomputable def ccmOddCoefficientIsometry
    (N : ℕ) :
    EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (CCMModeFinite N) :=
  (Matrix.toEuclideanLin (ccmOddCoefficientMatrix N)).isometryOfInner (by
    classical
    intro a b
    have ha :
        Matrix.toEuclideanLin (ccmOddCoefficientMatrix N) a =
          ∑ r, a r • ccmOddBasisVector N r := by
      ext j
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec,
        dotProduct, ccmOddCoefficientMatrix, smul_eq_mul, mul_comm]
    have hb :
        Matrix.toEuclideanLin (ccmOddCoefficientMatrix N) b =
          ∑ r, b r • ccmOddBasisVector N r := by
      ext j
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec,
        dotProduct, ccmOddCoefficientMatrix, smul_eq_mul, mul_comm]
    rw [ha, hb]
    simpa [PiLp.inner_apply, mul_comm] using
      (ccmOddBasisVector_orthonormal N).inner_sum a b Finset.univ)

private theorem ccmModeFinite_inj (N : ℕ) :
    Function.Injective (ccmModeFinite N) := by
  intro j k h
  apply Fin.ext
  simpa [ccmModeFinite] using h

private noncomputable def ccmFiniteShiftedFormDomainIsometry
    (i : PairIndex) :
    EuclideanSpace ℂ (CCMModeFinite i.N) →ₗᵢ[ℂ]
      sourceArchimedeanShiftedFormDomain i :=
  ({ toFun := fun c => ccmFiniteShiftedFormDomainSynthesis i c
     map_add' := by
       intro c d
       exact (ccmFiniteShiftedFormDomainSynthesis i).map_add c d
     map_smul' := by
       intro a c
       exact (ccmFiniteShiftedFormDomainSynthesis i).map_smul a c } :
      EuclideanSpace ℂ (CCMModeFinite i.N) →ₗ[ℂ]
        sourceArchimedeanShiftedFormDomain i).isometryOfInner (by
    classical
    intro c d
    change inner ℂ (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i d) =
      inner ℂ c d
    unfold ccmFiniteSynthesis
    have horth :
        Orthonormal ℂ
          (fun j : CCMModeFinite i.N => V_n_m i (ccmModeFinite i.N j)) :=
      (V_n_m_orthonormal i).comp (ccmModeFinite i.N)
        (ccmModeFinite_inj i.N)
    simpa [PiLp.inner_apply, mul_comm] using
      horth.inner_sum c d Finset.univ)

/-- The normalized odd coefficient synthesis on an arbitrary production
`PairIndex`.  Unlike the historical `m = 13` wrapper below, this definition
keeps both coordinates of the current source schedule. -/
noncomputable def sourceWeilOddSynthesis
    (i : PairIndex) :
    EuclideanSpace ℂ (Fin i.N) →ₗᵢ[ℂ]
      sourceArchimedeanShiftedFormDomain i :=
  (ccmFiniteShiftedFormDomainIsometry i).comp
    (ccmOddCoefficientIsometry i.N)

private theorem sourceWeilOddSynthesis_apply
    (i : PairIndex) (a : EuclideanSpace ℂ (Fin i.N)) :
    sourceWeilOddSynthesis i a =
      ccmFiniteShiftedFormDomainSynthesis i
        (ccmOddCoefficientIsometry i.N a) :=
  rfl

/-- The arbitrary-cell normalized odd synthesis is the literal sum of
antisymmetric source-mode pairs. -/
theorem sourceWeilOddSynthesis_eq_normalized_mode_sum
    (i : PairIndex) (a : EuclideanSpace ℂ (Fin i.N)) :
    sourceWeilOddSynthesis i a =
      ∑ r : Fin i.N, a r •
        ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
          (sourceArchimedeanModeInShiftedFormDomain i (r.1 + 1 : ℕ) -
            sourceArchimedeanModeInShiftedFormDomain i
              (-((r.1 + 1 : ℕ) : ℤ)))) := by
  classical
  rw [sourceWeilOddSynthesis_apply]
  rw [ccmFiniteShiftedFormDomainSynthesis_eq_sum]
  change
    (∑ j : CCMModeFinite i.N,
      (∑ r : Fin i.N, ccmOddBasisVector i.N r j * a r) •
        sourceArchimedeanModeInShiftedFormDomain i
          (ccmModeFinite i.N j)) = _
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  simp [ccmOddBasisVector]
  simp_rw [sub_mul, sub_smul]
  rw [Finset.sum_sub_distrib]
  simp [ccmOddPositiveFinite, ccmNegFinite, ccmModeFinite,
    smul_sub, smul_smul, mul_comm]
  congr 2 <;> congr 1 <;> omega

/-- The exact source-Weil form pulled back to normalized odd coefficients on
an arbitrary production cell. -/
theorem sourceWeilOddFormPullback
    (i : PairIndex)
    (a b : EuclideanSpace ℂ (Fin i.N)) :
    sourceWeilSesquilinearForm i
        (sourceWeilOddSynthesis i a)
        (sourceWeilOddSynthesis i b) =
      ∑ j, ∑ k,
        star ((ccmOddCoefficientIsometry i.N a) j) *
          (Q3.RouteB.ccmWeilMatFinite i.m i.N j k : ℂ) *
          (ccmOddCoefficientIsometry i.N b) k := by
  rw [sourceWeilOddSynthesis_apply, sourceWeilOddSynthesis_apply]
  rw [sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis]

/-- The normalized odd coefficients synthesized in the exact `m = 13`
shifted source-Weil form domain. -/
noncomputable def sourceWeilOddSynthesis13
    (N : ℕ) :
    EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ]
      sourceArchimedeanShiftedFormDomain ⟨13, N, by norm_num⟩ :=
  (ccmFiniteShiftedFormDomainIsometry ⟨13, N, by norm_num⟩).comp
    (ccmOddCoefficientIsometry N)

private theorem sourceWeilOddSynthesis13_apply
    (N : ℕ) (a : EuclideanSpace ℂ (Fin N)) :
    sourceWeilOddSynthesis13 N a =
      ccmFiniteShiftedFormDomainSynthesis ⟨13, N, by norm_num⟩
        (ccmOddCoefficientIsometry N a) :=
  rfl

private def sourceWeilOddIndex13 (N : ℕ) : PairIndex :=
  ⟨13, N, by norm_num⟩

/-- The normalized odd synthesis is the literal sum of antisymmetric source
mode pairs.  This public expansion is the cheap graph/finite-source crosswalk
used by downstream exact receivers; it avoids relying on a massive
definitional reduction through the matrix isometry. -/
theorem sourceWeilOddSynthesis13_eq_normalized_mode_sum
    (N : ℕ) (a : EuclideanSpace ℂ (Fin N)) :
    sourceWeilOddSynthesis13 N a =
      ∑ r : Fin N, a r •
        ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
          (sourceArchimedeanModeInShiftedFormDomain
              (sourceWeilOddIndex13 N) (r.1 + 1 : ℕ) -
            sourceArchimedeanModeInShiftedFormDomain
              (sourceWeilOddIndex13 N) (-((r.1 + 1 : ℕ) : ℤ)))) := by
  classical
  rw [sourceWeilOddSynthesis13_apply]
  rw [ccmFiniteShiftedFormDomainSynthesis_eq_sum]
  change
    (∑ j : CCMModeFinite N,
      (∑ r : Fin N, ccmOddBasisVector N r j * a r) •
        sourceArchimedeanModeInShiftedFormDomain
          (sourceWeilOddIndex13 N) (ccmModeFinite N j)) = _
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  simp [ccmOddBasisVector]
  simp_rw [sub_mul, sub_smul]
  rw [Finset.sum_sub_distrib]
  simp [ccmOddPositiveFinite, ccmNegFinite, ccmModeFinite,
    smul_sub, smul_smul, mul_comm]
  congr 2 <;> congr 1 <;> omega

/-- The exact sesquilinear source-Weil form pulled back to the normalized odd
coefficient carrier at `m = 13`. -/
theorem sourceWeilOddFormPullback13
    (N : ℕ)
    (a b : EuclideanSpace ℂ (Fin N)) :
    sourceWeilSesquilinearForm
        ⟨13, N, by norm_num⟩
        (sourceWeilOddSynthesis13 N a)
        (sourceWeilOddSynthesis13 N b) =
      ∑ j, ∑ k,
        star ((ccmOddCoefficientIsometry N a) j) *
          (Q3.RouteB.ccmWeilMatFinite 13 N j k : ℂ) *
          (ccmOddCoefficientIsometry N b) k := by
  rw [sourceWeilOddSynthesis13_apply, sourceWeilOddSynthesis13_apply]
  rw [sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis]

#print axioms ccmOddCoefficientIsometry
#print axioms sourceWeilOddSynthesis
#print axioms sourceWeilOddSynthesis_eq_normalized_mode_sum
#print axioms sourceWeilOddFormPullback
#print axioms sourceWeilOddSynthesis13
#print axioms sourceWeilOddFormPullback13

end Q3.RouteB.D0Pstar
