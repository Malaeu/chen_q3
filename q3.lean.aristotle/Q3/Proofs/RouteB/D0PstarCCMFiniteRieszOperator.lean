import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set Matrix
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Exact finite CCM Riesz carrier bind

This file transports the literal finite CCM coefficient operator through the
exact Euclidean coefficient carrier into the finite source subspace `E_m_N`.
It proves only a finite-carrier representation statement.  It does not
characterize a Weil form in Lean, define the ambient associated operator
`A_m`, prove membership in `Dom(A_m)`, identify an ambient compression, close
`H4a1b`, or produce the continuum numerator.
-/

private def exact_CCMModeFinite_to_modeSet_equivalence
    (i : PairIndex) :
    CCMModeFinite i.N ≃ {n : ℤ // n ∈ modeSet i} := by
  let toMode : CCMModeFinite i.N → {n : ℤ // n ∈ modeSet i} :=
    fun j => ⟨ccmModeFinite i.N j, by
      simpa [modeSet] using ccmModeFinite_range i.N j⟩
  refine Equiv.ofBijective toMode ?_
  constructor
  · intro j k hjk
    apply Fin.ext
    have hval := congrArg Subtype.val hjk
    change ccmModeFinite i.N j = ccmModeFinite i.N k at hval
    simp only [ccmModeFinite] at hval
    omega
  · intro n
    have hn : -(i.N : ℤ) ≤ n.1 ∧ n.1 ≤ i.N := by
      have hnmem : n.1 ∈ Finset.Icc (-(i.N : ℤ)) (i.N : ℤ) := by
        simpa only [modeSet] using n.2
      exact Finset.mem_Icc.mp hnmem
    have hnonneg : 0 ≤ n.1 + (i.N : ℤ) := by omega
    have hlt : n.1 + (i.N : ℤ) < (2 * i.N + 1 : ℕ) := by omega
    have hltNat : (n.1 + (i.N : ℤ)).toNat < 2 * i.N + 1 := by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hlt
    let j : CCMModeFinite i.N :=
      ⟨(n.1 + (i.N : ℤ)).toNat, hltNat⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    simp only [toMode, j, ccmModeFinite]
    rw [Int.toNat_of_nonneg hnonneg]
    omega

private noncomputable def ccmFiniteModeOrthonormalBasis
    (i : PairIndex) :
    OrthonormalBasis (CCMModeFinite i.N) ℂ (E_m_N i) := by
  classical
  let sourceCarrier : Submodule ℂ (H_m i) :=
    Submodule.span ℂ ((modeSet i).image (V_n_m i) : Set (H_m i))
  have hcarrier : sourceCarrier = E_m_N i := by
    change Submodule.span ℂ ((modeSet i).image (V_n_m i) : Set (H_m i)) =
      Submodule.span ℂ (V_n_m i '' (modeSet i : Set ℤ))
    rw [Finset.coe_image]
  let carrierEquiv : sourceCarrier ≃ₗᵢ[ℂ] E_m_N i :=
    LinearIsometryEquiv.ofEq sourceCarrier (E_m_N i) hcarrier
  let b0 : OrthonormalBasis (modeSet i) ℂ (E_m_N i) :=
    (OrthonormalBasis.span (V_n_m_orthonormal i) (modeSet i)).map carrierEquiv
  exact b0.reindex (exact_CCMModeFinite_to_modeSet_equivalence i).symm

private theorem coe_ccmFiniteModeOrthonormalBasis_apply
    (i : PairIndex) (j : CCMModeFinite i.N) :
    ((ccmFiniteModeOrthonormalBasis i j : E_m_N i) : H_m i) =
      V_n_m i (ccmModeFinite i.N j) := by
  classical
  simp only [ccmFiniteModeOrthonormalBasis, OrthonormalBasis.reindex_apply,
    Equiv.symm_symm, OrthonormalBasis.map_apply,
    LinearIsometryEquiv.coe_ofEq_apply, OrthonormalBasis.span_apply]
  change V_n_m i (ccmModeFinite i.N j) = V_n_m i (ccmModeFinite i.N j)
  rfl

/-- The literal ordered CCM Fourier synthesis as an isometric equivalence from
the Euclidean coefficient carrier to the finite source subspace. -/
noncomputable def ccmFiniteSynthesisEquiv
    (i : PairIndex) :
    EuclideanSpace ℂ (CCMModeFinite i.N) ≃ₗᵢ[ℂ] E_m_N i :=
  (ccmFiniteModeOrthonormalBasis i).repr.symm

private theorem ccmFiniteSynthesisEquiv_apply_toLp
    (i : PairIndex)
    (q : CCMModeFinite i.N → ℂ) :
    ((ccmFiniteSynthesisEquiv i (WithLp.toLp 2 q) : E_m_N i) : H_m i) =
      ccmFiniteSynthesis i q := by
  classical
  rw [ccmFiniteSynthesisEquiv]
  rw [← (ccmFiniteModeOrthonormalBasis i).sum_repr_symm (WithLp.toLp 2 q)]
  simp only [coe_ccmFiniteModeOrthonormalBasis_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower]
  rfl

private noncomputable def sourceCCMFiniteOperatorEuclidean
    (i : PairIndex) :
    Module.End ℂ (EuclideanSpace ℂ (CCMModeFinite i.N)) :=
  (WithLp.linearEquiv 2 ℂ
      (CCMModeFinite i.N → ℂ)).symm.conj
    (sourceCCMFiniteOperator i)

private theorem sourceCCMFiniteOperatorEuclidean_apply_toLp
    (i : PairIndex)
    (q : CCMModeFinite i.N → ℂ) :
    sourceCCMFiniteOperatorEuclidean i (WithLp.toLp 2 q) =
      WithLp.toLp 2 (sourceCCMFiniteOperator i q) := by
  simp [sourceCCMFiniteOperatorEuclidean, LinearEquiv.conj_apply_apply]

/-- The finite Riesz realization of the exact source CCM matrix on `E_m_N i`.
It is not the ambient associated operator `A_m`. -/
noncomputable def sourceCCMFiniteRieszOperator
    (i : PairIndex) :
    Module.End ℂ (E_m_N i) :=
  (ccmFiniteSynthesisEquiv i).toLinearEquiv.conj
    (sourceCCMFiniteOperatorEuclidean i)

/-- The source finite Riesz operator acts on the literal normalized projected
source trial by the synthesized exact CCM matrix action.

This theorem is finite-carrier semantics only.  It asserts neither membership
in `Dom(A_m)` nor ambient operator compression. -/
theorem sourceCCMFiniteRieszOperator_apply_sourceTrial
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    let xE : E_m_N i :=
      kTrial_m_N
        i
        (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i)
        (S.source.trialNonzero i)
    ((sourceCCMFiniteRieszOperator i xE : E_m_N i) : H_m i) =
      ccmFiniteSynthesis i
        (sourceCCMFiniteOperator i
          (sourceCCMComplexRow S i)) := by
  let q : CCMModeFinite i.N → ℂ := sourceCCMComplexRow S i
  let q₂ : EuclideanSpace ℂ (CCMModeFinite i.N) := WithLp.toLp 2 q
  let xE : E_m_N i :=
    kTrial_m_N
      i
      (prolateCombination (S.source.pair i))
      (S.source.eStar_memLp i)
      (S.source.trialNonzero i)
  have hx : ccmFiniteSynthesisEquiv i q₂ = xE := by
    apply Subtype.ext
    exact (ccmFiniteSynthesisEquiv_apply_toLp i q).trans
      (ccmFiniteSynthesis_sourceCCMComplexRow S i)
  change ((sourceCCMFiniteRieszOperator i xE : E_m_N i) : H_m i) =
    ccmFiniteSynthesis i (sourceCCMFiniteOperator i q)
  rw [← hx]
  calc
    ((sourceCCMFiniteRieszOperator i
        (ccmFiniteSynthesisEquiv i q₂) : E_m_N i) : H_m i) =
        ((ccmFiniteSynthesisEquiv i
          (sourceCCMFiniteOperatorEuclidean i q₂) : E_m_N i) : H_m i) := by
      simp [sourceCCMFiniteRieszOperator, LinearEquiv.conj_apply_apply]
    _ = ((ccmFiniteSynthesisEquiv i
          (WithLp.toLp 2 (sourceCCMFiniteOperator i q)) : E_m_N i) : H_m i) := by
      dsimp only [q₂]
      rw [sourceCCMFiniteOperatorEuclidean_apply_toLp]
    _ = ccmFiniteSynthesis i (sourceCCMFiniteOperator i q) :=
      ccmFiniteSynthesisEquiv_apply_toLp i
        (sourceCCMFiniteOperator i q)

#print axioms sourceCCMFiniteRieszOperator_apply_sourceTrial

end Q3.RouteB.D0Pstar
