import Q3.Proofs.RouteB.D0ProlateKTrialSource
import Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
import Q3.Proofs.RouteB.AmbientResidualSplit

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set Matrix
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Exact finite CCM residual of the source-complex coefficient row

This file binds the literal normalized `kTrial_m_N` coefficient row to the
literal finite CCM source matrix on the same ordered carrier `-N, ..., N`.
It proves only a finite-cell residual certificate.  In particular, it does
not identify the finite matrix action with a compressed continuum Weil
operator, prove a projection-leakage rate, close `H4a1b`, or claim a true gap.
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

private theorem finite_sum_reindex
    (i : PairIndex) (F : ℤ → H_m i) :
    (∑ j : CCMModeFinite i.N, F (ccmModeFinite i.N j)) =
      ∑ n ∈ modeSet i, F n := by
  classical
  let e := exact_CCMModeFinite_to_modeSet_equivalence i
  calc
    (∑ j : CCMModeFinite i.N, F (ccmModeFinite i.N j)) =
        ∑ n : {n : ℤ // n ∈ modeSet i}, F n.1 := by
      simpa [e, exact_CCMModeFinite_to_modeSet_equivalence] using
        e.sum_comp (fun n : {n : ℤ // n ∈ modeSet i} => F n.1)
    _ = ∑ n ∈ modeSet i, F n := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (modeSet i) F)

/-- Synthesis in the literal source mode order `-N, ..., N`. -/
noncomputable def ccmFiniteSynthesis
    (i : PairIndex) :
    (CCMModeFinite i.N → ℂ) →ₗ[ℂ] H_m i where
  toFun q :=
    ∑ j, q j • V_n_m i (ccmModeFinite i.N j)
  map_add' := by
    intro q r
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      smul_smul, Finset.smul_sum]

/-- Exact complex coefficient row of the normalized projected source trial. -/
noncomputable def sourceCCMComplexRow
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    CCMModeFinite i.N → ℂ :=
  fun j =>
    S.canonical.kTrial.kTrial i (ccmModeFinite i.N j)

/-- Literal CCM source matrix, complexified entrywise without changing order. -/
noncomputable def sourceCCMFiniteMatrix
    (i : PairIndex) :
    Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ :=
  fun j k => (ccmWeilMatFinite i.m i.N j k : ℂ)

/-- Finite source matrix action on the exact complex carrier. -/
noncomputable def sourceCCMFiniteOperator
    (i : PairIndex) :
    Module.End ℂ (CCMModeFinite i.N → ℂ) :=
  (sourceCCMFiniteMatrix i).mulVecLin

/-- Real Rayleigh value of the exact unit source row. -/
noncomputable def sourceCCMFiniteRayleigh
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) : ℝ :=
  (star (sourceCCMComplexRow S i) ⬝ᵥ
    (sourceCCMFiniteMatrix i *ᵥ sourceCCMComplexRow S i)).re

/-- Exact finite CCM Rayleigh residual of the source row. -/
noncomputable def sourceCCMFiniteResidual
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    CCMModeFinite i.N → ℂ :=
  ambientResidual
    (sourceCCMFiniteOperator i)
    (sourceCCMComplexRow S i)
    (sourceCCMFiniteRayleigh S i : ℂ)

theorem sourceCCMComplexRow_apply
    (S : ProlateCanonicalSourceData)
    (i : PairIndex)
    (j : CCMModeFinite i.N) :
    sourceCCMComplexRow S i j =
      c_n i
        (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i)
        (S.source.trialNonzero i)
        (ccmModeFinite i.N j) := by
  exact S.canonical_kTrial i (ccmModeFinite i.N j)

attribute [simp] sourceCCMComplexRow_apply

theorem ccmFiniteSynthesis_sourceCCMComplexRow
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    ccmFiniteSynthesis i (sourceCCMComplexRow S i) =
      (kTrial_m_N
        i
        (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i)
        (S.source.trialNonzero i) :
        H_m i) := by
  classical
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  let kE : E_m_N i :=
    kTrial_m_N i
      (prolateCombination (S.source.pair i))
      (S.source.eStar_memLp i)
      (S.source.trialNonzero i)
  have hprojection : P_m_N i (kE : H_m i) = kE := by
    rw [P_m_N]
    exact Submodule.orthogonalProjection_mem_subspace_eq_self kE
  have hreconstruction :=
    coe_P_m_N_apply_eq_sum_inner_V_n_m_smul i (kE : H_m i)
  rw [hprojection] at hreconstruction
  calc
    ccmFiniteSynthesis i (sourceCCMComplexRow S i) =
        ∑ j : CCMModeFinite i.N,
          inner ℂ (V_n_m i (ccmModeFinite i.N j)) (kE : H_m i) •
            V_n_m i (ccmModeFinite i.N j) := by
      simp only [ccmFiniteSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
        sourceCCMComplexRow_apply, c_n, kE]
    _ = ∑ n ∈ modeSet i,
          inner ℂ (V_n_m i n) (kE : H_m i) • V_n_m i n := by
      exact finite_sum_reindex i
        (fun n => inner ℂ (V_n_m i n) (kE : H_m i) • V_n_m i n)
    _ = (kE : H_m i) := hreconstruction.symm

private theorem finite_synthesis_inner_identity
    (i : PairIndex)
    (q : CCMModeFinite i.N → ℂ)
    (f : H_m i) :
    inner ℂ (ccmFiniteSynthesis i q) f =
      star q ⬝ᵥ
        (fun j => inner ℂ (V_n_m i (ccmModeFinite i.N j)) f) := by
  classical
  simp [ccmFiniteSynthesis, sum_inner, inner_smul_left, dotProduct]

theorem sourceCCMComplexRow_unit
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    star (sourceCCMComplexRow S i) ⬝ᵥ
      sourceCCMComplexRow S i = 1 := by
  let x : H_m i :=
    (kTrial_m_N
      i
      (prolateCombination (S.source.pair i))
      (S.source.eStar_memLp i)
      (S.source.trialNonzero i) : H_m i)
  have hsynthesis :
      ccmFiniteSynthesis i (sourceCCMComplexRow S i) = x :=
    ccmFiniteSynthesis_sourceCCMComplexRow S i
  have hinner :=
    finite_synthesis_inner_identity i (sourceCCMComplexRow S i) x
  have hcoeff :
      (fun j : CCMModeFinite i.N =>
        inner ℂ (V_n_m i (ccmModeFinite i.N j)) x) =
        sourceCCMComplexRow S i := by
    funext j
    simp [x, sourceCCMComplexRow_apply, c_n]
  rw [hcoeff, hsynthesis] at hinner
  calc
    star (sourceCCMComplexRow S i) ⬝ᵥ sourceCCMComplexRow S i =
        inner ℂ x x := hinner.symm
    _ = (‖x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K x
    _ = 1 := by
      rw [show ‖x‖ = 1 by
        exact norm_kTrial_m_N i
          (prolateCombination (S.source.pair i))
          (S.source.eStar_memLp i)
          (S.source.trialNonzero i)]
      norm_num

theorem sourceCCMFiniteMatrix_isHermitian
    (i : PairIndex) :
    (sourceCCMFiniteMatrix i).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro j k
  simpa [sourceCCMFiniteMatrix, ccmWeilMatFinite] using
    congrArg (fun x : ℝ => (x : ℂ))
      (ccmWeilTauN1_symm i.m i.hm
        (ccmModeFinite i.N k) (ccmModeFinite i.N j))

private theorem Hermitian_quadratic_reality_helper
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  have hreal :
      star x ⬝ᵥ A *ᵥ x = star (star x ⬝ᵥ A *ᵥ x) := by
    simp +decide [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr
    ext j
    congr
    ext k
    rw [← hA.apply]
    simp +decide [mul_comm, mul_left_comm]
  exact Complex.conj_eq_iff_im.mp hreal.symm

theorem sourceCCMFiniteRayleigh_coe
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    (sourceCCMFiniteRayleigh S i : ℂ) =
      star (sourceCCMComplexRow S i) ⬝ᵥ
        (sourceCCMFiniteMatrix i *ᵥ sourceCCMComplexRow S i) := by
  have him := Hermitian_quadratic_reality_helper
    (sourceCCMFiniteMatrix i) (sourceCCMFiniteMatrix_isHermitian i)
    (sourceCCMComplexRow S i)
  apply Complex.ext
  · simp [sourceCCMFiniteRayleigh]
  · simpa [sourceCCMFiniteRayleigh] using him.symm

theorem sourceCCMComplexRow_inner_residual_eq_zero
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    star (sourceCCMComplexRow S i) ⬝ᵥ
      sourceCCMFiniteResidual S i = 0 := by
  rw [sourceCCMFiniteResidual]
  simp only [ambientResidual, sourceCCMFiniteOperator,
    Matrix.mulVecLin_apply, dotProduct_sub, dotProduct_smul]
  rw [sourceCCMFiniteRayleigh_coe, sourceCCMComplexRow_unit]
  simp [smul_eq_mul]

#print axioms sourceCCMComplexRow_apply
#print axioms ccmFiniteSynthesis_sourceCCMComplexRow
#print axioms sourceCCMComplexRow_unit
#print axioms sourceCCMFiniteMatrix_isHermitian
#print axioms sourceCCMFiniteRayleigh_coe
#print axioms sourceCCMComplexRow_inner_residual_eq_zero

end Q3.RouteB.D0Pstar
