import Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
import Q3.Proofs.RouteB.D0PstarCCMFiniteRieszOperator

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Matrix MeasureTheory
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.4.0 — the selected Ferrers finite CCM residual variance lock

Floor `H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK` of verdict
`bba4c35e`.

The mandatory object lock before any cofinal residual rate: the exact
selected finite CCM Rayleigh residual is exposed as **one source-faithful
nonnegative scalar** — the residual energy — with three exact identities:

* it is the squared Euclidean norm of the literal residual row;
* it is the second moment minus the squared Rayleigh value (the variance
  identity `‖Kq − aq‖² = ‖Kq‖² − a²` in the unit state);
* it is the squared `E_m_N` norm of the finite Riesz defect
  `Riesz(x) − a·x` on the same selected `kTrial`.

The plant records the decisive kill: an exactly reflection-even unit row
can have zero odd mass and residual energy two, so no odd-mass decay and
no exact parity can imply a residual rate.

Deliberately NOT here: any residual or second-moment rate, sector floors,
an ambient associated operator `A_m` or a compression claim, simple
ground, Theorem 5.10.

LEDGER:
  CLOSES: [SELECTED_FERRERS_FINITE_CCM_RESIDUAL_ENERGY_OBJECT_LOCK,
           SELECTED_FERRERS_FINITE_CCM_RESIDUAL_VARIANCE_IDENTITY,
           SELECTED_FERRERS_FINITE_RIESZ_RESIDUAL_CROSSWALK]
  OPENS:  []
-/

/-! ## The mandatory plant -/

/-- **The plant.**  An exactly even unit row can have a nonzero Rayleigh
residual: on `Fin 3` with the reflection `J` swapping coordinates `0` and
`2`, the unit row `q = (0,1,0)` is exactly `J`-even (odd mass zero) under
the Hermitian reflection-commuting matrix `K = [[0,1,0],[1,0,1],[0,1,0]]`,
its exact Rayleigh value is zero, yet its Rayleigh residual is `(1,0,1)`
with residual energy two.  This kills `oddMass = 0 → residual = 0` and
therefore every attempt to derive H2A.4 from H2A.3 alone. -/
private theorem exact_even_unit_row_can_have_nonzero_rayleigh_residual_plant :
    ∃ (K J : Matrix (Fin 3) (Fin 3) ℂ) (q : Fin 3 → ℂ),
      K.IsHermitian ∧ J.IsHermitian ∧ J * J = 1 ∧ K * J = J * K ∧
      star q ⬝ᵥ q = 1 ∧ J *ᵥ q = q ∧
      (star ((2⁻¹ : ℂ) • (q - J *ᵥ q)) ⬝ᵥ
        ((2⁻¹ : ℂ) • (q - J *ᵥ q))).re = 0 ∧
      (star q ⬝ᵥ (K *ᵥ q)).re = 0 ∧
      K *ᵥ q - (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q =
        ![1, 0, 1] ∧
      (star (![1, 0, 1] : Fin 3 → ℂ) ⬝ᵥ (![1, 0, 1] : Fin 3 → ℂ)).re = 2 := by
  classical
  refine ⟨!![0, 1, 0; 1, 0, 1; 0, 1, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    ![0, 1, 0], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [dotProduct, Fin.sum_univ_three]
  · funext l
    fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · have hJq : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ
        (![0, 1, 0] : Fin 3 → ℂ) = ![0, 1, 0] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [hJq]
    simp
  · have hKq : (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ
        (![0, 1, 0] : Fin 3 → ℂ) = ![1, 0, 1] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [hKq]
    simp [dotProduct, Fin.sum_univ_three]
  · have hKq : (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ
        (![0, 1, 0] : Fin 3 → ℂ) = ![1, 0, 1] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hRay : (star (![0, 1, 0] : Fin 3 → ℂ) ⬝ᵥ
        (![(1:ℂ), 0, 1] : Fin 3 → ℂ)).re = 0 := by
      simp [dotProduct, Fin.sum_univ_three]
    rw [hKq, hRay]
    funext l
    fin_cases l <;> simp
  · have h : star (![1, 0, 1] : Fin 3 → ℂ) ⬝ᵥ
        (![1, 0, 1] : Fin 3 → ℂ) = (((2:ℝ)) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      norm_num
    rw [h, Complex.ofReal_re]

/-! ## Local dot-product groundwork (upstream helpers are private) -/

private lemma dot_star_self_re {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (star v ⬝ᵥ v).re = ∑ j, Complex.normSq (v j) := by
  classical
  have h : star v ⬝ᵥ v = ((∑ j, Complex.normSq (v j) : ℝ) : ℂ) := by
    unfold dotProduct
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.star_apply, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [h, Complex.ofReal_re]

private lemma dot_conj_swap {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    star u ⬝ᵥ v = (starRingEnd ℂ) (star v ⬝ᵥ u) := by
  classical
  unfold dotProduct
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  show star (u j) * v j = (starRingEnd ℂ) (star (v j) * u j)
  rw [map_mul]
  show star (u j) * v j =
    (starRingEnd ℂ) ((starRingEnd ℂ) (v j)) * (starRingEnd ℂ) (u j)
  rw [Complex.conj_conj]
  show (starRingEnd ℂ) (u j) * v j = v j * (starRingEnd ℂ) (u j)
  ring

private theorem hermitian_quadratic_real'
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (x : ι → ℂ) :
    ((star x ⬝ᵥ (A *ᵥ x)).re : ℂ) = star x ⬝ᵥ (A *ᵥ x) := by
  have hconj : (starRingEnd ℂ) (star x ⬝ᵥ (A *ᵥ x)) =
      star x ⬝ᵥ (A *ᵥ x) := by
    calc (starRingEnd ℂ) (star x ⬝ᵥ (A *ᵥ x))
        = star (star x ⬝ᵥ (A *ᵥ x)) := rfl
      _ = star (A *ᵥ x) ⬝ᵥ star (star x) := by
          simp [dotProduct, map_sum, mul_comm]
      _ = star (A *ᵥ x) ⬝ᵥ x := by rw [star_star]
      _ = star x ⬝ᵥ (A *ᵥ x) := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hA.eq]
  exact (Complex.conj_eq_iff_re.mp hconj)

private theorem norm_selected_synthesis_sq'
    (i : PairIndex)
    (c : CCMModeFinite i.N → ℂ) :
    ‖ccmFiniteSynthesis i c‖ ^ 2 =
      ∑ j, Complex.normSq (c j) := by
  classical
  have horth :
      Orthonormal ℂ
        (fun j : CCMModeFinite i.N => V_n_m i (ccmModeFinite i.N j)) :=
    (V_n_m_orthonormal i).comp (ccmModeFinite i.N)
      (ccmModeFinite_injective i.N)
  have hinner :
      inner ℂ (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i c) =
        ((∑ j, Complex.normSq (c j) : ℝ) : ℂ) := by
    unfold ccmFiniteSynthesis
    simpa [Complex.normSq_eq_conj_mul_self] using
      horth.inner_sum c c Finset.univ
  calc
    ‖ccmFiniteSynthesis i c‖ ^ 2 =
        (inner ℂ (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i c)).re :=
      by simpa using
        (norm_sq_eq_re_inner (𝕜 := ℂ) (ccmFiniteSynthesis i c))
    _ = ∑ j, Complex.normSq (c j) := by rw [hinner]; simp

/-! ## Local re-proof of the private Riesz carrier stack

The upstream `D0PstarCCMFiniteRieszOperator` keeps its orthonormal basis,
its Euclidean conjugated operator and their application lemmas private.
The definitions below are literal copies; the `rfl` bridges identify them
definitionally with the public `ccmFiniteSynthesisEquiv` and
`sourceCCMFiniteRieszOperator`, so no interface is substituted. -/

private def localModeEquivalence
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

private noncomputable def localModeOrthonormalBasis
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
  exact b0.reindex (localModeEquivalence i).symm

private theorem coe_localModeOrthonormalBasis_apply
    (i : PairIndex) (j : CCMModeFinite i.N) :
    ((localModeOrthonormalBasis i j : E_m_N i) : H_m i) =
      V_n_m i (ccmModeFinite i.N j) := by
  classical
  simp only [localModeOrthonormalBasis, OrthonormalBasis.reindex_apply,
    Equiv.symm_symm, OrthonormalBasis.map_apply,
    LinearIsometryEquiv.coe_ofEq_apply, OrthonormalBasis.span_apply]
  change V_n_m i (ccmModeFinite i.N j) = V_n_m i (ccmModeFinite i.N j)
  rfl

-- Definitional bridge: the public synthesis equivalence is the local
-- basis representation.  The kernel checks this through the private
-- upstream definition — no axiom, no substitution.
set_option maxHeartbeats 40000000 in
private theorem ccmFiniteSynthesisEquiv_eq_localBasis (i : PairIndex) :
    ccmFiniteSynthesisEquiv i = (localModeOrthonormalBasis i).repr.symm :=
  rfl

private theorem localSynthesisEquiv_apply_toLp
    (i : PairIndex)
    (q : CCMModeFinite i.N → ℂ) :
    ((ccmFiniteSynthesisEquiv i (WithLp.toLp 2 q) : E_m_N i) : H_m i) =
      ccmFiniteSynthesis i q := by
  classical
  rw [ccmFiniteSynthesisEquiv_eq_localBasis]
  rw [← (localModeOrthonormalBasis i).sum_repr_symm (WithLp.toLp 2 q)]
  simp only [coe_localModeOrthonormalBasis_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower]
  rfl

private noncomputable def localOperatorEuclidean
    (i : PairIndex) :
    Module.End ℂ (EuclideanSpace ℂ (CCMModeFinite i.N)) :=
  (WithLp.linearEquiv 2 ℂ
      (CCMModeFinite i.N → ℂ)).symm.conj
    (sourceCCMFiniteOperator i)

private theorem localOperatorEuclidean_apply_toLp
    (i : PairIndex)
    (q : CCMModeFinite i.N → ℂ) :
    localOperatorEuclidean i (WithLp.toLp 2 q) =
      WithLp.toLp 2 (sourceCCMFiniteOperator i q) := by
  simp [localOperatorEuclidean, LinearEquiv.conj_apply_apply]

/-- Definitional bridge: the public finite Riesz operator is the synthesis
conjugation of the local Euclidean operator. -/
private theorem sourceCCMFiniteRieszOperator_eq_localConj (i : PairIndex) :
    sourceCCMFiniteRieszOperator i =
      (ccmFiniteSynthesisEquiv i).toLinearEquiv.conj
        (localOperatorEuclidean i) :=
  rfl

/-! ## Transport of the selected row through the synthesis equivalence -/

private theorem synthesisEquiv_selectedRow_eq_kTrial
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    ccmFiniteSynthesisEquiv ((selectedFerrersCofinalSourceData P).index k)
      (WithLp.toLp 2 (selectedFerrersFiniteCCMRow P k)) =
      kTrial_m_N
        ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)
        ((selectedFerrersCofinalSourceData P).trialNonzero k) := by
  apply Subtype.ext
  exact (localSynthesisEquiv_apply_toLp _ _).trans
    (ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial P k)

set_option maxHeartbeats 6400000 in
private theorem riesz_conj_apply
    (i : PairIndex)
    (y : EuclideanSpace ℂ (CCMModeFinite i.N)) :
    sourceCCMFiniteRieszOperator i (ccmFiniteSynthesisEquiv i y) =
      ccmFiniteSynthesisEquiv i (localOperatorEuclidean i y) := by
  rw [sourceCCMFiniteRieszOperator_eq_localConj]
  rw [LinearEquiv.conj_apply_apply]
  show ccmFiniteSynthesisEquiv i
      (localOperatorEuclidean i
        ((ccmFiniteSynthesisEquiv i).symm (ccmFiniteSynthesisEquiv i y))) =
    ccmFiniteSynthesisEquiv i (localOperatorEuclidean i y)
  rw [LinearIsometryEquiv.symm_apply_apply]

set_option maxHeartbeats 6400000 in
private theorem riesz_apply_selected
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    (sourceCCMFiniteRieszOperator
        ((selectedFerrersCofinalSourceData P).index k)
        (kTrial_m_N
          ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)) :
        H_m ((selectedFerrersCofinalSourceData P).index k)) =
      ccmFiniteSynthesis ((selectedFerrersCofinalSourceData P).index k)
        (sourceCCMFiniteOperator
          ((selectedFerrersCofinalSourceData P).index k)
          (selectedFerrersFiniteCCMRow P k)) := by
  classical
  rw [← synthesisEquiv_selectedRow_eq_kTrial P k]
  rw [riesz_conj_apply]
  rw [localOperatorEuclidean_apply_toLp]
  exact localSynthesisEquiv_apply_toLp _ _

/-! ## The public residual energy and second moment -/

/-- **The exact selected residual energy**: the real part of the complex
self-dot of the literal selected Rayleigh residual.  One source-faithful
nonnegative scalar — the variance of the source CCM matrix in the selected
unit state. -/
noncomputable def selectedFerrersFiniteCCMResidualEnergy
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℝ :=
  (star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
    selectedFerrersFiniteCCMResidual P k).re

/-- **The exact selected second moment**: the squared Euclidean size of the
matrix action on the selected row. -/
noncomputable def selectedFerrersFiniteCCMSecondMoment
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℝ :=
  (star (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
      selectedFerrersFiniteCCMRow P k) ⬝ᵥ
    (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
      selectedFerrersFiniteCCMRow P k)).re

/-- The residual energy is nonnegative. -/
theorem selectedFerrersFiniteCCMResidualEnergy_nonneg
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    0 ≤ selectedFerrersFiniteCCMResidualEnergy P k := by
  unfold selectedFerrersFiniteCCMResidualEnergy
  rw [dot_star_self_re]
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- The residual energy is the squared Euclidean norm of the literal
selected residual row. -/
theorem selectedFerrersFiniteCCMResidualEnergy_eq_norm_sq
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMResidualEnergy P k =
      ‖WithLp.toLp 2 (selectedFerrersFiniteCCMResidual P k)‖ ^ 2 := by
  unfold selectedFerrersFiniteCCMResidualEnergy
  rw [dot_star_self_re]
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.normSq_eq_norm_sq]

/-- **The variance identity**: the residual energy is the second moment
minus the squared Rayleigh value.  This is `‖Kq − aq‖² = ‖Kq‖² − a²` for
the unit selected row at the exact selected Rayleigh shift. -/
theorem selectedFerrersFiniteCCMResidualEnergy_eq_secondMoment_sub_rayleigh_sq
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMResidualEnergy P k =
      selectedFerrersFiniteCCMSecondMoment P k -
        (selectedFerrersFiniteCCMRayleigh P k) ^ 2 := by
  classical
  set q : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
    selectedFerrersFiniteCCMRow P k with hq
  set w : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
    sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
      selectedFerrersFiniteCCMRow P k with hw
  set a : ℝ := selectedFerrersFiniteCCMRayleigh P k with ha
  have hqw : star q ⬝ᵥ w = ((a : ℝ) : ℂ) :=
    (hermitian_quadratic_real'
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
      (sourceCCMFiniteMatrix_isHermitian _)
      (selectedFerrersFiniteCCMRow P k)).symm
  have hwq : star w ⬝ᵥ q = ((a : ℝ) : ℂ) := by
    rw [dot_conj_swap, hqw]
    exact Complex.conj_ofReal a
  have hres : selectedFerrersFiniteCCMResidual P k =
      w - ((a : ℝ) : ℂ) • q := rfl
  have horth : star q ⬝ᵥ selectedFerrersFiniteCCMResidual P k = 0 :=
    selectedFerrersFiniteCCMResidual_orthogonal P k
  have hdot : star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
      selectedFerrersFiniteCCMResidual P k =
      star w ⬝ᵥ w - (((a ^ 2 : ℝ)) : ℂ) := by
    calc star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
        selectedFerrersFiniteCCMResidual P k
        = star (w - ((a : ℝ) : ℂ) • q) ⬝ᵥ
            selectedFerrersFiniteCCMResidual P k := by rw [← hres]
      _ = star w ⬝ᵥ selectedFerrersFiniteCCMResidual P k -
          (starRingEnd ℂ) ((a : ℝ) : ℂ) *
            (star q ⬝ᵥ selectedFerrersFiniteCCMResidual P k) := by
          rw [star_sub, sub_dotProduct, star_smul, smul_dotProduct,
            smul_eq_mul]
          rfl
      _ = star w ⬝ᵥ selectedFerrersFiniteCCMResidual P k := by
          rw [horth, mul_zero, sub_zero]
      _ = star w ⬝ᵥ w - ((a : ℝ) : ℂ) * (star w ⬝ᵥ q) := by
          rw [hres, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      _ = star w ⬝ᵥ w - (((a ^ 2 : ℝ)) : ℂ) := by
          rw [hwq]
          push_cast
          ring
  unfold selectedFerrersFiniteCCMResidualEnergy
    selectedFerrersFiniteCCMSecondMoment
  rw [hdot]
  rw [Complex.sub_re, Complex.ofReal_re]

/-! ## The exact finite Riesz crosswalk -/

/-- **The Riesz crosswalk**: the finite synthesis of the literal selected
residual row is exactly the finite Riesz defect on the same selected
`kTrial`, coerced to the window Hilbert space.  No ambient operator and no
compression claim — this is finite-carrier semantics only. -/
theorem ccmFiniteSynthesis_selectedFerrersFiniteCCMResidual_eq_finiteRieszDefect
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    ccmFiniteSynthesis ((selectedFerrersCofinalSourceData P).index k)
      (selectedFerrersFiniteCCMResidual P k) =
      ((sourceCCMFiniteRieszOperator
          ((selectedFerrersCofinalSourceData P).index k)
          (kTrial_m_N
            ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k)) -
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
          kTrial_m_N
            ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k) :
          E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
        H_m ((selectedFerrersCofinalSourceData P).index k)) := by
  classical
  have hres : selectedFerrersFiniteCCMResidual P k =
      sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
          selectedFerrersFiniteCCMRow P k -
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
          selectedFerrersFiniteCCMRow P k := rfl
  have hop : sourceCCMFiniteMatrix
      ((selectedFerrersCofinalSourceData P).index k) *ᵥ
      selectedFerrersFiniteCCMRow P k =
      sourceCCMFiniteOperator ((selectedFerrersCofinalSourceData P).index k)
        (selectedFerrersFiniteCCMRow P k) := rfl
  rw [hres, hop, map_sub, map_smul]
  rw [ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial P k]
  rw [← riesz_apply_selected P k]
  rw [Submodule.coe_sub, Submodule.coe_smul]

/-- The residual energy is the squared `E_m_N` norm of the exact finite
Riesz defect on the same selected `kTrial`. -/
theorem selectedFerrersFiniteCCMResidualEnergy_eq_finiteRieszDefect_norm_sq
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMResidualEnergy P k =
      ‖(sourceCCMFiniteRieszOperator
          ((selectedFerrersCofinalSourceData P).index k)
          (kTrial_m_N
            ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k)) -
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
          kTrial_m_N
            ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k) :
          E_m_N ((selectedFerrersCofinalSourceData P).index k))‖ ^ 2 := by
  classical
  have hcoe : ‖(sourceCCMFiniteRieszOperator
        ((selectedFerrersCofinalSourceData P).index k)
        (kTrial_m_N
          ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)) -
      ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
        kTrial_m_N
          ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) :
        E_m_N ((selectedFerrersCofinalSourceData P).index k))‖ =
      ‖ccmFiniteSynthesis ((selectedFerrersCofinalSourceData P).index k)
        (selectedFerrersFiniteCCMResidual P k)‖ := by
    rw [ccmFiniteSynthesis_selectedFerrersFiniteCCMResidual_eq_finiteRieszDefect P k]
    exact (Submodule.norm_coe _).symm
  rw [hcoe, norm_selected_synthesis_sq']
  unfold selectedFerrersFiniteCCMResidualEnergy
  rw [dot_star_self_re]

#print axioms selectedFerrersFiniteCCMResidualEnergy_nonneg
#print axioms selectedFerrersFiniteCCMResidualEnergy_eq_norm_sq
#print axioms selectedFerrersFiniteCCMResidualEnergy_eq_secondMoment_sub_rayleigh_sq
#print axioms ccmFiniteSynthesis_selectedFerrersFiniteCCMResidual_eq_finiteRieszDefect
#print axioms selectedFerrersFiniteCCMResidualEnergy_eq_finiteRieszDefect_norm_sq
#print axioms exact_even_unit_row_can_have_nonzero_rayleigh_residual_plant

end Q3.RouteB.D0Pstar

end
