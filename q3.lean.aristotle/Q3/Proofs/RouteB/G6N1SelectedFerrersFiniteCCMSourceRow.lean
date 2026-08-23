import Q3.Proofs.RouteB.G6N1SelectedFerrersCCMLemma73PreAnchorPort
import Q3.Proofs.RouteB.LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Filter Topology Matrix MeasureTheory
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a phase zero — the selected Ferrers finite CCM source row lock

Floor `H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_LOCK` of verdict
`4df7b14a`.

L73.8 lives on the selected-only Ferrers pre-anchor data and its
theorem-generated tail shift, while the existing literal CCM residual/floor
machinery is phrased for `ProlateCanonicalSourceData` on another interface.
Same index and unit norm alone do not identify a source row.  This file
closes the object-identity seam: it exposes, from the selected shell itself,

* the specialized shell `selectedFerrersCofinalSourceData` (exposed only
  because it is immediately consumed below — a shell-only alias transaction
  is rejected by the verdict);
* the exact finite coefficient row
  `q_{k,j} = c_n(i_k, prolateCombination(P_k), j)` stored by that shell;
* its exact application formula;
* its unit normalization `q* ⬝ q = 1` (through the finite synthesis and
  the exact `norm_kTrial_m_N` supplier); and
* the literal Proposition-59 crosswalk: the source-ordered raw transform of
  the row is exactly the shell's `rawFplus`.

The private plant exhibits two distinct unit rows on `Fin 2`: unit
normalization on a shared carrier does not identify the source row, so no
future proof may substitute an arbitrary unit vector for the selected row.

Deliberately NOT here: complement floor, penalty, residual spectral bounds,
Theorem 5.10, and the cofinal simple even ground supplier.

LEDGER:
  CLOSES: [SELECTED_FERRERS_COFINAL_SOURCE_SHELL_EXPOSED,
           SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_OBJECT_LOCK,
           SELECTED_FERRERS_FINITE_ROW_TO_RAW_TRANSFORM_CROSSWALK]
  OPENS:  []
-/

/-! ## The mandatory plant -/

/-- **The plant.**  Two distinct unit rows on the same finite carrier: unit
normalization does not identify the source row.  Any future proof that
replaces the selected row by an arbitrary unit vector merely because both
inhabit the same carrier with the same norm dies here. -/
private theorem unit_rows_do_not_identify_source_row_plant :
    ∃ q1 q2 : Fin 2 → ℂ,
      star q1 ⬝ᵥ q1 = 1 ∧ star q2 ⬝ᵥ q2 = 1 ∧ q1 ≠ q2 := by
  refine ⟨![1, 0], ![0, 1], ?_, ?_, ?_⟩
  · simp [dotProduct, Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two]
  · intro h
    have h0 := congrFun h 0
    simp at h0

/-! ## The selected shell, exposed for immediate consumption -/

/-- The selected Ferrers cofinal source shell: the existing generic
constructor applied to the exact selected pre-anchor data and a conditional
L73.8 port.  Exposed here only because the finite CCM row below consumes
it; a shell-only alias file is forbidden by the verdict. -/
noncomputable def selectedFerrersCofinalSourceData
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData) :
    SelectedProlateCofinalSourceData :=
  selectedProlateCofinalSourceDataOfPreAnchorPort
    selectedFerrersPreAnchorData P

/-! ## The exact finite CCM source row -/

/-- **The selected finite CCM source row**: the exact coefficient row
`q_{k,j} = c_n(i_k, prolateCombination(P_k), j)` of the normalized projected
trial stored by the selected shell, on the literal CCM carrier
`-N, ..., N`. -/
noncomputable def selectedFerrersFiniteCCMRow
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  fun j =>
    c_n ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)
      ((selectedFerrersCofinalSourceData P).trialNonzero k)
      (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j)

/-- Exact application formula of the selected row. -/
theorem selectedFerrersFiniteCCMRow_apply
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ)
    (j : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) :
    selectedFerrersFiniteCCMRow P k j =
      c_n ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)
        ((selectedFerrersCofinalSourceData P).trialNonzero k)
        (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j) :=
  rfl

/-! ## Private carrier reindex and synthesis identities (upstream copies are
private in their file and cannot be imported) -/

private def selectedModeEquiv (i : PairIndex) :
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

private theorem selected_finite_sum_reindex
    (i : PairIndex) (F : ℤ → H_m i) :
    (∑ j : CCMModeFinite i.N, F (ccmModeFinite i.N j)) =
      ∑ n ∈ modeSet i, F n := by
  classical
  let e := selectedModeEquiv i
  calc
    (∑ j : CCMModeFinite i.N, F (ccmModeFinite i.N j)) =
        ∑ n : {n : ℤ // n ∈ modeSet i}, F n.1 := by
      simpa [e, selectedModeEquiv] using
        e.sum_comp (fun n : {n : ℤ // n ∈ modeSet i} => F n.1)
    _ = ∑ n ∈ modeSet i, F n := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (modeSet i) F)

private theorem selected_finite_synthesis_inner_identity
    (i : PairIndex)
    (q : CCMModeFinite i.N → ℂ)
    (f : H_m i) :
    inner ℂ (ccmFiniteSynthesis i q) f =
      star q ⬝ᵥ
        (fun j => inner ℂ (V_n_m i (ccmModeFinite i.N j)) f) := by
  classical
  simp [ccmFiniteSynthesis, sum_inner, inner_smul_left, dotProduct]

/-- The synthesis of the selected row reconstructs the normalized projected
trial of the selected shell. -/
private theorem ccmFiniteSynthesis_selectedFerrersFiniteCCMRow
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    ccmFiniteSynthesis ((selectedFerrersCofinalSourceData P).index k)
      (selectedFerrersFiniteCCMRow P k) =
      (kTrial_m_N
        ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)
        ((selectedFerrersCofinalSourceData P).trialNonzero k) :
        H_m ((selectedFerrersCofinalSourceData P).index k)) := by
  classical
  set i : PairIndex := (selectedFerrersCofinalSourceData P).index k with hi
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  let kE : E_m_N i :=
    kTrial_m_N i
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)
      ((selectedFerrersCofinalSourceData P).trialNonzero k)
  have hprojection : P_m_N i (kE : H_m i) = kE := by
    rw [P_m_N]
    exact Submodule.orthogonalProjection_mem_subspace_eq_self kE
  have hreconstruction :=
    coe_P_m_N_apply_eq_sum_inner_V_n_m_smul i (kE : H_m i)
  rw [hprojection] at hreconstruction
  calc
    ccmFiniteSynthesis i (selectedFerrersFiniteCCMRow P k) =
        ∑ j : CCMModeFinite i.N,
          inner ℂ (V_n_m i (ccmModeFinite i.N j)) (kE : H_m i) •
            V_n_m i (ccmModeFinite i.N j) := by
      simp only [ccmFiniteSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
        selectedFerrersFiniteCCMRow_apply, c_n, kE]
      rfl
    _ = ∑ n ∈ modeSet i,
          inner ℂ (V_n_m i n) (kE : H_m i) • V_n_m i n := by
      exact selected_finite_sum_reindex i
        (fun n => inner ℂ (V_n_m i n) (kE : H_m i) • V_n_m i n)
    _ = (kE : H_m i) := hreconstruction.symm

/-! ## Unit normalization -/

/-- **The unit row theorem**: `q_k^* ⬝ q_k = 1` — the selected row is the
coefficient row of a unit vector, via the exact `norm_kTrial_m_N`. -/
theorem selectedFerrersFiniteCCMRow_unit
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    star (selectedFerrersFiniteCCMRow P k) ⬝ᵥ
      selectedFerrersFiniteCCMRow P k = 1 := by
  classical
  set i : PairIndex := (selectedFerrersCofinalSourceData P).index k with hi
  set x : H_m i :=
    (kTrial_m_N i
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)
      ((selectedFerrersCofinalSourceData P).trialNonzero k) : H_m i)
    with hx
  have hsynthesis :
      ccmFiniteSynthesis i (selectedFerrersFiniteCCMRow P k) = x :=
    ccmFiniteSynthesis_selectedFerrersFiniteCCMRow P k
  have hinner :=
    selected_finite_synthesis_inner_identity i
      (selectedFerrersFiniteCCMRow P k) x
  have hcoeff :
      (fun j : CCMModeFinite i.N =>
        inner ℂ (V_n_m i (ccmModeFinite i.N j)) x) =
        selectedFerrersFiniteCCMRow P k := by
    funext j
    rw [selectedFerrersFiniteCCMRow_apply, c_n]
  rw [hcoeff, hsynthesis] at hinner
  calc
    star (selectedFerrersFiniteCCMRow P k) ⬝ᵥ
        selectedFerrersFiniteCCMRow P k =
        inner ℂ x x := hinner.symm
    _ = (‖x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K x
    _ = 1 := by
      rw [show ‖x‖ = 1 by
        exact norm_kTrial_m_N i
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)]
      norm_num

/-! ## The literal Proposition-59 raw-transform crosswalk -/

/-- **The crosswalk**: the source-ordered Proposition-59 raw transform of
the selected row is exactly the shell's `rawFplus`.  The two coefficient
transports agree on the shared summation set `-N, ..., N`. -/
theorem sourceOrderedCCMRawTransform_selectedFerrersFiniteCCMRow_eq_rawFplus
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) (z : ℂ) :
    sourceOrderedCCMRawTransform
      (logLength ((selectedFerrersCofinalSourceData P).index k))
      ((selectedFerrersCofinalSourceData P).index k).N
      (selectedFerrersFiniteCCMRow P k) z =
      (selectedFerrersCofinalSourceData P).rawFplus k z := by
  classical
  set i : PairIndex := (selectedFerrersCofinalSourceData P).index k with hi
  rw [SelectedProlateCofinalSourceData.rawFplus,
    preAnchorRawTransformCoordinate, sourceOrderedCCMRawTransform]
  unfold proposition59RawTransform
  congr 1
  apply Finset.sum_congr
  · rfl
  · intro n hn
    congr 1
    have hnmem : n ∈ Finset.Icc (-(i.N : ℤ)) (i.N : ℤ) := by
      simpa only [modeSet] using hn
    rw [sourceOrderedCCMCoefficient, dif_pos hnmem,
      selectedFerrersFiniteCCMRow_apply]
    congr 1
    have happ := congrArg Subtype.val
      ((ccmModeFiniteEquivIcc i.N).apply_symm_apply ⟨n, hnmem⟩)
    exact happ

#print axioms selectedFerrersFiniteCCMRow_apply
#print axioms selectedFerrersFiniteCCMRow_unit
#print axioms sourceOrderedCCMRawTransform_selectedFerrersFiniteCCMRow_eq_rawFplus

end Q3.RouteB.D0Pstar

end
