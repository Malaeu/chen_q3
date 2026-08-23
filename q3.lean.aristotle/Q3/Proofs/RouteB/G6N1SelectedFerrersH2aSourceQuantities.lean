import Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMSourceRow
import Q3.Proofs.RouteB.CCMComplexTrialReflectionContaminationFloor

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Matrix
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.2 — the selected Ferrers H2a source-quantities lock

Floor `H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK` of verdict
`7a090cd0`.

The source-object firewall binding H2A.1 to the exact theorem-generated
selected Ferrers shell, without proving any analytic rate.  Exposed here:

* the exact complex reflection permutation matrix on the literal CCM
  carrier, its action, Hermitian property, involution square, and its
  commutation with the selected complex source matrix (from the existing
  exact centrosymmetry theorem);
* the exact selected Rayleigh shift and residual, with residual
  orthogonality from the selected unit theorem and Hermitian Rayleigh
  reality — not from a chosen shift;
* the exact selected odd part and odd mass, and the physical
  representation: selected odd mass equals one quarter of the squared norm
  of the exact reflection defect (selected `kTrial` synthesis minus finite
  synthesis of the reflected selected coefficient row, same `PairIndex`);
* the public re-proof that finite synthesis of the selected row is the
  exact selected `kTrial` (the H2A.0 helper is private and may not be
  invoked through an interface substitution);
* the literal selected-source H2A.1 receiver, leaving exactly the four
  genuine quantitative inputs open: even-sector floor, odd-sector floor,
  `η < 1` with the residual bound, and `betaEff > 0`.

The two plants: unit norm on a shared carrier does not determine
reflection mass, and a wrong shift breaks residual orthogonality — a fixed
or fitted shift is not the source residual.

Deliberately NOT here: any sector-floor rate, odd-mass decay, residual
decay, cofinal effective floor, simple ground, Theorem 5.10, real zeros.

LEDGER:
  CLOSES: [SELECTED_FERRERS_COMPLEX_REFLECTION_OBJECT_LOCK,
           SELECTED_FERRERS_RAYLEIGH_RESIDUAL_OBJECT_LOCK,
           SELECTED_FERRERS_ODD_MASS_OBJECT_LOCK,
           SELECTED_FERRERS_ODD_MASS_PHYSICAL_REFLECTION_DEFECT_REPRESENTATION,
           SELECTED_FERRERS_H2A1_LITERAL_SOURCE_RECEIVER]
  OPENS:  []
-/

/-! ## The complex reflection permutation on the literal CCM carrier -/

/-- The exact complex reflection permutation matrix on the CCM carrier
`-N, ..., N`: the mode `j` is sent to its central reflection. -/
noncomputable def ccmComplexReflectionMatrix (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℂ :=
  fun j k => if k = ccmNegFinite N j then 1 else 0

/-- Action: the reflected vector reads the row at the reflected mode. -/
theorem ccmComplexReflectionMatrix_mulVec
    (N : ℕ) (x : CCMModeFinite N → ℂ) (j : CCMModeFinite N) :
    (ccmComplexReflectionMatrix N *ᵥ x) j = x (ccmNegFinite N j) := by
  classical
  simp only [ccmComplexReflectionMatrix, Matrix.mulVec, dotProduct,
    ite_mul, one_mul, zero_mul]
  exact Finset.sum_ite_eq' Finset.univ (ccmNegFinite N j) x |>.trans
    (by simp)

private theorem ccmNegFinite_invol (N : ℕ) (j : CCMModeFinite N) :
    ccmNegFinite N (ccmNegFinite N j) = j := by
  apply Fin.ext
  simp only [ccmNegFinite]
  omega

private theorem ccmNegFinite_eq_comm (N : ℕ) (j k : CCMModeFinite N) :
    k = ccmNegFinite N j ↔ j = ccmNegFinite N k := by
  constructor
  · intro h
    rw [h, ccmNegFinite_invol]
  · intro h
    rw [h, ccmNegFinite_invol]

/-- The reflection matrix is Hermitian. -/
theorem ccmComplexReflectionMatrix_isHermitian (N : ℕ) :
    (ccmComplexReflectionMatrix N).IsHermitian := by
  classical
  show (ccmComplexReflectionMatrix N)ᴴ = ccmComplexReflectionMatrix N
  ext j k
  simp only [Matrix.conjTranspose_apply, ccmComplexReflectionMatrix]
  by_cases h : j = ccmNegFinite N k
  · rw [if_pos h, if_pos ((ccmNegFinite_eq_comm N j k).mpr h)]
    simp
  · rw [if_neg h, if_neg (fun hc => h ((ccmNegFinite_eq_comm N j k).mp hc))]
    simp

/-- The reflection matrix squares to the identity. -/
theorem ccmComplexReflectionMatrix_sq (N : ℕ) :
    ccmComplexReflectionMatrix N * ccmComplexReflectionMatrix N = 1 := by
  classical
  ext j k
  simp only [Matrix.mul_apply, ccmComplexReflectionMatrix, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (ccmNegFinite N j)
    (fun l => if k = ccmNegFinite N l then (1:ℂ) else 0)]
  simp only [Finset.mem_univ, if_true, ccmNegFinite_invol]
  by_cases h : k = j
  · rw [if_pos h, Matrix.one_apply, if_pos h.symm]
  · rw [if_neg h, Matrix.one_apply, if_neg (fun hc => h hc.symm)]

/-- The selected complex source matrix commutes with the reflection: exact
centrosymmetry of the literal CCM matrix, complexified entrywise. -/
theorem sourceCCMFiniteMatrix_commutes_ccmComplexReflectionMatrix
    (i : PairIndex) :
    sourceCCMFiniteMatrix i * ccmComplexReflectionMatrix i.N =
      ccmComplexReflectionMatrix i.N * sourceCCMFiniteMatrix i := by
  classical
  have hcentro : ∀ a b : CCMModeFinite i.N,
      ccmWeilMatFinite i.m i.N (ccmNegFinite i.N a) (ccmNegFinite i.N b) =
        ccmWeilMatFinite i.m i.N a b := by
    intro a b
    change ccmWeilTauN1 i.m
        (ccmModeFinite i.N (ccmNegFinite i.N a))
        (ccmModeFinite i.N (ccmNegFinite i.N b)) =
      ccmWeilTauN1 i.m (ccmModeFinite i.N a) (ccmModeFinite i.N b)
    simp only [ccmModeFinite_neg, ccmWeilTauN1_neg_neg i.m i.hm]
  ext j k
  have hfun : (fun l => sourceCCMFiniteMatrix i j l *
      (if k = ccmNegFinite i.N l then (1:ℂ) else 0)) =
      (fun l => if l = ccmNegFinite i.N k then
        sourceCCMFiniteMatrix i j l else 0) := by
    funext l
    by_cases h : k = ccmNegFinite i.N l
    · rw [if_pos h, if_pos ((ccmNegFinite_eq_comm i.N l k).mp h), mul_one]
    · rw [if_neg h,
        if_neg (fun hc => h ((ccmNegFinite_eq_comm i.N l k).mpr hc)),
        mul_zero]
  have hL : (sourceCCMFiniteMatrix i * ccmComplexReflectionMatrix i.N) j k =
      sourceCCMFiniteMatrix i j (ccmNegFinite i.N k) := by
    simp only [Matrix.mul_apply, ccmComplexReflectionMatrix]
    rw [hfun]
    exact (Finset.sum_ite_eq' Finset.univ (ccmNegFinite i.N k) _).trans
      (by simp)
  have hR : (ccmComplexReflectionMatrix i.N * sourceCCMFiniteMatrix i) j k =
      sourceCCMFiniteMatrix i (ccmNegFinite i.N j) k := by
    simp only [Matrix.mul_apply, ccmComplexReflectionMatrix, ite_mul,
      one_mul, zero_mul]
    exact (Finset.sum_ite_eq' Finset.univ (ccmNegFinite i.N j) _).trans
      (by simp)
  rw [hL, hR]
  have h1 := hcentro (ccmNegFinite i.N j) k
  rw [ccmNegFinite_invol] at h1
  simp only [sourceCCMFiniteMatrix]
  exact_mod_cast h1

/-! ## The two mandatory plants -/

/-- **Plant 1.**  Unit norm on a shared carrier does not determine
reflection mass: with the reflection swapping coordinates `0` and `2` on
`Fin 3`, the unit row `[2/3, 1/3, 2/3]` has odd mass `0` while the unit row
`[1, 0, 0]` has odd mass `1/2`. -/
private theorem unit_norm_does_not_determine_reflection_mass_plant :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℂ) (q1 q2 : Fin 3 → ℂ),
      R.IsHermitian ∧ R * R = 1 ∧
      star q1 ⬝ᵥ q1 = 1 ∧ star q2 ⬝ᵥ q2 = 1 ∧
      (star ((2⁻¹ : ℂ) • (q1 - R *ᵥ q1)) ⬝ᵥ
        ((2⁻¹ : ℂ) • (q1 - R *ᵥ q1))).re = 0 ∧
      (star ((2⁻¹ : ℂ) • (q2 - R *ᵥ q2)) ⬝ᵥ
        ((2⁻¹ : ℂ) • (q2 - R *ᵥ q2))).re = 1/2 := by
  classical
  refine ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0],
    ![(2/3 : ℂ), (1/3 : ℂ), (2/3 : ℂ)], ![1, 0, 0], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  · have h : star (![(2/3 : ℂ), (1/3 : ℂ), (2/3 : ℂ)] : Fin 3 → ℂ) ⬝ᵥ
        ![(2/3 : ℂ), (1/3 : ℂ), (2/3 : ℂ)] = (((1:ℝ)) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_three, map_div₀, map_ofNat]
      push_cast
      ring
    rw [h]
    norm_num
  · have h : star (![(1:ℂ), 0, 0] : Fin 3 → ℂ) ⬝ᵥ
        (![(1:ℂ), 0, 0] : Fin 3 → ℂ) = (((1:ℝ)) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_three]
    rw [h]
    norm_num
  · have hRq : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ
        ![(2/3 : ℂ), (1/3 : ℂ), (2/3 : ℂ)] =
        ![(2/3 : ℂ), (1/3 : ℂ), (2/3 : ℂ)] := by
      funext l
      fin_cases l <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [hRq]
    simp
  · have hRq : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ
        (![(1:ℂ), 0, 0] : Fin 3 → ℂ) = ![0, 0, 1] := by
      funext l
      fin_cases l <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [hRq]
    have hvec : (2⁻¹ : ℂ) • ((![(1:ℂ), 0, 0] : Fin 3 → ℂ) -
        (![0, 0, 1] : Fin 3 → ℂ)) = ![(1/2 : ℂ), 0, -(1/2 : ℂ)] := by
      funext l
      fin_cases l <;> simp <;> norm_num
    rw [hvec]
    have hdot : star (![(1/2 : ℂ), 0, -(1/2 : ℂ)] : Fin 3 → ℂ) ⬝ᵥ
        ![(1/2 : ℂ), 0, -(1/2 : ℂ)] = (((1:ℝ)/2 : ℝ) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_three, map_div₀, map_ofNat, map_neg,
        map_one]
      push_cast
      ring
    rw [hdot, Complex.ofReal_re]

/-- **Plant 2.**  A wrong shift breaks residual orthogonality: for the
diagonal Hermitian `diag(0, 1)` on `Fin 2` and the unit coordinate vector,
the exact Rayleigh shift makes the residual orthogonal to the vector, while
the shift `1` leaves a nonzero parallel component.  A fixed or fitted shift
is not the source residual. -/
private theorem wrong_shift_breaks_residual_orthogonality_plant :
    ∃ (K : Matrix (Fin 2) (Fin 2) ℂ) (q : Fin 2 → ℂ),
      K.IsHermitian ∧ star q ⬝ᵥ q = 1 ∧
      star q ⬝ᵥ (K *ᵥ q -
        (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q) = 0 ∧
      ∃ c : ℂ, star q ⬝ᵥ (K *ᵥ q - c • q) ≠ 0 := by
  classical
  refine ⟨!![0, 0; 0, 1], ![1, 0], ?_, ?_, ?_, ⟨1, ?_⟩⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · simp [dotProduct, Fin.sum_univ_two]
  · have hKq : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        (![1, 0] : Fin 2 → ℂ) = ![0, 0] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hKq]
    simp [dotProduct, Fin.sum_univ_two]
  · have hKq : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        (![1, 0] : Fin 2 → ℂ) = ![0, 0] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hKq]
    simp [dotProduct, Fin.sum_univ_two]

/-! ## The exact selected Rayleigh, residual, odd part and odd mass -/

/-- The exact selected Rayleigh value of the selected row against the
selected complex source matrix, at the selected index. -/
noncomputable def selectedFerrersFiniteCCMRayleigh
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℝ :=
  (star (selectedFerrersFiniteCCMRow P k) ⬝ᵥ
    (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
      selectedFerrersFiniteCCMRow P k)).re

/-- The exact selected residual at the exact selected Rayleigh shift. -/
noncomputable def selectedFerrersFiniteCCMResidual
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
      selectedFerrersFiniteCCMRow P k -
    ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
      selectedFerrersFiniteCCMRow P k

/-- The exact reflection-odd part of the selected row. -/
noncomputable def selectedFerrersFiniteCCMOddPart
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  fun j =>
    (selectedFerrersFiniteCCMRow P k j -
      selectedFerrersFiniteCCMRow P k
        (ccmNegFinite ((selectedFerrersCofinalSourceData P).index k).N j)) / 2

/-- The exact selected odd mass. -/
noncomputable def selectedFerrersFiniteCCMOddMass
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℝ :=
  ∑ j, Complex.normSq (selectedFerrersFiniteCCMOddPart P k j)

/-- The exact physical reflection defect: the selected `kTrial` synthesis
minus the finite synthesis of the reflected selected coefficient row, on
the same selected `PairIndex`. -/
noncomputable def selectedFerrersFiniteCCMReflectionDefect
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : H_m ((selectedFerrersCofinalSourceData P).index k) :=
  (kTrial_m_N
      ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)
      ((selectedFerrersCofinalSourceData P).trialNonzero k) :
      H_m ((selectedFerrersCofinalSourceData P).index k)) -
    ccmFiniteSynthesis ((selectedFerrersCofinalSourceData P).index k)
      (fun j => selectedFerrersFiniteCCMRow P k
        (ccmNegFinite ((selectedFerrersCofinalSourceData P).index k).N j))

/-! ## The public synthesis crosswalk (H2A.0's helper is private) -/

private theorem selectedModeEquiv' (i : PairIndex) :
    Function.Injective (ccmModeFinite i.N) := by
  intro j k h
  apply Fin.ext
  simp only [ccmModeFinite] at h
  omega

private theorem selected_finite_sum_reindex'
    (i : PairIndex) (F : ℤ → H_m i) :
    (∑ j : CCMModeFinite i.N, F (ccmModeFinite i.N j)) =
      ∑ n ∈ modeSet i, F n := by
  classical
  let toMode : CCMModeFinite i.N → {n : ℤ // n ∈ modeSet i} :=
    fun j => ⟨ccmModeFinite i.N j, by
      simpa [modeSet] using ccmModeFinite_range i.N j⟩
  have hbij : Function.Bijective toMode := by
    constructor
    · intro j k hjk
      exact selectedModeEquiv' i (congrArg Subtype.val hjk)
    · intro n
      have hn : -(i.N : ℤ) ≤ n.1 ∧ n.1 ≤ i.N := by
        have hnmem : n.1 ∈ Finset.Icc (-(i.N : ℤ)) (i.N : ℤ) := by
          simpa only [modeSet] using n.2
        exact Finset.mem_Icc.mp hnmem
      have hnonneg : 0 ≤ n.1 + (i.N : ℤ) := by omega
      have hlt : n.1 + (i.N : ℤ) < (2 * i.N + 1 : ℕ) := by omega
      have hltNat : (n.1 + (i.N : ℤ)).toNat < 2 * i.N + 1 :=
        (Int.toNat_lt_of_ne_zero (by omega)).2 hlt
      refine ⟨⟨(n.1 + (i.N : ℤ)).toNat, hltNat⟩, ?_⟩
      apply Subtype.ext
      simp only [toMode, ccmModeFinite]
      rw [Int.toNat_of_nonneg hnonneg]
      omega
  let e := Equiv.ofBijective toMode hbij
  calc
    (∑ j : CCMModeFinite i.N, F (ccmModeFinite i.N j)) =
        ∑ n : {n : ℤ // n ∈ modeSet i}, F n.1 := by
      simpa [e, Equiv.ofBijective, toMode] using
        e.sum_comp (fun n : {n : ℤ // n ∈ modeSet i} => F n.1)
    _ = ∑ n ∈ modeSet i, F n := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (modeSet i) F)

/-- **Public synthesis crosswalk**: the finite synthesis of the selected
row is the exact selected normalized projected `kTrial`. -/
theorem ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial
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
      exact selected_finite_sum_reindex' i
        (fun n => inner ℂ (V_n_m i n) (kE : H_m i) • V_n_m i n)
    _ = (kE : H_m i) := hreconstruction.symm

/-! ## The physical odd-mass identity -/

private theorem norm_selected_synthesis_sq
    (i : PairIndex)
    (c : CCMModeFinite i.N → ℂ) :
    ‖ccmFiniteSynthesis i c‖ ^ 2 =
      ∑ j, Complex.normSq (c j) := by
  classical
  have horth :
      Orthonormal ℂ
        (fun j : CCMModeFinite i.N => V_n_m i (ccmModeFinite i.N j)) :=
    (V_n_m_orthonormal i).comp (ccmModeFinite i.N)
      (selectedModeEquiv' i)
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

/-- **The physical odd-mass identity**: the selected odd mass equals one
quarter of the squared norm of the exact physical reflection defect. -/
theorem selectedFerrersFiniteCCMOddMass_eq_quarter_norm_reflectionDefect_sq
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMOddMass P k =
      (1 / 4 : ℝ) *
        ‖selectedFerrersFiniteCCMReflectionDefect P k‖ ^ 2 := by
  classical
  have hdefect : selectedFerrersFiniteCCMReflectionDefect P k =
      ccmFiniteSynthesis ((selectedFerrersCofinalSourceData P).index k)
        (fun j => selectedFerrersFiniteCCMRow P k j -
          selectedFerrersFiniteCCMRow P k
            (ccmNegFinite
              ((selectedFerrersCofinalSourceData P).index k).N j)) := by
    unfold selectedFerrersFiniteCCMReflectionDefect
    rw [← ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial P k]
    change
      ccmFiniteSynthesis _ (selectedFerrersFiniteCCMRow P k) -
          ccmFiniteSynthesis _
            (fun j => selectedFerrersFiniteCCMRow P k
              (ccmNegFinite _ j)) =
        ccmFiniteSynthesis _
          (selectedFerrersFiniteCCMRow P k -
            fun j => selectedFerrersFiniteCCMRow P k (ccmNegFinite _ j))
    exact ((ccmFiniteSynthesis _).map_sub _ _).symm
  rw [hdefect, norm_selected_synthesis_sq]
  unfold selectedFerrersFiniteCCMOddMass selectedFerrersFiniteCCMOddPart
  simp_rw [Complex.normSq_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  norm_num [Complex.normSq]
  ring

/-! ## Residual orthogonality at the exact Rayleigh shift -/

private theorem hermitian_quadratic_real
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

/-- **Residual orthogonality**: at the exact selected Rayleigh shift, the
selected residual is orthogonal to the selected row.  This uses the
selected unit theorem and Hermitian Rayleigh reality — not a chosen
shift. -/
theorem selectedFerrersFiniteCCMResidual_orthogonal
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    star (selectedFerrersFiniteCCMRow P k) ⬝ᵥ
      selectedFerrersFiniteCCMResidual P k = 0 := by
  classical
  unfold selectedFerrersFiniteCCMResidual
  rw [dotProduct_sub, dotProduct_smul,
    selectedFerrersFiniteCCMRow_unit]
  rw [smul_eq_mul, mul_one]
  unfold selectedFerrersFiniteCCMRayleigh
  rw [hermitian_quadratic_real _ (sourceCCMFiniteMatrix_isHermitian _) _]
  exact sub_self _

/-! ## The literal selected-source H2A.1 receiver -/

/-- **The selected-source receiver.**  H2A.1 instantiated literally on the
selected Ferrers row, matrix, reflection, exact Rayleigh shift, exact odd
mass and exact residual.  The remaining hypotheses are exactly the four
genuine quantitative inputs: even-sector floor, odd-sector floor, `η < 1`
with the residual bound `ρ`, and `betaEff > 0`. -/
theorem selectedFerrersFiniteCCMComplementFloor_of_sectorFloors_oddMass_residual
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) (βp βm ρ betaEff : ℝ)
    (hη1 : selectedFerrersFiniteCCMOddMass P k < 1)
    (heven : ∀ x, ccmComplexReflectionMatrix
        ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = x →
      star ((2⁻¹ : ℂ) • (selectedFerrersFiniteCCMRow P k +
        ccmComplexReflectionMatrix
          ((selectedFerrersCofinalSourceData P).index k).N *ᵥ
          selectedFerrersFiniteCCMRow P k)) ⬝ᵥ x = 0 →
      βp * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ
          ((sourceCCMFiniteMatrix
              ((selectedFerrersCofinalSourceData P).index k) -
            ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
              (1 : Matrix _ _ ℂ)) *ᵥ x)).re)
    (hodd : ∀ x, ccmComplexReflectionMatrix
        ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = -x →
      βm * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ
          ((sourceCCMFiniteMatrix
              ((selectedFerrersCofinalSourceData P).index k) -
            ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
              (1 : Matrix _ _ ℂ)) *ᵥ x)).re)
    (hρ0 : 0 ≤ ρ)
    (hρ : (star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
      selectedFerrersFiniteCCMResidual P k).re ≤ ρ ^ 2)
    (hbeta : betaEff = min βp βm *
        (1 - selectedFerrersFiniteCCMOddMass P k) -
      (2 * Real.sqrt (selectedFerrersFiniteCCMOddMass P k) +
        selectedFerrersFiniteCCMOddMass P k) /
        Real.sqrt (1 - selectedFerrersFiniteCCMOddMass P k) * ρ)
    (hbeta0 : 0 < betaEff) :
    complexTrialComplementFloor
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
      (selectedFerrersFiniteCCMRow P k)
      ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ)
      betaEff := by
  classical
  set i : PairIndex := (selectedFerrersCofinalSourceData P).index k with hi
  -- odd-mass identity in the H2A.1 hypothesis shape
  have hoddvec : (2⁻¹ : ℂ) • (selectedFerrersFiniteCCMRow P k -
      ccmComplexReflectionMatrix i.N *ᵥ selectedFerrersFiniteCCMRow P k) =
      selectedFerrersFiniteCCMOddPart P k := by
    funext j
    rw [Pi.smul_apply, Pi.sub_apply, ccmComplexReflectionMatrix_mulVec]
    unfold selectedFerrersFiniteCCMOddPart
    rw [smul_eq_mul]
    ring
  have hdotsum : ∀ (x : CCMModeFinite i.N → ℂ),
      (star x ⬝ᵥ x).re = ∑ j, Complex.normSq (x j) := by
    intro x
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (starRingEnd ℂ) (x j) * x j =
      ((Complex.normSq (x j) : ℝ) : ℂ) by
        rw [mul_comm, Complex.mul_conj]]
    rw [Complex.ofReal_re]
  have hη_ident : selectedFerrersFiniteCCMOddMass P k =
      (star ((2⁻¹ : ℂ) • (selectedFerrersFiniteCCMRow P k -
        ccmComplexReflectionMatrix i.N *ᵥ selectedFerrersFiniteCCMRow P k)) ⬝ᵥ
      ((2⁻¹ : ℂ) • (selectedFerrersFiniteCCMRow P k -
        ccmComplexReflectionMatrix i.N *ᵥ
          selectedFerrersFiniteCCMRow P k))).re := by
    rw [hoddvec, hdotsum]
    rfl
  have hη0 : 0 ≤ selectedFerrersFiniteCCMOddMass P k :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hresid_eq : (sourceCCMFiniteMatrix i -
      ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
        (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *ᵥ
      selectedFerrersFiniteCCMRow P k =
      selectedFerrersFiniteCCMResidual P k := by
    unfold selectedFerrersFiniteCCMResidual
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  have hρ' : (star ((sourceCCMFiniteMatrix i -
      ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
        (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *ᵥ
      selectedFerrersFiniteCCMRow P k) ⬝ᵥ
      ((sourceCCMFiniteMatrix i -
      ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
        (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *ᵥ
      selectedFerrersFiniteCCMRow P k)).re ≤ ρ ^ 2 := by
    rw [hresid_eq]
    exact hρ
  exact complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual
    (sourceCCMFiniteMatrix i) (ccmComplexReflectionMatrix i.N)
    (selectedFerrersFiniteCCMRow P k)
    (selectedFerrersFiniteCCMRayleigh P k)
    (selectedFerrersFiniteCCMOddMass P k)
    βp βm ρ betaEff
    (sourceCCMFiniteMatrix_isHermitian i)
    (ccmComplexReflectionMatrix_isHermitian i.N)
    (ccmComplexReflectionMatrix_sq i.N)
    (sourceCCMFiniteMatrix_commutes_ccmComplexReflectionMatrix i)
    (selectedFerrersFiniteCCMRow_unit P k)
    hη_ident hη0 hη1 heven hodd hρ0 hρ' hbeta hbeta0

#print axioms ccmComplexReflectionMatrix_mulVec
#print axioms ccmComplexReflectionMatrix_isHermitian
#print axioms ccmComplexReflectionMatrix_sq
#print axioms sourceCCMFiniteMatrix_commutes_ccmComplexReflectionMatrix
#print axioms ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial
#print axioms selectedFerrersFiniteCCMOddMass_eq_quarter_norm_reflectionDefect_sq
#print axioms selectedFerrersFiniteCCMResidual_orthogonal
#print axioms selectedFerrersFiniteCCMComplementFloor_of_sectorFloors_oddMass_residual
#print axioms unit_norm_does_not_determine_reflection_mass_plant
#print axioms wrong_shift_breaks_residual_orthogonality_plant

end Q3.RouteB.D0Pstar

end
