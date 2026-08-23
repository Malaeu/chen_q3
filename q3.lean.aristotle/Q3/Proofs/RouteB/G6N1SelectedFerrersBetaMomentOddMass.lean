import Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
import Q3.Proofs.RouteB.CCMFiniteWeilShiftedRankOne

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

open Complex Matrix Filter
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.4.1b.3a — the selected Ferrers beta-moment source lock

Floor `H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND` of
verdict `af4ca219`.

The first structured moment inside the source commutator becomes a
precise finite theorem on the exact selected row:

* the **beta moment** `β_k ⬝ q_k` is exactly the center coordinate of the
  source matrix acting on the mode-weighted selected row — a genuine
  source-action functional, NOT the all-ones moment, NOT the zero-mode
  anchor, NOT a Mellin value (the two plants record both kills);
* the source beta vector is reflection-odd, so the beta moment sees only
  the exact selected odd part;
* finite complex Cauchy–Schwarz then bounds its squared modulus by the
  explicit source beta-energy times the already-rate-controlled odd mass.

This theorem does not prove the weighted residual source rate and does
not control the beta energy; both remain open (`H2A_4_1B_3B`).

Deliberately NOT here: beta-energy growth, commutator defect rate,
prime/archimedean analysis, sector floors, simple ground, Theorem 5.10.

LEDGER:
  CLOSES: [SELECTED_FERRERS_BETA_MOMENT_SOURCE_CROSSWALK,
           SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND]
  OPENS:  []
-/

/-! ## The two mandatory plants -/

/-- **Plant 1.**  The all-ones moment does not determine the beta moment:
on `Fin 3` with `beta = (-1,0,1)`, the rows `(1,0,0)` and `(0,1,0)` have
the same all-ones moment `1` but beta moments `-1` and `0`.  Substituting
`ccmEtaFinite ⬝ᵥ q` (or any unweighted transform value) for the beta
moment is a C04/C10 object substitution. -/
private theorem allOnesMoment_does_not_determine_betaMoment_plant :
    ∃ (eta beta q1 q2 : Fin 3 → ℂ),
      eta = ![1, 1, 1] ∧ beta = ![-1, 0, 1] ∧
      eta ⬝ᵥ q1 = 1 ∧ eta ⬝ᵥ q2 = 1 ∧
      beta ⬝ᵥ q1 = -1 ∧ beta ⬝ᵥ q2 = 0 := by
  refine ⟨![1, 1, 1], ![-1, 0, 1], ![1, 0, 0], ![0, 1, 0],
    rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [dotProduct, Fin.sum_univ_three]

/-- **Plant 2.**  Beta oddness is load-bearing: with the reflection
swapping coordinates `0` and `2`, the unit row `(0,1,0)` is exactly even
(odd mass zero), yet the arbitrary even vector `beta = (0,1,0)` has beta
moment `1`.  The odd-mass bound holds only for the exact source beta
vector with its proved reflection-odd law. -/
private theorem beta_oddness_is_load_bearing_plant :
    ∃ (J : Matrix (Fin 3) (Fin 3) ℂ) (q beta : Fin 3 → ℂ),
      J.IsHermitian ∧ J * J = 1 ∧ J *ᵥ q = q ∧
      (star ((2⁻¹ : ℂ) • (q - J *ᵥ q)) ⬝ᵥ
        ((2⁻¹ : ℂ) • (q - J *ᵥ q))).re = 0 ∧
      beta ⬝ᵥ q = 1 := by
  classical
  refine ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], ![0, 1, 0], ![0, 1, 0],
    ?_, ?_, ?_, ?_, ?_⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  · funext l
    fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · have hJq : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ
        (![0, 1, 0] : Fin 3 → ℂ) = ![0, 1, 0] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [hJq]
    simp
  · simp [dotProduct, Fin.sum_univ_three]

/-! ## Schedule arithmetic through the public H2A.3 crosswalk -/

private lemma selected_m_ge_two
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    2 ≤ ((selectedFerrersCofinalSourceData P).index k).m := by
  rw [selectedFerrersCofinalSourceData_index_eq_preAnchorIndex P k]
  show 2 ≤ selectedFerrersCofinalPreAnchorRank P k + 2
  omega

private lemma selected_N_ge_one
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    1 ≤ ((selectedFerrersCofinalSourceData P).index k).N := by
  rw [selectedFerrersCofinalSourceData_index_eq_preAnchorIndex P k]
  show 1 ≤ selectedFerrersCofinalPreAnchorRank P k + 2
  omega

/-! ## The public source objects -/

/-- **The selected beta vector**: the exact source beta vector
`β_j = n_j · M_{j,center}` of the literal CCM matrix at the selected
index, cast to the complex carrier. -/
noncomputable def selectedFerrersFiniteCCMBetaVector
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  fun j =>
    ((ccmBetaFinite ((selectedFerrersCofinalSourceData P).index k).m
      ((selectedFerrersCofinalSourceData P).index k).N j : ℝ) : ℂ)

/-- **The selected beta moment**: the pairing of the source beta vector
with the exact selected row. -/
noncomputable def selectedFerrersFiniteCCMBetaMoment
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℂ :=
  selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
    selectedFerrersFiniteCCMRow P k

/-- **The selected beta energy**: the squared Euclidean size of the exact
source beta vector.  Its selected-schedule growth is NOT controlled
here. -/
noncomputable def selectedFerrersFiniteCCMBetaEnergy
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℝ :=
  ∑ j, (ccmBetaFinite ((selectedFerrersCofinalSourceData P).index k).m
    ((selectedFerrersCofinalSourceData P).index k).N j) ^ 2

/-- **The mode-weighted selected row**: `j ↦ n_j · q_j`, the exact `D q`
of the structured commutator. -/
noncomputable def selectedFerrersFiniteCCMModeWeightedRow
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  fun j =>
    ((ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j :
        ℤ) : ℂ) *
      selectedFerrersFiniteCCMRow P k j

/-! ## The center-action source crosswalk -/

/-- **The source lock**: the beta moment is exactly the center coordinate
of the literal source matrix acting on the mode-weighted selected row —
`β ⬝ q = (M (D q))_center`.  This is the C04/C10 crosswalk that
distinguishes the mode-weighted source-action functional from every
unweighted transform value. -/
theorem selectedFerrersFiniteCCMBetaMoment_eq_center_modeWeighted_sourceAction
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMBetaMoment P k =
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
        selectedFerrersFiniteCCMModeWeightedRow P k)
        (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N) := by
  classical
  have hsym := ccmWeilMatFinite_transpose_eq
    ((selectedFerrersCofinalSourceData P).index k).m
    ((selectedFerrersCofinalSourceData P).index k).N
    (selected_m_ge_two P k) (selected_N_ge_one P k)
  have hswap : ∀ j,
      ccmWeilMatFinite
        ((selectedFerrersCofinalSourceData P).index k).m
        ((selectedFerrersCofinalSourceData P).index k).N
        (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N)
        j =
      ccmWeilMatFinite
        ((selectedFerrersCofinalSourceData P).index k).m
        ((selectedFerrersCofinalSourceData P).index k).N
        j
        (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N) := by
    intro j
    conv_rhs => rw [show ccmWeilMatFinite
        ((selectedFerrersCofinalSourceData P).index k).m
        ((selectedFerrersCofinalSourceData P).index k).N
        j
        (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N) =
      (ccmWeilMatFinite
        ((selectedFerrersCofinalSourceData P).index k).m
        ((selectedFerrersCofinalSourceData P).index k).N)ᵀ
        (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N)
        j from rfl]
    rw [hsym]
  show selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
      selectedFerrersFiniteCCMRow P k =
    sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)
      (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N) ⬝ᵥ
      selectedFerrersFiniteCCMModeWeightedRow P k
  unfold dotProduct selectedFerrersFiniteCCMBetaVector
    selectedFerrersFiniteCCMModeWeightedRow
  apply Finset.sum_congr rfl
  intro j _
  rw [show sourceCCMFiniteMatrix
      ((selectedFerrersCofinalSourceData P).index k)
      (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N) j =
    ((ccmWeilMatFinite
      ((selectedFerrersCofinalSourceData P).index k).m
      ((selectedFerrersCofinalSourceData P).index k).N
      (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N)
      j : ℝ) : ℂ) from rfl]
  rw [hswap j]
  unfold ccmBetaFinite
  push_cast
  ring

/-! ## The beta moment sees only the selected odd part -/

private def selectedNegEquiv
    (N : ℕ) : CCMModeFinite N ≃ CCMModeFinite N where
  toFun := ccmNegFinite N
  invFun := ccmNegFinite N
  left_inv := ccmNegFinite_involutive N
  right_inv := ccmNegFinite_involutive N

/-- **The oddness lock**: because the source beta vector is
reflection-odd, the beta moment equals its pairing with the exact
selected odd part — the reflection-even part is annihilated. -/
theorem selectedFerrersFiniteCCMBetaMoment_eq_beta_dot_oddPart
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMBetaMoment P k =
      selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
        selectedFerrersFiniteCCMOddPart P k := by
  classical
  have hm := selected_m_ge_two P k
  have hN := selected_N_ge_one P k
  set Nc : ℕ := ((selectedFerrersCofinalSourceData P).index k).N with hNc
  -- decompose the row into even plus odd parts
  have hdecomp : selectedFerrersFiniteCCMRow P k =
      (fun j => (selectedFerrersFiniteCCMRow P k j +
        selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2) +
      selectedFerrersFiniteCCMOddPart P k := by
    funext j
    show selectedFerrersFiniteCCMRow P k j =
      (selectedFerrersFiniteCCMRow P k j +
        selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2 +
      (selectedFerrersFiniteCCMRow P k j -
        selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2
    ring
  -- the beta pairing with the even part vanishes by reflection oddness
  have heven : selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
      (fun j => (selectedFerrersFiniteCCMRow P k j +
        selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2) = 0 := by
    set S : ℂ := ∑ j, selectedFerrersFiniteCCMBetaVector P k j *
      ((selectedFerrersFiniteCCMRow P k j +
        selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2) with hS
    have hSdot : selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
        (fun j => (selectedFerrersFiniteCCMRow P k j +
          selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2) = S :=
      rfl
    rw [hSdot]
    have hreindex : S =
        ∑ j, selectedFerrersFiniteCCMBetaVector P k (ccmNegFinite Nc j) *
          ((selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j) +
            selectedFerrersFiniteCCMRow P k
              (ccmNegFinite Nc (ccmNegFinite Nc j))) / 2) := by
      rw [hS]
      exact ((selectedNegEquiv Nc).sum_comp
        (fun j => selectedFerrersFiniteCCMBetaVector P k j *
          ((selectedFerrersFiniteCCMRow P k j +
            selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2))).symm
    have hterm : ∀ j,
        selectedFerrersFiniteCCMBetaVector P k (ccmNegFinite Nc j) *
          ((selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j) +
            selectedFerrersFiniteCCMRow P k
              (ccmNegFinite Nc (ccmNegFinite Nc j))) / 2) =
        -(selectedFerrersFiniteCCMBetaVector P k j *
          ((selectedFerrersFiniteCCMRow P k j +
            selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2)) := by
      intro j
      have hβ : selectedFerrersFiniteCCMBetaVector P k (ccmNegFinite Nc j) =
          -(selectedFerrersFiniteCCMBetaVector P k j) := by
        unfold selectedFerrersFiniteCCMBetaVector
        rw [show ccmBetaFinite
            ((selectedFerrersCofinalSourceData P).index k).m Nc
            (ccmNegFinite Nc j) =
          -(ccmBetaFinite
            ((selectedFerrersCofinalSourceData P).index k).m Nc j) from
          ccmBetaFinite_neg _ _ hm hN j]
        push_cast
        ring
      rw [hβ, ccmNegFinite_involutive]
      ring
    have hneg : S = -S := by
      nth_rewrite 1 [hreindex]
      calc (∑ j, selectedFerrersFiniteCCMBetaVector P k (ccmNegFinite Nc j) *
          ((selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j) +
            selectedFerrersFiniteCCMRow P k
              (ccmNegFinite Nc (ccmNegFinite Nc j))) / 2))
          = ∑ j, -(selectedFerrersFiniteCCMBetaVector P k j *
              ((selectedFerrersFiniteCCMRow P k j +
                selectedFerrersFiniteCCMRow P k (ccmNegFinite Nc j)) / 2)) :=
            Finset.sum_congr rfl fun j _ => hterm j
        _ = -S := by
            rw [Finset.sum_neg_distrib, ← hS]
    have h2 : (2:ℂ) * S = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  show selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
    selectedFerrersFiniteCCMRow P k = _
  rw [hdecomp, dotProduct_add, heven, zero_add]

/-! ## The Cauchy–Schwarz odd-mass bound -/

/-- **The odd-mass bound**: the squared modulus of the beta moment is at
most the explicit source beta-energy times the exact selected odd mass.
This does not claim the beta moment is small: its beta-energy factor is
not controlled here. -/
theorem selectedFerrersFiniteCCMBetaMoment_normSq_le_betaEnergy_mul_oddMass
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    Complex.normSq (selectedFerrersFiniteCCMBetaMoment P k) ≤
      selectedFerrersFiniteCCMBetaEnergy P k *
        selectedFerrersFiniteCCMOddMass P k := by
  classical
  rw [selectedFerrersFiniteCCMBetaMoment_eq_beta_dot_oddPart P k]
  rw [Complex.normSq_eq_norm_sq]
  have h1 : ‖selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
      selectedFerrersFiniteCCMOddPart P k‖ ≤
      ∑ j, |ccmBetaFinite ((selectedFerrersCofinalSourceData P).index k).m
          ((selectedFerrersCofinalSourceData P).index k).N j| *
        ‖selectedFerrersFiniteCCMOddPart P k j‖ := by
    calc ‖∑ j, selectedFerrersFiniteCCMBetaVector P k j *
        selectedFerrersFiniteCCMOddPart P k j‖
        ≤ ∑ j, ‖selectedFerrersFiniteCCMBetaVector P k j *
            selectedFerrersFiniteCCMOddPart P k j‖ :=
          norm_sum_le _ _
      _ = ∑ j, |ccmBetaFinite
            ((selectedFerrersCofinalSourceData P).index k).m
            ((selectedFerrersCofinalSourceData P).index k).N j| *
          ‖selectedFerrersFiniteCCMOddPart P k j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul]
          congr 1
          unfold selectedFerrersFiniteCCMBetaVector
          rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : (∑ j, |ccmBetaFinite
        ((selectedFerrersCofinalSourceData P).index k).m
        ((selectedFerrersCofinalSourceData P).index k).N j| *
      ‖selectedFerrersFiniteCCMOddPart P k j‖) ^ 2 ≤
      (∑ j, |ccmBetaFinite
          ((selectedFerrersCofinalSourceData P).index k).m
          ((selectedFerrersCofinalSourceData P).index k).N j| ^ 2) *
      (∑ j, ‖selectedFerrersFiniteCCMOddPart P k j‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have h3 : (∑ j, |ccmBetaFinite
      ((selectedFerrersCofinalSourceData P).index k).m
      ((selectedFerrersCofinalSourceData P).index k).N j| ^ 2) =
      selectedFerrersFiniteCCMBetaEnergy P k := by
    unfold selectedFerrersFiniteCCMBetaEnergy
    apply Finset.sum_congr rfl
    intro j _
    exact sq_abs _
  have h4 : (∑ j, ‖selectedFerrersFiniteCCMOddPart P k j‖ ^ 2) =
      selectedFerrersFiniteCCMOddMass P k := by
    unfold selectedFerrersFiniteCCMOddMass
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.normSq_eq_norm_sq]
  calc ‖selectedFerrersFiniteCCMBetaVector P k ⬝ᵥ
      selectedFerrersFiniteCCMOddPart P k‖ ^ 2
      ≤ (∑ j, |ccmBetaFinite
            ((selectedFerrersCofinalSourceData P).index k).m
            ((selectedFerrersCofinalSourceData P).index k).N j| *
          ‖selectedFerrersFiniteCCMOddPart P k j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, |ccmBetaFinite
          ((selectedFerrersCofinalSourceData P).index k).m
          ((selectedFerrersCofinalSourceData P).index k).N j| ^ 2) *
        (∑ j, ‖selectedFerrersFiniteCCMOddPart P k j‖ ^ 2) := h2
    _ = selectedFerrersFiniteCCMBetaEnergy P k *
        selectedFerrersFiniteCCMOddMass P k := by
        rw [h3, h4]

#print axioms selectedFerrersFiniteCCMBetaMoment_eq_center_modeWeighted_sourceAction
#print axioms selectedFerrersFiniteCCMBetaMoment_eq_beta_dot_oddPart
#print axioms selectedFerrersFiniteCCMBetaMoment_normSq_le_betaEnergy_mul_oddMass
#print axioms allOnesMoment_does_not_determine_betaMoment_plant
#print axioms beta_oddness_is_load_bearing_plant

end Q3.RouteB.D0Pstar

end
