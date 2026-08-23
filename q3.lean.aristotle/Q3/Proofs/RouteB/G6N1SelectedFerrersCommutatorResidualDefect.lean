import Q3.Proofs.RouteB.G6N1SelectedFerrersBetaMomentOddMass
import Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Matrix Filter
open scoped BigOperators Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.4.1b.3b — the selected Ferrers commutator residual ratio lock

Floor `H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK` of
verdict `4abf5ac2`.

The full residual energy is compressed to **one source-faithful commutator
ratio**.  The combined commutator defect

`Γ_k = S_k(D_k q_k) + A_k·β_k − B_k·𝟙`

is proved **exactly equal** to the mode-weighted literal residual `D_k r_k`
— the cancellation inside the source commutator is preserved, never split
into component norms.  The center coefficient is nonvanishing on the
selected tail (from the shell's raw-zero nonvanishing — no numerical
floor), the center-anchored reconstruction inequality

`|q_{0,k}|²·‖r_k‖² ≤ ‖Γ_k‖²`

follows from unit normalization, residual orthogonality and `|n| ≥ 1` off
the center, and the receiver turns

`R_k := η_k·‖Γ_k‖²/|q_{0,k}|² → 0`  into  `√η_k·√E_res,k → 0`.

The source-derived decay of `R_k` is NOT proved here (`H2A_4_1B_3C`).
The beta-correction budget from B3A enters only as an auxiliary one-sided
bound.  The two plants record the kills: the mode diagonal annihilates the
center mode (no theorem may omit the center anchor), and a zero beta
moment does not control the commutator defect.

Deliberately NOT here: any rate for the ratio, beta-energy growth, sector
floors, simple ground, Theorem 5.10.

LEDGER:
  CLOSES: [SELECTED_FERRERS_COMPLEX_COMMUTATOR_RESIDUAL_IDENTITY,
           SELECTED_FERRERS_MODE_WEIGHTED_RESIDUAL_ENERGY_LOCK,
           SELECTED_FERRERS_CENTER_COEFFICIENT_NONVANISHING,
           SELECTED_FERRERS_CENTER_WEIGHTED_RESIDUAL_BOUND,
           SELECTED_FERRERS_BETA_CORRECTION_ODD_MASS_BUDGET,
           SELECTED_FERRERS_COMMUTATOR_RATIO_TO_WEIGHTED_RESIDUAL_RECEIVER]
  OPENS:  [SELECTED_FERRERS_WEIGHTED_COMMUTATOR_RATIO_SOURCE_RATE]
-/

/-! ## The two mandatory plants -/

/-- **Plant 1.**  The center-mode kernel is load-bearing: on `Fin 2` with
`K = [[0,1],[1,0]]` and the unit row `q = e₁`, the exact Rayleigh residual
is `e₀`, so the mode-weighted residual `D r` vanishes identically while
the residual energy is `1` — and the center coefficient of `q` is zero.
Every theorem omitting the center anchor dies here. -/
private theorem center_mode_kernel_is_load_bearing_plant :
    ∃ (K : Matrix (Fin 2) (Fin 2) ℂ) (q : Fin 2 → ℂ),
      K.IsHermitian ∧ star q ⬝ᵥ q = 1 ∧
      (fun j : Fin 2 => ((j : ℕ) : ℂ) *
        (K *ᵥ q - (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q) j) = 0 ∧
      (star (K *ᵥ q - (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q) ⬝ᵥ
        (K *ᵥ q - (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q)).re = 1 ∧
      q 0 = 0 := by
  classical
  refine ⟨!![0, 1; 1, 0], ![0, 1], ?_, ?_, ?_, ?_, rfl⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · simp [dotProduct, Fin.sum_univ_two]
  · have hKq : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        (![0, 1] : Fin 2 → ℂ) = ![1, 0] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hRay : (star (![0, 1] : Fin 2 → ℂ) ⬝ᵥ
        (![(1:ℂ), 0] : Fin 2 → ℂ)).re = 0 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [hKq, hRay]
    funext j
    fin_cases j <;> simp
  · have hKq : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        (![0, 1] : Fin 2 → ℂ) = ![1, 0] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hRay : (star (![0, 1] : Fin 2 → ℂ) ⬝ᵥ
        (![(1:ℂ), 0] : Fin 2 → ℂ)).re = 0 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [hKq, hRay]
    have hres : (![(1:ℂ), 0] : Fin 2 → ℂ) -
        (((0:ℝ) : ℂ)) • (![0, 1] : Fin 2 → ℂ) = ![1, 0] := by
      funext l
      fin_cases l <;> simp
    rw [hres]
    simp [dotProduct, Fin.sum_univ_two]

/-- **Plant 2.**  A zero beta moment does not control the commutator
defect: on `Fin 2` with `K = diag(0,1)` (which commutes with the mode
diagonal, so the source-style beta vector vanishes) and the unit row
`q = (3/5, 4/5)`, the beta moment is zero while the mode-weighted Rayleigh
residual has a nonzero component.  The shortcut `B_k = 0 → Γ_k = 0` is
dead. -/
private theorem beta_moment_zero_does_not_control_commutator_defect_plant :
    ∃ (K : Matrix (Fin 2) (Fin 2) ℂ) (q beta : Fin 2 → ℂ),
      K.IsHermitian ∧ star q ⬝ᵥ q = 1 ∧
      beta = 0 ∧ beta ⬝ᵥ q = 0 ∧
      ((1 : ℂ) *
        (K *ᵥ q - (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q) 1) ≠ 0 := by
  classical
  refine ⟨!![0, 0; 0, 1], ![(3/5 : ℂ), (4/5 : ℂ)], 0, ?_, ?_, rfl, ?_, ?_⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · have h : star (![(3/5 : ℂ), (4/5 : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
        ![(3/5 : ℂ), (4/5 : ℂ)] = (((1:ℝ)) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_two, map_div₀, map_ofNat]
      norm_num
    rw [h]
    norm_num
  · simp [dotProduct]
  · have hKq : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        (![(3/5 : ℂ), (4/5 : ℂ)] : Fin 2 → ℂ) = ![0, (4/5 : ℂ)] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hRay : (star (![(3/5 : ℂ), (4/5 : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
        (![0, (4/5 : ℂ)] : Fin 2 → ℂ)).re = 16/25 := by
      simp [dotProduct, Fin.sum_univ_two, map_div₀, map_ofNat]
      norm_num
    rw [hKq, hRay]
    have h2 : ((![0, (4/5 : ℂ)] : Fin 2 → ℂ) -
        (((16/25 : ℝ)) : ℂ) • (![(3/5 : ℂ), (4/5 : ℂ)] : Fin 2 → ℂ)) 1 =
        (36/125 : ℂ) := by
      show (4/5 : ℂ) - (((16/25 : ℝ)) : ℂ) * (4/5 : ℂ) = (36/125 : ℂ)
      push_cast
      ring
    rw [h2]
    norm_num

/-! ## Local schedule and cast groundwork -/

private lemma local_m_ge_two
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    2 ≤ ((selectedFerrersCofinalSourceData P).index k).m := by
  rw [selectedFerrersCofinalSourceData_index_eq_preAnchorIndex P k]
  show 2 ≤ selectedFerrersCofinalPreAnchorRank P k + 2
  omega

private lemma local_N_ge_one
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    1 ≤ ((selectedFerrersCofinalSourceData P).index k).N := by
  rw [selectedFerrersCofinalSourceData_index_eq_preAnchorIndex P k]
  show 1 ≤ selectedFerrersCofinalPreAnchorRank P k + 2
  omega

private lemma local_L_pos (i : PairIndex) : 0 < L_m i := by
  have h := i.hm
  show (0:ℝ) < Real.log i.m
  apply Real.log_pos
  exact_mod_cast (by omega : 1 < i.m)

private lemma local_dot_star_self_re
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (star v ⬝ᵥ v).re = ∑ j, Complex.normSq (v j) := by
  classical
  unfold dotProduct
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.star_apply, show star (v j) * v j =
    ((Complex.normSq (v j) : ℝ) : ℂ) by
      rw [show star (v j) = (starRingEnd ℂ) (v j) from rfl, mul_comm,
        Complex.mul_conj]]
  rw [Complex.ofReal_re]

/-- The real structured identity valid for every pair of carrier labels:
`(n_j − n_l)·M_{jl} = β_j − β_l` — trivial on the diagonal, the exact
Loewner divided-difference law off it. -/
private lemma structured_all
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ)
    (j l : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) :
    ((ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j : ℝ) -
      (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N l : ℝ)) *
      ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m
        ((selectedFerrersCofinalSourceData P).index k).N j l =
    ccmBetaFinite ((selectedFerrersCofinalSourceData P).index k).m
      ((selectedFerrersCofinalSourceData P).index k).N j -
    ccmBetaFinite ((selectedFerrersCofinalSourceData P).index k).m
      ((selectedFerrersCofinalSourceData P).index k).N l := by
  classical
  by_cases hjl : j = l
  · subst hjl
    simp
  · have hmode : ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j ≠
        ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N l := by
      intro h
      exact hjl (ccmModeFinite_injective _ h)
    have hden : ((ccmModeFinite
        ((selectedFerrersCofinalSourceData P).index k).N j : ℝ) -
        (ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N l : ℝ)) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hmode
    have h := ccmWeilMatFinite_structured_offdiag
      ((selectedFerrersCofinalSourceData P).index k).m
      ((selectedFerrersCofinalSourceData P).index k).N
      (local_m_ge_two P k) (local_N_ge_one P k) hjl
    rw [h, mul_div_cancel₀ _ hden]

/-! ## The public source objects -/

/-- The all-ones commutator vector on the selected carrier.  This is
`ccmEtaFinite` in complex coordinates — NOT the reflection odd mass. -/
noncomputable def selectedFerrersFiniteCCMAllOnesVector
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  fun _ => 1

/-- The all-ones moment `A_k = 𝟙 ⬝ q_k`.  NOT `Gwin(0)`, NOT a Mellin
anchor, NOT the beta moment, NOT the center coefficient. -/
noncomputable def selectedFerrersFiniteCCMAllOnesMoment
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℂ :=
  selectedFerrersFiniteCCMAllOnesVector P k ⬝ᵥ
    selectedFerrersFiniteCCMRow P k

/-- The exact center coefficient of the selected row. -/
noncomputable def selectedFerrersFiniteCCMCenterCoefficient
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℂ :=
  selectedFerrersFiniteCCMRow P k
    (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N)

/-- The exact shifted selected source matrix `S_k = M_k − a_k·I`. -/
noncomputable def selectedFerrersFiniteCCMShiftedSourceMatrix
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    Matrix (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N)
      (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) ℂ :=
  sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) -
    ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)

/-- **The combined commutator residual defect**
`Γ_k = S_k(D_k q_k) + A_k·β_k − B_k·𝟙`, kept as ONE vector — the source
cancellation is never split into component norms. -/
noncomputable def selectedFerrersFiniteCCMCommutatorResidualDefect
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  selectedFerrersFiniteCCMShiftedSourceMatrix P k *ᵥ
      selectedFerrersFiniteCCMModeWeightedRow P k +
    selectedFerrersFiniteCCMAllOnesMoment P k •
      selectedFerrersFiniteCCMBetaVector P k -
    selectedFerrersFiniteCCMBetaMoment P k •
      selectedFerrersFiniteCCMAllOnesVector P k

/-- The energy of the combined commutator defect. -/
noncomputable def selectedFerrersFiniteCCMCommutatorResidualDefectEnergy
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℝ :=
  ∑ j, Complex.normSq
    (selectedFerrersFiniteCCMCommutatorResidualDefect P k j)

/-- **The weighted commutator ratio**
`R_k = η_k·‖Γ_k‖²/|q_{0,k}|²` — the single source scalar whose decay is
the remaining analytic wall (`H2A_4_1B_3C`). -/
noncomputable def selectedFerrersFiniteCCMWeightedCommutatorRatio
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℝ :=
  selectedFerrersFiniteCCMOddMass P k *
    selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k /
    Complex.normSq (selectedFerrersFiniteCCMCenterCoefficient P k)

/-! ## The exact complex commutator identity -/

/-- **The commutator residual identity**: the combined defect is exactly
the mode-weighted literal residual, `Γ_k = D_k r_k`, entrywise.  The
cancellation of the rank-two commutator correction is preserved. -/
theorem selectedFerrersFiniteCCMCommutatorResidualDefect_eq_modeDiag_residual
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMCommutatorResidualDefect P k =
      fun j =>
        ((ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N j : ℤ) : ℂ) *
          selectedFerrersFiniteCCMResidual P k j := by
  classical
  funext j
  have hkey : (∑ l,
      (((ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j :
          ℤ) : ℂ) -
        ((ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N l :
          ℤ) : ℂ)) *
        sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)
          j l *
        selectedFerrersFiniteCCMRow P k l) =
      selectedFerrersFiniteCCMAllOnesMoment P k *
        selectedFerrersFiniteCCMBetaVector P k j -
      selectedFerrersFiniteCCMBetaMoment P k := by
    have hterm : ∀ l,
        (((ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j :
            ℤ) : ℂ) -
          ((ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N l :
            ℤ) : ℂ)) *
          sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)
            j l *
          selectedFerrersFiniteCCMRow P k l =
        (selectedFerrersFiniteCCMBetaVector P k j -
          selectedFerrersFiniteCCMBetaVector P k l) *
          selectedFerrersFiniteCCMRow P k l := by
      intro l
      have h := structured_all P k j l
      have hC : (((ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N j : ℤ) : ℂ) -
          ((ccmModeFinite
            ((selectedFerrersCofinalSourceData P).index k).N l : ℤ) : ℂ)) *
          sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)
            j l =
          selectedFerrersFiniteCCMBetaVector P k j -
            selectedFerrersFiniteCCMBetaVector P k l := by
        unfold selectedFerrersFiniteCCMBetaVector
        rw [show sourceCCMFiniteMatrix
            ((selectedFerrersCofinalSourceData P).index k) j l =
          ((ccmWeilMatFinite
            ((selectedFerrersCofinalSourceData P).index k).m
            ((selectedFerrersCofinalSourceData P).index k).N j l : ℝ) : ℂ)
          from rfl]
        rw [show (((ccmModeFinite
            ((selectedFerrersCofinalSourceData P).index k).N j : ℤ) : ℂ) -
            ((ccmModeFinite
              ((selectedFerrersCofinalSourceData P).index k).N l : ℤ) : ℂ)) =
          ((((ccmModeFinite
              ((selectedFerrersCofinalSourceData P).index k).N j : ℝ) -
            (ccmModeFinite
              ((selectedFerrersCofinalSourceData P).index k).N l : ℝ)) : ℝ) :
            ℂ) by push_cast; ring]
        rw [← Complex.ofReal_mul, h]
        push_cast
        ring
      rw [hC]
    calc (∑ l, _) = ∑ l,
        (selectedFerrersFiniteCCMBetaVector P k j -
          selectedFerrersFiniteCCMBetaVector P k l) *
          selectedFerrersFiniteCCMRow P k l :=
        Finset.sum_congr rfl fun l _ => hterm l
      _ = (∑ l, selectedFerrersFiniteCCMBetaVector P k j *
            selectedFerrersFiniteCCMRow P k l) -
          ∑ l, selectedFerrersFiniteCCMBetaVector P k l *
            selectedFerrersFiniteCCMRow P k l := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro l _
          ring
      _ = selectedFerrersFiniteCCMAllOnesMoment P k *
            selectedFerrersFiniteCCMBetaVector P k j -
          selectedFerrersFiniteCCMBetaMoment P k := by
          congr 1
          · rw [← Finset.mul_sum, mul_comm]
            congr 1
            unfold selectedFerrersFiniteCCMAllOnesMoment
              selectedFerrersFiniteCCMAllOnesVector dotProduct
            apply Finset.sum_congr rfl
            intro l _
            rw [one_mul]
  -- expand both sides entrywise and use the key sum
  show (selectedFerrersFiniteCCMShiftedSourceMatrix P k *ᵥ
      selectedFerrersFiniteCCMModeWeightedRow P k) j +
      selectedFerrersFiniteCCMAllOnesMoment P k *
        selectedFerrersFiniteCCMBetaVector P k j -
      selectedFerrersFiniteCCMBetaMoment P k * 1 =
    ((ccmModeFinite
      ((selectedFerrersCofinalSourceData P).index k).N j : ℤ) : ℂ) *
      selectedFerrersFiniteCCMResidual P k j
  rw [mul_one]
  have hSrow : (selectedFerrersFiniteCCMShiftedSourceMatrix P k *ᵥ
      selectedFerrersFiniteCCMModeWeightedRow P k) j =
      (∑ l, sourceCCMFiniteMatrix
          ((selectedFerrersCofinalSourceData P).index k) j l *
        (((ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N l : ℤ) : ℂ) *
          selectedFerrersFiniteCCMRow P k l)) -
      ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) *
        (((ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N j : ℤ) : ℂ) *
          selectedFerrersFiniteCCMRow P k j) := by
    unfold selectedFerrersFiniteCCMShiftedSourceMatrix
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hres : selectedFerrersFiniteCCMResidual P k j =
      (∑ l, sourceCCMFiniteMatrix
          ((selectedFerrersCofinalSourceData P).index k) j l *
        selectedFerrersFiniteCCMRow P k l) -
      ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) *
        selectedFerrersFiniteCCMRow P k j := by
    show (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)
        *ᵥ selectedFerrersFiniteCCMRow P k) j -
      (((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
        selectedFerrersFiniteCCMRow P k) j = _
    rfl
  rw [hSrow, hres]
  have hexpand := hkey
  -- rearrange: Σ M n_l q_l = n_j Σ M q_l − (A β_j − B)
  have hgoal : (∑ l, sourceCCMFiniteMatrix
      ((selectedFerrersCofinalSourceData P).index k) j l *
      (((ccmModeFinite
        ((selectedFerrersCofinalSourceData P).index k).N l : ℤ) : ℂ) *
        selectedFerrersFiniteCCMRow P k l)) =
      ((ccmModeFinite
        ((selectedFerrersCofinalSourceData P).index k).N j : ℤ) : ℂ) *
        (∑ l, sourceCCMFiniteMatrix
          ((selectedFerrersCofinalSourceData P).index k) j l *
          selectedFerrersFiniteCCMRow P k l) -
      (selectedFerrersFiniteCCMAllOnesMoment P k *
        selectedFerrersFiniteCCMBetaVector P k j -
        selectedFerrersFiniteCCMBetaMoment P k) := by
    rw [← hexpand, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hgoal]
  ring

/-! ## The mode-weighted residual energy lock -/

/-- The defect energy is exactly the mode-weighted residual energy. -/
theorem selectedFerrersFiniteCCMCommutatorResidualDefectEnergy_eq_modeWeightedResidualEnergy
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k =
      ∑ j, ((ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N j : ℝ)) ^ 2 *
        Complex.normSq (selectedFerrersFiniteCCMResidual P k j) := by
  classical
  unfold selectedFerrersFiniteCCMCommutatorResidualDefectEnergy
  rw [selectedFerrersFiniteCCMCommutatorResidualDefect_eq_modeDiag_residual P k]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.normSq_mul]
  congr 1
  rw [show (((ccmModeFinite
      ((selectedFerrersCofinalSourceData P).index k).N j : ℤ) : ℂ)) =
    (((ccmModeFinite
      ((selectedFerrersCofinalSourceData P).index k).N j : ℝ)) : ℂ) by
      push_cast; ring]
  rw [Complex.normSq_ofReal]
  ring

/-! ## Center nonvanishing on the selected tail -/

/-- **Center nonvanishing**: the exact center coefficient of the selected
row is pointwise nonzero on the selected tail — from the shell's
theorem-generated raw-zero nonvanishing and the exact
`raw(0) = √L·c₀` identity; no numerical floor is introduced. -/
theorem selectedFerrersFiniteCCMCenterCoefficient_ne
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    selectedFerrersFiniteCCMCenterCoefficient P k ≠ 0 := by
  classical
  have hraw := (selectedFerrersCofinalSourceData P).rawZeroNonzero k
  have hzero := preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0
    ((selectedFerrersCofinalSourceData P).index k)
    (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
    ((selectedFerrersCofinalSourceData P).eStar_memLp k)
    ((selectedFerrersCofinalSourceData P).trialNonzero k)
  rw [hzero] at hraw
  have hc0 : c_n ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)
      ((selectedFerrersCofinalSourceData P).trialNonzero k) 0 ≠ 0 := by
    intro h0
    apply hraw
    rw [h0, mul_zero]
  intro hcc
  apply hc0
  rw [← hcc]
  show c_n _ _ _ _ 0 =
    c_n _ _ _ _
      (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N
        (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N))
  rw [ccmModeFinite_center]

/-! ## The center-weighted residual bound -/

/-- **The center-anchored reconstruction inequality**:
`|q₀|²·E_res ≤ ‖Γ‖²` — from unit normalization, residual orthogonality,
Cauchy–Schwarz off the center, and `|n| ≥ 1` off the center.  Finite
Hermitian geometry only; no operator norm, no rate hypothesis. -/
theorem selectedFerrersFiniteCCMCenterCoeff_normSq_mul_residualEnergy_le_commutatorDefectEnergy
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    Complex.normSq (selectedFerrersFiniteCCMCenterCoefficient P k) *
      selectedFerrersFiniteCCMResidualEnergy P k ≤
      selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k := by
  classical
  set Nc : ℕ := ((selectedFerrersCofinalSourceData P).index k).N with hNc
  set c : CCMModeFinite Nc := ccmCenterFinite Nc with hcdef
  set q : CCMModeFinite Nc → ℂ := selectedFerrersFiniteCCMRow P k with hq
  set r : CCMModeFinite Nc → ℂ := selectedFerrersFiniteCCMResidual P k
    with hr
  -- unit normalization as a normSq sum
  have hunit : (∑ j, Complex.normSq (q j)) = 1 := by
    have h := selectedFerrersFiniteCCMRow_unit P k
    have h2 := congrArg Complex.re h
    rw [local_dot_star_self_re] at h2
    simpa using h2
  -- orthogonality as a sum
  have horth : (∑ j, (starRingEnd ℂ) (q j) * r j) = 0 := by
    have h := selectedFerrersFiniteCCMResidual_orthogonal P k
    have h2 : star q ⬝ᵥ r = 0 := h
    calc (∑ j, (starRingEnd ℂ) (q j) * r j) = star q ⬝ᵥ r := by
          unfold dotProduct
          apply Finset.sum_congr rfl
          intro j _
          rw [Pi.star_apply]
          rfl
      _ = 0 := h2
  -- split off the center
  have hsplit_q : Complex.normSq (q c) +
      (∑ j ∈ Finset.univ.erase c, Complex.normSq (q j)) = 1 := by
    rw [← hunit]
    exact (Finset.add_sum_erase Finset.univ
      (fun j => Complex.normSq (q j)) (Finset.mem_univ c))
  have hsplit_orth : (starRingEnd ℂ) (q c) * r c =
      -(∑ j ∈ Finset.univ.erase c, (starRingEnd ℂ) (q j) * r j) := by
    have h := horth
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => (starRingEnd ℂ) (q j) * r j) (Finset.mem_univ c)] at h
    exact eq_neg_of_add_eq_zero_left h
  -- Cauchy–Schwarz off the center
  have hCS : Complex.normSq (q c) * Complex.normSq (r c) ≤
      (∑ j ∈ Finset.univ.erase c, Complex.normSq (q j)) *
      (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j)) := by
    have h1 : ‖(starRingEnd ℂ) (q c) * r c‖ ≤
        ∑ j ∈ Finset.univ.erase c, ‖q j‖ * ‖r j‖ := by
      rw [hsplit_orth, norm_neg]
      calc ‖∑ j ∈ Finset.univ.erase c, (starRingEnd ℂ) (q j) * r j‖
          ≤ ∑ j ∈ Finset.univ.erase c,
            ‖(starRingEnd ℂ) (q j) * r j‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.univ.erase c, ‖q j‖ * ‖r j‖ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [norm_mul, RCLike.norm_conj]
    have h2 : (∑ j ∈ Finset.univ.erase c, ‖q j‖ * ‖r j‖) ^ 2 ≤
        (∑ j ∈ Finset.univ.erase c, ‖q j‖ ^ 2) *
        (∑ j ∈ Finset.univ.erase c, ‖r j‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : Complex.normSq (q c) * Complex.normSq (r c) =
        ‖(starRingEnd ℂ) (q c) * r c‖ ^ 2 := by
      rw [norm_mul, RCLike.norm_conj, mul_pow,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have h4 : (∑ j ∈ Finset.univ.erase c, ‖q j‖ ^ 2) =
        ∑ j ∈ Finset.univ.erase c, Complex.normSq (q j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Complex.normSq_eq_norm_sq]
    have h5 : (∑ j ∈ Finset.univ.erase c, ‖r j‖ ^ 2) =
        ∑ j ∈ Finset.univ.erase c, Complex.normSq (r j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Complex.normSq_eq_norm_sq]
    calc Complex.normSq (q c) * Complex.normSq (r c)
        = ‖(starRingEnd ℂ) (q c) * r c‖ ^ 2 := h3
      _ ≤ (∑ j ∈ Finset.univ.erase c, ‖q j‖ * ‖r j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j ∈ Finset.univ.erase c, ‖q j‖ ^ 2) *
          (∑ j ∈ Finset.univ.erase c, ‖r j‖ ^ 2) := h2
      _ = _ := by rw [h4, h5]
  -- residual energy split
  have hEsplit : selectedFerrersFiniteCCMResidualEnergy P k =
      Complex.normSq (r c) +
      (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j)) := by
    unfold selectedFerrersFiniteCCMResidualEnergy
    rw [local_dot_star_self_re]
    exact (Finset.add_sum_erase Finset.univ
      (fun j => Complex.normSq (r j)) (Finset.mem_univ c)).symm
  -- the defect energy dominates the noncentral residual energy
  have hG : (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j)) ≤
      selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k := by
    rw [selectedFerrersFiniteCCMCommutatorResidualDefectEnergy_eq_modeWeightedResidualEnergy P k]
    have hterm : ∀ j ∈ Finset.univ.erase c,
        Complex.normSq (r j) ≤
        ((ccmModeFinite Nc j : ℝ)) ^ 2 * Complex.normSq (r j) := by
      intro j hj
      have hjc : j ≠ c := Finset.ne_of_mem_erase hj
      have hne0 : ccmModeFinite Nc j ≠ 0 := by
        intro h0
        apply hjc
        apply ccmModeFinite_injective Nc
        rw [h0, ccmModeFinite_center]
      have habs : (1:ℤ) ≤ |ccmModeFinite Nc j| := Int.one_le_abs hne0
      have habsR : (1:ℝ) ≤ |((ccmModeFinite Nc j : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast habs
      have hsq : (1:ℝ) ≤ ((ccmModeFinite Nc j : ℝ)) ^ 2 := by
        nlinarith [sq_abs ((ccmModeFinite Nc j : ℤ) : ℝ), habsR]
      nlinarith [Complex.normSq_nonneg (r j), hsq]
    calc (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j))
        ≤ ∑ j ∈ Finset.univ.erase c,
          ((ccmModeFinite Nc j : ℝ)) ^ 2 * Complex.normSq (r j) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ j, ((ccmModeFinite Nc j : ℝ)) ^ 2 * Complex.normSq (r j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _)
          intro j _ _
          exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  -- assemble the scalar chain
  have hQ0 : (0:ℝ) ≤ Complex.normSq (q c) := Complex.normSq_nonneg _
  have hR0 : (0:ℝ) ≤ Complex.normSq (r c) := Complex.normSq_nonneg _
  have hRe : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase c, Complex.normSq (r j) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hQe : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase c, Complex.normSq (q j) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  rw [hEsplit]
  have hQe_eq : (∑ j ∈ Finset.univ.erase c, Complex.normSq (q j)) =
      1 - Complex.normSq (q c) := by linarith [hsplit_q]
  have hstep : Complex.normSq (q c) * Complex.normSq (r c) ≤
      (1 - Complex.normSq (q c)) *
        (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j)) := by
    rw [← hQe_eq]
    exact hCS
  calc Complex.normSq (q c) *
      (Complex.normSq (r c) +
        ∑ j ∈ Finset.univ.erase c, Complex.normSq (r j))
      = Complex.normSq (q c) * Complex.normSq (r c) +
        Complex.normSq (q c) *
          (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j)) := by ring
    _ ≤ (1 - Complex.normSq (q c)) *
          (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j)) +
        Complex.normSq (q c) *
          (∑ j ∈ Finset.univ.erase c, Complex.normSq (r j)) := by
        linarith [hstep]
    _ = ∑ j ∈ Finset.univ.erase c, Complex.normSq (r j) := by ring
    _ ≤ selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k := hG

/-! ## The beta-correction odd-mass budget -/

/-- **The beta-correction budget**: the all-ones correction energy inside
the combined defect is bounded by the carrier cardinality times the beta
energy times the odd mass — an auxiliary one-sided bound that must not
force a termwise decomposition of `Γ`. -/
theorem selectedFerrersFiniteCCMBetaCorrectionEnergy_le_card_mul_betaEnergy_mul_oddMass
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    (Fintype.card
        (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) : ℝ) *
      Complex.normSq (selectedFerrersFiniteCCMBetaMoment P k) ≤
      (Fintype.card
        (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) : ℝ) *
        selectedFerrersFiniteCCMBetaEnergy P k *
        selectedFerrersFiniteCCMOddMass P k := by
  have h := selectedFerrersFiniteCCMBetaMoment_normSq_le_betaEnergy_mul_oddMass
    P k
  have hcard : (0:ℝ) ≤ (Fintype.card
      (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) : ℝ) :=
    Nat.cast_nonneg _
  calc (Fintype.card
      (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) : ℝ) *
      Complex.normSq (selectedFerrersFiniteCCMBetaMoment P k)
      ≤ (Fintype.card
          (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) :
          ℝ) *
        (selectedFerrersFiniteCCMBetaEnergy P k *
          selectedFerrersFiniteCCMOddMass P k) :=
        mul_le_mul_of_nonneg_left h hcard
    _ = _ := by ring

/-! ## The ratio receiver -/

private lemma local_oddMass_nonneg
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    0 ≤ selectedFerrersFiniteCCMOddMass P k := by
  unfold selectedFerrersFiniteCCMOddMass
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- **The receiver**: decay of the single weighted commutator ratio
`R_k = η_k·‖Γ_k‖²/|q₀|²` forces the ratified weighted-residual consumer
`√η_k·√E_res,k → 0`.  The source-derived decay of `R_k` itself is the
open floor `H2A_4_1B_3C`. -/
theorem selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_commutatorRatio
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (hratio : Filter.Tendsto
      (fun k => selectedFerrersFiniteCCMWeightedCommutatorRatio P k)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
        Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
      Filter.atTop (nhds 0) := by
  classical
  have hbound : ∀ k,
      Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
        Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k) ≤
      Real.sqrt (selectedFerrersFiniteCCMWeightedCommutatorRatio P k) := by
    intro k
    have hc0 : Complex.normSq
        (selectedFerrersFiniteCCMCenterCoefficient P k) ≠ 0 := by
      intro h
      exact selectedFerrersFiniteCCMCenterCoefficient_ne P k
        (Complex.normSq_eq_zero.mp h)
    have hc0pos : 0 < Complex.normSq
        (selectedFerrersFiniteCCMCenterCoefficient P k) :=
      lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hc0)
    have hkey :=
      selectedFerrersFiniteCCMCenterCoeff_normSq_mul_residualEnergy_le_commutatorDefectEnergy
        P k
    have hηE : selectedFerrersFiniteCCMOddMass P k *
        selectedFerrersFiniteCCMResidualEnergy P k ≤
        selectedFerrersFiniteCCMWeightedCommutatorRatio P k := by
      unfold selectedFerrersFiniteCCMWeightedCommutatorRatio
      rw [le_div_iff₀ hc0pos]
      rw [show selectedFerrersFiniteCCMOddMass P k *
          selectedFerrersFiniteCCMResidualEnergy P k *
          Complex.normSq (selectedFerrersFiniteCCMCenterCoefficient P k) =
        selectedFerrersFiniteCCMOddMass P k *
          (Complex.normSq (selectedFerrersFiniteCCMCenterCoefficient P k) *
            selectedFerrersFiniteCCMResidualEnergy P k) by ring]
      exact mul_le_mul_of_nonneg_left hkey (local_oddMass_nonneg P k)
    calc Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
        Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k)
        = Real.sqrt (selectedFerrersFiniteCCMOddMass P k *
            selectedFerrersFiniteCCMResidualEnergy P k) :=
          (Real.sqrt_mul (local_oddMass_nonneg P k) _).symm
      _ ≤ Real.sqrt
            (selectedFerrersFiniteCCMWeightedCommutatorRatio P k) :=
          Real.sqrt_le_sqrt hηE
  have hsq : Filter.Tendsto
      (fun k => Real.sqrt
        (selectedFerrersFiniteCCMWeightedCommutatorRatio P k))
      Filter.atTop (nhds 0) := by
    have := hratio.sqrt
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsq ?_ (Filter.Eventually.of_forall hbound)
  refine Filter.Eventually.of_forall fun k => ?_
  positivity

#print axioms selectedFerrersFiniteCCMCommutatorResidualDefect_eq_modeDiag_residual
#print axioms selectedFerrersFiniteCCMCommutatorResidualDefectEnergy_eq_modeWeightedResidualEnergy
#print axioms selectedFerrersFiniteCCMCenterCoefficient_ne
#print axioms selectedFerrersFiniteCCMCenterCoeff_normSq_mul_residualEnergy_le_commutatorDefectEnergy
#print axioms selectedFerrersFiniteCCMBetaCorrectionEnergy_le_card_mul_betaEnergy_mul_oddMass
#print axioms selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_commutatorRatio
#print axioms center_mode_kernel_is_load_bearing_plant
#print axioms beta_moment_zero_does_not_control_commutator_defect_plant

end Q3.RouteB.D0Pstar

end
