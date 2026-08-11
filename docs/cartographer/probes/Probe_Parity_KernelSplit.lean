-- I-P1 ДОБИТ: блочная эквивалентность `hsimple` через два сектора чётности.
--
-- ЦЕПЬ: секторы дополнительны → ядро сдвинутого оператора расщепляется по ним →
-- арифметика размерностей → мост «нет ядра в секторе ⟺ форма строго положительна» →
-- свод к входу потребителя `hsimple`.
--
-- Приём (счёт инерцией вместо локализации) заимствован у формализации Anthropic
-- `zeta-23-lean`, Apache 2.0: идея свободно, код НЕ копируется. Здесь всё своё, Mathlib-first.
--
-- ОЖИДАЕМЫЙ ИСХОД: пять теорем, у каждой [propext, Classical.choice, Quot.sound].
--
-- Прогон: cd q3.lean.aristotle && lake env lean ../docs/cartographer/probes/<этот файл>

import Q3.Proofs.RouteB.CCMFiniteWeilParity
import Mathlib
set_option maxHeartbeats 1000000
open Q3.RouteB Matrix

variable (N : ℕ)

noncomputable abbrev evenSec := Module.End.eigenspace (ccmReflectionEndFinite N) 1
noncomputable abbrev oddSec := Module.End.eigenspace (ccmReflectionEndFinite N) (-1)

theorem refl_apply_apply (x : CCMModeFinite N → ℝ) :
    ccmReflectionEndFinite N (ccmReflectionEndFinite N x) = x := by
  have := LinearMap.congr_fun (ccmReflectionEndFinite_involutive N) x
  simpa using this

theorem sectors_isCompl : IsCompl (evenSec N) (oddSec N) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxe hxo
    rw [Module.End.mem_eigenspace_iff] at hxe hxo
    have h : x = -x := by
      have := hxe.symm.trans hxo
      simpa using this
    have : (2:ℝ) • x = 0 := by
      rw [two_smul]; nth_rewrite 2 [h]; simp
    simpa using this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (2:ℝ)⁻¹ • (x + ccmReflectionEndFinite N x)
                + (2:ℝ)⁻¹ • (x - ccmReflectionEndFinite N x) := by module
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · refine Submodule.smul_mem _ _ ?_
      rw [Module.End.mem_eigenspace_iff, map_add, refl_apply_apply]
      module
    · refine Submodule.smul_mem _ _ ?_
      rw [Module.End.mem_eigenspace_iff, map_sub, refl_apply_apply]
      module

#print axioms sectors_isCompl

/-- ШАГ 2. Сдвинутый оператор тоже коммутирует с отражением. -/
theorem shifted_commutes_reflection (mProject : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N) (x : CCMModeFinite N → ℝ) :
    ccmShiftedWeilOpFinite mProject N epsilon (ccmReflectionEndFinite N x)
      = ccmReflectionEndFinite N (ccmShiftedWeilOpFinite mProject N epsilon x) := by
  have h := LinearMap.congr_fun
    (ccmWeilOpFinite_commutes_reflection mProject N hm hN) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [ccmShiftedWeilOpFinite_eq_sub_smul_id]
  simp [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, ← h]

/-- ШАГ 3. Ядро сдвинутого оператора расщепляется по секторам —
внутри ЯДРА, а не во всём пространстве. -/
theorem ker_eq_sup_sectors (mProject : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon)
      = (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ evenSec N)
        ⊔ (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ oddSec N) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  have hxr : ccmReflectionEndFinite N x
      ∈ LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) := by
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [shifted_commutes_reflection N mProject epsilon hm hN x, hx, map_zero]
  have hd : x = (2:ℝ)⁻¹ • (x + ccmReflectionEndFinite N x)
              + (2:ℝ)⁻¹ • (x - ccmReflectionEndFinite N x) := by module
  rw [hd]
  refine Submodule.add_mem_sup ?_ ?_
  · refine Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨Submodule.add_mem _ hx hxr, ?_⟩)
    rw [Module.End.mem_eigenspace_iff, map_add, refl_apply_apply]; module
  · refine Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hx hxr, ?_⟩)
    rw [Module.End.mem_eigenspace_iff, map_sub, refl_apply_apply]; module

#print axioms ker_eq_sup_sectors

/-! ## Добивание: две блочные подцели -/

/-- Размерность ядра есть сумма размерностей его чётной и нечётной частей. -/
theorem finrank_ker_eq_add (mProject : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    Module.finrank ℝ (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon))
      = Module.finrank ℝ
          (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ evenSec N : Submodule ℝ _)
        + Module.finrank ℝ
          (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ oddSec N : Submodule ℝ _) := by
  classical
  set K := LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon)
  have hdisj : (K ⊓ evenSec N) ⊓ (K ⊓ oddSec N) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Submodule.disjoint_def.mp (sectors_isCompl N).disjoint) x hx.1.2 hx.2.2
  have hsup : (K ⊓ evenSec N) ⊔ (K ⊓ oddSec N) = K :=
    (ker_eq_sup_sectors N mProject epsilon hm hN).symm
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ⊓ evenSec N) (K ⊓ oddSec N)
  rw [hsup, hdisj] at h
  simpa using h

/-- **ДВЕ БЛОЧНЫЕ ПОДЦЕЛИ.** При наличии ненулевого чётного вектора в ядре простота
равносильна паре: нечётный блок без ядра, чётный блок ровно одномерен. -/
theorem simple_iff_two_blocks (mProject : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    {xi : CCMModeFinite N → ℝ} (hxi0 : xi ≠ 0)
    (hxiK : xi ∈ LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon))
    (hxiE : xi ∈ evenSec N) :
    Module.finrank ℝ (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon)) = 1
      ↔ (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ oddSec N = ⊥
          ∧ Module.finrank ℝ
              (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ evenSec N
                : Submodule ℝ _) = 1) := by
  classical
  have hadd := finrank_ker_eq_add N mProject epsilon hm hN
  have hEne : (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ evenSec N
                : Submodule ℝ _) ≠ ⊥ := by
    intro h
    apply hxi0
    have : xi ∈ (⊥ : Submodule ℝ (CCMModeFinite N → ℝ)) := by
      rw [← h]; exact Submodule.mem_inf.mpr ⟨hxiK, hxiE⟩
    simpa using this
  have hEpos : 1 ≤ Module.finrank ℝ
      (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ evenSec N
        : Submodule ℝ _) := Submodule.one_le_finrank_iff.mpr hEne
  constructor
  · intro h1
    rw [h1] at hadd
    refine ⟨Submodule.finrank_eq_zero.mp (by omega), by omega⟩
  · rintro ⟨hO, hE⟩
    rw [hadd, hE, hO]
    simp

#print axioms simple_iff_two_blocks

/-! ## Мост: «нет ядра в секторе» ⟺ «форма строго положительна на секторе» -/

/-- Строгая положительность формы на подпространстве. -/
def PosDefOnSub (S : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ)
    (W : Submodule ℝ (CCMModeFinite N → ℝ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < x ⬝ᵥ (S *ᵥ x)

/-- Для неотрицательной матрицы строгая положительность на `W` равносильна
отсутствию ядра в `W`. -/
theorem posDefOnSub_iff_inf_ker_bot
    (S : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) (hS : S.PosSemidef)
    (W : Submodule ℝ (CCMModeFinite N → ℝ)) :
    PosDefOnSub N S W ↔ LinearMap.ker S.mulVecLin ⊓ W = ⊥ := by
  constructor
  · intro hpos
    rw [eq_bot_iff]
    intro x hx
    by_contra hne
    have hx0 : x ≠ 0 := by simpa using hne
    have hker : S *ᵥ x = 0 := hx.1
    have := hpos x hx.2 hx0
    rw [hker] at this
    simp at this
  · intro hbot x hxW hx0
    have hnn : ∀ y, 0 ≤ y ⬝ᵥ (S *ᵥ y) :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hS).2
    rcases lt_or_eq_of_le (hnn x) with h | h
    · exact h
    · exfalso
      have hker : S *ᵥ x = 0 :=
        (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hS x).mp h.symm
      have : x ∈ LinearMap.ker S.mulVecLin ⊓ W := ⟨hker, hxW⟩
      rw [hbot] at this
      exact hx0 (by simpa using this)

#print axioms posDefOnSub_iff_inf_ker_bot

/-! ## Свод: `hsimple` через два блока -/

/-- **ИТОГ.** При `hbottom` (то есть `S ⪰ 0`) и ненулевом чётном `ξ` в ядре простота
нижнего состояния равносильна паре блочных условий:
строгая положительность на НЕЧЁТНОМ секторе плюс одномерность ЧЁТНОЙ части ядра. -/
theorem hsimple_iff_odd_posdef_and_even_one
    (mProject : ℕ) (epsilon : ℝ) (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (hS : (ccmShiftedWeilMatFinite mProject N epsilon).PosSemidef)
    {xi : CCMModeFinite N → ℝ} (hxi0 : xi ≠ 0)
    (hxiK : xi ∈ LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon))
    (hxiE : xi ∈ evenSec N) :
    Module.finrank ℝ ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1
      ↔ (PosDefOnSub N (ccmShiftedWeilMatFinite mProject N epsilon) (oddSec N)
          ∧ Module.finrank ℝ
              (LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) ⊓ evenSec N
                : Submodule ℝ _) = 1) := by
  rw [← ccmShiftedWeilOpFinite_ker_eq_eigenspace mProject N epsilon,
      simple_iff_two_blocks N mProject epsilon hm hN hxi0 hxiK hxiE,
      posDefOnSub_iff_inf_ker_bot N _ hS (oddSec N)]
  rfl

#print axioms hsimple_iff_odd_posdef_and_even_one
