-- I-P1 (conf 0.70): блочная эквивалентность из чётности «малой кровью».
-- ЧАСТИЧНО. Структурная половина компилируется; см. скоринг в TRANSLATION_DICTIONARY.
-- ОЖИДАЕМЫЙ ИСХОД: две теоремы, аксиомы [propext, Classical.choice, Quot.sound].
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
