-- ОЖИДАЕМЫЙ ИСХОД: компилируется, [propext, Classical.choice, Quot.sound].
-- СКЛЕЙКА: от заключения `simplicity_clause` к форме `hsimple` потребителя.
-- Приёмник даёт «любые два собственных вектора пропорциональны».
-- Потребителю нужно `finrank (eigenspace …) = 1`. Это и есть недостающее звено.
import Mathlib
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Подпространство, в котором любые два элемента пропорциональны и есть ненулевой,
одномерно. -/
theorem finrank_eq_one_of_pairwise_proportional
    (W : Submodule K V) [FiniteDimensional K W]
    {v : V} (hv : v ∈ W) (hv0 : v ≠ 0)
    (hprop : ∀ y ∈ W, ∃ c : K, y = c • v) :
    Module.finrank K W = 1 := by
  have hspan : W = Submodule.span K {v} := by
    refine le_antisymm (fun y hy => ?_) ?_
    · obtain ⟨c, rfl⟩ := hprop y hy
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hv
  rw [hspan]
  exact finrank_span_singleton hv0

#print axioms finrank_eq_one_of_pairwise_proportional
