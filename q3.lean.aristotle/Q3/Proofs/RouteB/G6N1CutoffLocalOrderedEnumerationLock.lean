import Q3.Proofs.RouteB.G6N1OrderedEnumerationLock

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB.D0Pstar

/-!
# The cutoff-local ordered enumeration lock

Floor V3.1 of verdict `0ca5991a` (`CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK`).

The global lock `eq_of_strictMono_of_low_range_eq` asks for global strict
monotonicity of both sequences and a separate source cutoff.  The production
carrier only offers *cutoff-local* strictness — `a i < a j` is known when
`a j` is below the cutoff — and the source cutoff is not a separate input.
This lemma proves that the local contract suffices: termwise equality up to
rank `R` **and** the source cutoff both follow.

The plant `cutoffLocal_rank_swap_plant` shows the local order hypothesis is
necessary: a rank swap below the cutoff preserves both low ranges and the
project cutoff data, yet termwise equality fails.

LEDGER:
  CLOSES: [GLOBAL_PROJECT_STRICTMONO_OVERSTRENGTH, HSRC_CUT_AS_SEPARATE_INPUT]
  OPENS:  []
-/

/-- **V3.1.**  Cutoff-local order lock: a cutoff-locally strict project
enumeration and a strictly increasing source enumeration with the same low
range agree termwise as far as the project stays below the cutoff, and the
source cutoff is an output. -/
theorem eq_of_cutoffLocalStrictMono_of_low_range_eq
    {a b : ℕ → ℝ}
    (hb : StrictMono b)
    {C : ℝ} {R : ℕ}
    (haLocal : ∀ {i j : ℕ}, i < j → a j < C → a i < a j)
    (hrange : Set.range a ∩ Set.Iio C = Set.range b ∩ Set.Iio C)
    (haCut : ∀ j ≤ R, a j < C) :
    ∀ j ≤ R, a j = b j ∧ b j < C := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjR
    have hIH : ∀ m, m < j → a m = b m := fun m hm =>
      (ih m hm (le_trans (le_of_lt hm) hjR)).1
    have hajC : a j < C := haCut j hjR
    have hmem1 : a j ∈ Set.range b ∩ Set.Iio C := by
      rw [← hrange]
      exact ⟨Set.mem_range_self j, hajC⟩
    obtain ⟨⟨m, hm⟩, _⟩ := hmem1
    have hjm : j ≤ m := by
      by_contra hlt
      push_neg at hlt
      have heq := hIH m hlt
      have hlt2 : a m < a j := haLocal hlt hajC
      rw [heq, hm] at hlt2
      exact lt_irrefl _ hlt2
    have hbj_le : b j ≤ a j := by
      calc b j ≤ b m := hb.monotone hjm
        _ = a j := hm
    have hbjC : b j < C := lt_of_le_of_lt hbj_le hajC
    have hmem2 : b j ∈ Set.range a ∩ Set.Iio C := by
      rw [hrange]
      exact ⟨Set.mem_range_self j, hbjC⟩
    obtain ⟨⟨n, hn⟩, _⟩ := hmem2
    have hjn : j ≤ n := by
      by_contra hlt
      push_neg at hlt
      have heq := hIH n hlt
      rw [heq] at hn
      have hbb := hb hlt
      rw [hn] at hbb
      exact lt_irrefl _ hbb
    have haj_le : a j ≤ b j := by
      rcases eq_or_lt_of_le hjn with heq | hlt
      · rw [← hn, ← heq]
      · have hanC : a n < C := by
          rw [hn]
          exact hbjC
        have := haLocal hlt hanC
        rw [hn] at this
        exact le_of_lt this
    exact ⟨le_antisymm haj_le hbj_le, hbjC⟩

/-- **The plant.**  Dropping the cutoff-local order hypothesis makes the lock
false: a rank swap below the cutoff preserves the strictly increasing source,
the low-range equality and the project cutoff data, yet termwise equality
fails at rank zero. -/
theorem cutoffLocal_rank_swap_plant :
    ∃ (a b : ℕ → ℝ) (C : ℝ) (R : ℕ),
      StrictMono b ∧
      (Set.range a ∩ Set.Iio C = Set.range b ∩ Set.Iio C) ∧
      (∀ j ≤ R, a j < C) ∧
      ¬ (∀ j ≤ R, a j = b j) := by
  set σ : ℕ → ℕ := fun n => if n = 0 then 1 else if n = 1 then 0 else n with hσ
  set b : ℕ → ℝ := fun n => (n : ℝ) with hbdef
  refine ⟨b ∘ σ, b, 2, 1, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simpa [hbdef] using (Nat.cast_lt (α := ℝ)).mpr hij
  · have hσsurj : Function.Surjective σ := by
      intro n
      match n with
      | 0 => exact ⟨1, by simp [hσ]⟩
      | 1 => exact ⟨0, by simp [hσ]⟩
      | (k + 2) => exact ⟨k + 2, by simp [hσ]⟩
    rw [Set.range_comp, hσsurj.range_eq, Set.image_univ]
  · intro j hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h | h <;>
      subst h <;>
      norm_num [hσ, hbdef]
  · intro hall
    have h0 := hall 0 (by norm_num)
    norm_num [hσ, hbdef] at h0

#print axioms eq_of_cutoffLocalStrictMono_of_low_range_eq
#print axioms cutoffLocal_rank_swap_plant

end Q3.RouteB.D0Pstar
