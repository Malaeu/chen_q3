import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Interval.Set.Basic

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB.D0Pstar

/-!
# W13.7D — the ordered-enumeration lock

Authorized for execution in the judge's REQ-2026-08-21-N verdict
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_21_N_BOOK_EXHAUSTIVENESS_AND_W13_7D_AUTHORIZATION_2026-08-21.md`),
which states the semantic content to implement:

> For strictly increasing `a, b : ℕ → ℝ`, cutoff `C` and rank `R`, if
> `range a ∩ (−∞, C) = range b ∩ (−∞, C)` and `a j, b j < C` for every `j ≤ R`,
> then `a j = b j` for every `j ≤ R`.

This is the step that identifies our eigenvalue branch with the book's, and it
is deliberately abstract: no spheroidal function, no eigenvalue, no parameter
appears. Two strictly increasing sequences whose low parts enumerate the same
set of reals agree termwise as far as both stay low.

Why this is the right shape, from the same verdict. The cutoff is
`ADMISSION_ONLY` and explicitly **not** a selector: `Λ < 20` lets our branches
through but higher even branches drop below it as the parameter grows, so no
theorem may infer a rank bound from the cutoff alone. What does the selecting
is the order, and that is exactly the hypothesis used here — `a` and `b` are
strictly monotone, and nothing else about them is assumed.

In production `R = 2`: project ordinals `j = 0, 1, 2` against source degrees
`n = 2j = 0, 2, 4`. The middle ordinal carries no packet data but is
load-bearing for the order argument, which is why the statement quantifies over
all `j ≤ R` rather than over the two we consume.

LEDGER:
  CLOSES: [W13_7D_FIXED_G_ORDERED_ENUMERATION_LOCK]
  OPENS:  []
-/

/-- One direction of the lock, under the inductive hypothesis that the two
sequences already agree strictly below `j`.

If `a j` lies in the shared low part, it is some `b m`; it cannot be an earlier
one, because that would make `a j` equal to an earlier `a` value and contradict
strict monotonicity. Hence `m` is at least `j`, and monotonicity of `b` gives
the inequality. -/
private theorem le_of_agree_below
    {a b : ℕ → ℝ} (ha : StrictMono a) (hb : StrictMono b)
    {C : ℝ} {j : ℕ}
    (hsub : range a ∩ Iio C ⊆ range b ∩ Iio C)
    (hajC : a j < C)
    (hagree : ∀ i < j, a i = b i) :
    b j ≤ a j := by
  have hmem : a j ∈ range b ∩ Iio C := hsub ⟨⟨j, rfl⟩, hajC⟩
  obtain ⟨⟨m, hm⟩, _⟩ := hmem
  have hjm : j ≤ m := by
    by_contra hlt
    push_neg at hlt
    have hbm : b m = a m := (hagree m hlt).symm
    have : a j = a m := by rw [← hm, hbm]
    exact absurd (ha hlt) (by rw [this]; exact lt_irrefl _)
  calc b j ≤ b m := hb.monotone hjm
    _ = a j := hm

/-- **The lock.**  Two strictly increasing sequences whose parts below a common
cutoff enumerate the same set agree termwise as far as both stay below it.

Nothing about eigenvalues, parameters or special functions enters. -/
theorem eq_of_strictMono_of_low_range_eq
    {a b : ℕ → ℝ} (ha : StrictMono a) (hb : StrictMono b)
    {C : ℝ} {R : ℕ}
    (hrange : range a ∩ Iio C = range b ∩ Iio C)
    (haC : ∀ j ≤ R, a j < C) (hbC : ∀ j ≤ R, b j < C) :
    ∀ j ≤ R, a j = b j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjR
    have hagree : ∀ i < j, a i = b i := fun i hij =>
      ih i hij (le_trans hij.le hjR)
    have hagree' : ∀ i < j, b i = a i := fun i hij => (hagree i hij).symm
    have h1 : b j ≤ a j :=
      le_of_agree_below ha hb hrange.subset (haC j hjR) hagree
    have h2 : a j ≤ b j :=
      le_of_agree_below hb ha hrange.symm.subset (hbC j hjR) hagree'
    exact le_antisymm h2 h1

/-- The production instance, `R = 2`: the three lowest terms agree.  The middle
one is not consumed by the packet but is what makes the argument reach the
third. -/
theorem eq_of_strictMono_of_low_range_eq_rank_two
    {a b : ℕ → ℝ} (ha : StrictMono a) (hb : StrictMono b)
    {C : ℝ}
    (hrange : range a ∩ Iio C = range b ∩ Iio C)
    (haC : ∀ j ≤ 2, a j < C) (hbC : ∀ j ≤ 2, b j < C) :
    a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 := by
  have h := eq_of_strictMono_of_low_range_eq ha hb hrange haC hbC
  exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega)⟩

#print axioms le_of_agree_below
#print axioms eq_of_strictMono_of_low_range_eq
#print axioms eq_of_strictMono_of_low_range_eq_rank_two

end Q3.RouteB.D0Pstar
