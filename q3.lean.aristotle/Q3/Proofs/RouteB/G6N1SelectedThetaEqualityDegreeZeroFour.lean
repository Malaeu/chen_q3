import Q3.Proofs.RouteB.G6N1BookRegularSpectrumSourceInterface
import Q3.Proofs.RouteB.G6N1OrderedEnumerationLock

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB

open Q3.RouteB.D0Pstar

/-!
# W13.7E — selected theta equality at source degrees zero and four

This composes the two pieces that are already closed:

```text
W13.7B   below the cutoff, characteristic roots = even-degree branch values
W13.7D   two strictly increasing sequences enumerating the same low set
         agree termwise as far as both stay below the cutoff
```

The project-side ordered enumeration enters as a **hypothesis**, not as a
construction, because it is not built here: the caller must supply a strictly
increasing `projectBranch` whose values below the cutoff are exactly the
characteristic roots. That is honest — it is a real obligation on the consumer,
and pretending otherwise would put an unbuilt object into a closed node.

**The cutoff is not what selects the branches.** It only lets them through;
higher even branches enter below it as the parameter grows. Selection comes from strict
order at fixed parameter, which is why the lock and not the bound does the work,
and why the middle ordinal is load-bearing even though the packet consumes only
the outer two.

LEDGER:
  CLOSES: [W13_7E_SELECTED_THETA_EQUALITY_DEGREE_ZERO_FOUR]
  OPENS:  []
-/

namespace BookRegularEvenSpectrum

variable {G : ℝ} {splitDegree : ℕ}

/-- A set carved out by a cutoff and a range is the same thing written two
ways.  Stated separately because the source interface speaks in set-builder
form and the ordered lock speaks in `range ∩ Iio` form. -/
theorem range_inter_Iio_eq_setOf (f : ℕ → ℝ) (C : ℝ) :
    range f ∩ Iio C = {Λ : ℝ | Λ < C ∧ ∃ r : ℕ, f r = Λ} := by
  ext Λ
  simp [and_comm]

/-- **W13.7E.**  A project ordered enumeration of the characteristic roots and
the even-degree source branches agree at the three lowest ordinals.

`j = 0, 1, 2` on the project side meet source degrees `0, 2, 4`. -/
theorem selected_theta_equality_rank_two
    (S : BookRegularEvenSpectrum G splitDegree)
    (projectBranch : ℕ → ℝ)
    (hproj : StrictMono projectBranch)
    (hprojRange :
      range projectBranch ∩ Iio 20 =
        {Λ : ℝ | Λ < 20 ∧
          mode4DLMF3035EvenCharacteristicEquation G Λ splitDegree})
    (hprojCut : ∀ j ≤ 2, projectBranch j < 20)
    (hsrcCut : ∀ j ≤ 2, S.branch (2 * j) < 20) :
    projectBranch 0 = S.branch 0 ∧
      projectBranch 1 = S.branch 2 ∧
      projectBranch 2 = S.branch 4 := by
  have hsrcRange :
      range (fun r : ℕ => S.branch (2 * r)) ∩ Iio 20 =
        {Λ : ℝ | Λ < 20 ∧
          mode4DLMF3035EvenCharacteristicEquation G Λ splitDegree} := by
    rw [range_inter_Iio_eq_setOf]
    exact (S.characteristic_setOf_eq_even_branch_setOf).symm
  have hrange :
      range projectBranch ∩ Iio 20 =
        range (fun r : ℕ => S.branch (2 * r)) ∩ Iio 20 := by
    rw [hprojRange, hsrcRange]
  have h :=
    eq_of_strictMono_of_low_range_eq_rank_two
      hproj S.evenBranch_strictMono hrange hprojCut hsrcCut
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The packet consumption: only degrees zero and four are carried forward.

The middle ordinal is discarded here but was required to reach the third term
of the two ordered spectra, so it cannot be dropped from the hypotheses. -/
theorem selected_theta_equality_degree_zero_four
    (S : BookRegularEvenSpectrum G splitDegree)
    (projectBranch : ℕ → ℝ)
    (hproj : StrictMono projectBranch)
    (hprojRange :
      range projectBranch ∩ Iio 20 =
        {Λ : ℝ | Λ < 20 ∧
          mode4DLMF3035EvenCharacteristicEquation G Λ splitDegree})
    (hprojCut : ∀ j ≤ 2, projectBranch j < 20)
    (hsrcCut : ∀ j ≤ 2, S.branch (2 * j) < 20) :
    projectBranch 0 = S.branch 0 ∧ projectBranch 2 = S.branch 4 := by
  obtain ⟨h0, _h2, h4⟩ :=
    selected_theta_equality_rank_two S projectBranch hproj hprojRange
      hprojCut hsrcCut
  exact ⟨h0, h4⟩

end BookRegularEvenSpectrum

#print axioms BookRegularEvenSpectrum.range_inter_Iio_eq_setOf
#print axioms BookRegularEvenSpectrum.selected_theta_equality_rank_two
#print axioms BookRegularEvenSpectrum.selected_theta_equality_degree_zero_four

end Q3.RouteB
