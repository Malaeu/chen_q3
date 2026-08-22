import Q3.Proofs.RouteB.G6N1FiniteLimitCharacteristicRange
import Q3.Proofs.RouteB.G6N1SpheroidalCharacteristicRange
import Q3.Proofs.RouteB.G6N1CutoffLocalOrderedEnumerationLock

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set
open Q3.RouteB.D0Pstar

namespace Q3.RouteB

/-!
# The finite-limit / source selected-theta modular bind

Floor V3.2 of verdict `8fd8ab3f` (`FINITE_LIMIT_SELECTED_THETA_MODULAR_BIND`).
The last two apparent obligations of the ordering front — a strictly
increasing project enumeration and a numeric cutoff bound — collapse to one
exact production bind, universal in the source package `P`:

```text
V3.0   range(mode4ClassicalEvenEigenvalue G) ∩ Iio 20 = characteristic ∩ Iio 20
U2.4   characteristic ∩ Iio 20                        = range(P.evenBranch) ∩ Iio 20
------------------------------------------------------------------------------
       range(mode4ClassicalEvenEigenvalue G) ∩ Iio 20 = range(P.evenBranch) ∩ Iio 20
```

fed into the cutoff-local order lock (V3.1) with the project's own local
strictness and head cutoff, both already kernel-proved and imported here as
suppliers — not reproved.  `P` is never instantiated: any source package
agrees with the same independently constructed project carrier through rank
two.  `projectBranch := P.evenBranch` is not defined anywhere in this file.

LEDGER:
  CLOSES: [PROJECT_BRANCH_INHABITANT, SOURCE_RANK_TWO_CUTOFF,
           W13_7_SELECTED_THETA_EQUALITY_DEGREE_ZERO_FOUR]
  OPENS:  []
-/

/-- **V3.2, full rank-two bundle.**  The project finite-limit carrier and any
source-pure even branch agree through rank two, and the agreeing value is
below the cutoff — the source cutoff is derived, not assumed. -/
theorem finiteLimit_source_evenBranch_agree_through_rank_two
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject)) :
    ∀ j ≤ 2,
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) j =
          P.evenBranch j ∧
        P.evenBranch j < 20 := by
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG; positivity
  have hsetOf : range P.evenBranch ∩ Iio 20 =
      {Λ : ℝ | Λ < 20 ∧ ∃ r : ℕ, P.evenBranch r = Λ} := by
    ext Λ
    simp [and_comm]
  have hrange : range (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject)) ∩ Iio 20
      = range P.evenBranch ∩ Iio 20 := by
    rw [hsetOf,
      mode4FiniteLimitCharacteristicRangeEquality mProject K hm hK hsep,
      mode4ModularCharacteristicRangeEquality mProject K hm hK hsep P]
  have haLocal : ∀ {i j : ℕ}, i < j →
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) j < 20 →
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) i <
        mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) j := by
    intro i j hij hj20
    exact mode4ClassicalEvenEigenvalue_lt_of_index_lt_of_upper_lt_twenty
      mProject K i j hm hK hsep hij hj20
  have haCut : ∀ j ≤ 2, mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) j < 20 := by
    intro j hj
    exact mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three
      (mode4JacobiG mProject) hG j (by omega)
  exact eq_of_cutoffLocalStrictMono_of_low_range_eq
    P.evenBranch_strictMono haLocal hrange haCut

/-- **The packet consumption.**  Only the outer two ordinals — the ones the
degree-zero/degree-four consumer needs. -/
theorem finiteLimit_selected_theta_equality_degree_zero_four_modular
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject)) :
    mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0 =
        P.evenBranch 0 ∧
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 =
        P.evenBranch 2 := by
  have hall := finiteLimit_source_evenBranch_agree_through_rank_two
    mProject K hm hK hsep P
  exact ⟨(hall 0 (by omega)).1, (hall 2 (by omega)).1⟩

#print axioms finiteLimit_source_evenBranch_agree_through_rank_two
#print axioms finiteLimit_selected_theta_equality_degree_zero_four_modular

end Q3.RouteB
