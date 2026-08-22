import Q3.Proofs.RouteB.G6N1SpheroidalCharacteristicRange
import Q3.Proofs.RouteB.G6N1OrderedEnumerationLock

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB

open Q3.RouteB.D0Pstar

/-!
# Selected theta equality, modular consumer

Floor U2.5 of verdict `68e9cd78`.  This replaces the frozen consumer
`G6N1SelectedThetaEqualityDegreeZeroFour` (which took the deprecated mixed
structure `BookRegularEvenSpectrum` as a hypothesis) with the mandated modular
composition: the range equality theorem
`mode4ModularCharacteristicRangeEquality` — now **proved**, not hypothesized —
feeds the already ratified strict-order lock.

The source-pure package `BookRegularEvenSpectrumEven` is rank-indexed: its
`evenBranch r` is the `r`-th regular even eigenvalue in increasing order.
Project ranks `j = 0, 1, 2` meet source ranks `0, 1, 2`; under the classical
even-degree labeling of the source family these carry degrees `0, 2, 4`, which
is what the packet's name records.  No degree field enters the statement — the
new interface carries none, and `splitDegree` is nowhere identified with a
source eigenvalue degree.

**The cutoff is not what selects the branches.**  It only lets them through;
selection comes from strict order at fixed parameter.  The middle ordinal is
discarded by the packet but remains load-bearing for reaching the third
ordered value.

LEDGER:
  CLOSES: [U2_5_SELECTED_THETA_MODULAR_CONSUMER]
  OPENS:  []
-/

/-- **Rank-two agreement, modular.**  A strictly increasing project
enumeration of the characteristic solutions below the cutoff agrees with the
source-pure even branch at the three lowest ordinals. -/
theorem selected_theta_equality_rank_two_modular
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject))
    (projectBranch : ℕ → ℝ)
    (hproj : StrictMono projectBranch)
    (hprojRange :
      range projectBranch ∩ Iio 20 =
        {Λ : ℝ | Λ < 20 ∧
          mode4DLMF3035EvenCharacteristicEquation
            (mode4JacobiG mProject) Λ (2 * (K - 1))})
    (hprojCut : ∀ j ≤ 2, projectBranch j < 20)
    (hsrcCut : ∀ j ≤ 2, P.evenBranch j < 20) :
    projectBranch 0 = P.evenBranch 0 ∧
      projectBranch 1 = P.evenBranch 1 ∧
      projectBranch 2 = P.evenBranch 2 := by
  have hsetOf : range P.evenBranch ∩ Iio 20 =
      {Λ : ℝ | Λ < 20 ∧ ∃ r : ℕ, P.evenBranch r = Λ} := by
    ext Λ
    simp [and_comm]
  have hrange : range projectBranch ∩ Iio 20 = range P.evenBranch ∩ Iio 20 := by
    rw [hprojRange, hsetOf,
      mode4ModularCharacteristicRangeEquality mProject K hm hK hsep P]
  exact eq_of_strictMono_of_low_range_eq_rank_two
    hproj P.evenBranch_strictMono hrange hprojCut hsrcCut

/-- **The packet consumption, modular.**  Only the outer two ordinals are
carried forward; the middle one was required to reach the third. -/
theorem selected_theta_equality_degree_zero_four_modular
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject))
    (projectBranch : ℕ → ℝ)
    (hproj : StrictMono projectBranch)
    (hprojRange :
      range projectBranch ∩ Iio 20 =
        {Λ : ℝ | Λ < 20 ∧
          mode4DLMF3035EvenCharacteristicEquation
            (mode4JacobiG mProject) Λ (2 * (K - 1))})
    (hprojCut : ∀ j ≤ 2, projectBranch j < 20)
    (hsrcCut : ∀ j ≤ 2, P.evenBranch j < 20) :
    projectBranch 0 = P.evenBranch 0 ∧ projectBranch 2 = P.evenBranch 2 := by
  obtain ⟨h0, _h1, h2⟩ :=
    selected_theta_equality_rank_two_modular mProject K hm hK hsep P
      projectBranch hproj hprojRange hprojCut hsrcCut
  exact ⟨h0, h2⟩

#print axioms selected_theta_equality_rank_two_modular
#print axioms selected_theta_equality_degree_zero_four_modular

end Q3.RouteB
