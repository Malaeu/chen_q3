import Q3.Proofs.RouteB.G6N1SpheroidalCrosswalkForward
import Q3.Proofs.RouteB.G6N1SpheroidalCrosswalkReverse

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB

/-!
# The modular characteristic range equality

Floor U2.4 of verdict `68e9cd78` — the composition module
`G6N1SpheroidalCharacteristicRange` of the mandated modular interface.

Both inclusions are separately named lemmas, exactly as the floor requires:

* forward — `evenBranch_mode4DLMF3035EvenCharacteristic` (the U2.3 theorem):
  every admitted branch value below the cutoff satisfies the pole-safe
  characteristic predicate;
* reverse — `mode4DLMF3035EvenCharacteristic_mem_evenBranch` (this file,
  wrapping the ratified reverse crosswalk): every characteristic solution
  below the cutoff is a branch value.

The equality theorem composes them into the exact set identity below the
cutoff.  No mixed data structure is introduced; the composition point is a
theorem, not an inhabited object.

LEDGER:
  CLOSES: [U2_4_MODULAR_CHARACTERISTIC_RANGE_ASSEMBLY]
  OPENS:  []
-/

/-- **Reverse inclusion at the characteristic predicate.**  A pole-safe DLMF
30.3.5 even characteristic solution below the cutoff is a value of the
source-pure even branch. -/
theorem mode4DLMF3035EvenCharacteristic_mem_evenBranch
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hchar : mode4DLMF3035EvenCharacteristicEquation
      (mode4JacobiG mProject) Λ (2 * (K - 1)))
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject)) :
    ∃ r : ℕ, P.evenBranch r = Λ :=
  mode4Root_mem_evenBranch mProject K Λ hm hK hsep hΛ
    ((mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero
      mProject K Λ hm hK hsep hΛ).mp hchar) P

/-- **The modular characteristic range equality.**  Below the cutoff, the
solution set of the pole-safe DLMF 30.3.5 even characteristic equation at the
locked split is exactly the value set of the source-pure even branch. -/
theorem mode4ModularCharacteristicRangeEquality
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject)) :
    {Λ : ℝ | Λ < 20 ∧
        mode4DLMF3035EvenCharacteristicEquation
          (mode4JacobiG mProject) Λ (2 * (K - 1))}
      = {Λ : ℝ | Λ < 20 ∧ ∃ r : ℕ, P.evenBranch r = Λ} := by
  ext Λ
  constructor
  · rintro ⟨hcut, hchar⟩
    exact ⟨hcut, mode4DLMF3035EvenCharacteristic_mem_evenBranch
      mProject K Λ hm hK hsep (le_of_lt hcut) hchar P⟩
  · rintro ⟨hcut, r, hr⟩
    refine ⟨hcut, ?_⟩
    rw [← hr]
    exact evenBranch_mode4DLMF3035EvenCharacteristic mProject K r hm hK hsep P
      (by rw [hr]; exact hcut)

#print axioms mode4DLMF3035EvenCharacteristic_mem_evenBranch
#print axioms mode4ModularCharacteristicRangeEquality

end Q3.RouteB
