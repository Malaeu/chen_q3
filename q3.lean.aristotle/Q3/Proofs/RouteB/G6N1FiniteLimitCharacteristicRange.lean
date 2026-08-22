import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierToDLMF3035EvenL2

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

namespace Q3.RouteB

/-!
# The project finite-limit carrier has exactly the low characteristic range

Floor V3.0 of verdict `a132138c` (`MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE`).

The project-side branch is `mode4ClassicalEvenEigenvalue` — the fixed-index
limit of the literal finite DLMF/Jacobi spectra, constructed independently of
the source package.  Below the cutoff its value set is exactly the solution
set of the pole-safe DLMF 30.3.5 even characteristic equation at the locked
split.  The proof is the extensional composition of two existing iff theorems
through square summability of the normalized left row:

```text
characteristic  <->  l2 left row          (L2 solution crosswalk)
l2 left row     <->  finite-limit member  (classical carrier crosswalk)
```

No source spectrum package is imported; the project branch is characterized
entirely on the project side.  `Λ < 20` is the domain guard; the weaker
`Λ ≤ 20` is passed only where the characteristic/l2 iff requires it.

LEDGER:
  CLOSES: [PROJECT_BRANCH_LOW_RANGE_PROPERTY]
  OPENS:  []
-/

/-- **V3.0.**  Below the cutoff, the range of the project finite-limit even
carrier is exactly the pole-safe DLMF 30.3.5 even characteristic solution
set at the locked split. -/
theorem mode4FiniteLimitCharacteristicRangeEquality
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    range (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject)) ∩ Iio 20
      = {Λ : ℝ | Λ < 20 ∧
          mode4DLMF3035EvenCharacteristicEquation
            (mode4JacobiG mProject) Λ (2 * (K - 1))} := by
  ext Λ
  simp only [mem_inter_iff, mem_range, mem_Iio, mem_setOf_eq]
  constructor
  · rintro ⟨⟨j, hj⟩, hcut⟩
    refine ⟨hcut, ?_⟩
    have hsum :=
      (mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_exists_finiteLimitSpectrum
        mProject K Λ hm hK hsep hcut).mpr ⟨j, hj⟩
    exact
      (mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
        mProject K Λ hm hK hsep hcut.le).mpr hsum
  · rintro ⟨hcut, hchar⟩
    have hsum :=
      (mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
        mProject K Λ hm hK hsep hcut.le).mp hchar
    obtain ⟨j, hj⟩ :=
      (mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_exists_finiteLimitSpectrum
        mProject K Λ hm hK hsep hcut).mp hsum
    exact ⟨⟨j, hj⟩, hcut⟩

#print axioms mode4FiniteLimitCharacteristicRangeEquality

end Q3.RouteB
