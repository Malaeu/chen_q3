import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped BigOperators FourierTransform ComplexConjugate

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- Positive one-sided source prime pairing.  The complete Weil ledger
subtracts this object; the minus sign is not stored here. -/
noncomputable def sourcePrimeModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 i.m,
    ((ArithmeticFunction.vonMangoldt k *
        (Real.sqrt (k : ℝ))⁻¹ : ℝ) : ℂ) *
      (2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * Real.log (k : ℝ)) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t)

theorem sourcePrimeModePairing_eq_ccmPrimeEntryN1
    (i : PairIndex) (n r : ℤ) :
    sourcePrimeModePairing i n r =
      (Q3.RouteB.ccmPrimeEntryN1 i.m n r : ℂ) := by
  classical
  unfold sourcePrimeModePairing Q3.RouteB.ccmPrimeEntryN1
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkBounds := Finset.mem_Icc.mp hk
  have hkOne : (1 : ℝ) ≤ k := by
    exact_mod_cast (show 1 ≤ k by omega)
  have hkPos : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hkOne
  have hlogNonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkOne
  have hlogLe : Real.log (k : ℝ) ≤ L_m i := by
    change Real.log (k : ℝ) ≤ Real.log (i.m : ℝ)
    exact Real.log_le_log hkPos (by exact_mod_cast hkBounds.2)
  rw [two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    i n r (Real.log (k : ℝ)) hlogNonneg, if_pos hlogLe]
  simp only [Q3.RouteB.ccmL, L_m, logLength]
  push_cast
  ring

#print axioms sourcePrimeModePairing_eq_ccmPrimeEntryN1

end Q3.RouteB.D0Pstar
