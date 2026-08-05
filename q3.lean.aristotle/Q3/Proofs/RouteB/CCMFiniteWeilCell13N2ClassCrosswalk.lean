import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

/-!
# Exact antipodal class crosswalk for the CCM `(13, 2)` cell

This file proves the source identity that identifies the `(-2, 2)` and
`(-2, 0)` entries used by the seven-class enclosure layout.  The proof is
purely symbolic: it uses the literal production definitions and no numerical
certificate, interval endpoint, or reconstructed functional.
-/

namespace Q3.RouteB

open MeasureTheory

private theorem ccmQKernel_neg_self_eq_neg_zero
    (L x : ℝ) (r : ℤ) :
    ccmQKernel L (-r) r x = ccmQKernel L (-r) 0 x := by
  by_cases hr : r = 0
  · subst r
    rfl
  · have hnegSelf : -r ≠ r := by
      intro h
      apply hr
      omega
    have hnegZero : -r ≠ 0 := neg_ne_zero.mpr hr
    have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [ccmQKernel, ccmQKernel, if_neg hnegSelf, if_neg hnegZero]
    simp only [Int.cast_neg, Int.cast_zero, mul_zero, zero_mul, zero_div,
      Real.sin_zero, sub_zero]
    rw [show 2 * Real.pi * (-(r : ℝ)) * x / L =
      -(2 * Real.pi * (r : ℝ) * x / L) by ring, Real.sin_neg]
    field_simp [Real.pi_ne_zero, hrReal]
    ring

private theorem ccmW02Entry_neg_self_eq_neg_zero
    (L : ℝ) (r : ℤ) :
    ccmW02Entry L (-r) r = ccmW02Entry L (-r) 0 := by
  by_cases hr : r = 0
  · subst r
    rfl
  · by_cases hL : L = 0
    · simp [ccmW02Entry, hL]
    · have hLsq : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
      have hden :
          L ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2 ≠ 0 := by
        have hLpos : 0 < L ^ 2 := sq_pos_of_ne_zero hL
        have hterm : 0 ≤ 16 * Real.pi ^ 2 * (r : ℝ) ^ 2 := by positivity
        linarith
      unfold ccmW02Entry
      simp only [Int.cast_neg, Int.cast_zero, mul_zero, zero_mul,
        sub_zero]
      field_simp [hLsq, hden]
      ring

private theorem ccmPrimeEntryN1_neg_self_eq_neg_zero
    (mProject : ℕ) (r : ℤ) :
    ccmPrimeEntryN1 mProject (-r) r =
      ccmPrimeEntryN1 mProject (-r) 0 := by
  unfold ccmPrimeEntryN1
  apply Finset.sum_congr rfl
  intro k hk
  rw [ccmQKernel_neg_self_eq_neg_zero]

private theorem ccmWRIntegrand_neg_self_eq_neg_zero
    (L : ℝ) (r : ℤ) (x : ℝ) :
    ccmWRIntegrand L (-r) r x = ccmWRIntegrand L (-r) 0 x := by
  simp only [ccmWRIntegrand, ccmQKernel_neg_self_eq_neg_zero]

private theorem ccmWREntry_neg_self_eq_neg_zero
    (L : ℝ) (r : ℤ) :
    ccmWREntry L (-r) r = ccmWREntry L (-r) 0 := by
  unfold ccmWREntry
  rw [ccmQKernel_neg_self_eq_neg_zero]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc fun x _ =>
    ccmWRIntegrand_neg_self_eq_neg_zero L r x

/-- Exact source identity supplying the missing antipodal class crosswalk in
the seven-class layout of the CCM `(13, 2)` finite Weil cell. -/
theorem ccmWeilTauN1_neg_self_eq_neg_zero
    (mProject : ℕ) (r : ℤ) :
    ccmWeilTauN1 mProject (-r) r =
      ccmWeilTauN1 mProject (-r) 0 := by
  simp only [ccmWeilTauN1, ccmW02Entry_neg_self_eq_neg_zero,
    ccmWREntry_neg_self_eq_neg_zero,
    ccmPrimeEntryN1_neg_self_eq_neg_zero]

#print axioms ccmWeilTauN1_neg_self_eq_neg_zero

end Q3.RouteB
