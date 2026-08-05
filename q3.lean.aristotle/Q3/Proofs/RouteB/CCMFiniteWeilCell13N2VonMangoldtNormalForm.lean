import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2SevenClassLayout

/-!
# Exact finite von-Mangoldt normal form for the CCM cell `(13, 2)`

This file reduces the literal finite sum on `Finset.Icc 2 13` to its exact
prime-power support.  It does not unfold or enclose the CCM kernel and proves
no numerical cell bound.
-/

namespace Q3.RouteB

open ArithmeticFunction

private theorem ccmVonMangoldt_two :
    vonMangoldt 2 = Real.log 2 := by
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_three :
    vonMangoldt 3 = Real.log 3 := by
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_four :
    vonMangoldt 4 = Real.log 2 := by
  rw [show 4 = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num)]
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_five :
    vonMangoldt 5 = Real.log 5 := by
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_six :
    vonMangoldt 6 = 0 := by
  rw [vonMangoldt_apply, if_neg]
  intro h
  rw [isPrimePow_nat_iff_bounded_log_minFac] at h
  rcases h with ⟨k, hk, _hkpos, heq⟩
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem ccmVonMangoldt_seven :
    vonMangoldt 7 = Real.log 7 := by
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_eight :
    vonMangoldt 8 = Real.log 2 := by
  rw [show 8 = 2 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num)]
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_nine :
    vonMangoldt 9 = Real.log 3 := by
  rw [show 9 = 3 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num)]
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_ten :
    vonMangoldt 10 = 0 := by
  rw [vonMangoldt_apply, if_neg]
  intro h
  rw [isPrimePow_nat_iff_bounded_log_minFac] at h
  rcases h with ⟨k, hk, _hkpos, heq⟩
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem ccmVonMangoldt_eleven :
    vonMangoldt 11 = Real.log 11 := by
  exact vonMangoldt_apply_prime (by norm_num)

private theorem ccmVonMangoldt_twelve :
    vonMangoldt 12 = 0 := by
  rw [vonMangoldt_apply, if_neg]
  intro h
  rw [isPrimePow_nat_iff_bounded_log_minFac] at h
  rcases h with ⟨k, hk, _hkpos, heq⟩
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem ccmVonMangoldt_thirteen :
    vonMangoldt 13 = Real.log 13 := by
  exact vonMangoldt_apply_prime (by norm_num)

/--
The exact weighted von-Mangoldt normal form on the finite CCM range
`Finset.Icc 2 13`.
-/
theorem ccmVonMangoldt_sum_Icc_2_13 (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 2 13,
        ArithmeticFunction.vonMangoldt k * f k =
      Real.log 2 * (f 2 + f 4 + f 8) +
      Real.log 3 * (f 3 + f 9) +
      Real.log 5 * f 5 +
      Real.log 7 * f 7 +
      Real.log 11 * f 11 +
      Real.log 13 * f 13 := by
  norm_num [Finset.sum_Icc_succ_top, ccmVonMangoldt_two,
    ccmVonMangoldt_three, ccmVonMangoldt_four, ccmVonMangoldt_five,
    ccmVonMangoldt_six, ccmVonMangoldt_seven, ccmVonMangoldt_eight,
    ccmVonMangoldt_nine, ccmVonMangoldt_ten, ccmVonMangoldt_eleven,
    ccmVonMangoldt_twelve, ccmVonMangoldt_thirteen]
  ring

/- The public theorem is wired to the literal production prime entry. -/
private theorem ccmPrimeEntryN1_thirteen_normal_form (n m : ℤ) :
    ccmPrimeEntryN1 13 n m =
      Real.log 2 *
          ((Real.sqrt (2 : ℝ))⁻¹ *
              ccmQKernel (ccmL 13) n m (Real.log 2) +
           (Real.sqrt (4 : ℝ))⁻¹ *
              ccmQKernel (ccmL 13) n m (Real.log 4) +
           (Real.sqrt (8 : ℝ))⁻¹ *
              ccmQKernel (ccmL 13) n m (Real.log 8)) +
      Real.log 3 *
          ((Real.sqrt (3 : ℝ))⁻¹ *
              ccmQKernel (ccmL 13) n m (Real.log 3) +
           (Real.sqrt (9 : ℝ))⁻¹ *
              ccmQKernel (ccmL 13) n m (Real.log 9)) +
      Real.log 5 * ((Real.sqrt (5 : ℝ))⁻¹ *
        ccmQKernel (ccmL 13) n m (Real.log 5)) +
      Real.log 7 * ((Real.sqrt (7 : ℝ))⁻¹ *
        ccmQKernel (ccmL 13) n m (Real.log 7)) +
      Real.log 11 * ((Real.sqrt (11 : ℝ))⁻¹ *
        ccmQKernel (ccmL 13) n m (Real.log 11)) +
      Real.log 13 * ((Real.sqrt (13 : ℝ))⁻¹ *
        ccmQKernel (ccmL 13) n m (Real.log 13)) := by
  unfold ccmPrimeEntryN1
  simpa [mul_assoc] using ccmVonMangoldt_sum_Icc_2_13 (fun k =>
    (Real.sqrt (k : ℝ))⁻¹ *
      ccmQKernel (ccmL 13) n m (Real.log (k : ℝ)))

/- P-VM-1: the prime-power support at `8` contributes `log 2`. -/
private theorem ccmVonMangoldt_plant_delta_eight :
    ∑ k ∈ Finset.Icc 2 13,
        ArithmeticFunction.vonMangoldt k * (if k = 8 then 1 else 0 : ℝ) =
      Real.log 2 := by
  rw [ccmVonMangoldt_sum_Icc_2_13]
  norm_num

/- P-VM-2: the unsupported value `6` contributes exactly zero. -/
private theorem ccmVonMangoldt_plant_delta_six :
    ∑ k ∈ Finset.Icc 2 13,
        ArithmeticFunction.vonMangoldt k * (if k = 6 then 1 else 0 : ℝ) =
      0 := by
  rw [ccmVonMangoldt_sum_Icc_2_13]
  norm_num

/- P-VM-3: `3` and `9` have equal, not exponent-weighted, coefficients. -/
private theorem ccmVonMangoldt_plant_three_sub_nine :
    ∑ k ∈ Finset.Icc 2 13,
        ArithmeticFunction.vonMangoldt k *
          (if k = 3 then 1 else if k = 9 then -1 else 0 : ℝ) =
      0 := by
  rw [ccmVonMangoldt_sum_Icc_2_13]
  norm_num

#print axioms ccmVonMangoldt_sum_Icc_2_13

end Q3.RouteB
