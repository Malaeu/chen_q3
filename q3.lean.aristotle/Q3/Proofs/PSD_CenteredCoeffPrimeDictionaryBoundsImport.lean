import Q3.Proofs.PSD_CenteredCoeffDictionaryImport
import Q3.Proofs.PrimeCert.IntervalLemmas

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 800000

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDictionaryBoundsImport

open CenteredCoeffDictionaryImport

/-!
Step32M prime-dictionary bounds.

The finite-prime `P` hbox generator needs reusable Lean facts about the active
L=3 prime-power dictionary before it can emit entry certificates.  This file
proves the dictionary-level positivity facts and the generic bridge from
generated exponential bounds on `p` to bounds for `r * log p`.
-/

theorem activeL3PrimeBase_ge_two (n : PrimeShiftIndexL3) :
    2 ≤ activeL3PrimeBase n := by
  fin_cases n <;> decide

theorem activeL3PrimeBase_pos (n : PrimeShiftIndexL3) :
    0 < activeL3PrimeBase n :=
  lt_of_lt_of_le (by norm_num) (activeL3PrimeBase_ge_two n)

theorem activeL3PrimeBase_gt_one (n : PrimeShiftIndexL3) :
    1 < activeL3PrimeBase n :=
  lt_of_lt_of_le (by norm_num) (activeL3PrimeBase_ge_two n)

theorem activeL3PrimeExponent_pos (n : PrimeShiftIndexL3) :
    0 < activeL3PrimeExponent n := by
  fin_cases n <;> decide

theorem activeL3PrimeLog_pos (n : PrimeShiftIndexL3) :
    0 < Real.log (activeL3PrimeBase n : Real) := by
  exact Real.log_pos (by exact_mod_cast activeL3PrimeBase_gt_one n)

theorem activeL3PrimeShift_pos (n : PrimeShiftIndexL3) :
    0 < activeL3PrimeShift n := by
  have hexp : 0 < (activeL3PrimeExponent n : Real) := by
    exact_mod_cast activeL3PrimeExponent_pos n
  exact mul_pos hexp (activeL3PrimeLog_pos n)

theorem activeL3PrimeShift_nonneg (n : PrimeShiftIndexL3) :
    0 ≤ activeL3PrimeShift n :=
  le_of_lt (activeL3PrimeShift_pos n)

/-- Uniform lower bound strong enough for the active `ell = 0.30` support cut. -/
theorem activeL3PrimeShift_ge_three_fifths (n : PrimeShiftIndexL3) :
    (3 / 5 : Real) <= activeL3PrimeShift n := by
  have hlog2 : (3 / 5 : Real) <= Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hbase : (2 : Real) <= (activeL3PrimeBase n : Real) := by
    exact_mod_cast activeL3PrimeBase_ge_two n
  have hlog_ge :
      Real.log 2 <= Real.log (activeL3PrimeBase n : Real) := by
    exact Real.log_le_log (by norm_num) hbase
  have hexp_one :
      (1 : Real) <= (activeL3PrimeExponent n : Real) := by
    exact_mod_cast activeL3PrimeExponent_pos n
  have hlog_nonneg :
      0 <= Real.log (activeL3PrimeBase n : Real) :=
    le_of_lt (activeL3PrimeLog_pos n)
  have hscale :
      Real.log (activeL3PrimeBase n : Real) <=
        (activeL3PrimeExponent n : Real) *
          Real.log (activeL3PrimeBase n : Real) := by
    calc
      Real.log (activeL3PrimeBase n : Real)
          = (1 : Real) * Real.log (activeL3PrimeBase n : Real) := by ring
      _ <= (activeL3PrimeExponent n : Real) *
          Real.log (activeL3PrimeBase n : Real) := by
            exact mul_le_mul_of_nonneg_right hexp_one hlog_nonneg
  calc
    (3 / 5 : Real) <= Real.log 2 := hlog2
    _ <= Real.log (activeL3PrimeBase n : Real) := hlog_ge
    _ <= activeL3PrimeShift n := by
      simpa [activeL3PrimeShift] using hscale

theorem activeL3PrimeWeight_pos (n : PrimeShiftIndexL3) :
    0 < activeL3PrimeWeight n := by
  exact mul_pos (activeL3PrimeLog_pos n) (Real.exp_pos _)

theorem activeL3PrimeWeight_nonneg (n : PrimeShiftIndexL3) :
    0 ≤ activeL3PrimeWeight n :=
  le_of_lt (activeL3PrimeWeight_pos n)

theorem primaryK11PrimeShift_pos (n : PrimeShiftIndexL3) :
    0 < primaryK11PrimeShift n := by
  simpa [primaryK11PrimeShift] using activeL3PrimeShift_pos n

theorem primaryK11PrimeWeight_pos (n : PrimeShiftIndexL3) :
    0 < primaryK11PrimeWeight n := by
  simpa [primaryK11PrimeWeight] using activeL3PrimeWeight_pos n

theorem controlK9PrimeShift_pos (n : PrimeShiftIndexL3) :
    0 < controlK9PrimeShift n := by
  simpa [controlK9PrimeShift] using activeL3PrimeShift_pos n

theorem controlK9PrimeWeight_pos (n : PrimeShiftIndexL3) :
    0 < controlK9PrimeWeight n := by
  simpa [controlK9PrimeWeight] using activeL3PrimeWeight_pos n

theorem primaryK11_two_le_primeShift_div_ell (n : PrimeShiftIndexL3) :
    (2 : Real) <=
      primaryK11PrimeShift n / CenteredCoeffPayloadImport.primaryK11Ell := by
  have hell : 0 < CenteredCoeffPayloadImport.primaryK11Ell := by
    norm_num [CenteredCoeffPayloadImport.primaryK11Ell,
      CenteredCoeffPayloadImport.primaryK11EllRat]
  exact (le_div_iff₀ hell).2
    (by
      have h := activeL3PrimeShift_ge_three_fifths n
      norm_num [primaryK11PrimeShift, CenteredCoeffPayloadImport.primaryK11Ell,
        CenteredCoeffPayloadImport.primaryK11EllRat] at h ⊢
      exact h)

theorem controlK9_two_le_primeShift_div_ell (n : PrimeShiftIndexL3) :
    (2 : Real) <=
      controlK9PrimeShift n / CenteredCoeffPayloadImport.controlK9Ell := by
  have hell : 0 < CenteredCoeffPayloadImport.controlK9Ell := by
    norm_num [CenteredCoeffPayloadImport.controlK9Ell,
      CenteredCoeffPayloadImport.controlK9EllRat]
  exact (le_div_iff₀ hell).2
    (by
      have h := activeL3PrimeShift_ge_three_fifths n
      norm_num [controlK9PrimeShift, CenteredCoeffPayloadImport.controlK9Ell,
        CenteredCoeffPayloadImport.controlK9EllRat] at h ⊢
      exact h)

/-- Generated exponential lower/upper bounds for the prime base give a Lean
interval for `log p`. -/
theorem activeL3PrimeLog_bounds_of_exp_bounds
    (n : PrimeShiftIndexL3) {lo hi : Real}
    (hlo : Real.exp lo ≤ (activeL3PrimeBase n : Real))
    (hhi : (activeL3PrimeBase n : Real) ≤ Real.exp hi) :
    lo ≤ Real.log (activeL3PrimeBase n : Real) ∧
      Real.log (activeL3PrimeBase n : Real) ≤ hi := by
  exact Q3.Proofs.PrimeCert.log_nat_bounds_of_exp_bounds
    (n := activeL3PrimeBase n) (hn := activeL3PrimeBase_pos n)
    (a := lo) (b := hi) hlo hhi

/-- Bounds for `log p` scale to bounds for the active shift `r * log p`. -/
theorem activeL3PrimeShift_bounds_of_log_bounds
    (n : PrimeShiftIndexL3) {lo hi : Real}
    (hlog : lo ≤ Real.log (activeL3PrimeBase n : Real) ∧
      Real.log (activeL3PrimeBase n : Real) ≤ hi) :
    (activeL3PrimeExponent n : Real) * lo ≤ activeL3PrimeShift n ∧
      activeL3PrimeShift n ≤ (activeL3PrimeExponent n : Real) * hi := by
  have hexp_nonneg : 0 ≤ (activeL3PrimeExponent n : Real) := by positivity
  constructor
  · simpa [activeL3PrimeShift] using
      mul_le_mul_of_nonneg_left hlog.1 hexp_nonneg
  · simpa [activeL3PrimeShift] using
      mul_le_mul_of_nonneg_left hlog.2 hexp_nonneg

/-- Generated exponential lower/upper bounds for `p` directly give bounds for
the active prime-power shift `r * log p`. -/
theorem activeL3PrimeShift_bounds_of_exp_bounds
    (n : PrimeShiftIndexL3) {lo hi : Real}
    (hlo : Real.exp lo ≤ (activeL3PrimeBase n : Real))
    (hhi : (activeL3PrimeBase n : Real) ≤ Real.exp hi) :
    (activeL3PrimeExponent n : Real) * lo ≤ activeL3PrimeShift n ∧
      activeL3PrimeShift n ≤ (activeL3PrimeExponent n : Real) * hi :=
  activeL3PrimeShift_bounds_of_log_bounds n
    (activeL3PrimeLog_bounds_of_exp_bounds n hlo hhi)

end CenteredCoeffPrimeDictionaryBoundsImport
end PSDpd
end Q3
