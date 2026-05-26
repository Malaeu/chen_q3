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
