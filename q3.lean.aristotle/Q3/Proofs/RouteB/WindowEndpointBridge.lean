import Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- Changing a finite positive window from closed to open endpoints does not
change its set integral.

The local-integrability and positivity/order hypotheses reproduce the future
Müntz-port interface.  The equality itself is stronger: Lebesgue volume is
atomless, so the two endpoint values never contribute.
-/
theorem windowIntegral_Icc_eq_Ioo
    (f : ℝ → ℂ)
    (_hf : LocallyIntegrable f)
    {A B : ℝ}
    (_hA : 0 < A)
    (_hAB : A < B) :
    (∫ u : ℝ in Icc A B, f u) = ∫ u : ℝ in Ioo A B, f u := by
  exact integral_Icc_eq_integral_Ioo

/-- The cloud scalar-first Mellin convention agrees with Mathlib's
vector-valued `mellin` convention for complex-valued functions.
-/
theorem integral_mul_cpow_eq_mellin
    (k : ℝ → ℂ)
    (s : ℂ) :
    (∫ u : ℝ in Ioi 0, k u * (u : ℂ) ^ (s - 1)) = mellin k s := by
  simp only [mellin, smul_eq_mul, mul_comm]

#print axioms windowIntegral_Icc_eq_Ioo
#print axioms integral_mul_cpow_eq_mellin

end Q3.RouteB.D0Pstar
