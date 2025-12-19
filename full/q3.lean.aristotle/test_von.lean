import Mathlib

#check ArithmeticFunction.vonMangoldt_apply_prime
#check ArithmeticFunction.vonMangoldt_apply_primePow
#check ArithmeticFunction.vonMangoldt

-- Check if vonMangoldt ≤ log exists
example (n : ℕ) (hn : n ≥ 2) : ArithmeticFunction.vonMangoldt n ≤ Real.log n := by
  exact?
