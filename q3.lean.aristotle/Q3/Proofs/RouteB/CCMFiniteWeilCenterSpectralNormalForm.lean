import Q3.Proofs.RouteB.CCMFiniteWeilSourceCommutator

set_option linter.mathlibStandardSet false

/-!
# Center spectral normal form of the CCM source field `beta`

`ccmBetaScalar m n = n * ccmWeilTauN1 m n 0` carries the three ledgers of the
finite explicit formula: the pole term `W02`, the archimedean term `W_R`, and
the von-Mangoldt prime term.

This file proves that at the center all three collapse onto **one** angle
variable.  The explicit factor `n` cancels against the off-diagonal `1/(pi n)`
of the CCM kernel in both the archimedean and the prime ledger, and what
remains in each is a sine transform in the same variable `2 pi * (log-length) / L`.

No estimate, no asymptotics: these are exact rewrites of the literal source
definitions.
-/

namespace Q3.RouteB

open MeasureTheory
open scoped BigOperators

section CenterEvaluation

variable (L : ℝ) (n : ℤ)

/-- At the center the CCM kernel takes its off-diagonal branch and is a pure
sine, with the whole `n`-dependence sitting in the prefactor `1/(pi n)`. -/
theorem ccmQKernel_center (hn : n ≠ 0) (x : ℝ) :
    ccmQKernel L n 0 x
      = -(Real.sin (2 * Real.pi * (n : ℝ) * x / L) / (Real.pi * (n : ℝ))) := by
  unfold ccmQKernel
  rw [if_neg hn]
  push_cast
  simp
  ring

/-- The center kernel vanishes at `x = 0`; this is what deletes the whole
Euler--Mascheroni head of the archimedean ledger. -/
theorem ccmQKernel_center_zero (hn : n ≠ 0) :
    ccmQKernel L n 0 0 = 0 := by
  rw [ccmQKernel_center L n hn]
  simp

/-- The pole ledger at the center is a single Cauchy/Poisson profile. -/
theorem ccmW02Entry_center (hL : L ≠ 0) :
    ccmW02Entry L n 0
      = 32 * L * Real.sinh (L / 4) ^ 2 / (L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  have hL2 : (0 : ℝ) < L ^ 2 := by
    rcases lt_trichotomy L 0 with h | h | h
    · nlinarith
    · exact absurd h hL
    · nlinarith
  have hden : L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≠ 0 := by positivity
  unfold ccmW02Entry
  push_cast
  field_simp
  ring

end CenterEvaluation

/-- The archimedean integrand at the center, with the explicit factor `n`
cancelled. -/
theorem ccmWRIntegrand_center (L : ℝ) (n : ℤ) (hn : n ≠ 0) (x : ℝ) :
    (n : ℝ) * ccmWRIntegrand L n 0 x
      = -(Real.exp (x / 2) * Real.sin (2 * Real.pi * (n : ℝ) * x / L))
          / (2 * Real.pi * Real.sinh x) := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.exp x - Real.exp (-x) = 2 * Real.sinh x := by
    rw [Real.sinh_eq]; ring
  unfold ccmWRIntegrand
  rw [ccmQKernel_center L n hn, ccmQKernel_center L n hn, hs]
  have h0 : Real.sin (2 * Real.pi * (n : ℝ) * 0 / L) = 0 := by simp
  rw [h0]
  have hnum :
      (n : ℝ) *
          (Real.exp (x / 2) * -(Real.sin (2 * Real.pi * (n : ℝ) * x / L) / (Real.pi * (n : ℝ)))
            - -(0 / (Real.pi * (n : ℝ))))
        = -(Real.exp (x / 2) * Real.sin (2 * Real.pi * (n : ℝ) * x / L)) / Real.pi := by
    field_simp
    ring
  rw [mul_div_assoc', hnum, div_div]
  ring_nf

/-- The archimedean ledger at the center: the Euler--Mascheroni head is gone and
what remains is a sine transform against the density `exp(x/2)/(2 sinh x)`. -/
theorem ccmWREntry_center (L : ℝ) (n : ℤ) (hn : n ≠ 0) :
    (n : ℝ) * ccmWREntry L n 0
      = -(1 / (2 * Real.pi)) *
          ∫ x in Set.Ioc (0 : ℝ) L,
            Real.exp (x / 2) * Real.sin (2 * Real.pi * (n : ℝ) * x / L) / Real.sinh x := by
  unfold ccmWREntry
  rw [ccmQKernel_center_zero L n hn]
  simp only [zero_div, zero_mul, zero_add]
  rw [← MeasureTheory.integral_const_mul]
  simp only [ccmWRIntegrand_center L n hn]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  dsimp only
  ring

/-- The prime ledger at the center: the explicit factor `n` cancels and what
remains is a sine transform against the von-Mangoldt atoms placed at the
log-lengths `log k`. -/
theorem ccmPrimeEntryN1_center (mProject : ℕ) (n : ℤ) (hn : n ≠ 0) :
    (n : ℝ) * ccmPrimeEntryN1 mProject n 0
      = -(1 / Real.pi) *
          ∑ k ∈ Finset.Icc 2 mProject,
            ArithmeticFunction.vonMangoldt k * (Real.sqrt (k : ℝ))⁻¹ *
              Real.sin (2 * Real.pi * (n : ℝ) * Real.log (k : ℝ) / ccmL mProject) := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold ccmPrimeEntryN1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ccmQKernel_center (ccmL mProject) n hn]
  field_simp

/-- **Center spectral normal form.**  The completed source field is a sine
transform in one angle variable.  The pole ledger contributes a Cauchy profile,
the archimedean ledger the absolutely continuous density `exp(x/2)/(2 sinh x)`
on `(0, L]`, and the prime ledger the von-Mangoldt atoms at `log k` — all three
against `sin(2 pi n * (·) / L)` in the *same* variable. -/
theorem ccmBetaScalar_center_spectral_normal_form
    (mProject : ℕ) (n : ℤ) (hn : n ≠ 0) (hL : ccmL mProject ≠ 0) :
    ccmBetaScalar mProject n
      = 32 * ccmL mProject * Real.sinh (ccmL mProject / 4) ^ 2 * (n : ℝ)
          / ((ccmL mProject) ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2)
        + (1 / (2 * Real.pi)) *
            (∫ x in Set.Ioc (0 : ℝ) (ccmL mProject),
              Real.exp (x / 2) * Real.sin (2 * Real.pi * (n : ℝ) * x / ccmL mProject)
                / Real.sinh x)
        + (1 / Real.pi) *
            ∑ k ∈ Finset.Icc 2 mProject,
              ArithmeticFunction.vonMangoldt k * (Real.sqrt (k : ℝ))⁻¹ *
                Real.sin (2 * Real.pi * (n : ℝ) * Real.log (k : ℝ) / ccmL mProject) := by
  have hW02 := ccmW02Entry_center (ccmL mProject) n hL
  have hWR := ccmWREntry_center (ccmL mProject) n hn
  have hPr := ccmPrimeEntryN1_center mProject n hn
  unfold ccmBetaScalar ccmWeilTauN1
  rw [mul_sub, mul_sub, hW02, hWR, hPr]
  ring

end Q3.RouteB
