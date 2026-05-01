/-
PSD form algebra for the corrected positive-definite route.

This lightweight module records the finite-form algebra behind the fallback
`PSD-pd` route without importing the heavy Q3 analytic stack:

  arch floor + prime cap + cap <= floor  ==>  arch - prime is nonnegative.

Later bridge files can instantiate `qA`, `qP`, and `qDiff` with the concrete
Rayleigh quotients coming from Q3 matrices.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option linter.mathlibStandardSet false

namespace Q3.Proofs

/-- Positive semidefiniteness for an abstract finite quadratic form. -/
def FormPSD {ι : Type*} [Zero (ι → ℝ)] (q : (ι → ℝ) → ℝ) : Prop :=
  ∀ v : ι → ℝ, v ≠ 0 → 0 ≤ q v

/-- Difference of two real forms. -/
def formDiff {ι : Type*} (qA qP : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun v => qA v - qP v

/-- One-vector domination: an Archimedean lower bound and a prime upper bound
make the difference form nonnegative when the cap is no larger than the floor. -/
lemma formDiff_nonneg_of_floor_cap {ι : Type*}
    (qA qP : (ι → ℝ) → ℝ) (v : ι → ℝ)
    {floor cap : ℝ}
    (hA : floor ≤ qA v)
    (hP : qP v ≤ cap)
    (hcap : cap ≤ floor) :
    0 ≤ formDiff qA qP v := by
  unfold formDiff
  linarith

/-- Finite PSD-pd contract: if every nonzero vector sees an Archimedean floor
and a prime cap below that floor, then the difference form is PSD. -/
theorem formPSD_diff_of_uniform_floor_cap {ι : Type*} [Zero (ι → ℝ)]
    (qA qP : (ι → ℝ) → ℝ)
    {floor cap : ℝ}
    (hA : ∀ v : ι → ℝ, v ≠ 0 → floor ≤ qA v)
    (hP : ∀ v : ι → ℝ, v ≠ 0 → qP v ≤ cap)
    (hcap : cap ≤ floor) :
    FormPSD (formDiff qA qP) := by
  intro v hv
  exact formDiff_nonneg_of_floor_cap
    (qA := qA) (qP := qP) (v := v) (hA v hv) (hP v hv) hcap

/-- Strict-margin version of `formPSD_diff_of_uniform_floor_cap`. -/
theorem formPSD_diff_of_strict_uniform_floor_cap {ι : Type*} [Zero (ι → ℝ)]
    (qA qP : (ι → ℝ) → ℝ)
    {floor cap : ℝ}
    (hA : ∀ v : ι → ℝ, v ≠ 0 → floor ≤ qA v)
    (hP : ∀ v : ι → ℝ, v ≠ 0 → qP v ≤ cap)
    (hcap : cap < floor) :
    FormPSD (formDiff qA qP) := by
  exact formPSD_diff_of_uniform_floor_cap
    (qA := qA) (qP := qP) (floor := floor) (cap := cap) hA hP (le_of_lt hcap)

/-- Uniform explicit margin form. -/
theorem formDiff_margin_of_uniform_floor_cap {ι : Type*}
    (qA qP : (ι → ℝ) → ℝ)
    {floor cap : ℝ}
    (hA : ∀ v : ι → ℝ, floor ≤ qA v)
    (hP : ∀ v : ι → ℝ, qP v ≤ cap) :
    ∀ v : ι → ℝ, floor - cap ≤ formDiff qA qP v := by
  intro v
  unfold formDiff
  linarith [hA v, hP v]

end Q3.Proofs
