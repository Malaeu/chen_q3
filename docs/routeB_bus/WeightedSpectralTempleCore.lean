import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators

noncomputable section

namespace Q3.RouteB

/-- A probability-weighted spectral mean is nonnegative after shifting the
ground level to zero and placing every complementary level above a
nonnegative gap. -/
theorem weighted_rayleigh_excess_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ground : ι) (weight level : ι → ℝ) (alpha gap : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hground : level ground = 0)
    (hgap_nonneg : 0 ≤ gap)
    (hgap : ∀ i, i ≠ ground → gap ≤ level i)
    (halpha : alpha = ∑ i, weight i * level i) :
    0 ≤ alpha := by
  rw [halpha]
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (hweight i)
  by_cases hig : i = ground
  · subst i
    rw [hground]
  · exact hgap_nonneg.trans (hgap i hig)

theorem weighted_residual_sq_ge_rayleigh_excess_mul_gap_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ground : ι) (weight level : ι → ℝ) (alpha etaSq gap : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1)
    (hground : level ground = 0)
    (hgap_nonneg : 0 ≤ gap)
    (hgap : ∀ i, i ≠ ground → gap ≤ level i)
    (halpha : alpha = ∑ i, weight i * level i)
    (hetaSq : etaSq = ∑ i, weight i * (level i - alpha) ^ 2) :
    alpha * (gap - alpha) ≤ etaSq := by
  have hlevel_sq : ∀ i, gap * level i ≤ (level i) ^ 2 := by
    intro i
    by_cases hi : i = ground
    · subst i
      rw [hground]
      norm_num
    · have hgi := hgap i hi
      nlinarith
  have hsecond : gap * alpha ≤ ∑ i, weight i * (level i) ^ 2 := by
    rw [halpha, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      gap * (weight i * level i) = weight i * (gap * level i) := by ring
      _ ≤ weight i * (level i) ^ 2 :=
        mul_le_mul_of_nonneg_left (hlevel_sq i) (hweight i)
  have hvariance : etaSq = (∑ i, weight i * (level i) ^ 2) - alpha ^ 2 := by
    rw [hetaSq]
    calc
      (∑ i, weight i * (level i - alpha) ^ 2) =
          ∑ i, (weight i * (level i) ^ 2 -
            2 * alpha * (weight i * level i) + alpha ^ 2 * weight i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i, weight i * (level i) ^ 2) -
          2 * alpha * (∑ i, weight i * level i) +
          alpha ^ 2 * (∑ i, weight i) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [Finset.mul_sum, Finset.mul_sum]
      _ = (∑ i, weight i * (level i) ^ 2) - alpha ^ 2 := by
              rw [← halpha, hweight_sum]
              ring
  rw [hvariance]
  nlinarith

/-- The exact Temple denominator is the distance from the Rayleigh center to
the complementary spectral floor. -/
theorem rayleigh_excess_le_residual_sq_div_gap_sub
    {alpha etaSq gap : ℝ}
    (hmain : alpha * (gap - alpha) ≤ etaSq)
    (hcenter : alpha < gap) :
    alpha ≤ etaSq / (gap - alpha) := by
  exact (le_div_iff₀ (sub_pos.mpr hcenter)).2 hmain

/-- On the certified half-gap locus, the exact Temple denominator yields the
safe polynomial upper bound used by the quantitative Route B contract. -/
theorem rayleigh_excess_le_two_mul_residual_sq_div_gap
    {alpha etaSq gap : ℝ}
    (halpha : 0 ≤ alpha)
    (hgap : 0 < gap)
    (hhalf : 2 * alpha ≤ gap)
    (hmain : alpha * (gap - alpha) ≤ etaSq) :
    alpha ≤ 2 * etaSq / gap := by
  apply (le_div_iff₀ hgap).2
  have hprod : 0 ≤ alpha * (gap - 2 * alpha) :=
    mul_nonneg halpha (sub_nonneg.mpr hhalf)
  nlinarith

#print axioms weighted_rayleigh_excess_nonneg
#print axioms weighted_residual_sq_ge_rayleigh_excess_mul_gap_sub
#print axioms rayleigh_excess_le_residual_sq_div_gap_sub
#print axioms rayleigh_excess_le_two_mul_residual_sq_div_gap

end Q3.RouteB
