import Mathlib

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Generic transfer principle:
if `f ≤ g` pointwise and both tails are summable, any upper bound for `∑ g`
immediately gives the same upper bound for `∑ f`. -/
theorem tail_bound_of_pointwise_majorant
    {f g : ℕ → ℝ} {bound : ℝ}
    (hsum_f : Summable f)
    (hsum_g : Summable g)
    (hfg : ∀ n, f n ≤ g n)
    (hbound_g : (∑' n, g n) ≤ bound) :
    (∑' n, f n) ≤ bound := by
  exact (Summable.tsum_le_tsum hfg hsum_f hsum_g).trans hbound_g

/-- Shifted-tail version of `tail_bound_of_pointwise_majorant`. -/
theorem shifted_tail_bound_of_pointwise_majorant
    (N0 : ℕ) {f g : ℕ → ℝ} {bound : ℝ}
    (hsum_f : Summable (fun n => f (n + N0)))
    (hsum_g : Summable (fun n => g (n + N0)))
    (hfg : ∀ n, f (n + N0) ≤ g (n + N0))
    (hbound_g : (∑' n, g (n + N0)) ≤ bound) :
    (∑' n, f (n + N0)) ≤ bound := by
  exact tail_bound_of_pointwise_majorant hsum_f hsum_g hfg hbound_g

end Q3.Proofs.PrimeCert

