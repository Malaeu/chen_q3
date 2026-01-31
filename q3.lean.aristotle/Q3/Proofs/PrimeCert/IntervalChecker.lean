import Mathlib

/-!
Generic helpers for interval-certificate proofs.

These lemmas isolate the summation steps needed to turn pointwise bounds into
finite/tsum bounds. They are intentionally minimal and can be reused by
pilot/grid/heat interval certificates.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

lemma finset_sum_le_sum_of_le {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → ℝ) (h : ∀ a ∈ s, f a ≤ g a) :
    s.sum f ≤ s.sum g := by
  exact Finset.sum_le_sum h

lemma tsum_le_tsum_of_le {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (h : ∀ n, f n ≤ g n) :
    (∑' n, f n) ≤ ∑' n, g n := by
  exact Summable.tsum_le_tsum h hf hg

end Q3.Proofs.PrimeCert
