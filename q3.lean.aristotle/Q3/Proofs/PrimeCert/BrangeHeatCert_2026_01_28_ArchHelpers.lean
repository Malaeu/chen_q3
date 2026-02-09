import Mathlib

noncomputable section

namespace Q3.Proofs.PrimeCert

lemma finset_sup'_le_sum_abs {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    s.sup' hs f ≤ ∑ i ∈ s, |f i| := by
  refine Finset.sup'_le (s := s) (f := f) hs ?_
  intro i hi
  calc
    f i ≤ |f i| := le_abs_self (f i)
    _ ≤ ∑ j ∈ s, |f j| := by
      exact Finset.single_le_sum (fun j hj => abs_nonneg (f j)) hi

lemma finset_exp_sup'_le_sum_exp {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    Real.exp (s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (f i) := by
  rcases Finset.exists_mem_eq_sup' hs f with ⟨i, hi, hsup⟩
  calc
    Real.exp (s.sup' hs f) = Real.exp (f i) := by simpa [hsup]
    _ ≤ ∑ j ∈ s, Real.exp (f j) := by
      exact Finset.single_le_sum (fun j hj => Real.exp_nonneg (f j)) hi

lemma finset_exp_mul_sup'_le_sum_exp {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c : ℝ) (f : ι → ℝ) :
    Real.exp (s.sup' hs (fun i => c * f i)) ≤
      ∑ i ∈ s, Real.exp (c * f i) := by
  rcases Finset.exists_mem_eq_sup' hs (fun i => c * f i) with ⟨i, hi, hsup⟩
  calc
    Real.exp (s.sup' hs (fun i => c * f i)) = Real.exp (c * f i) := by
      simpa [hsup]
    _ ≤ ∑ j ∈ s, Real.exp (c * f j) := by
      exact Finset.single_le_sum (fun j hj => Real.exp_nonneg (c * f j)) hi

lemma integral_Icc_mul_const_le {a b c M : ℝ} {f : ℝ → ℝ}
    (hc : 0 ≤ c)
    (h : ∫ x in Set.Icc a b, f x ≤ M) :
    ∫ x in Set.Icc a b, f x * c ≤ M * c := by
  have hmul := mul_le_mul_of_nonneg_right h hc
  simpa [MeasureTheory.integral_mul_const] using hmul

end Q3.Proofs.PrimeCert
