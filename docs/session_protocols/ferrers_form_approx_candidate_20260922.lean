import Mathlib
import Q3.Proofs.RouteB.D0Mode4FerrersRegularEvenProlateSolution
open Set Filter
open scoped Topology
noncomputable section
namespace Q3FerrersFormApprox
open Q3.RouteB

theorem weighted_derivative_term_bound (a : ℕ → ℝ) (q : ℕ) (x : ℝ)
    (hx : x ∈ Icc (-1:ℝ) 1) :
    ‖Real.sqrt (1-x^2)*mode4FerrersFirstDerivativeTerm a q x‖ ≤
      4*((q+1:ℕ):ℝ)*|a q| := by
  let d := (mode4OrdinaryLegendrePolynomial (2*q)).derivative.eval x
  let N : ℝ := ((2*q:ℕ):ℝ)*(((2*q:ℕ):ℝ)+1)
  have hw : 0 ≤ 1-x^2 := by nlinarith [hx.1,hx.2]
  have he := mode4OrdinaryLegendreEnergyPolynomial_eval_le_endpoint (2*q) x hx
  simp only [mode4OrdinaryLegendreEnergyPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at he
  have hp : 0 ≤ N*(mode4OrdinaryLegendrePolynomial (2*q)).eval x ^ 2 := by
    dsimp [N]; positivity
  have hd : (1-x^2)*d^2 ≤ N := by dsimp [d,N] at *; nlinarith
  have hs : (Real.sqrt (1-x^2)*d)^2 ≤ N := by
    rw [mul_pow,Real.sq_sqrt hw]; exact hd
  have hn : N ≤ (4*((q+1:ℕ):ℝ))^2 := by
    dsimp [N]; push_cast; nlinarith [sq_nonneg (q:ℝ)]
  have hab : |Real.sqrt (1-x^2)*d| ≤ 4*((q+1:ℕ):ℝ) := by
    have hh : 0 ≤ 4*((q+1:ℕ):ℝ) := by positivity
    nlinarith [sq_abs (Real.sqrt (1-x^2)*d),abs_nonneg (Real.sqrt (1-x^2)*d)]
  calc
    ‖Real.sqrt (1-x^2)*mode4FerrersFirstDerivativeTerm a q x‖ =
      |a q| *|Real.sqrt (1-x^2)*d| := by
        simp only [mode4FerrersFirstDerivativeTerm,Real.norm_eq_abs,abs_mul,abs_pow,abs_neg,abs_one,one_pow]
        dsimp [d]; ring
    _ ≤ |a q| *(4*((q+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    _ = _ := by ring

theorem weighted_derivative_partial_sums_uniform (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => ((q+1:ℕ):ℝ)*|a q|)) :
    TendstoUniformlyOn
      (fun n x => Real.sqrt (1-x^2)*∑ q ∈ Finset.range n, mode4FerrersFirstDerivativeTerm a q x)
      (fun x => Real.sqrt (1-x^2)*mode4FerrersFirstDerivativeSeries a x)
      atTop (Icc (-1:ℝ) 1) := by
  have h := tendstoUniformlyOn_tsum_nat (ha.mul_left 4)
    (f := fun q x => Real.sqrt (1-x^2)*mode4FerrersFirstDerivativeTerm a q x)
    (fun q x hx => by simpa [mul_assoc] using weighted_derivative_term_bound a q x hx)
  simpa only [mode4FerrersFirstDerivativeSeries,Finset.mul_sum,tsum_mul_left,mul_assoc] using h
#print axioms weighted_derivative_partial_sums_uniform


theorem actual_source_weighted_derivative_partial_sums_uniform
    {m K : ℕ} {Λ : ℝ} (S : Mode4FerrersRegularEvenProlateSolution m K Λ)
    (hm : 2 ≤ m) (hK : 3 ≤ K)
    (hsep : ∀ q ≥ K, (31/24:ℝ)*mode4JacobiG m ≤
      mode4JacobiIndex q*(mode4JacobiIndex q+1)-20)
    (hΛ : Λ ≤ 20) :
    TendstoUniformlyOn
      (fun n x => Real.sqrt (1-x^2)*∑ q ∈ Finset.range n,
        mode4FerrersFirstDerivativeTerm S.coefficients q x)
      (fun x => Real.sqrt (1-x^2)*mode4FerrersFirstDerivativeSeries S.coefficients x)
      atTop (Icc (-1:ℝ) 1) := by
  apply weighted_derivative_partial_sums_uniform
  simpa using mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
    m K Λ hm hK hsep hΛ S.coefficients S.tail_splice 1
#print axioms actual_source_weighted_derivative_partial_sums_uniform
end Q3FerrersFormApprox
