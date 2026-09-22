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


theorem uniform_square_error_integral_tendsto (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (h : TendstoUniformlyOn f g atTop (Icc (-1:ℝ) 1)) :
    Tendsto (fun n => ∫ x in (-1:ℝ)..1, (f n x-g x)^2) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min 1 (ε/4)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hd1 : δ ≤ 1 := min_le_left _ _
  have hde : δ ≤ ε/4 := min_le_right _ _
  have he := (Metric.tendstoUniformlyOn_iff.mp h) δ hd
  filter_upwards [he] with n hn
  have hb : ‖∫ x in (-1:ℝ)..1, (f n x-g x)^2‖ ≤ δ^2*2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1:ℝ)) (b := 1) (C := δ^2) (f := fun x => (f n x-g x)^2) (by
        intro x hx
        have hx' : x ∈ Icc (-1:ℝ) 1 := by
          simp only [uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1),mem_Ioc] at hx
          exact ⟨hx.1.le,hx.2⟩
        have hh := hn x hx'
        rw [Real.dist_eq] at hh
        rw [norm_pow,Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [abs_sub_comm] using hh.le) 2)
    norm_num at hh ⊢
    exact hh
  rw [dist_zero_right]
  have hs : δ^2 ≤ δ := by nlinarith
  nlinarith
#print axioms uniform_square_error_integral_tendsto

theorem weighted_derivative_error_energy_tendsto (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => ((q+1:ℕ):ℝ)*|a q|)) :
    Tendsto (fun n => ∫ x in (-1:ℝ)..1, (1-x^2)*
      ((∑ q ∈ Finset.range n, mode4FerrersFirstDerivativeTerm a q x)-
        mode4FerrersFirstDerivativeSeries a x)^2) atTop (𝓝 0) := by
  have h := uniform_square_error_integral_tendsto _ _ (weighted_derivative_partial_sums_uniform a ha)
  convert h using 1
  funext n
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (-1:ℝ) 1 := by simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hx
  have hw : 0 ≤ 1-x^2 := by nlinarith [hx'.1,hx'.2]
  dsimp only
  rw [← mul_sub,mul_pow,Real.sq_sqrt hw]
#print axioms weighted_derivative_error_energy_tendsto


theorem weighted_derivative_continuousOn (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => ((q+1:ℕ):ℝ)*|a q|)) :
    ContinuousOn (fun x => Real.sqrt (1-x^2)*mode4FerrersFirstDerivativeSeries a x)
      (Icc (-1:ℝ) 1) := by
  have hc : ∀ q, Continuous (fun x => Real.sqrt (1-x^2)*mode4FerrersFirstDerivativeTerm a q x) := by
    intro q
    unfold mode4FerrersFirstDerivativeTerm
    fun_prop
  have h := continuousOn_tsum (fun q => (hc q).continuousOn) (ha.mul_left 4)
    (fun q x hx => by simpa [mul_assoc] using weighted_derivative_term_bound a q x hx)
  simpa only [mode4FerrersFirstDerivativeSeries,tsum_mul_left] using h

theorem weighted_derivative_error_integrable (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => ((q+1:ℕ):ℝ)*|a q|)) (n : ℕ) :
    IntervalIntegrable (fun x => (1-x^2)*
      ((∑ q ∈ Finset.range n, mode4FerrersFirstDerivativeTerm a q x)-
        mode4FerrersFirstDerivativeSeries a x)^2) MeasureTheory.volume (-1:ℝ) 1 := by
  have hc : Continuous (fun x => Real.sqrt (1-x^2)*∑ q ∈ Finset.range n,
      mode4FerrersFirstDerivativeTerm a q x) := by
    unfold mode4FerrersFirstDerivativeTerm
    fun_prop
  have hh := (hc.continuousOn.sub (weighted_derivative_continuousOn a ha)).pow 2
  have he : ContinuousOn (fun x => (1-x^2)*
      ((∑ q ∈ Finset.range n, mode4FerrersFirstDerivativeTerm a q x)-
        mode4FerrersFirstDerivativeSeries a x)^2) (Icc (-1:ℝ) 1) := by
    apply hh.congr
    intro x hx
    have hw : 0 ≤ 1-x^2 := by nlinarith [hx.1,hx.2]
    dsimp only
    rw [← mul_sub,mul_pow,Real.sq_sqrt hw]
  apply ContinuousOn.intervalIntegrable
  simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using he
#print axioms weighted_derivative_error_integrable


theorem source_partial_sums_uniform (a : ℕ → ℝ)
    (ha : Summable (fun q => |a q|)) :
    TendstoUniformlyOn (fun n x => ∑ q ∈ Finset.range n, mode4FerrersTerm a q x)
      (mode4FerrersSeries a) atTop (Icc (-1:ℝ) 1) := by
  exact tendstoUniformlyOn_tsum_nat ha (mode4FerrersTerm_norm_le_coefficientAbs a)

theorem source_form_error_tendsto (a : ℕ → ℝ)
    (ha : Summable (fun q => |a q|))
    (ha1 : Summable (fun q : ℕ => ((q+1:ℕ):ℝ)*|a q|)) :
    Tendsto (fun n =>
      (∫ x in (-1:ℝ)..1, ((∑ q ∈ Finset.range n, mode4FerrersTerm a q x)-mode4FerrersSeries a x)^2) +
      (∫ x in (-1:ℝ)..1, (1-x^2)*
        ((∑ q ∈ Finset.range n, mode4FerrersFirstDerivativeTerm a q x)-
          mode4FerrersFirstDerivativeSeries a x)^2)) atTop (𝓝 0) := by
  simpa using (uniform_square_error_integral_tendsto _ _ (source_partial_sums_uniform a ha)).add
    (weighted_derivative_error_energy_tendsto a ha1)
#print axioms source_form_error_tendsto
end Q3FerrersFormApprox
