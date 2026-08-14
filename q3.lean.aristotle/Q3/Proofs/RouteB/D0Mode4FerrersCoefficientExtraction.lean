import Q3.Proofs.RouteB.D0Mode4FerrersRegularEvenProlateSolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Goal 058 G3: mode-four Ferrers coefficient extraction

The zeroth coefficient of an absolutely summable even Ferrers series is
recovered by integration on the source interval.  This is sufficient to turn
the normalized positive zeroth coefficient into function nontriviality.
-/

open MeasureTheory Polynomial Set

namespace Q3.RouteB

/-- Every positive-degree ordinary Legendre polynomial has zero mean on the
source interval.  The proof integrates the exact polynomial ODE in divergence
form; no orthogonality theorem is assumed. -/
theorem mode4OrdinaryLegendre_intervalIntegral_eq_zero_of_pos
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (-1 : ℝ)..1, mode4OrdinaryLegendre n x) = 0 := by
  let p : ℝ[X] := mode4OrdinaryLegendrePolynomial n
  let fluxPoly : ℝ[X] := (1 - X ^ 2) * p.derivative
  have hfluxDerivative :
      fluxPoly.derivative =
        -C ((n : ℝ) * (n + 1)) * p := by
    have hODE :
        (1 - X ^ 2) * p.derivative.derivative -
              2 * X * p.derivative +
            C ((n : ℝ) * (n + 1)) * p = 0 := by
      simpa [p] using
        mode4OrdinaryLegendrePolynomial_differentialEquation n
    calc
      fluxPoly.derivative =
          (1 - X ^ 2) * p.derivative.derivative -
            2 * X * p.derivative := by
        dsimp [fluxPoly]
        rw [Polynomial.derivative_mul, Polynomial.derivative_sub,
          Polynomial.derivative_one, Polynomial.derivative_pow]
        norm_num
        have hCtwo : (C (2 : ℝ) : ℝ[X]) = 2 :=
          Polynomial.C_ofNat 2
        rw [hCtwo]
        ring
      _ = -C ((n : ℝ) * (n + 1)) * p := by
        linear_combination hODE
  have hderiv :
      deriv (fun x : ℝ => fluxPoly.eval x) =
        fun x : ℝ =>
          -((n : ℝ) * (n + 1)) *
            mode4OrdinaryLegendre n x := by
    funext x
    have hp := fluxPoly.hasDerivAt x
    rw [hfluxDerivative] at hp
    simpa [p, mode4OrdinaryLegendre] using hp.deriv
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ => fluxPoly.eval x)
    hderiv
    (fun x _ => fluxPoly.differentiableAt)
    (by
      simpa [mode4OrdinaryLegendre] using
        ((continuous_const.mul
          (mode4OrdinaryLegendrePolynomial n).continuous).neg).continuousOn)
  have hzero :
      (∫ x in (-1 : ℝ)..1,
        -((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendre n x) = 0 := by
    simpa [fluxPoly, p] using hftc
  rw [intervalIntegral.integral_const_mul] at hzero
  have hc : 0 < (n : ℝ) * (n + 1) := by
    positivity
  nlinarith

/-- The zeroth Ferrers coefficient is recovered by the interval mean. -/
theorem mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
    (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => |a q|)) :
    (∫ x in (-1 : ℝ)..1, mode4FerrersSeries a x) = 2 * a 0 := by
  have htermInt : ∀ q : ℕ,
      Integrable
        (fun x : ℝ => mode4FerrersTerm a q x)
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
    intro q
    change IntegrableOn
      (fun x : ℝ => mode4FerrersTerm a q x)
      (Set.Ioc (-1 : ℝ) 1)
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    unfold mode4FerrersTerm
    exact
      (continuous_const.mul
        (mode4OrdinaryLegendrePolynomial (2 * q)).continuous).intervalIntegrable
          (-1) 1
  have hnormSum : Summable (fun q : ℕ =>
      ∫ x in Set.Ioc (-1 : ℝ) 1,
        ‖mode4FerrersTerm a q x‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun q : ℕ => 2 * |a q|) ?_ ?_ ?_
    · intro q
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro q
      have hbound := norm_setIntegral_le_of_norm_le_const
        (μ := volume)
        (f := fun x : ℝ => ‖mode4FerrersTerm a q x‖)
        (s := Set.Ioc (-1 : ℝ) 1)
        (C := |a q|)
        (by simp)
        (fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact mode4FerrersTerm_norm_le_coefficientAbs a q x
            ⟨le_of_lt hx.1, hx.2⟩)
      have hnonneg :
          0 ≤ ∫ x in Set.Ioc (-1 : ℝ) 1,
            ‖mode4FerrersTerm a q x‖ :=
        integral_nonneg (fun _ => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
      norm_num at hbound ⊢
      nlinarith
    · simpa only [mul_comm] using ha.mul_left 2
  have hswap :=
    MeasureTheory.integral_tsum_of_summable_integral_norm htermInt hnormSum
  have hswap' :
      (∑' q : ℕ,
        ∫ x in (-1 : ℝ)..1, mode4FerrersTerm a q x) =
        ∫ x in (-1 : ℝ)..1, mode4FerrersSeries a x := by
    simpa only [intervalIntegral.integral_of_le
      (by norm_num : (-1 : ℝ) ≤ 1), mode4FerrersSeries] using hswap
  rw [← hswap']
  calc
    (∑' q : ℕ,
        ∫ x in (-1 : ℝ)..1, mode4FerrersTerm a q x) =
        ∫ x in (-1 : ℝ)..1, mode4FerrersTerm a 0 x := by
      apply tsum_eq_single 0
      intro q hq
      have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      unfold mode4FerrersTerm
      rw [intervalIntegral.integral_const_mul]
      rw [mode4OrdinaryLegendre_intervalIntegral_eq_zero_of_pos
        (2 * q) (by omega)]
      ring
    _ = 2 * a 0 := by
      norm_num [mode4FerrersTerm]

/-- A nonzero zeroth coefficient forces the Ferrers series itself to be a
nonzero function. -/
theorem mode4FerrersSeries_ne_zero_of_coefficient_zero_ne_zero
    (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => |a q|))
    (ha0 : a 0 ≠ 0) :
    mode4FerrersSeries a ≠ 0 := by
  intro hzero
  have hmean :=
    mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero a ha
  have hleft :
      (∫ x in (-1 : ℝ)..1, mode4FerrersSeries a x) = 0 := by
    simp [hzero]
  rw [hleft] at hmean
  exact ha0 (by linarith)

/-- The accepted regular-even assembly object is functionally nontrivial. -/
theorem Mode4FerrersRegularEvenProlateSolution.ferrersSeries_ne_zero
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    mode4FerrersSeries S.coefficients ≠ 0 :=
  mode4FerrersSeries_ne_zero_of_coefficient_zero_ne_zero
    S.coefficients S.coefficients_abs_summable
    (ne_of_gt S.coefficient_zero_pos)

#print axioms mode4OrdinaryLegendre_intervalIntegral_eq_zero_of_pos
#print axioms mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
#print axioms mode4FerrersSeries_ne_zero_of_coefficient_zero_ne_zero
#print axioms Mode4FerrersRegularEvenProlateSolution.ferrersSeries_ne_zero

end Q3.RouteB
