import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open MeasureTheory intervalIntegral

namespace Q3.RouteB.D0Pstar

/-!
# The subcritical weighted integral of the derived pointwise rate

The judge's `DERIVED_MAIN_ERROR_RATE` (verdict `17720ac1`) takes the pointwise
main error `C · λ⁻¹ · exp (−t/2)` on the window `[−log λ, log λ]` and derives

```text
weighted integral ≤ C · ( λ^(−1/2+σ) / (1/2+σ)  +  λ^(−1) / (1/2−σ) )
```

for each fixed `0 ≤ σ < 1/2`. This file proves that calculus outright. It is
unconditional: nothing about the source, the rate hypothesis, or L73.2 enters.
What L73.2 must eventually supply is the **pointwise** rate; the passage from
the pointwise rate to the weighted bound is closed here.

The two sides of the window behave differently and are kept separate:

* on `[0, L]` the weight loses to the decay, the exponent is `−(1/2−σ)`, and
  the integral is bounded by `1/(1/2−σ)` uniformly in `L`;
* on `[−L, 0]` the weight and the growth of `exp(−t/2)` compound, the exponent
  is `−(1/2+σ)`, and the integral grows like `exp((1/2+σ)L)/(1/2+σ)` — this is
  the term that the outer factor `λ⁻¹` must beat, and after multiplication it
  becomes `λ^(σ−1/2)`, vanishing precisely because `σ < 1/2`.

The final bound tends to zero for each fixed `σ < 1/2` and is not uniform as
`σ → 1/2`; the verdict states the consumer accepts exactly that.

LEDGER:
  CLOSES: []
  OPENS:  []
-/

/-- Antiderivative of the decaying exponential. -/
private theorem hasDerivAt_neg_inv_mul_exp (c t : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun s : ℝ => -(1 / c) * Real.exp (-(c * s)))
      (Real.exp (-(c * t))) t := by
  have h0 : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using HasDerivAt.const_mul c (hasDerivAt_id t)
  have h1 : HasDerivAt (fun s : ℝ => -(c * s)) (-c) t := h0.neg
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(c * s)))
      (Real.exp (-(c * t)) * -c) t := h1.exp
  have h3 := HasDerivAt.const_mul (-(1 / c)) h2
  convert h3 using 1
  field_simp

/-- The exact value of the exponential integral on any interval. -/
private theorem integral_exp_neg_mul (c a b : ℝ) (hc : c ≠ 0) :
    (∫ t in a..b, Real.exp (-(c * t))) =
      -(1 / c) * Real.exp (-(c * b)) + (1 / c) * Real.exp (-(c * a)) := by
  have h :=
    integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => -(1 / c) * Real.exp (-(c * s)))
      (f' := fun s : ℝ => Real.exp (-(c * s)))
      (fun t _ => hasDerivAt_neg_inv_mul_exp c t hc)
      ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable a b)
  rw [h]; ring

/-- **The favourable side.**  On `[0, L]` the integral is bounded by `1/c`
uniformly in `L`. -/
theorem integral_exp_neg_mul_Icc_le (c L : ℝ) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..L, Real.exp (-(c * t))) ≤ 1 / c := by
  rw [integral_exp_neg_mul c 0 L hc.ne']
  have h0 : -(c * 0) = (0 : ℝ) := by ring
  rw [h0, Real.exp_zero]
  have hexp : 0 ≤ Real.exp (-(c * L)) := Real.exp_nonneg _
  have hinv : 0 ≤ 1 / c := by positivity
  nlinarith [mul_nonneg hinv hexp]

/-- **The compounding side.**  On `[−L, 0]` the integral is bounded by
`exp (c L) / c`; the growth is real and is not hidden. -/
theorem integral_exp_neg_mul_neg_Icc_le (c L : ℝ) (hc : 0 < c) :
    (∫ t in (-L)..(0 : ℝ), Real.exp (-(c * t))) ≤ Real.exp (c * L) / c := by
  rw [integral_exp_neg_mul c (-L) 0 hc.ne']
  have h1 : -(c * 0) = (0 : ℝ) := by ring
  have h2 : -(c * -L) = c * L := by ring
  rw [h1, h2, Real.exp_zero]
  have hinv : 0 < 1 / c := by positivity
  have hdiv : Real.exp (c * L) / c = 1 / c * Real.exp (c * L) := by ring
  rw [hdiv]
  linarith [hinv.le]

/-- **The two-sided weighted bound.**  For `0 ≤ σ < 1/2` and any window
half-length `L ≥ 0`,

`∫_{−L}^{L} exp(−t/2) · exp(σ|t|) dt ≤ exp((1/2+σ)L)/(1/2+σ) + 1/(1/2−σ)`. -/
theorem integral_exp_half_weight_le
    (σ L : ℝ) (hσ0 : 0 ≤ σ) (hσh : σ < 1 / 2) (hL : 0 ≤ L) :
    (∫ t in (-L)..L, Real.exp (-t / 2) * Real.exp (σ * |t|)) ≤
      Real.exp ((1 / 2 + σ) * L) / (1 / 2 + σ) + 1 / (1 / 2 - σ) := by
  have hcont :
      Continuous fun t : ℝ => Real.exp (-t / 2) * Real.exp (σ * |t|) := by
    fun_prop
  have hsplit :
      (∫ t in (-L)..L, Real.exp (-t / 2) * Real.exp (σ * |t|)) =
        (∫ t in (-L)..(0 : ℝ), Real.exp (-t / 2) * Real.exp (σ * |t|)) +
          ∫ t in (0 : ℝ)..L, Real.exp (-t / 2) * Real.exp (σ * |t|) :=
    (integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  -- on [−L, 0] the weight uses |t| = −t and the exponents compound
  have hneg :
      (∫ t in (-L)..(0 : ℝ), Real.exp (-t / 2) * Real.exp (σ * |t|)) =
        ∫ t in (-L)..(0 : ℝ), Real.exp (-((1 / 2 + σ) * t)) := by
    refine integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -L ≤ (0 : ℝ))] at ht
    have habs : |t| = -t := abs_of_nonpos ht.2
    dsimp only
    rw [habs, ← Real.exp_add]
    congr 1
    ring
  -- on [0, L] the weight uses |t| = t and the decay wins
  have hpos :
      (∫ t in (0 : ℝ)..L, Real.exp (-t / 2) * Real.exp (σ * |t|)) =
        ∫ t in (0 : ℝ)..L, Real.exp (-((1 / 2 - σ) * t)) := by
    refine integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hL] at ht
    have habs : |t| = t := abs_of_nonneg ht.1
    dsimp only
    rw [habs, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit, hneg, hpos]
  have hb : (0 : ℝ) < 1 / 2 + σ := by linarith
  have ha : (0 : ℝ) < 1 / 2 - σ := by linarith
  have h1 := integral_exp_neg_mul_neg_Icc_le (1 / 2 + σ) L hb
  have h2 := integral_exp_neg_mul_Icc_le (1 / 2 - σ) L ha
  calc
    (∫ t in (-L)..(0 : ℝ), Real.exp (-((1 / 2 + σ) * t))) +
        ∫ t in (0 : ℝ)..L, Real.exp (-((1 / 2 - σ) * t))
      ≤ Real.exp ((1 / 2 + σ) * L) / (1 / 2 + σ) + 1 / (1 / 2 - σ) :=
        add_le_add h1 h2

/-- **The judge's displayed form.**  With `L = log λ` and the outer factor
`λ⁻¹`, the bound becomes `λ^(σ−1/2)/(1/2+σ) + λ⁻¹/(1/2−σ)`.

Each factor of the first term is spelled with the real power so the exponent
`σ − 1/2 < 0` is visible: the compounding side loses to the outer factor
precisely because `σ < 1/2`. -/
theorem inv_mul_integral_exp_half_weight_le
    (σ lam : ℝ) (hσ0 : 0 ≤ σ) (hσh : σ < 1 / 2) (hlam : 1 ≤ lam) :
    lam⁻¹ *
        ∫ t in (-(Real.log lam))..(Real.log lam),
          Real.exp (-t / 2) * Real.exp (σ * |t|) ≤
      lam ^ (σ - 1 / 2) / (1 / 2 + σ) + lam⁻¹ / (1 / 2 - σ) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hlogL : 0 ≤ Real.log lam := Real.log_nonneg hlam
  have hinv : 0 ≤ lam⁻¹ := by positivity
  have hbase :=
    integral_exp_half_weight_le σ (Real.log lam) hσ0 hσh hlogL
  have hmul := mul_le_mul_of_nonneg_left hbase hinv
  have hexp :
      Real.exp ((1 / 2 + σ) * Real.log lam) = lam ^ ((1 : ℝ) / 2 + σ) := by
    rw [Real.rpow_def_of_pos hlam0, mul_comm]
  have hkey :
      lam⁻¹ * (Real.exp ((1 / 2 + σ) * Real.log lam) / (1 / 2 + σ)) =
        lam ^ (σ - 1 / 2) / (1 / 2 + σ) := by
    rw [hexp, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc,
      ← Real.rpow_neg_one lam, ← Real.rpow_add hlam0]
    congr 2
    ring
  have hfinal :
      lam⁻¹ *
          (Real.exp ((1 / 2 + σ) * Real.log lam) / (1 / 2 + σ) +
            1 / (1 / 2 - σ)) =
        lam ^ (σ - 1 / 2) / (1 / 2 + σ) + lam⁻¹ / (1 / 2 - σ) := by
    rw [mul_add, hkey]
    ring
  exact hmul.trans (le_of_eq hfinal)

#print axioms integral_exp_neg_mul_Icc_le
#print axioms integral_exp_neg_mul_neg_Icc_le
#print axioms integral_exp_half_weight_le
#print axioms inv_mul_integral_exp_half_weight_le

end Q3.RouteB.D0Pstar
