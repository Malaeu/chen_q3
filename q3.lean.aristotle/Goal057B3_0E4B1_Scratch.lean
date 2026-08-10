import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option linter.mathlibStandardSet false
set_option linter.unnecessarySeqFocus false

open scoped Real
open Filter MeasureTheory Set

namespace Q3.RouteB.D0Pstar

private noncomputable def diagonalFinitePrimitive (x : ℝ) : ℝ :=
  2 * x - 2 * Real.log (Real.exp x + 1)

private noncomputable def diagonalTailPrimitive (x : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-2 * x))

private theorem diagonalFiniteIntegrand_eq (x : ℝ) (hx : 0 < x) :
    2 * (1 - Real.exp (-x)) /
        (Real.exp x - Real.exp (-x)) =
      2 / (Real.exp x + 1) := by
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hexp_ne : Real.exp x ≠ 0 := ne_of_gt hexp_pos
  have hexp_one : Real.exp x ≠ 1 :=
    ne_of_gt ((Real.one_lt_exp_iff).2 hx)
  have hden_left : Real.exp x - Real.exp (-x) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.2 (by linarith)))
  have hden_right : Real.exp x + 1 ≠ 0 :=
    ne_of_gt (add_pos hexp_pos zero_lt_one)
  apply (div_eq_div_iff hden_left hden_right).2
  rw [Real.exp_neg]
  field_simp [hexp_ne, hexp_one]
  ring

private theorem diagonalFinitePrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt diagonalFinitePrimitive (2 / (Real.exp x + 1)) x := by
  have hden : Real.exp x + 1 ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos x) zero_lt_one)
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (Real.exp y + 1))
        (Real.exp x / (Real.exp x + 1)) x :=
    ((Real.hasDerivAt_exp x).add_const 1).log hden
  unfold diagonalFinitePrimitive
  convert ((hasDerivAt_id x).const_mul 2).sub (hlog.const_mul 2) using 1 <;>
    field_simp <;> ring

private theorem diagonalFiniteIntegral (L : ℝ) (hL : 0 < L) :
    (∫ x in Set.Ioc 0 L,
      2 * (1 - Real.exp (-x)) /
        (Real.exp x - Real.exp (-x))) =
      diagonalFinitePrimitive L - diagonalFinitePrimitive 0 := by
  have hcongr :
      (∫ x in Set.Ioc 0 L,
        2 * (1 - Real.exp (-x)) /
          (Real.exp x - Real.exp (-x))) =
        ∫ x in Set.Ioc 0 L, 2 / (Real.exp x + 1) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact diagonalFiniteIntegrand_eq x hx.1
  rw [hcongr, ← intervalIntegral.integral_of_le hL.le]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact diagonalFinitePrimitive_hasDerivAt x
  · exact
      (continuous_const.div
        (Real.continuous_exp.add continuous_const)
        (fun x => ne_of_gt (add_pos (Real.exp_pos x) zero_lt_one))).intervalIntegrable 0 L

private theorem diagonalTailPrimitive_hasDerivAt
    (L x : ℝ) (hL : 0 < L) (hx : L ≤ x) :
    HasDerivAt diagonalTailPrimitive
      (2 * Real.exp (-x) / (Real.exp x - Real.exp (-x))) x := by
  have hxpos : 0 < x := lt_of_lt_of_le hL hx
  have hexp_lt : Real.exp (-2 * x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hinner : 1 - Real.exp (-2 * x) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hexp_lt)
  have harg :
      HasDerivAt (fun y : ℝ => 1 - Real.exp (-2 * y))
        (2 * Real.exp (-2 * x)) x := by
    convert (hasDerivAt_const x 1).sub
      ((Real.hasDerivAt_exp (-2 * x)).comp x
        ((hasDerivAt_id x).const_mul (-2))) using 1 <;> ring
  have hlog := harg.log hinner
  unfold diagonalTailPrimitive
  convert hlog using 1
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hexp_ne : Real.exp x ≠ 0 := ne_of_gt hexp_pos
  have hexp_one : Real.exp x ≠ 1 :=
    ne_of_gt ((Real.one_lt_exp_iff).2 hxpos)
  rw [show -2 * x = -x + -x by ring, Real.exp_add, Real.exp_neg]
  field_simp [hexp_ne, hexp_one]

private theorem diagonalTailIntegral (L : ℝ) (hL : 0 < L) :
    (∫ x in Set.Ioi L,
      2 * Real.exp (-x) /
        (Real.exp x - Real.exp (-x))) =
      -diagonalTailPrimitive L := by
  have hderiv : ∀ x ∈ Set.Ici L,
      HasDerivAt diagonalTailPrimitive
        (2 * Real.exp (-x) / (Real.exp x - Real.exp (-x))) x := by
    intro x hx
    exact diagonalTailPrimitive_hasDerivAt L x hL hx
  have hnonneg : ∀ x ∈ Set.Ioi L,
      0 ≤ 2 * Real.exp (-x) /
        (Real.exp x - Real.exp (-x)) := by
    intro x hx
    have hxpos : 0 < x := lt_trans hL hx
    have hden : 0 < Real.exp x - Real.exp (-x) :=
      sub_pos.mpr (Real.exp_lt_exp.2 (by linarith))
    positivity
  have hexp : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have harg : Tendsto (fun x : ℝ => 1 - Real.exp (-2 * x)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hexp
  have hlim : Tendsto diagonalTailPrimitive atTop (nhds 0) := by
    unfold diagonalTailPrimitive
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv hnonneg hlim
  simpa using hFTC

theorem sourceArchimedeanDiagonalRegularizer_endpointLedger
    (L : ℝ) (hL : 0 < L) :
    -Real.log Real.pi -
        (∫ x in Set.Ioc 0 L,
          2 * (1 - Real.exp (-x)) /
            (Real.exp x - Real.exp (-x))) +
        (∫ x in Set.Ioi L,
          2 * Real.exp (-x) /
            (Real.exp x - Real.exp (-x))) =
      -Real.log
        (4 * Real.pi *
          ((Real.exp L - 1) / (Real.exp L + 1))) := by
  rw [diagonalFiniteIntegral L hL, diagonalTailIntegral L hL]
  unfold diagonalFinitePrimitive diagonalTailPrimitive
  norm_num only [Real.exp_zero, mul_zero, zero_sub, one_add_one_eq_two]
  have hexp_gt : 1 < Real.exp L := (Real.one_lt_exp_iff).2 hL
  have hexp_minus_pos : 0 < Real.exp L - 1 := sub_pos.mpr hexp_gt
  have hexp_plus_pos : 0 < Real.exp L + 1 :=
    add_pos (Real.exp_pos L) zero_lt_one
  have hpi : 0 < Real.pi := Real.pi_pos
  have hinner_eq :
      1 - Real.exp (-2 * L) =
        ((Real.exp L - 1) * (Real.exp L + 1)) / (Real.exp L) ^ 2 := by
    rw [show -2 * L = -L + -L by ring, Real.exp_add, Real.exp_neg]
    field_simp [(Real.exp_pos L).ne']
    ring
  have hlog_inner :
      Real.log (1 - Real.exp (-2 * L)) =
        Real.log (Real.exp L - 1) + Real.log (Real.exp L + 1) - 2 * L := by
    rw [hinner_eq,
      Real.log_div
        (mul_pos hexp_minus_pos hexp_plus_pos).ne'
        (pow_ne_zero 2 (Real.exp_pos L).ne'),
      Real.log_mul hexp_minus_pos.ne' hexp_plus_pos.ne',
      Real.log_pow, Real.log_exp]
    norm_num
  rw [hlog_inner,
    Real.log_mul
      (mul_pos (by norm_num : (0 : ℝ) < 4) hpi).ne'
      (div_ne_zero hexp_minus_pos.ne' hexp_plus_pos.ne'),
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hpi.ne',
    Real.log_div hexp_minus_pos.ne' hexp_plus_pos.ne']
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog_four]
  ring

#print axioms sourceArchimedeanDiagonalRegularizer_endpointLedger

end Q3.RouteB.D0Pstar
