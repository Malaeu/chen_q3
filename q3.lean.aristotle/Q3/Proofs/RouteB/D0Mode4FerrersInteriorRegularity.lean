import Q3.Proofs.RouteB.D0Mode4FerrersCoefficientAbsoluteSummability
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Interior regularity of the mode-four Ferrers series

The exact geometric splice makes every polynomial moment of the coefficient
row summable.  Combined with the committed first- and second-derivative
Legendre bounds, this gives summable majorants for both differentiated series
on every strict compact subinterval of `(-1, 1)`.

This file proves the legal two-step termwise differentiation and exports
`ContDiffOn ℝ 2` for the Ferrers series on the full open source window.  It
does not yet transfer the coefficient recurrence to the prolate differential
equation or identify an ordered PSWF mode.
-/

noncomputable section

noncomputable def mode4FerrersFirstDerivativeTerm
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ q * a q *
    (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x

noncomputable def mode4FerrersSecondDerivativeTerm
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ q * a q *
    (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.derivative.eval x

theorem mode4FerrersTerm_hasDerivAt
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    HasDerivAt (mode4FerrersTerm a q)
      (mode4FerrersFirstDerivativeTerm a q x) x := by
  simpa [mode4FerrersTerm, mode4FerrersFirstDerivativeTerm,
    mode4OrdinaryLegendre] using
      ((mode4OrdinaryLegendrePolynomial (2 * q)).hasDerivAt x).const_mul
        ((-1 : ℝ) ^ q * a q)

theorem mode4FerrersFirstDerivativeTerm_hasDerivAt
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    HasDerivAt (mode4FerrersFirstDerivativeTerm a q)
      (mode4FerrersSecondDerivativeTerm a q x) x := by
  simpa [mode4FerrersFirstDerivativeTerm,
    mode4FerrersSecondDerivativeTerm] using
      ((mode4OrdinaryLegendrePolynomial (2 * q)).derivative.hasDerivAt x).const_mul
        ((-1 : ℝ) ^ q * a q)

noncomputable def mode4FerrersFirstDerivativeMajorant
    (a : ℕ → ℝ) (r : ℝ) (q : ℕ) : ℝ :=
  (4 / (1 - r ^ 2) + 1) *
    (((q + 1 : ℕ) : ℝ) ^ 2 * |a q|)

noncomputable def mode4FerrersSecondDerivativeMajorant
    (a : ℕ → ℝ) (r : ℝ) (q : ℕ) : ℝ :=
  ((2 * r * (4 / (1 - r ^ 2) + 1) + 4) / (1 - r ^ 2)) *
    (((q + 1 : ℕ) : ℝ) ^ 2 * |a q|)

private theorem mode4EvenDegree_spectralFactor_le
    (q : ℕ) :
    ((2 * q : ℕ) : ℝ) * ((2 * q : ℕ) + 1) ≤
      4 * (((q + 1 : ℕ) : ℝ) ^ 2) := by
  push_cast
  nlinarith [sq_nonneg (q : ℝ)]

theorem mode4FerrersFirstDerivativeTerm_norm_le
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (q : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-r) r) :
    ‖mode4FerrersFirstDerivativeTerm a q x‖ ≤
      mode4FerrersFirstDerivativeMajorant a r q := by
  let d : ℝ := 1 - r ^ 2
  let w : ℝ := ((q + 1 : ℕ) : ℝ) ^ 2
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hw : 1 ≤ w := by
    dsimp [w]
    have ht : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
    simpa using (sq_le_sq₀ zero_le_one (by positivity)).2 ht
  have hN := mode4EvenDegree_spectralFactor_le q
  have hP := mode4OrdinaryLegendrePolynomial_derivative_abs_le
    (2 * q) r x hr0 hr1 hx
  have hquot :
      (((2 * q : ℕ) : ℝ) * ((2 * q : ℕ) + 1)) / d ≤
        (4 / d) * w := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [inv_pos.mpr hd]
  have hPbound :
      |(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x| ≤
        (4 / d + 1) * w := by
    change
      |(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x| ≤
        (((2 * q : ℕ) : ℝ) * ((2 * q : ℕ) + 1)) / d + 1 at hP
    calc
      _ ≤ (((2 * q : ℕ) : ℝ) * ((2 * q : ℕ) + 1)) / d + 1 := hP
      _ ≤ (4 / d) * w + 1 := by linarith [hquot]
      _ ≤ (4 / d) * w + w := by linarith [hw]
      _ = (4 / d + 1) * w := by ring
  rw [Real.norm_eq_abs]
  unfold mode4FerrersFirstDerivativeTerm
  rw [abs_mul, abs_mul, abs_pow]
  norm_num
  unfold mode4FerrersFirstDerivativeMajorant
  change |a q| *
      |(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x| ≤
    (4 / d + 1) * (w * |a q|)
  calc
    _ ≤ |a q| * ((4 / d + 1) * w) :=
      mul_le_mul_of_nonneg_left hPbound (abs_nonneg _)
    _ = _ := by ring

theorem mode4FerrersSecondDerivativeTerm_norm_le
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (q : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-r) r) :
    ‖mode4FerrersSecondDerivativeTerm a q x‖ ≤
      mode4FerrersSecondDerivativeMajorant a r q := by
  let d : ℝ := 1 - r ^ 2
  let w : ℝ := ((q + 1 : ℕ) : ℝ) ^ 2
  let N : ℝ := ((2 * q : ℕ) : ℝ) * ((2 * q : ℕ) + 1)
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hw : 1 ≤ w := by
    dsimp [w]
    have ht : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
    simpa using (sq_le_sq₀ zero_le_one (by positivity)).2 ht
  have hN : N ≤ 4 * w := by
    simpa [N, w] using mode4EvenDegree_spectralFactor_le q
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hquot : N / d + 1 ≤ (4 / d + 1) * w := by
    have hdiv : N / d ≤ (4 / d) * w := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [inv_pos.mpr hd]
    calc
      N / d + 1 ≤ (4 / d) * w + 1 := by linarith [hdiv]
      _ ≤ (4 / d) * w + w := by linarith [hw]
      _ = (4 / d + 1) * w := by ring
  have hnum :
      2 * r * (N / d + 1) + N ≤
        (2 * r * (4 / d + 1) + 4) * w := by
    calc
      _ ≤ 2 * r * ((4 / d + 1) * w) + 4 * w := by
        gcongr
      _ = _ := by ring
  have hP := mode4OrdinaryLegendrePolynomial_secondDerivative_abs_le
    (2 * q) r x hr0 hr1 hx
  have hPbound :
      |(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.derivative.eval x| ≤
        ((2 * r * (4 / d + 1) + 4) / d) * w := by
    change
      |(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.derivative.eval x| ≤
        (2 * r * (N / d + 1) + N) / d at hP
    calc
      _ ≤ (2 * r * (N / d + 1) + N) / d := hP
      _ ≤ ((2 * r * (4 / d + 1) + 4) * w) / d := by
        exact (div_le_div_iff_of_pos_right hd).2 hnum
      _ = ((2 * r * (4 / d + 1) + 4) / d) * w := by ring
  rw [Real.norm_eq_abs]
  unfold mode4FerrersSecondDerivativeTerm
  rw [abs_mul, abs_mul, abs_pow]
  norm_num
  unfold mode4FerrersSecondDerivativeMajorant
  change |a q| *
      |(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.derivative.eval x| ≤
    ((2 * r * (4 / d + 1) + 4) / d) * (w * |a q|)
  calc
    _ ≤ |a q| * (((2 * r * (4 / d + 1) + 4) / d) * w) :=
      mul_le_mul_of_nonneg_left hPbound (abs_nonneg _)
    _ = _ := by ring

noncomputable def mode4FerrersFirstDerivativeSeries
    (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' q : ℕ, mode4FerrersFirstDerivativeTerm a q x

noncomputable def mode4FerrersSecondDerivativeSeries
    (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' q : ℕ, mode4FerrersSecondDerivativeTerm a q x

theorem mode4FerrersFirstDerivativeMajorant_summable
    (a : ℕ → ℝ) (r : ℝ)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|)) :
    Summable (mode4FerrersFirstDerivativeMajorant a r) := by
  change Summable (fun q : ℕ =>
    (4 / (1 - r ^ 2) + 1) *
      ((((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
  exact ha2.mul_left (4 / (1 - r ^ 2) + 1)

theorem mode4FerrersSecondDerivativeMajorant_summable
    (a : ℕ → ℝ) (r : ℝ)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|)) :
    Summable (mode4FerrersSecondDerivativeMajorant a r) := by
  change Summable (fun q : ℕ =>
    ((2 * r * (4 / (1 - r ^ 2) + 1) + 4) / (1 - r ^ 2)) *
      ((((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
  exact ha2.mul_left
    ((2 * r * (4 / (1 - r ^ 2) + 1) + 4) / (1 - r ^ 2))

theorem mode4FerrersFirstDerivativeTerm_summable
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (x : ℝ) (hx : x ∈ Set.Icc (-r) r) :
    Summable (fun q : ℕ => mode4FerrersFirstDerivativeTerm a q x) := by
  have hnorm : Summable (fun q : ℕ =>
      ‖mode4FerrersFirstDerivativeTerm a q x‖) :=
    Summable.of_nonneg_of_le
      (fun q => norm_nonneg _)
      (fun q => mode4FerrersFirstDerivativeTerm_norm_le
        a r hr0 hr1 q x hx)
      (mode4FerrersFirstDerivativeMajorant_summable a r ha2)
  exact hnorm.of_norm

theorem mode4FerrersSecondDerivativeTerm_summable
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (x : ℝ) (hx : x ∈ Set.Icc (-r) r) :
    Summable (fun q : ℕ => mode4FerrersSecondDerivativeTerm a q x) := by
  have hnorm : Summable (fun q : ℕ =>
      ‖mode4FerrersSecondDerivativeTerm a q x‖) :=
    Summable.of_nonneg_of_le
      (fun q => norm_nonneg _)
      (fun q => mode4FerrersSecondDerivativeTerm_norm_le
        a r hr0 hr1 q x hx)
      (mode4FerrersSecondDerivativeMajorant_summable a r ha2)
  exact hnorm.of_norm

theorem mode4FerrersFirstDerivativeSeries_continuousOn
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|)) :
    ContinuousOn (mode4FerrersFirstDerivativeSeries a) (Set.Icc (-r) r) := by
  unfold mode4FerrersFirstDerivativeSeries
  apply continuousOn_tsum
  · intro q
    unfold mode4FerrersFirstDerivativeTerm
    exact
      (continuous_const.mul
        (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.continuous).continuousOn
  · exact mode4FerrersFirstDerivativeMajorant_summable a r ha2
  · intro q x hx
    exact mode4FerrersFirstDerivativeTerm_norm_le a r hr0 hr1 q x hx

theorem mode4FerrersSecondDerivativeSeries_continuousOn
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|)) :
    ContinuousOn (mode4FerrersSecondDerivativeSeries a) (Set.Icc (-r) r) := by
  unfold mode4FerrersSecondDerivativeSeries
  apply continuousOn_tsum
  · intro q
    unfold mode4FerrersSecondDerivativeTerm
    exact
      (continuous_const.mul
        (mode4OrdinaryLegendrePolynomial
          (2 * q)).derivative.derivative.continuous).continuousOn
  · exact mode4FerrersSecondDerivativeMajorant_summable a r ha2
  · intro q x hx
    exact mode4FerrersSecondDerivativeTerm_norm_le a r hr0 hr1 q x hx

theorem mode4FerrersSeries_hasDerivAt_of_mem_Ioo
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (x : ℝ) (hx : x ∈ Set.Ioo (-r) r) :
    HasDerivAt (mode4FerrersSeries a)
      (mode4FerrersFirstDerivativeSeries a x) x := by
  unfold mode4FerrersSeries mode4FerrersFirstDerivativeSeries
  apply hasDerivAt_tsum_of_isPreconnected
    (u := mode4FerrersFirstDerivativeMajorant a r)
    (t := Set.Ioo (-r) r)
    (y₀ := 0)
  · exact mode4FerrersFirstDerivativeMajorant_summable a r ha2
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro q y hy
    exact mode4FerrersTerm_hasDerivAt a q y
  · intro q y hy
    exact mode4FerrersFirstDerivativeTerm_norm_le
      a r hr0.le hr1 q y ⟨hy.1.le, hy.2.le⟩
  · constructor <;> linarith
  · exact mode4FerrersTerm_summable a haAbs 0 (by
      constructor <;> norm_num)
  · exact hx

theorem mode4FerrersFirstDerivativeSeries_hasDerivAt_of_mem_Ioo
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (x : ℝ) (hx : x ∈ Set.Ioo (-r) r) :
    HasDerivAt (mode4FerrersFirstDerivativeSeries a)
      (mode4FerrersSecondDerivativeSeries a x) x := by
  unfold mode4FerrersFirstDerivativeSeries mode4FerrersSecondDerivativeSeries
  apply hasDerivAt_tsum_of_isPreconnected
    (u := mode4FerrersSecondDerivativeMajorant a r)
    (t := Set.Ioo (-r) r)
    (y₀ := 0)
  · exact mode4FerrersSecondDerivativeMajorant_summable a r ha2
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro q y hy
    exact mode4FerrersFirstDerivativeTerm_hasDerivAt a q y
  · intro q y hy
    exact mode4FerrersSecondDerivativeTerm_norm_le
      a r hr0.le hr1 q y ⟨hy.1.le, hy.2.le⟩
  · constructor <;> linarith
  · exact mode4FerrersFirstDerivativeTerm_summable
      a r hr0.le hr1 ha2 0 (by constructor <;> linarith)
  · exact hx

/-- Absolute and quadratic weighted coefficient summability make the Ferrers
series twice continuously differentiable on every strict interior window. -/
theorem mode4FerrersSeries_contDiffOn_two_Ioo
    (a : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|)) :
    ContDiffOn ℝ 2 (mode4FerrersSeries a) (Set.Ioo (-r) r) := by
  let s := Set.Ioo (-r) r
  have hfHas : ∀ x ∈ s,
      HasDerivAt (mode4FerrersSeries a)
        (mode4FerrersFirstDerivativeSeries a x) x := by
    intro x hx
    exact mode4FerrersSeries_hasDerivAt_of_mem_Ioo
      a r hr0 hr1 haAbs ha2 x hx
  have hfirstHas : ∀ x ∈ s,
      HasDerivAt (mode4FerrersFirstDerivativeSeries a)
        (mode4FerrersSecondDerivativeSeries a x) x := by
    intro x hx
    exact mode4FerrersFirstDerivativeSeries_hasDerivAt_of_mem_Ioo
      a r hr0 hr1 ha2 x hx
  have hfDiff : DifferentiableOn ℝ (mode4FerrersSeries a) s := by
    intro x hx
    exact (hfHas x hx).differentiableAt.differentiableWithinAt
  have hfirstDiff :
      DifferentiableOn ℝ (mode4FerrersFirstDerivativeSeries a) s := by
    intro x hx
    exact (hfirstHas x hx).differentiableAt.differentiableWithinAt
  have hsecondCont :
      ContinuousOn (mode4FerrersSecondDerivativeSeries a) s :=
    (mode4FerrersSecondDerivativeSeries_continuousOn
      a r hr0.le hr1 ha2).mono (by
        intro x hx
        exact ⟨hx.1.le, hx.2.le⟩)
  have hfirstC1 :
      ContDiffOn ℝ 1 (mode4FerrersFirstDerivativeSeries a) s := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨hfirstDiff, ?_, ?_⟩
    · intro h
      norm_num at h
    · rw [contDiffOn_zero]
      exact hsecondCont.congr fun x hx => (hfirstHas x hx).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨hfDiff, ?_, ?_⟩
  · intro h
    norm_num at h
  · exact hfirstC1.congr fun x hx => (hfHas x hx).deriv

/-- The local compact-window statements cover the whole open source window. -/
theorem mode4FerrersSeries_contDiffOn_two_Ioo_unit
    (a : ℕ → ℝ)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|)) :
    ContDiffOn ℝ 2 (mode4FerrersSeries a) (Set.Ioo (-1 : ℝ) 1) := by
  rw [isOpen_Ioo.contDiffOn_iff]
  intro x hx
  let r : ℝ := (|x| + 1) / 2
  have hxAbs : |x| < 1 := (abs_lt).2 hx
  have hr0 : 0 < r := by
    dsimp [r]
    linarith [abs_nonneg x]
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hxSmall : x ∈ Set.Ioo (-r) r := by
    change -r < x ∧ x < r
    rw [← abs_lt]
    dsimp [r]
    linarith
  have hsmall := mode4FerrersSeries_contDiffOn_two_Ioo
    a r hr0 hr1 haAbs ha2
  exact (isOpen_Ioo.contDiffOn_iff.mp hsmall) hxSmall

/-- The exact canonical-tail splice discharges both analytic summability
premises, so a matched recurrence row directly yields `C²` interior
regularity of its Ferrers series. -/
theorem mode4FerrersSeries_contDiffOn_two_of_tail_splice
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (a : ℕ → ℝ)
    (hsplice : ∀ n : ℕ,
      a (K - 1 + n) =
        a (K - 1) *
          mode4TailCoefficientRow mProject Λ K n) :
    ContDiffOn ℝ 2 (mode4FerrersSeries a) (Set.Ioo (-1 : ℝ) 1) := by
  have haAbs := mode4RecurrenceRow_abs_summable_of_tail_splice
    mProject K Λ hm hK hsep hΛ a hsplice
  have ha2 :=
    mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
      mProject K Λ hm hK hsep hΛ a hsplice 2
  exact mode4FerrersSeries_contDiffOn_two_Ioo_unit a haAbs ha2
