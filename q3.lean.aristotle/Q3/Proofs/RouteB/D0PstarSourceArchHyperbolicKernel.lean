import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

noncomputable section

open scoped Real
open Set MeasureTheory

namespace Q3.RouteB.D0Pstar

private theorem integral_exp_neg_mul_cos_Ioi
    (a b : ℝ) (ha : 0 < a) :
    ∫ x in Ioi 0, Real.exp (-a * x) * Real.cos (b * x) =
      a / (a ^ 2 + b ^ 2) := by
  let c : ℂ := (-a : ℂ) + Complex.I * (b : ℂ)
  have hc_re : c.re < 0 := by simp [c, ha]
  have hc_int : IntegrableOn (fun x : ℝ => Complex.exp (c * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hc_re 0
  have hvalue := integral_exp_mul_complex_Ioi hc_re 0
  have hre := integral_re hc_int
  rw [hvalue] at hre
  have hpoint (x : ℝ) :
      (Complex.exp (c * x)).re =
        Real.exp (-a * x) * Real.cos (b * x) := by
    rw [Complex.exp_re]
    simp [c]
  have hre' :
      ∫ x in Ioi 0, Real.exp (-a * x) * Real.cos (b * x) =
        (-Complex.exp (c * (0 : ℝ)) / c).re := by
    calc
      _ = ∫ (x : ℝ) in Ioi 0, (Complex.exp (c * (x : ℂ))).re := by
        apply integral_congr_ae
        filter_upwards with x
        exact (hpoint x).symm
      _ = RCLike.re (-Complex.exp (c * (0 : ℝ)) / c) := hre
      _ = (-Complex.exp (c * (0 : ℝ)) / c).re := rfl
  rw [hre']
  have hden : a ^ 2 + b ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  simp [c, div_eq_mul_inv, Complex.inv_re, Complex.normSq_apply]
  field_simp [hden]
  simp

def sourceArchimedeanRegularizedKernel (t x : ℝ) : ℝ :=
  (Real.exp (x / 2) * Real.cos (2 * Real.pi * t * x) - Real.exp (-x)) /
    (Real.exp x - Real.exp (-x))

private def digammaPairNumerator (t u : ℝ) : ℝ :=
  Real.exp (-u) - Real.exp (-u / 4) * Real.cos (Real.pi * t * u)

private def digammaPairDenominator (u : ℝ) : ℝ :=
  1 - Real.exp (-u)

private def digammaPairNumeratorSlope (t : ℝ) : ℝ → ℝ :=
  Function.update
    (fun u =>
      (digammaPairNumerator t u - digammaPairNumerator t 0) / (u - 0))
    0 (deriv (digammaPairNumerator t) 0)

private def digammaPairDenominatorSlope : ℝ → ℝ :=
  Function.update
    (fun u =>
      (digammaPairDenominator u - digammaPairDenominator 0) / (u - 0))
    0 1

private def digammaPairExtendedKernel (t u : ℝ) : ℝ :=
  digammaPairNumeratorSlope t u / digammaPairDenominatorSlope u

private theorem digammaPairNumerator_zero (t : ℝ) :
    digammaPairNumerator t 0 = 0 := by
  simp [digammaPairNumerator]

private theorem digammaPairDenominator_zero :
    digammaPairDenominator 0 = 0 := by
  simp [digammaPairDenominator]

private theorem digammaPairNumerator_differentiable (t : ℝ) :
    Differentiable ℝ (digammaPairNumerator t) := by
  unfold digammaPairNumerator
  fun_prop

private theorem digammaPairDenominator_hasDerivAt_zero :
    HasDerivAt digammaPairDenominator 1 0 := by
  unfold digammaPairDenominator
  convert (hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub
      ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)) using 1 <;>
    norm_num [Function.comp_def]

private theorem digammaPairNumeratorSlope_continuous (t : ℝ) :
    Continuous (digammaPairNumeratorSlope t) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    exact (digammaPairNumerator_differentiable t 0).hasDerivAt.continuousAt_div
  · rw [digammaPairNumeratorSlope, continuousAt_update_of_ne hu]
    apply ContinuousAt.div
    · exact (digammaPairNumerator_differentiable t u).continuousAt.sub
        continuousAt_const
    · exact continuousAt_id.sub continuousAt_const
    · simpa using hu

private theorem digammaPairDenominatorSlope_continuous :
    Continuous digammaPairDenominatorSlope := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    exact digammaPairDenominator_hasDerivAt_zero.continuousAt_div
  · rw [digammaPairDenominatorSlope, continuousAt_update_of_ne hu]
    apply ContinuousAt.div
    · unfold digammaPairDenominator
      fun_prop
    · fun_prop
    · simpa using hu

private theorem digammaPairDenominator_ne_zero {u : ℝ} (hu : u ≠ 0) :
    digammaPairDenominator u ≠ 0 := by
  intro h
  have hexp : Real.exp (-u) = Real.exp 0 := by
    simpa [digammaPairDenominator] using (sub_eq_zero.mp h).symm
  have : -u = 0 := Real.exp_injective hexp
  exact hu (by linarith)

private theorem digammaPairDenominatorSlope_ne_zero (u : ℝ) :
    digammaPairDenominatorSlope u ≠ 0 := by
  by_cases hu : u = 0
  · subst u
    simp [digammaPairDenominatorSlope]
  · rw [digammaPairDenominatorSlope, Function.update_of_ne hu]
    apply div_ne_zero
    · simpa [digammaPairDenominator_zero] using digammaPairDenominator_ne_zero hu
    · simpa using hu

private theorem digammaPairExtendedKernel_continuous (t : ℝ) :
    Continuous (digammaPairExtendedKernel t) := by
  exact (digammaPairNumeratorSlope_continuous t).div
    digammaPairDenominatorSlope_continuous digammaPairDenominatorSlope_ne_zero

private theorem digammaPairExtendedKernel_eq_raw
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    digammaPairExtendedKernel t u =
      digammaPairNumerator t u / digammaPairDenominator u := by
  have hden := digammaPairDenominator_ne_zero hu
  simp only [digammaPairExtendedKernel, digammaPairNumeratorSlope,
    digammaPairDenominatorSlope, Function.update_of_ne hu]
  rw [digammaPairNumerator_zero, digammaPairDenominator_zero]
  field_simp [hu, hden]
  ring

private theorem digammaPairKernel_integrableOn_Ioc (t : ℝ) :
    IntegrableOn
      (fun u => digammaPairNumerator t u / digammaPairDenominator u)
      (Ioc 0 1) := by
  apply (digammaPairExtendedKernel_continuous t).integrableOn_Ioc.congr_fun
  · intro u hu
    exact digammaPairExtendedKernel_eq_raw t (ne_of_gt hu.1)
  · exact measurableSet_Ioc

private theorem digammaPairKernel_tail_bound
    (t : ℝ) {u : ℝ} (hu : 1 < u) :
    ‖digammaPairNumerator t u / digammaPairDenominator u‖ ≤
      (1 - Real.exp (-1))⁻¹ *
        (Real.exp (-u) + Real.exp ((-1 / 4 : ℝ) * u)) := by
  have hdpos : 0 < 1 - Real.exp (-1) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hexp_le : Real.exp (-u) ≤ Real.exp (-1) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hdenpos : 0 < digammaPairDenominator u := by
    unfold digammaPairDenominator
    linarith
  have hden : 1 - Real.exp (-1) ≤ digammaPairDenominator u := by
    unfold digammaPairDenominator
    linarith
  have hnum :
      |digammaPairNumerator t u| ≤
        Real.exp (-u) + Real.exp ((-1 / 4 : ℝ) * u) := by
    unfold digammaPairNumerator
    calc
      |Real.exp (-u) - Real.exp (-u / 4) * Real.cos (Real.pi * t * u)|
          ≤ |Real.exp (-u)| +
              |Real.exp (-u / 4) * Real.cos (Real.pi * t * u)| := abs_sub _ _
      _ = Real.exp (-u) +
            Real.exp (-u / 4) * |Real.cos (Real.pi * t * u)| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-u) + Real.exp (-u / 4) * 1 := by
          gcongr
          exact Real.abs_cos_le_one _
      _ = Real.exp (-u) + Real.exp ((-1 / 4 : ℝ) * u) := by
          congr 2
          ring_nf
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
  calc
    |digammaPairNumerator t u| / digammaPairDenominator u
        ≤ (Real.exp (-u) + Real.exp ((-1 / 4 : ℝ) * u)) /
            digammaPairDenominator u :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (Real.exp (-u) + Real.exp ((-1 / 4 : ℝ) * u)) /
          (1 - Real.exp (-1)) := by
      exact div_le_div_of_nonneg_left
        (by positivity) hdpos hden
    _ = (1 - Real.exp (-1))⁻¹ *
          (Real.exp (-u) + Real.exp ((-1 / 4 : ℝ) * u)) := by
      field_simp

private theorem digammaPairKernel_integrableOn_Ioi_one (t : ℝ) :
    IntegrableOn
      (fun u => digammaPairNumerator t u / digammaPairDenominator u)
      (Ioi 1) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 1) := by
    simpa only [neg_mul, one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1)
  have hquarter :
      IntegrableOn (fun u : ℝ => Real.exp ((-1 / 4 : ℝ) * u)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (a := (-1 / 4 : ℝ)) (by norm_num) 1
  have hmajorant : IntegrableOn
      (fun u : ℝ =>
        (1 - Real.exp (-1))⁻¹ *
          (Real.exp (-u) + Real.exp ((-1 / 4 : ℝ) * u)))
      (Ioi 1) :=
    (h1.add hquarter).const_mul ((1 - Real.exp (-1))⁻¹)
  have hext : IntegrableOn (digammaPairExtendedKernel t) (Ioi 1) := by
    refine hmajorant.mono' (digammaPairExtendedKernel_continuous t).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [digammaPairExtendedKernel_eq_raw t (ne_of_gt (zero_lt_one.trans hu))]
    exact digammaPairKernel_tail_bound t hu
  exact hext.congr_fun
    (fun u hu => digammaPairExtendedKernel_eq_raw t
      (ne_of_gt (zero_lt_one.trans hu))) measurableSet_Ioi

private theorem digammaPairKernel_integrableOn (t : ℝ) :
    IntegrableOn
      (fun u => digammaPairNumerator t u / digammaPairDenominator u)
      (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  exact ⟨digammaPairKernel_integrableOn_Ioc t,
    digammaPairKernel_integrableOn_Ioi_one t⟩

private theorem sourceArchimedeanRegularizedKernel_eq_pairKernel
    (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    sourceArchimedeanRegularizedKernel t x =
      -(digammaPairNumerator t (2 * x) /
        digammaPairDenominator (2 * x)) := by
  have h2x : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hpairDen : digammaPairDenominator (2 * x) ≠ 0 :=
    digammaPairDenominator_ne_zero h2x
  have hsourceDen : Real.exp x - Real.exp (-x) ≠ 0 := by
    intro h
    have harg : x = -x := Real.exp_injective (sub_eq_zero.mp h)
    exact hx (by linarith)
  have hneg2 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [show -(2 * x) = -x + -x by ring, Real.exp_add]
  have hnegHalf : Real.exp (-(2 * x) / 4) = Real.exp (-x / 2) := by
    congr 1
    ring
  have hangle : Real.pi * t * (2 * x) = 2 * Real.pi * t * x := by ring
  have hAB : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hAJ : Real.exp x * Real.exp (-x / 2) = Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hHB : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpairDen' : 1 - Real.exp (-x) * Real.exp (-x) ≠ 0 := by
    simpa [digammaPairDenominator, hneg2] using hpairDen
  have hpairDenSq : 1 - Real.exp (-x) ^ 2 ≠ 0 := by
    simpa [pow_two] using hpairDen'
  unfold sourceArchimedeanRegularizedKernel digammaPairNumerator
    digammaPairDenominator
  rw [hneg2, hnegHalf, hangle]
  field_simp [hpairDen', hpairDenSq, hsourceDen]
  ring_nf
  have hhalfNormPos : Real.exp (x * (1 / 2)) = Real.exp (x / 2) := by
    congr 1
    ring
  have hhalfNormNeg : Real.exp (x * (-1 / 2)) = Real.exp (-x / 2) := by
    congr 1
    ring
  have hcosNorm : Real.cos (x * Real.pi * t * 2) =
      Real.cos (2 * Real.pi * t * x) := by
    congr 1
    ring
  rw [hhalfNormPos, hhalfNormNeg, hcosNorm]
  have hCBA :
      Real.cos (2 * Real.pi * t * x) * Real.exp (-x) * Real.exp x =
        Real.cos (2 * Real.pi * t * x) := by
    calc
      _ = Real.cos (2 * Real.pi * t * x) *
          (Real.exp x * Real.exp (-x)) := by ring
      _ = _ := by rw [hAB, mul_one]
  have hBBA : Real.exp (-x) ^ 2 * Real.exp x = Real.exp (-x) := by
    calc
      _ = Real.exp (-x) * (Real.exp x * Real.exp (-x)) := by ring
      _ = _ := by rw [hAB, mul_one]
  have hCJA :
      Real.cos (2 * Real.pi * t * x) * Real.exp (-x / 2) * Real.exp x =
        Real.cos (2 * Real.pi * t * x) * Real.exp (x / 2) := by
    calc
      _ = Real.cos (2 * Real.pi * t * x) *
          (Real.exp x * Real.exp (-x / 2)) := by ring
      _ = _ := by rw [hAJ]
  have hCAJ :
      Real.cos (2 * Real.pi * t * x) * Real.exp x * Real.exp (-x / 2) =
        Real.cos (2 * Real.pi * t * x) * Real.exp (x / 2) := by
    calc
      _ = Real.cos (2 * Real.pi * t * x) *
          (Real.exp x * Real.exp (-x / 2)) := by ring
      _ = _ := by rw [hAJ]
  have hHCB :
      Real.exp (x / 2) * Real.cos (2 * Real.pi * t * x) * Real.exp (-x) ^ 2 =
        Real.cos (2 * Real.pi * t * x) * Real.exp (-x) * Real.exp (-x / 2) := by
    calc
      _ = Real.cos (2 * Real.pi * t * x) * Real.exp (-x) *
          (Real.exp (x / 2) * Real.exp (-x)) := by ring
      _ = _ := by rw [hHB]
  rw [hHCB]
  rw [hCAJ, hBBA]
  ring

theorem sourceArchimedeanRegularizedKernel_integrableOn (t : ℝ) :
    IntegrableOn (sourceArchimedeanRegularizedKernel t) (Ioi 0) := by
  have hscaled : IntegrableOn
      (fun x : ℝ =>
        digammaPairNumerator t (2 * x) /
          digammaPairDenominator (2 * x))
      (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => digammaPairNumerator t u / digammaPairDenominator u)
      0 (show (0 : ℝ) < 2 by norm_num)]
    simpa using digammaPairKernel_integrableOn t
  have hneg : IntegrableOn
      (fun x : ℝ =>
        -(digammaPairNumerator t (2 * x) /
          digammaPairDenominator (2 * x)))
      (Ioi 0) := hscaled.neg
  exact hneg.congr_fun
    (fun x hx => (sourceArchimedeanRegularizedKernel_eq_pairKernel t
      (ne_of_gt hx)).symm) measurableSet_Ioi

private def sourceArchimedeanArgument (t : ℝ) : ℂ :=
  (1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)

private def digammaPairTerm (t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) + 1) * u) -
    Real.exp (-((n : ℝ) + 1 / 4) * u) * Real.cos (Real.pi * t * u)

private theorem digammaPairTerm_eq_factor
    (t : ℝ) (n : ℕ) (u : ℝ) :
    digammaPairTerm t n u =
      Real.exp (-u) ^ n * digammaPairNumerator t u := by
  have hfirst : Real.exp (-((n : ℝ) + 1) * u) =
      Real.exp (-u) ^ n * Real.exp (-u) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hsecond : Real.exp (-((n : ℝ) + 1 / 4) * u) =
      Real.exp (-u) ^ n * Real.exp (-u / 4) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [digammaPairTerm, digammaPairNumerator, hfirst, hsecond]
  ring

private theorem digammaPairTerm_hasSum
    (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => digammaPairTerm t n u)
      (digammaPairNumerator t u / digammaPairDenominator u) := by
  have hr0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hr1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_right (digammaPairNumerator t u)
  have hs : HasSum (fun n : ℕ => digammaPairTerm t n u)
      ((1 - Real.exp (-u))⁻¹ * digammaPairNumerator t u) :=
    HasSum.congr_fun hgeom (fun n => digammaPairTerm_eq_factor t n u)
  convert hs using 1
  simp [digammaPairDenominator, div_eq_mul_inv, mul_comm]

private theorem digammaPairTerm_norm_hasSum
    (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => ‖digammaPairTerm t n u‖)
      ‖digammaPairNumerator t u / digammaPairDenominator u‖ := by
  have hr0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hr1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_right ‖digammaPairNumerator t u‖
  have hdenpos : 0 < digammaPairDenominator u := by
    unfold digammaPairDenominator
    linarith
  have hs : HasSum (fun n : ℕ => ‖digammaPairTerm t n u‖)
      ((1 - Real.exp (-u))⁻¹ * ‖digammaPairNumerator t u‖) :=
    HasSum.congr_fun hgeom (fun n => by
      rw [digammaPairTerm_eq_factor]
      simp only [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos (Real.exp_pos _)])
  convert hs using 1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
  simp [digammaPairDenominator, div_eq_mul_inv, mul_comm]

private theorem digammaPairTerm_integrableOn (t : ℝ) (n : ℕ) :
    IntegrableOn (digammaPairTerm t n) (Ioi 0) := by
  have hfirst : IntegrableOn
      (fun u : ℝ => Real.exp (-((n : ℝ) + 1) * u)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi
      (a := -((n : ℝ) + 1)) (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) 0
  have hsecondExp : IntegrableOn
      (fun u : ℝ => Real.exp (-((n : ℝ) + 1 / 4) * u)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi
      (a := -((n : ℝ) + 1 / 4)) (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) 0
  have hcosBound : ∀ u : ℝ,
      ‖Real.exp (-((n : ℝ) + 1 / 4) * u) * Real.cos (Real.pi * t * u)‖ ≤
        Real.exp (-((n : ℝ) + 1 / 4) * u) := by
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [Real.abs_cos_le_one (Real.pi * t * u), Real.exp_pos
      (-((n : ℝ) + 1 / 4) * u)]
  have hsecond : IntegrableOn
      (fun u : ℝ =>
        Real.exp (-((n : ℝ) + 1 / 4) * u) * Real.cos (Real.pi * t * u))
      (Ioi 0) := by
    refine hsecondExp.mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall hcosBound
  exact hfirst.sub hsecond

private theorem digammaPairIntegral_hasSum (t : ℝ) :
    HasSum
      (fun n : ℕ => ∫ u in Ioi 0, digammaPairTerm t n u)
      (∫ u in Ioi 0,
        digammaPairNumerator t u / digammaPairDenominator u) := by
  have hnormSumIntegrable : Integrable
      (fun u : ℝ => ∑' n : ℕ, ‖digammaPairTerm t n u‖)
      (volume.restrict (Ioi 0)) := by
    have hrawNorm : Integrable
        (fun u : ℝ =>
          ‖digammaPairNumerator t u / digammaPairDenominator u‖)
        (volume.restrict (Ioi 0)) :=
      (digammaPairKernel_integrableOn t).norm
    exact hrawNorm.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (digammaPairTerm_norm_hasSum t hu).tsum_eq.symm)
  exact MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi 0))
    (F := digammaPairTerm t)
    (f := fun u : ℝ =>
      digammaPairNumerator t u / digammaPairDenominator u)
    (bound := fun n u => ‖digammaPairTerm t n u‖)
    (fun n => (digammaPairTerm_integrableOn t n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun u => le_rfl))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (digammaPairTerm_norm_hasSum t hu).summable)
    hnormSumIntegrable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact digammaPairTerm_hasSum t hu)

private theorem digammaPairTerm_integral_eq_seriesTerm
    (t : ℝ) (n : ℕ) :
    (∫ u in Ioi 0, digammaPairTerm t n u) =
      ((1 / (n + 1 : ℂ) -
        1 / (sourceArchimedeanArgument t + n)).re) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfirstCoeff : -((n : ℝ) + 1) < 0 := by linarith
  have hfirstInt : IntegrableOn
      (fun u : ℝ => Real.exp (-((n : ℝ) + 1) * u)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi
      (a := -((n : ℝ) + 1)) hfirstCoeff 0
  have hsecondInt : IntegrableOn
      (fun u : ℝ =>
        Real.exp (-((n : ℝ) + 1 / 4) * u) *
          Real.cos (Real.pi * t * u))
      (Ioi 0) := by
    have hfull := digammaPairTerm_integrableOn t n
    have hfirst := hfirstInt
    have hdiff : IntegrableOn
        (fun u : ℝ =>
          Real.exp (-((n : ℝ) + 1) * u) - digammaPairTerm t n u)
        (Ioi 0) := hfirst.sub hfull
    exact hdiff.congr_fun
      (fun u _ => by
        unfold digammaPairTerm
        ring) measurableSet_Ioi
  have hfirstValue :
      (∫ u in Ioi 0, Real.exp (-((n : ℝ) + 1) * u)) =
        1 / ((n : ℝ) + 1) := by
    have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
    have hneg : -1 - (n : ℝ) ≠ 0 := by linarith
    rw [integral_exp_mul_Ioi hfirstCoeff 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hnp, hneg, hfirstCoeff.ne]
  have hsecondValue :
      (∫ u in Ioi 0,
        Real.exp (-((n : ℝ) + 1 / 4) * u) *
          Real.cos (Real.pi * t * u)) =
        ((n : ℝ) + 1 / 4) /
          (((n : ℝ) + 1 / 4) ^ 2 + (Real.pi * t) ^ 2) := by
    exact integral_exp_neg_mul_cos_Ioi
      ((n : ℝ) + 1 / 4) (Real.pi * t) (by linarith)
  change
    (∫ u in Ioi 0,
      Real.exp (-((n : ℝ) + 1) * u) -
        Real.exp (-((n : ℝ) + 1 / 4) * u) *
          Real.cos (Real.pi * t * u)) = _
  rw [integral_sub hfirstInt hsecondInt,
    hfirstValue, hsecondValue]
  simp [sourceArchimedeanArgument, Complex.div_re, Complex.normSq_apply]
  ring

private theorem sourceArchimedeanArgument_re_pos (t : ℝ) :
    0 < (sourceArchimedeanArgument t).re := by
  simp [sourceArchimedeanArgument]

private theorem sourceArchimedeanArgument_add_nat_ne_zero
    (t : ℝ) (n : ℕ) :
    sourceArchimedeanArgument t + n ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [sourceArchimedeanArgument] at hre
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem re_digamma_sourceArchimedeanArgument_eq_pairIntegral
    (t : ℝ) :
    (Q3.digamma (sourceArchimedeanArgument t)).re =
      -Real.eulerMascheroniConstant +
        ∫ u in Ioi 0,
          digammaPairNumerator t u / digammaPairDenominator u := by
  let z := sourceArchimedeanArgument t
  have hzpos : 0 < z.re := sourceArchimedeanArgument_re_pos t
  have hz : ∀ n : ℕ, z + n ≠ 0 :=
    sourceArchimedeanArgument_add_nat_ne_zero t
  have hdig := Q3.re_digamma_eq_sum_of_tendsto z hz
    (Q3.digammaSeq_tendsto_Q3_digamma z hzpos)
  have hIntegral := digammaPairIntegral_hasSum t
  have hSeries : HasSum
      (fun n : ℕ =>
        ((1 / (n + 1 : ℂ) - 1 / (sourceArchimedeanArgument t + n)).re))
      (∫ u in Ioi 0,
        digammaPairNumerator t u / digammaPairDenominator u) :=
    HasSum.congr_fun hIntegral
      (fun n => (digammaPairTerm_integral_eq_seriesTerm t n).symm)
  rw [hdig, hSeries.tsum_eq]

private theorem pairIntegral_eq_neg_two_sourceKernelIntegral (t : ℝ) :
    (∫ u in Ioi 0,
      digammaPairNumerator t u / digammaPairDenominator u) =
      -2 * ∫ x in Ioi 0, sourceArchimedeanRegularizedKernel t x := by
  let g : ℝ → ℝ := fun u =>
    digammaPairNumerator t u / digammaPairDenominator u
  have hscale := integral_comp_mul_left_Ioi g 0
    (show (0 : ℝ) < 2 by norm_num)
  have hscale' :
      (∫ x in Ioi 0, g (2 * x)) =
        (1 / 2 : ℝ) * ∫ u in Ioi 0, g u := by
    simpa [one_div] using hscale
  have hsource :
      (∫ x in Ioi 0, sourceArchimedeanRegularizedKernel t x) =
        -(∫ x in Ioi 0, g (2 * x)) := by
    calc
      _ = ∫ x in Ioi 0, -g (2 * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact sourceArchimedeanRegularizedKernel_eq_pairKernel t
          (ne_of_gt hx)
      _ = _ := integral_neg _
  dsimp only [g] at hscale' ⊢
  rw [hsource]
  linarith

theorem sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral
    (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Real.log Real.pi - Real.eulerMascheroniConstant -
        2 * ∫ x in Ioi 0, sourceArchimedeanRegularizedKernel t x := by
  have hdig := re_digamma_sourceArchimedeanArgument_eq_pairIntegral t
  have hscale := pairIntegral_eq_neg_two_sourceKernelIntegral t
  unfold sourceArchimedeanMultiplier
  change -Real.log Real.pi +
      (Q3.digamma (sourceArchimedeanArgument t)).re = _
  rw [hdig, hscale]
  ring


end Q3.RouteB.D0Pstar
