import Q3.Proofs.RouteB.G6N1SelectedFerrersAbelPoissonL2
import Q3.Proofs.RouteB.D0PstarActualProlateEStarMemLp
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 2400000

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology FourierTransform ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

private theorem absolutelyContinuousOnInterval_congrOn
    {F : Type*} [SeminormedAddCommGroup F]
    {f g : ℝ → F} {a b : ℝ}
    (hfg : Set.EqOn f g (Set.uIcc a b))
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := hg ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have hbound := hgδ E hE hlen
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfg (hE.1 i hi).1, hfg (hE.1 i hi).2]

private theorem complex_re_absolutelyContinuousOnInterval
    {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x).re) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  calc
    ∑ i ∈ Finset.range E.1,
        dist (f (E.2 i).1).re (f (E.2 i).2).re ≤
        ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [Real.dist_eq, Complex.dist_eq] using
        Complex.abs_re_le_norm (f (E.2 i).1 - f (E.2 i).2)
    _ < ε := hfδ E hE hlen

private theorem complex_im_absolutelyContinuousOnInterval
    {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x).im) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  calc
    ∑ i ∈ Finset.range E.1,
        dist (f (E.2 i).1).im (f (E.2 i).2).im ≤
        ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [Real.dist_eq, Complex.dist_eq] using
        Complex.abs_im_le_norm (f (E.2 i).1 - f (E.2 i).2)
    _ < ε := hfδ E hE hlen

private theorem intervalIntegrable_continuousLinearMap_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (L : E →L[ℝ] F) :
    IntervalIntegrable (fun x => L (f x)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

private theorem complex_deriv_intervalIntegrable_of_absolutelyContinuousOnInterval
    {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b := by
  let fre : ℝ → ℝ := fun x => (f x).re
  let fim : ℝ → ℝ := fun x => (f x).im
  have hreAC : AbsolutelyContinuousOnInterval fre a b := by
    simpa only [fre] using complex_re_absolutelyContinuousOnInterval hf
  have himAC : AbsolutelyContinuousOnInterval fim a b := by
    simpa only [fim] using complex_im_absolutelyContinuousOnInterval hf
  have hreI : IntervalIntegrable (deriv fre) volume a b :=
    hreAC.intervalIntegrable_deriv
  have himI : IntervalIntegrable (deriv fim) volume a b :=
    himAC.intervalIntegrable_deriv
  have hreC : IntervalIntegrable (fun x => ((deriv fre x : ℝ) : ℂ)) volume a b := by
    simpa only [Complex.ofRealCLM_apply] using
      intervalIntegrable_continuousLinearMap_comp hreI Complex.ofRealCLM
  have himC : IntervalIntegrable (fun x => ((deriv fim x : ℝ) : ℂ)) volume a b := by
    simpa only [Complex.ofRealCLM_apply] using
      intervalIntegrable_continuousLinearMap_comp himI Complex.ofRealCLM
  have hreconstruct : IntervalIntegrable
      (fun x => ((deriv fre x : ℝ) : ℂ) +
        Complex.I * ((deriv fim x : ℝ) : ℂ)) volume a b := by
    have hI := himC.smul Complex.I
    simpa [Pi.smul_apply, smul_eq_mul] using hreC.add hI
  have heq : deriv f =ᵐ[volume.restrict (Set.uIoc a b)]
      (fun x => ((deriv fre x : ℝ) : ℂ) +
        Complex.I * ((deriv fim x : ℝ) : ℂ)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hreAC.ae_differentiableAt, himAC.ae_differentiableAt] with
      x hreDiff himDiff
    intro hx
    have hxU : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    have hreHas : HasDerivAt (fun y => ((fre y : ℝ) : ℂ))
        ((deriv fre x : ℝ) : ℂ) x := by
      simpa only [Complex.ofRealCLM_apply, Function.comp_apply] using
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
          ((hreDiff hxU).hasDerivAt)
    have himHas : HasDerivAt (fun y => ((fim y : ℝ) : ℂ))
        ((deriv fim x : ℝ) : ℂ) x := by
      simpa only [Complex.ofRealCLM_apply, Function.comp_apply] using
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
          ((himDiff hxU).hasDerivAt)
    have hsum := hreHas.add (himHas.const_mul Complex.I)
    have hfun : (fun y => ((fre y : ℝ) : ℂ) +
        Complex.I * ((fim y : ℝ) : ℂ)) = f := by
      funext y
      apply Complex.ext <;> simp [fre, fim]
    have hfHas : HasDerivAt f
        (((deriv fre x : ℝ) : ℂ) +
          Complex.I * ((deriv fim x : ℝ) : ℂ)) x := by
      rw [← hfun]
      simpa [mul_comm] using hsum
    exact hfHas.deriv
  exact hreconstruct.congr_ae heq.symm

/-!
# H2a.4.1b.3c.1.13A — selected Ferrers piecewise-AC Fourier decay (W4)

This is the exact production full-endpoint, complex-valued, fixed-`k` node.
The lower additive endpoint is both a zero-extension boundary and the
`n = k + 2` production seam.  The public safe jump ledger therefore pays that
seam as its final finite summand.
-/

noncomputable def selectedFerrersAbelLogRepresentative
    (k : ℕ) : ℝ → ℂ :=
  fun x =>
    selectedFerrersAbelLimit k
      (Real.exp x /
        lambda_m (selectedFerrersPreAnchorIndex k))

noncomputable def selectedFerrersAbelLogZeroExtension
    (k : ℕ) : ℝ → ℂ :=
  Set.indicator
    (Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k)))
    (selectedFerrersAbelLogRepresentative k)

/-- A compact additive-log interval lies in the selected window and avoids
every full-endpoint production seam. -/
def selectedFerrersAbelLogSeamFreeOn
    (k : ℕ) (a b : ℝ) : Prop :=
  Set.uIcc a b ⊆
      Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k)) ∧
    ∀ n : ℕ+, ∀ x ∈ Set.uIcc a b,
      (((n : ℕ) : ℝ) *
          (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k))) ≠
        lambda_m (selectedFerrersPreAnchorIndex k)

private noncomputable def selectedFerrersAbelLogArgument
    (k : ℕ) (n : ℕ+) (x : ℝ) : ℝ :=
  ((n : ℕ) : ℝ) *
    (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))

private noncomputable def selectedFerrersAbelLogProductionTerm
    (k : ℕ) (n : ℕ+) (x : ℝ) : ℂ :=
  (Real.sqrt
      (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) *
    selectedFerrersLemma73SourcePacket k
      (selectedFerrersAbelLogArgument k n x)

private noncomputable def selectedFerrersAbelLogSeam
    (k : ℕ) (n : ℕ+) : ℝ :=
  Real.log (((k + 2 : ℕ) : ℝ) / ((n : ℕ) : ℝ))

private noncomputable def selectedFerrersAbelLogCellRepresentative
    (k : ℕ) (j : ℕ+) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc (1 : ℕ+) j,
    selectedFerrersAbelLogProductionTerm k n x) +
  (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
    (Real.sqrt
      (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)

private theorem selectedFerrersAbelLogArgument_continuous
    (k : ℕ) (n : ℕ+) :
    Continuous (selectedFerrersAbelLogArgument k n) := by
  unfold selectedFerrersAbelLogArgument
  fun_prop

private theorem selectedFerrersAbelLogArgument_hasDerivAt
    (k : ℕ) (n : ℕ+) (x : ℝ) :
    HasDerivAt (selectedFerrersAbelLogArgument k n)
      ((((n : ℕ) : ℝ) /
          lambda_m (selectedFerrersPreAnchorIndex k)) * Real.exp x) x := by
  simpa only [selectedFerrersAbelLogArgument, div_eq_mul_inv, mul_assoc,
    mul_comm, mul_left_comm] using
    (Real.hasDerivAt_exp x).const_mul
      (((n : ℕ) : ℝ) /
        lambda_m (selectedFerrersPreAnchorIndex k))

/-- On a seam-free connected interval, one production term is either active
throughout or already strictly beyond the closed physical support throughout. -/
private theorem selectedFerrersAbelLogArgument_side_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) (n : ℕ+) :
    (∀ x ∈ Set.uIcc a b,
        selectedFerrersAbelLogArgument k n x <
          lambda_m (selectedFerrersPreAnchorIndex k)) ∨
      (∀ x ∈ Set.uIcc a b,
        lambda_m (selectedFerrersPreAnchorIndex k) <
          selectedFerrersAbelLogArgument k n x) := by
  let f := selectedFerrersAbelLogArgument k n
  let lam := lambda_m (selectedFerrersPreAnchorIndex k)
  have hf : Continuous f := selectedFerrersAbelLogArgument_continuous k n
  have himage : IsPreconnected (f '' Set.uIcc a b) :=
    isPreconnected_uIcc.image f hf.continuousOn
  have hcover : f '' Set.uIcc a b ⊆ Set.Iio lam ∪ Set.Ioi lam := by
    rintro y ⟨x, hx, rfl⟩
    have hne : f x ≠ lam := by
      simpa only [f, lam, selectedFerrersAbelLogArgument] using hfree.2 n x hx
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt
  have hdisj : Disjoint (Set.Iio lam) (Set.Ioi lam) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge (le_of_lt (Set.mem_Iio.mp hx))) (Set.mem_Ioi.mp hy)
  rcases IsPreconnected.subset_or_subset isOpen_Iio isOpen_Ioi hdisj hcover himage with
      hleft | hright
  · left
    intro x hx
    exact hleft ⟨x, hx, rfl⟩
  · right
    intro x hx
    exact hright ⟨x, hx, rfl⟩

private theorem selectedFerrersAbelLogArgument_lipschitzOn
    (k : ℕ) (n : ℕ+) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      LipschitzOnWith (Real.toNNReal C)
        (selectedFerrersAbelLogArgument k n) (Set.uIcc a b) := by
  let lam := lambda_m (selectedFerrersPreAnchorIndex k)
  let C : ℝ := (((n : ℕ) : ℝ) / lam) * Real.exp (max a b)
  have hlam : 0 < lam := by
    simp only [lam, lambda_m, selectedFerrersPreAnchorIndex]
    exact Real.sqrt_pos.2 (by positivity)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  have hderiv : ∀ z ∈ Set.uIcc a b,
      HasDerivWithinAt (selectedFerrersAbelLogArgument k n)
        ((((n : ℕ) : ℝ) / lam) * Real.exp z) (Set.uIcc a b) z := by
    intro z hz
    apply HasDerivAt.hasDerivWithinAt
    simpa only [selectedFerrersAbelLogArgument, lam, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using
      (Real.hasDerivAt_exp z).const_mul (((n : ℕ) : ℝ) / lam)
  have hbound : ∀ z ∈ Set.uIcc a b,
      ‖(((n : ℕ) : ℝ) / lam) * Real.exp z‖ ≤ C := by
    intro z hz
    have hzle : z ≤ max a b := by
      rcases Set.mem_uIcc.mp hz with hz | hz
      · exact hz.2.trans (le_max_right _ _)
      · exact hz.2.trans (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (((n : ℕ) : ℝ) / lam) * Real.exp z)]
    dsimp [C]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzle) (by positivity)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_uIcc a b) hx hy
  simpa [Real.dist_eq, Real.coe_toNNReal C hC, norm_sub_rev] using hmv

private theorem selectedFerrersLemma73SourcePacket_eq_zero_of_lambda_lt
    (k : ℕ) {u : ℝ}
    (hu : lambda_m (selectedFerrersPreAnchorIndex k) < u) :
    selectedFerrersLemma73SourcePacket k u = 0 := by
  rw [selectedFerrersLemma73SourcePacket,
    prolateCombination_eq_zero_outside]
  · simp
  · intro hmem
    rw [(selectedFerrersPreAnchorPair_spec k).1] at hmem
    exact (not_lt_of_ge hmem.2) hu

private theorem firstDerivativeTerm_abs_le_closed
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |mode4FerrersFirstDerivativeTerm a q x| ≤
      4 * ((((q + 1 : ℕ) : ℝ)) ^ 2 * |a q|) := by
  have hP :=
    mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed (2 * q) x hx
  rw [mode4FerrersFirstDerivativeTerm, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul]
  have hcoef : ((2 * q : ℕ) : ℝ) * ((2 * q : ℕ) + 1) ≤
      4 * (((q + 1 : ℕ) : ℝ)) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((q : ℝ) + 1)]
  calc
    |a q| * |(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x| ≤
        |a q| * (((2 * q : ℕ) : ℝ) * ((2 * q : ℕ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact_mod_cast hP
    _ ≤ |a q| * (4 * (((q + 1 : ℕ) : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)
    _ = 4 * ((((q + 1 : ℕ) : ℝ)) ^ 2 * |a q|) := by ring

/-- Closed-interval bound for the derivative series under the weighted
coefficient summability. -/
private theorem firstDerivativeSeries_abs_le_closed
    (a : ℕ → ℝ)
    (hW : Summable (fun q : ℕ => (((q + 1 : ℕ) : ℝ)) ^ 2 * |a q|))
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |mode4FerrersFirstDerivativeSeries a x| ≤
      4 * ∑' q : ℕ, (((q + 1 : ℕ) : ℝ)) ^ 2 * |a q| := by
  have hW4 : Summable (fun q : ℕ =>
      4 * ((((q + 1 : ℕ) : ℝ)) ^ 2 * |a q|)) := hW.mul_left 4
  have hnorm : Summable (fun q : ℕ =>
      ‖mode4FerrersFirstDerivativeTerm a q x‖) := by
    apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ hW4
    intro q
    rw [Real.norm_eq_abs]
    exact firstDerivativeTerm_abs_le_closed a q x hx
  rw [mode4FerrersFirstDerivativeSeries, ← Real.norm_eq_abs]
  calc
    ‖∑' q : ℕ, mode4FerrersFirstDerivativeTerm a q x‖ ≤
        ∑' q : ℕ, ‖mode4FerrersFirstDerivativeTerm a q x‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, 4 * ((((q + 1 : ℕ) : ℝ)) ^ 2 * |a q|) := by
      apply hnorm.tsum_le_tsum _ hW4
      intro q
      rw [Real.norm_eq_abs]
      exact firstDerivativeTerm_abs_le_closed a q x hx
    _ = 4 * ∑' q : ℕ, (((q + 1 : ℕ) : ℝ)) ^ 2 * |a q| := tsum_mul_left

/-- The selected schedule supplies the weighted summability from the
tail splice: weight `(q+1)²` is the polynomially weighted row at `r = 2`. -/
private theorem selected_weighted_summable
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep : ∀ q ≥ K,
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q|) := by
  have h :=
    mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
      mProject K Λ hm hK hsep hΛ S.coefficients S.tail_splice 2
  apply h.congr
  intro q
  push_cast
  ring

/-! ## Step 3 — Lipschitz bound on the closed dimensionless interval -/

/-- Pairwise Lipschitz estimate on the open interval extends to the closed
interval through continuity, along the exact contraction family
`z_n(t) = t·(n+1)/(n+2)` toward the center. -/
private theorem lipschitz_pairs_closed_of_open
    {f : ℝ → ℝ} {C : ℝ}
    (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hpair : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      |f y - f x| ≤ C * |y - x|) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |f y - f x| ≤ C * |y - x| := by
  intro x hx y hy
  set z : ℕ → ℝ → ℝ := fun n t => t * (((n : ℝ) + 1) / ((n : ℝ) + 2))
    with hz
  have hratio_lt : ∀ n : ℕ, ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
    intro n
    rw [div_lt_one (by positivity)]
    linarith
  have hratio_nonneg : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    intro n
    positivity
  have hmemz : ∀ n : ℕ, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      z n t ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro n t ht
    have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hzabs : |z n t| < 1 := by
      rw [hz]
      simp only []
      rw [abs_mul, abs_of_nonneg (hratio_nonneg n)]
      calc
        |t| * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ≤
            1 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_right habs (hratio_nonneg n)
        _ = ((n : ℝ) + 1) / ((n : ℝ) + 2) := one_mul _
        _ < 1 := hratio_lt n
    exact ⟨neg_lt_of_abs_lt hzabs, lt_of_abs_lt hzabs⟩
  have hratio_tendsto :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2))
        Filter.atTop (nhds 1) := by
    have hrw : ∀ n : ℕ, ((n : ℝ) + 1) / ((n : ℝ) + 2) =
        1 - (((n : ℝ) + 2))⁻¹ := by
      intro n
      field_simp
      ring
    simp only [hrw]
    have hinv : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 2))⁻¹)
        Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.comp tendsto_inv_atTop_zero
      exact Filter.tendsto_atTop_add_const_right _ 2
        tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (x := (1 : ℝ))
      (f := Filter.atTop (α := ℕ))).sub hinv
    simpa using this
  have hztend : ∀ t : ℝ, Filter.Tendsto (fun n : ℕ => z n t)
      Filter.atTop (nhds t) := by
    intro t
    have := (tendsto_const_nhds (x := t)
      (f := Filter.atTop (α := ℕ))).mul hratio_tendsto
    simpa [hz] using this
  have hftend : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ => f (z n t)) Filter.atTop (nhds (f t)) := by
    intro t ht
    have hcw : ContinuousWithinAt f (Set.Icc (-1 : ℝ) 1) t := hcont t ht
    apply hcw.tendsto.comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hztend t
    · exact Filter.Eventually.of_forall
        (fun n => Set.Ioo_subset_Icc_self (hmemz n t ht))
  have hA : Filter.Tendsto
      (fun n : ℕ => |f (z n y) - f (z n x)|)
      Filter.atTop (nhds (|f y - f x|)) :=
    ((hftend y hy).sub (hftend x hx)).abs
  have hB : Filter.Tendsto
      (fun n : ℕ => C * |z n y - z n x|)
      Filter.atTop (nhds (C * |y - x|)) := by
    apply Filter.Tendsto.const_mul
    exact ((hztend y).sub (hztend x)).abs
  apply le_of_tendsto_of_tendsto' hA hB
  intro n
  exact hpair (z n x) (hmemz n x hx) (z n y) (hmemz n y hy)

/-- The dimensionless Ferrers series of any regular even prolate solution on
the selected schedule is Lipschitz on the closed interval, with the exact
series constant `4·∑ (q+1)²|a_q|`. -/
private theorem ferrersSeries_lipschitz_closed
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hW : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q|)) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |mode4FerrersSeries S.coefficients y -
          mode4FerrersSeries S.coefficients x| ≤
        (4 * ∑' q : ℕ, (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q|) *
          |y - x| := by
  have hopen : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      |mode4FerrersSeries S.coefficients y -
          mode4FerrersSeries S.coefficients x| ≤
        (4 * ∑' q : ℕ, (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q|) *
          |y - x| := by
    intro x hx y hy
    have hmvt :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := mode4FerrersSeries S.coefficients)
        (f' := mode4FerrersFirstDerivativeSeries S.coefficients)
        (C := 4 * ∑' q : ℕ,
          (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q|)
        (s := Set.Ioo (-1 : ℝ) 1)
        (fun t ht =>
          (S.ferrersSeries_hasDerivAt_firstDerivativeSeries t
            ht).hasDerivWithinAt)
        (fun t ht => by
          rw [Real.norm_eq_abs]
          exact firstDerivativeSeries_abs_le_closed S.coefficients hW t
            (Set.Ioo_subset_Icc_self ht))
        (convex_Ioo _ _) hx hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  exact lipschitz_pairs_closed_of_open S.continuousOn_closed hopen

/-! ## Step 4 — transport to the physical normalized modes -/

/-- The normalized physical mode of a selected-schedule solution is Lipschitz
on its closed physical window.  The constant pays the dimensionless series
constant, the physical scale `√m` and the positive `L²` normalization. -/
private theorem normalizedPhysicalMode_lipschitz_on_window
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hW : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q|)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ Set.Icc (-Real.sqrt mProject) (Real.sqrt mProject),
      ∀ v ∈ Set.Icc (-Real.sqrt mProject) (Real.sqrt mProject),
        ‖S.normalizedPhysicalMode u - S.normalizedPhysicalMode v‖ ≤
          C * |u - v| := by
  have hmpos : (0 : ℝ) < (mProject : ℝ) := by
    have : (2 : ℝ) ≤ (mProject : ℝ) := by exact_mod_cast hm
    linarith
  have hsq : (0 : ℝ) < Real.sqrt mProject := Real.sqrt_pos.mpr hmpos
  set M : ℝ :=
    4 * ∑' q : ℕ, (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q| with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have : 0 ≤ ∑' q : ℕ, (((q + 1 : ℕ) : ℝ)) ^ 2 * |S.coefficients q| :=
      tsum_nonneg fun q => by positivity
    linarith
  have hN0 : 0 ≤ S.physicalL2Normalization := Real.sqrt_nonneg _
  refine ⟨M / (Real.sqrt mProject * S.physicalL2Normalization),
    div_nonneg hM0 (mul_nonneg hsq.le hN0), ?_⟩
  intro u hu v hv
  by_cases hN : S.physicalL2Normalization = 0
  · simp only [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      hN, Complex.ofReal_zero, div_zero, sub_zero, norm_zero]
    rw [mul_zero, div_zero, zero_mul]
  have hNpos : 0 < S.physicalL2Normalization :=
    lt_of_le_of_ne hN0 (Ne.symm hN)
  have hmemdiv : ∀ w ∈ Set.Icc (-Real.sqrt mProject) (Real.sqrt mProject),
      w / Real.sqrt mProject ∈ Set.Icc (-1 : ℝ) 1 := by
    intro w hw
    constructor
    · rw [le_div_iff₀ hsq]
      linarith [hw.1]
    · rw [div_le_one hsq]
      exact hw.2
  have hlip := ferrersSeries_lipschitz_closed S hW
    (v / Real.sqrt mProject) (hmemdiv v hv)
    (u / Real.sqrt mProject) (hmemdiv u hu)
  have hueq : S.normalizedPhysicalMode u =
      ((mode4PhysicalFerrersSeries mProject S.coefficients u : ℝ) : ℂ) /
        (S.physicalL2Normalization : ℂ) := by
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      Set.indicator_of_mem hu, mode4PhysicalFerrersSeriesComplex]
  have hveq : S.normalizedPhysicalMode v =
      ((mode4PhysicalFerrersSeries mProject S.coefficients v : ℝ) : ℂ) /
        (S.physicalL2Normalization : ℂ) := by
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      Set.indicator_of_mem hv, mode4PhysicalFerrersSeriesComplex]
  rw [hueq, hveq, div_sub_div_same, ← Complex.ofReal_sub, norm_div,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hN0]
  have hseries :
      |mode4PhysicalFerrersSeries mProject S.coefficients u -
          mode4PhysicalFerrersSeries mProject S.coefficients v| ≤
        M * |u - v| / Real.sqrt mProject := by
    have h1 := hlip
    rw [← hMdef] at h1
    simp only [mode4PhysicalFerrersSeries] at *
    calc
      |mode4FerrersSeries S.coefficients (u / Real.sqrt mProject) -
          mode4FerrersSeries S.coefficients (v / Real.sqrt mProject)| ≤
          M * |u / Real.sqrt mProject - v / Real.sqrt mProject| := h1
      _ = M * (|u - v| / Real.sqrt mProject) := by
        rw [div_sub_div_same, abs_div, abs_of_pos hsq]
      _ = M * |u - v| / Real.sqrt mProject := by ring
  calc
    |mode4PhysicalFerrersSeries mProject S.coefficients u -
        mode4PhysicalFerrersSeries mProject S.coefficients v| /
        S.physicalL2Normalization ≤
        (M * |u - v| / Real.sqrt mProject) / S.physicalL2Normalization := by
      gcongr
    _ = M / (Real.sqrt mProject * S.physicalL2Normalization) * |u - v| := by
      field_simp

private theorem selectedPacket_lipschitz_on_window (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda,
      ∀ v ∈ Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda,
        ‖selectedFerrersLemma73SourcePacket k u -
            selectedFerrersLemma73SourcePacket k v‖ ≤ C * |u - v| := by
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  have hG : 0 < mode4JacobiG (k + 2) := by
    rw [mode4JacobiG]
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    push_cast
    positivity
  have hm : 2 ≤ k + 2 := by omega
  have hK : 3 ≤ 5 * (k + 2) := by omega
  have hsep := selectedFerrersPreAnchorSeparation k
  have hΛ0 : mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 ≤ 20 :=
    (mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three
      (mode4JacobiG (k + 2)) hG 0 (by omega)).le
  have hΛ4 : mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 ≤ 20 :=
    (mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three
      (mode4JacobiG (k + 2)) hG 2 (by omega)).le
  have hW0 := selected_weighted_summable
    (selectedFerrersPreAnchorSolution0 k) hm hK hsep hΛ0
  have hW4 := selected_weighted_summable
    (selectedFerrersPreAnchorSolution4 k) hm hK hsep hΛ4
  obtain ⟨C0, hC00, hlip0⟩ := normalizedPhysicalMode_lipschitz_on_window
    (selectedFerrersPreAnchorSolution0 k) hm hW0
  obtain ⟨C4, hC40, hlip4⟩ := normalizedPhysicalMode_lipschitz_on_window
    (selectedFerrersPreAnchorSolution4 k) hm hW4
  set P := selectedFerrersPreAnchorPair k with hP
  set den : ℝ := Real.sqrt (P.I0 ^ 2 + P.I4 ^ 2) with hden
  have hden0 : 0 ≤ den := Real.sqrt_nonneg _
  refine ⟨‖selectedFerrersLemma73SourceScale k‖ *
    ((|P.I4| * C0 + |P.I0| * C4) / den), ?_, ?_⟩
  · apply mul_nonneg (norm_nonneg _)
    apply div_nonneg _ hden0
    have h1 : 0 ≤ |P.I4| * C0 := mul_nonneg (abs_nonneg _) hC00
    have h2 : 0 ≤ |P.I0| * C4 := mul_nonneg (abs_nonneg _) hC40
    linarith
  intro u hu v hv
  have hwin : Set.Icc (-P.pw.lambda) P.pw.lambda =
      Set.Icc (-Real.sqrt (((k + 2 : ℕ) : ℝ))) (Real.sqrt (((k + 2 : ℕ) : ℝ))) := by
    rw [hlam]
  rw [hwin] at hu hv
  have hd0 : ‖P.h0 u - P.h0 v‖ ≤ C0 * |u - v| := by
    rw [hh0]
    exact hlip0 u hu v hv
  have hd4 : ‖P.h4 u - P.h4 v‖ ≤ C4 * |u - v| := by
    rw [hh4]
    exact hlip4 u hu v hv
  have hpacket : ∀ x : ℝ, selectedFerrersLemma73SourcePacket k x =
      selectedFerrersLemma73SourceScale k *
        (((P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x) / (den : ℂ)) := by
    intro x
    rw [selectedFerrersLemma73SourcePacket, prolateCombination,
      ProlatePair.normalizingDenominator_eq]
  rw [hpacket u, hpacket v, ← mul_sub, div_sub_div_same, norm_mul,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hden0]
  have hnum : ‖(P.I4 : ℂ) * P.h0 u - (P.I0 : ℂ) * P.h4 u -
      ((P.I4 : ℂ) * P.h0 v - (P.I0 : ℂ) * P.h4 v)‖ ≤
      (|P.I4| * C0 + |P.I0| * C4) * |u - v| := by
    have hre : (P.I4 : ℂ) * P.h0 u - (P.I0 : ℂ) * P.h4 u -
        ((P.I4 : ℂ) * P.h0 v - (P.I0 : ℂ) * P.h4 v) =
        (P.I4 : ℂ) * (P.h0 u - P.h0 v) - (P.I0 : ℂ) * (P.h4 u - P.h4 v) := by
      ring
    rw [hre]
    calc
      ‖(P.I4 : ℂ) * (P.h0 u - P.h0 v) -
          (P.I0 : ℂ) * (P.h4 u - P.h4 v)‖ ≤
          ‖(P.I4 : ℂ) * (P.h0 u - P.h0 v)‖ +
            ‖(P.I0 : ℂ) * (P.h4 u - P.h4 v)‖ := norm_sub_le _ _
      _ = |P.I4| * ‖P.h0 u - P.h0 v‖ + |P.I0| * ‖P.h4 u - P.h4 v‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |P.I4| * (C0 * |u - v|) + |P.I0| * (C4 * |u - v|) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hd0 (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left hd4 (abs_nonneg _)
      _ = (|P.I4| * C0 + |P.I0| * C4) * |u - v| := by ring
  by_cases hdz : den = 0
  · rw [hdz]
    simp only [div_zero, mul_zero, zero_mul]
    positivity
  have hdpos : 0 < den := lt_of_le_of_ne hden0 (Ne.symm hdz)
  calc
    ‖selectedFerrersLemma73SourceScale k‖ *
        (‖(P.I4 : ℂ) * P.h0 u - (P.I0 : ℂ) * P.h4 u -
          ((P.I4 : ℂ) * P.h0 v - (P.I0 : ℂ) * P.h4 v)‖ / den) ≤
        ‖selectedFerrersLemma73SourceScale k‖ *
          (((|P.I4| * C0 + |P.I0| * C4) * |u - v|) / den) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      gcongr
    _ = ‖selectedFerrersLemma73SourceScale k‖ *
        ((|P.I4| * C0 + |P.I0| * C4) / den) * |u - v| := by
      ring

/-- The exact selected packet is differentiable at every point strictly inside
its physical window.  The derivative value is deliberately existential: W4
only needs a right-derivative supplier for integration by parts, not another
public formula. -/
private theorem selectedFerrersLemma73SourcePacket_hasDerivAt_of_mem_Ioo
    (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioo
      (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda) :
    ∃ u' : ℂ, HasDerivAt
      (selectedFerrersLemma73SourcePacket k) u' u := by
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  have hm : 2 ≤ k + 2 := by omega
  have hu' : u ∈ Set.Ioo
      (-Real.sqrt (((k + 2 : ℕ) : ℝ)))
      (Real.sqrt (((k + 2 : ℕ) : ℝ))) := by
    simpa [hlam] using hu
  obtain ⟨d0, hd0⟩ : ∃ d0 : ℂ,
      HasDerivAt
        (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode d0 u := by
    exact ⟨_, normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution0 k) hm hu'⟩
  obtain ⟨d4, hd4⟩ : ∃ d4 : ℂ,
      HasDerivAt
        (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode d4 u := by
    exact ⟨_, normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution4 k) hm hu'⟩
  refine ⟨selectedFerrersLemma73SourceScale k *
      (((selectedFerrersPreAnchorPair k).I4 : ℂ) * d0 -
        ((selectedFerrersPreAnchorPair k).I0 : ℂ) * d4) /
      ((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ), ?_⟩
  change HasDerivAt
    (fun x => selectedFerrersLemma73SourceScale k *
      ((((selectedFerrersPreAnchorPair k).I4 : ℂ) *
          (selectedFerrersPreAnchorPair k).h0 x -
        ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
          (selectedFerrersPreAnchorPair k).h4 x) /
        ((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ))) _ u
  rw [hh0, hh4]
  convert (((hd0.const_mul
      ((selectedFerrersPreAnchorPair k).I4 : ℂ)).sub
        (hd4.const_mul
          ((selectedFerrersPreAnchorPair k).I0 : ℂ))).div_const
      ((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ)).const_mul
        (selectedFerrersLemma73SourceScale k) using 1 <;> ring

private theorem selectedFerrersAbelLogPacketTerm_hasDerivAt_of_argument_mem_Ioo
    (k : ℕ) (n : ℕ+) {x : ℝ}
    (hx : selectedFerrersAbelLogArgument k n x ∈ Set.Ioo
      (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda) :
    ∃ d : ℂ, HasDerivAt
      (fun y => selectedFerrersLemma73SourcePacket k
        (selectedFerrersAbelLogArgument k n y)) d x := by
  obtain ⟨d, hd⟩ :=
    selectedFerrersLemma73SourcePacket_hasDerivAt_of_mem_Ioo k hx
  refine ⟨((((n : ℕ) : ℝ) /
      lambda_m (selectedFerrersPreAnchorIndex k)) * Real.exp x) • d, ?_⟩
  simpa only [Function.comp_apply] using
    hd.scomp x (selectedFerrersAbelLogArgument_hasDerivAt k n x)

private theorem
    selectedFerrersAbelLogPacketTerm_absolutelyContinuousOnInterval_of_mapsToWindow
    (k : ℕ) (n : ℕ+) {a b : ℝ}
    (hmem : ∀ x ∈ Set.uIcc a b,
      selectedFerrersAbelLogArgument k n x ∈
        Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
          (selectedFerrersPreAnchorPair k).pw.lambda) :
    AbsolutelyContinuousOnInterval
      (fun x => selectedFerrersLemma73SourcePacket k
        (selectedFerrersAbelLogArgument k n x)) a b := by
  obtain ⟨Cpacket, hCpacket, hpacket⟩ :=
    selectedPacket_lipschitz_on_window k
  obtain ⟨Carg, hCarg, harg⟩ :=
    selectedFerrersAbelLogArgument_lipschitzOn k n a b
  have hlip : LipschitzOnWith (Real.toNNReal (Cpacket * Carg))
      (fun x => selectedFerrersLemma73SourcePacket k
        (selectedFerrersAbelLogArgument k n x)) (Set.uIcc a b) := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    have hp := hpacket _ (hmem x hx) _ (hmem y hy)
    have ha := harg.dist_le_mul x hx y hy
    rw [Complex.dist_eq, Real.dist_eq]
    rw [Real.coe_toNNReal Carg hCarg] at ha
    calc
      ‖selectedFerrersLemma73SourcePacket k
            (selectedFerrersAbelLogArgument k n x) -
          selectedFerrersLemma73SourcePacket k
            (selectedFerrersAbelLogArgument k n y)‖ ≤
          Cpacket * |selectedFerrersAbelLogArgument k n x -
            selectedFerrersAbelLogArgument k n y| := hp
      _ ≤ Cpacket * (Carg * |x - y|) :=
        mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using ha) hCpacket
      _ = (Cpacket * Carg) * |x - y| := by ring
  exact hlip.absolutelyContinuousOnInterval



private theorem selectedFerrersAbelLogPacketTerm_lipschitzOn_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) (n : ℕ+) :
    ∃ C : ℝ, 0 ≤ C ∧
      LipschitzOnWith (Real.toNNReal C)
        (fun x => selectedFerrersLemma73SourcePacket k
          (selectedFerrersAbelLogArgument k n x)) (Set.uIcc a b) := by
  rcases selectedFerrersAbelLogArgument_side_of_seamFree k hfree n with
      hinside | houtside
  · obtain ⟨Cpacket, hCpacket, hpacket⟩ :=
      selectedPacket_lipschitz_on_window k
    obtain ⟨Carg, hCarg, harg⟩ :=
      selectedFerrersAbelLogArgument_lipschitzOn k n a b
    refine ⟨Cpacket * Carg, mul_nonneg hCpacket hCarg, ?_⟩
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    have hlam : 0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
      simp only [lambda_m, selectedFerrersPreAnchorIndex]
      exact Real.sqrt_pos.2 (by positivity)
    have hxarg0 : 0 ≤ selectedFerrersAbelLogArgument k n x := by
      unfold selectedFerrersAbelLogArgument
      positivity
    have hyarg0 : 0 ≤ selectedFerrersAbelLogArgument k n y := by
      unfold selectedFerrersAbelLogArgument
      positivity
    have hxmem : selectedFerrersAbelLogArgument k n x ∈
        Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
          (selectedFerrersPreAnchorPair k).pw.lambda := by
      constructor
      · calc
          -(selectedFerrersPreAnchorPair k).pw.lambda =
              -lambda_m (selectedFerrersPreAnchorIndex k) := by
                exact congrArg Neg.neg (selectedFerrersPreAnchorPair_spec k).1
          _ ≤ 0 := neg_nonpos.mpr hlam.le
          _ ≤ selectedFerrersAbelLogArgument k n x := hxarg0
      · rw [(selectedFerrersPreAnchorPair_spec k).1]
        exact (hinside x hx).le
    have hymem : selectedFerrersAbelLogArgument k n y ∈
        Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
          (selectedFerrersPreAnchorPair k).pw.lambda := by
      constructor
      · calc
          -(selectedFerrersPreAnchorPair k).pw.lambda =
              -lambda_m (selectedFerrersPreAnchorIndex k) := by
                exact congrArg Neg.neg (selectedFerrersPreAnchorPair_spec k).1
          _ ≤ 0 := neg_nonpos.mpr hlam.le
          _ ≤ selectedFerrersAbelLogArgument k n y := hyarg0
      · rw [(selectedFerrersPreAnchorPair_spec k).1]
        exact (hinside y hy).le
    have hp := hpacket _ hxmem _ hymem
    have ha := harg.dist_le_mul x hx y hy
    rw [Complex.dist_eq, Real.dist_eq]
    rw [Real.dist_eq, Real.coe_toNNReal Carg hCarg] at ha
    calc
      ‖selectedFerrersLemma73SourcePacket k
            (selectedFerrersAbelLogArgument k n x) -
          selectedFerrersLemma73SourcePacket k
            (selectedFerrersAbelLogArgument k n y)‖ ≤
          Cpacket * |selectedFerrersAbelLogArgument k n x -
            selectedFerrersAbelLogArgument k n y| := hp
      _ ≤ Cpacket * (Carg * |x - y|) :=
        mul_le_mul_of_nonneg_left ha hCpacket
      _ = (Cpacket * Carg) * |x - y| := by ring
  · refine ⟨0, le_rfl, ?_⟩
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    rw [selectedFerrersLemma73SourcePacket_eq_zero_of_lambda_lt k (houtside x hx),
      selectedFerrersLemma73SourcePacket_eq_zero_of_lambda_lt k (houtside y hy)]
    simp

private theorem selectedFerrersAbelLogFiniteCore_absolutelyContinuousOnInterval_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) :
    AbsolutelyContinuousOnInterval
      (fun x => finiteEStarCore
        (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
        (selectedFerrersLemma73SourcePacket k)
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) a b := by
  classical
  have hterm : ∀ n : ℕ+,
      AbsolutelyContinuousOnInterval
        (fun x => selectedFerrersLemma73SourcePacket k
          (selectedFerrersAbelLogArgument k n x)) a b := by
    intro n
    obtain ⟨C, hC, hlip⟩ :=
      selectedFerrersAbelLogPacketTerm_lipschitzOn_of_seamFree k hfree n
    exact hlip.absolutelyContinuousOnInterval
  have hsum : ∀ S : Finset ℕ+,
      AbsolutelyContinuousOnInterval
        (fun x => ∑ n ∈ S,
          selectedFerrersLemma73SourcePacket k
            (selectedFerrersAbelLogArgument k n x)) a b := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        have hzlip : LipschitzOnWith 0 (fun _ : ℝ => (0 : ℂ))
            (Set.uIcc a b) :=
          (LipschitzWith.const (α := ℝ) (0 : ℂ)).lipschitzOnWith
        simpa using hzlip.absolutelyContinuousOnInterval
    | @insert n S hn ih =>
        simpa [Finset.sum_insert, hn] using (hterm n).fun_add ih
  simpa only [finiteEStarCore, selectedFerrersAbelLogArgument] using
    hsum (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))

private theorem selectedFerrersAbelLogSqrtWeight_eq
    (k : ℕ) (x : ℝ) :
    Real.sqrt
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) =
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ *
        Real.exp (x / 2) := by
  rw [div_eq_mul_inv, Real.sqrt_mul (Real.exp_nonneg x), ← Real.exp_half]
  ring

private theorem selectedFerrersAbelLogSqrtWeight_hasDerivAt
    (k : ℕ) (x : ℝ) :
    ∃ d : ℂ, HasDerivAt
      (fun y =>
        (Real.sqrt
          (Real.exp y /
            lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)) d x := by
  have heq : (fun y =>
      (Real.sqrt
        (Real.exp y /
          lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)) =
      (fun y =>
        ((Real.sqrt
          (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ *
            Real.exp (y / 2) : ℝ) : ℂ)) := by
    funext y
    rw [selectedFerrersAbelLogSqrtWeight_eq]
  rw [heq]
  let D : ℝ := Real.sqrt
    (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹
  have hr : HasDerivAt (fun y : ℝ => D * Real.exp (y / 2))
      (D * ((1 / 2 : ℝ) * Real.exp (x / 2))) x := by
    convert ((Real.hasDerivAt_exp (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)).const_mul D using 1 <;> ring
  refine ⟨((D * ((1 / 2 : ℝ) * Real.exp (x / 2)) : ℝ) : ℂ), ?_⟩
  simpa only [D, Complex.ofRealCLM_apply, Function.comp_apply] using
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hr

private theorem selectedFerrersAbelLogProductionTerm_hasDerivAt_of_argument_mem_Ioo
    (k : ℕ) (n : ℕ+) {x : ℝ}
    (hx : selectedFerrersAbelLogArgument k n x ∈ Set.Ioo
      (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda) :
    ∃ d : ℂ, HasDerivAt
      (selectedFerrersAbelLogProductionTerm k n) d x := by
  obtain ⟨dw, hw⟩ := selectedFerrersAbelLogSqrtWeight_hasDerivAt k x
  obtain ⟨dh, hh⟩ :=
    selectedFerrersAbelLogPacketTerm_hasDerivAt_of_argument_mem_Ioo k n hx
  exact ⟨_, hw.mul hh⟩

private theorem selectedFerrersAbelLogSqrtWeight_lipschitzOn
    (k : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      LipschitzOnWith (Real.toNNReal C)
        (fun x => Real.sqrt
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))
        (Set.uIcc a b) := by
  let D : ℝ := Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹
  let C : ℝ := D * ((1 / 2 : ℝ) * Real.exp (max a b / 2))
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  have hderiv : ∀ z ∈ Set.uIcc a b,
      HasDerivWithinAt (fun w : ℝ => D * Real.exp (w / 2))
        (D * ((1 / 2 : ℝ) * Real.exp (z / 2))) (Set.uIcc a b) z := by
    intro z hz
    apply HasDerivAt.hasDerivWithinAt
    convert ((Real.hasDerivAt_exp (z / 2)).comp z
      ((hasDerivAt_id z).div_const 2)).const_mul D using 1
    all_goals ring
  have hbound : ∀ z ∈ Set.uIcc a b,
      ‖D * ((1 / 2 : ℝ) * Real.exp (z / 2))‖ ≤ C := by
    intro z hz
    have hzle : z ≤ max a b := by
      rcases Set.mem_uIcc.mp hz with hz | hz
      · exact hz.2.trans (le_max_right _ _)
      · exact hz.2.trans (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ D * ((1 / 2 : ℝ) * Real.exp (z / 2)))]
    dsimp [C]
    apply mul_le_mul_of_nonneg_left _ hD
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.exp_le_exp.mpr (by linarith)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_uIcc a b) hx hy
  rw [selectedFerrersAbelLogSqrtWeight_eq k x,
    selectedFerrersAbelLogSqrtWeight_eq k y]
  simpa [D, Real.dist_eq, Real.coe_toNNReal C hC, norm_sub_rev] using hmv

private theorem selectedFerrersAbelLogSqrtWeight_absolutelyContinuousOnInterval
    (k : ℕ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun x =>
        (Real.sqrt
          (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)) a b := by
  obtain ⟨C, hC, hreal⟩ :=
    selectedFerrersAbelLogSqrtWeight_lipschitzOn k a b
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  have hxy := hreal.dist_le_mul x hx y hy
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Real.dist_eq]
  simpa [Real.dist_eq, Real.coe_toNNReal C hC] using hxy

private theorem
    selectedFerrersAbelLogProductionTerm_absolutelyContinuousOnInterval_of_mapsToWindow
    (k : ℕ) (n : ℕ+) {a b : ℝ}
    (hmem : ∀ x ∈ Set.uIcc a b,
      selectedFerrersAbelLogArgument k n x ∈
        Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
          (selectedFerrersPreAnchorPair k).pw.lambda) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersAbelLogProductionTerm k n) a b := by
  have hw := selectedFerrersAbelLogSqrtWeight_absolutelyContinuousOnInterval
    k a b
  have hp :=
    selectedFerrersAbelLogPacketTerm_absolutelyContinuousOnInterval_of_mapsToWindow
      k n hmem
  simpa only [selectedFerrersAbelLogProductionTerm, smul_eq_mul] using
    hw.fun_smul hp

private theorem selectedFerrersAbelLogScale_mem_window
    (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k))) :
    Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k) ∈
      I_m (selectedFerrersPreAnchorIndex k) := by
  let i := selectedFerrersPreAnchorIndex k
  let lam := lambda_m i
  have hlam : 0 < lam := by
    simp only [lam, i, lambda_m, selectedFerrersPreAnchorIndex]
    exact Real.sqrt_pos.2 (by positivity)
  have hsq : lam * lam = (i.m : ℝ) := by
    simp only [lam, lambda_m]
    rw [Real.mul_self_sqrt]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm).le
  have hexp1 : (1 : ℝ) ≤ Real.exp x :=
    (Real.one_le_exp_iff.mpr hx.1)
  have hlog : Real.exp (L_m i) = (i.m : ℝ) := by
    rw [L_m, logLength, Real.exp_log]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hexpUpper : Real.exp x ≤ (i.m : ℝ) := by
    rw [← hlog]
    exact Real.exp_le_exp.mpr hx.2
  change lam⁻¹ ≤ Real.exp x / lam ∧ Real.exp x / lam ≤ lam
  constructor
  · rw [inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hlam).2 hexp1
  · exact (div_le_iff₀ hlam).2 (by simpa [hsq] using hexpUpper)

private theorem selectedFerrersLemma73SourcePacket_windowFiniteSupport
    (k : ℕ) :
    WindowFiniteSupport
      (lambda_m (selectedFerrersPreAnchorIndex k))
      (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
      (selectedFerrersLemma73SourcePacket k) := by
  intro u hu n hn
  rw [selectedFerrersLemma73SourcePacket]
  rw [(prolateCombination_windowFiniteSupport
    (selectedFerrersPreAnchorIndex k) (selectedFerrersPreAnchorPair k)
    (selectedFerrersPreAnchorPair_spec k).1) u hu n hn]
  simp

private theorem selectedFerrersAbelLogRepresentative_eq_finite
    (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k))) :
    selectedFerrersAbelLogRepresentative k x =
      finiteEStar
        (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
        (selectedFerrersLemma73SourcePacket k)
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) +
      (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
        (Real.sqrt
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) := by
  unfold selectedFerrersAbelLogRepresentative selectedFerrersAbelLimit
  rw [E_star_eq_finiteEStar_of_windowFiniteSupport
    (selectedFerrersLemma73SourcePacket_windowFiniteSupport k)
    (selectedFerrersAbelLogScale_mem_window k hx)]

private theorem selectedFerrersAbelLogRepresentative_eq_productionSum
    (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k))) :
    selectedFerrersAbelLogRepresentative k x =
      (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
        selectedFerrersAbelLogProductionTerm k n x) +
      (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
        (Real.sqrt
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) := by
  rw [selectedFerrersAbelLogRepresentative_eq_finite k hx]
  simp only [finiteEStar, finiteEStarCore,
    selectedFerrersAbelLogProductionTerm,
    selectedFerrersAbelLogArgument, Finset.mul_sum]

theorem selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
    (k : ℕ) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersLemma73SourcePacket k)
      (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda := by
  obtain ⟨C, hC, hlip⟩ :=
    selectedPacket_lipschitz_on_window k
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  rw [Set.uIcc_of_le]
  · apply LipschitzOnWith.of_dist_le'
    intro u hu v hv
    simpa [Complex.dist_eq, Real.dist_eq, Real.coe_toNNReal C hC] using
      hlip u hu v hv
  · obtain ⟨hlam, -⟩ := selectedFerrersPreAnchorPair_spec k
    rw [hlam]
    linarith [Real.sqrt_nonneg (((k + 2 : ℕ) : ℝ))]

theorem
    selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersAbelLogRepresentative k) a b := by
  obtain ⟨Cw, hCw, hwReal⟩ :=
    selectedFerrersAbelLogSqrtWeight_lipschitzOn k a b
  have hwComplex : LipschitzOnWith (Real.toNNReal Cw)
      (fun x => (Real.sqrt
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ))
      (Set.uIcc a b) := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    have hw := hwReal.dist_le_mul x hx y hy
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Real.dist_eq]
    rw [Real.dist_eq, Real.coe_toNNReal Cw hCw] at hw
    exact hw
  have hwAC : AbsolutelyContinuousOnInterval
      (fun x => (Real.sqrt
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)) a b :=
    hwComplex.absolutelyContinuousOnInterval
  have hcore :=
    selectedFerrersAbelLogFiniteCore_absolutelyContinuousOnInterval_of_seamFree
      k hfree
  have hfinite : AbsolutelyContinuousOnInterval
      (fun x =>
        (Real.sqrt
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) *
        finiteEStarCore
          (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
          (selectedFerrersLemma73SourcePacket k)
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) a b := by
    simpa [smul_eq_mul] using hwAC.fun_smul hcore
  have hshadow : AbsolutelyContinuousOnInterval
      (fun x =>
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (Real.sqrt
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)) a b := by
    simpa [smul_eq_mul, mul_assoc] using
      hwAC.const_smul ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0)
  apply absolutelyContinuousOnInterval_congrOn _ (hfinite.fun_add hshadow)
  intro x hx
  rw [selectedFerrersAbelLogRepresentative_eq_finite k (hfree.1 hx)]
  rfl

theorem
    selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) :
    IntervalIntegrable
      (deriv (selectedFerrersAbelLogRepresentative k)) volume a b :=
  complex_deriv_intervalIntegrable_of_absolutelyContinuousOnInterval
    (selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
      k hfree)

noncomputable def selectedFerrersAbelLogDerivativeBudget
    (k : ℕ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
    ‖deriv (selectedFerrersAbelLogRepresentative k) x‖

/-- The unconditional safe jump budget.  The last summand is the lower
one-sided seam `n = k + 2`, separate from the full value at `x = 0`. -/
noncomputable def selectedFerrersAbelLogJumpBudget
    (k : ℕ) : ℝ :=
  ‖selectedFerrersAbelLogRepresentative k 0‖ +
  ‖selectedFerrersAbelLogRepresentative k
      (L_m (selectedFerrersPreAnchorIndex k))‖ +
  ∑ n ∈ Finset.Icc 2 (k + 2),
    ‖((Real.sqrt
        (lambda_m (selectedFerrersPreAnchorIndex k) / (n : ℝ)) : ℝ) : ℂ) *
      selectedFerrersLemma73SourcePacket k
        (lambda_m (selectedFerrersPreAnchorIndex k))‖

private noncomputable def selectedFerrersAbelLogLowerEndpointSeam
    (k : ℕ) : ℂ :=
  (((Real.sqrt
      (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ : ℝ) : ℂ) *
    selectedFerrersLemma73SourcePacket k
      (lambda_m (selectedFerrersPreAnchorIndex k)))

private noncomputable def selectedFerrersAbelLogLowerRightValue
    (k : ℕ) : ℂ :=
  selectedFerrersAbelLogRepresentative k 0 -
    selectedFerrersAbelLogLowerEndpointSeam k

private theorem selectedFerrersW4_lambda_pos (k : ℕ) :
    0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
  simp only [lambda_m, selectedFerrersPreAnchorIndex]
  exact Real.sqrt_pos.2 (by positivity)

private theorem selectedFerrersW4_lambda_sq (k : ℕ) :
    lambda_m (selectedFerrersPreAnchorIndex k) *
        lambda_m (selectedFerrersPreAnchorIndex k) = (k + 2 : ℕ) := by
  simp only [lambda_m, selectedFerrersPreAnchorIndex, Nat.cast_add,
    Nat.cast_ofNat]
  rw [Real.mul_self_sqrt]
  positivity

private theorem selectedFerrersAbelLogSeam_exp
    (k : ℕ) (n : ℕ+) :
    Real.exp (selectedFerrersAbelLogSeam k n) =
      ((k + 2 : ℕ) : ℝ) / ((n : ℕ) : ℝ) := by
  rw [selectedFerrersAbelLogSeam, Real.exp_log]
  positivity

private theorem selectedFerrersAbelLogArgument_at_seam
    (k : ℕ) (n : ℕ+) :
    selectedFerrersAbelLogArgument k n
        (selectedFerrersAbelLogSeam k n) =
      lambda_m (selectedFerrersPreAnchorIndex k) := by
  have hlam := selectedFerrersW4_lambda_pos k
  have hsq := selectedFerrersW4_lambda_sq k
  have hsq' :
      lambda_m (selectedFerrersPreAnchorIndex k) *
          lambda_m (selectedFerrersPreAnchorIndex k) = (k : ℝ) + 2 := by
    exact_mod_cast hsq
  rw [selectedFerrersAbelLogArgument,
    selectedFerrersAbelLogSeam_exp]
  have hn : (((n : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hn, hlam.ne']
  nlinarith

private theorem selectedFerrersAbelLogSeam_antitone
    (k : ℕ) {n j : ℕ+} (hnj : n ≤ j) :
    selectedFerrersAbelLogSeam k j ≤
      selectedFerrersAbelLogSeam k n := by
  have hcast : ((n : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by
    exact_mod_cast hnj
  have hratio :
      ((k + 2 : ℕ) : ℝ) / ((j : ℕ) : ℝ) ≤
        ((k + 2 : ℕ) : ℝ) / ((n : ℕ) : ℝ) := by
    gcongr
  exact Real.strictMonoOn_log.monotoneOn
    (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity) hratio

private theorem selectedFerrersAbelLogCell_argument_mapsToWindow
    (k : ℕ) {j n : ℕ+}
    (hn : n ∈ Finset.Icc (1 : ℕ+) j) :
    ∀ x ∈ Set.uIcc
        (selectedFerrersAbelLogSeam k ⟨(j : ℕ) + 1, by omega⟩)
        (selectedFerrersAbelLogSeam k j),
      selectedFerrersAbelLogArgument k n x ∈
        Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
          (selectedFerrersPreAnchorPair k).pw.lambda := by
  have horder :
      selectedFerrersAbelLogSeam k ⟨(j : ℕ) + 1, by omega⟩ ≤
        selectedFerrersAbelLogSeam k j :=
    selectedFerrersAbelLogSeam_antitone k (by
      change (j : ℕ) ≤ (j : ℕ) + 1
      omega)
  intro x hx
  rw [Set.uIcc_of_le horder] at hx
  have hlam := selectedFerrersW4_lambda_pos k
  have hsq := selectedFerrersW4_lambda_sq k
  have hsq' :
      lambda_m (selectedFerrersPreAnchorIndex k) *
          lambda_m (selectedFerrersPreAnchorIndex k) = (k : ℝ) + 2 := by
    exact_mod_cast hsq
  have hexp : Real.exp x ≤
      ((k + 2 : ℕ) : ℝ) / ((j : ℕ) : ℝ) := by
    rw [← selectedFerrersAbelLogSeam_exp k j]
    exact Real.exp_le_exp.mpr hx.2
  have hnj : ((n : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn).2
  have harg0 : 0 ≤ selectedFerrersAbelLogArgument k n x := by
    unfold selectedFerrersAbelLogArgument
    positivity
  have hargle : selectedFerrersAbelLogArgument k n x ≤
      lambda_m (selectedFerrersPreAnchorIndex k) := by
    unfold selectedFerrersAbelLogArgument
    calc
      ((n : ℕ) : ℝ) *
          (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) ≤
          ((n : ℕ) : ℝ) *
            ((((k + 2 : ℕ) : ℝ) / ((j : ℕ) : ℝ)) /
              lambda_m (selectedFerrersPreAnchorIndex k)) := by
        gcongr
      _ ≤ ((j : ℕ) : ℝ) *
            ((((k + 2 : ℕ) : ℝ) / ((j : ℕ) : ℝ)) /
              lambda_m (selectedFerrersPreAnchorIndex k)) := by
        gcongr
      _ = lambda_m (selectedFerrersPreAnchorIndex k) := by
        have hj0 : (((j : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp [hj0, hlam.ne']
        nlinarith
  rw [(selectedFerrersPreAnchorPair_spec k).1]
  exact ⟨(neg_nonpos.mpr hlam.le).trans harg0, hargle⟩

private theorem selectedFerrersAbelLogCell_argument_mem_Ioo
    (k : ℕ) {j n : ℕ+}
    (hn : n ∈ Finset.Icc (1 : ℕ+) j) {x : ℝ}
    (hx : x ∈ Set.Ioo
      (selectedFerrersAbelLogSeam k ⟨(j : ℕ) + 1, by omega⟩)
      (selectedFerrersAbelLogSeam k j)) :
    selectedFerrersAbelLogArgument k n x ∈
      Set.Ioo (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda := by
  have hlam := selectedFerrersW4_lambda_pos k
  have hsq := selectedFerrersW4_lambda_sq k
  have hsq' :
      lambda_m (selectedFerrersPreAnchorIndex k) *
          lambda_m (selectedFerrersPreAnchorIndex k) = (k : ℝ) + 2 := by
    exact_mod_cast hsq
  have hexp : Real.exp x <
      ((k + 2 : ℕ) : ℝ) / ((j : ℕ) : ℝ) := by
    rw [← selectedFerrersAbelLogSeam_exp k j]
    exact Real.exp_lt_exp.mpr hx.2
  have hnj : ((n : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by positivity
  have hargpos : 0 < selectedFerrersAbelLogArgument k n x := by
    unfold selectedFerrersAbelLogArgument
    positivity
  have harglt : selectedFerrersAbelLogArgument k n x <
      lambda_m (selectedFerrersPreAnchorIndex k) := by
    unfold selectedFerrersAbelLogArgument
    calc
      ((n : ℕ) : ℝ) *
          (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) <
          ((n : ℕ) : ℝ) *
            ((((k + 2 : ℕ) : ℝ) / ((j : ℕ) : ℝ)) /
              lambda_m (selectedFerrersPreAnchorIndex k)) := by
        gcongr
      _ ≤ ((j : ℕ) : ℝ) *
            ((((k + 2 : ℕ) : ℝ) / ((j : ℕ) : ℝ)) /
              lambda_m (selectedFerrersPreAnchorIndex k)) := by
        gcongr
      _ = lambda_m (selectedFerrersPreAnchorIndex k) := by
        have hj0 : (((j : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp [hj0, hlam.ne']
        nlinarith
  rw [(selectedFerrersPreAnchorPair_spec k).1]
  exact ⟨(neg_nonpos.mpr hlam.le).trans_lt hargpos, harglt⟩

private theorem selectedFerrersAbelLogCellRepresentative_absolutelyContinuousOnInterval
    (k : ℕ) (j : ℕ+) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersAbelLogCellRepresentative k j)
      (selectedFerrersAbelLogSeam k ⟨(j : ℕ) + 1, by omega⟩)
      (selectedFerrersAbelLogSeam k j) := by
  classical
  let a := selectedFerrersAbelLogSeam k ⟨(j : ℕ) + 1, by omega⟩
  let b := selectedFerrersAbelLogSeam k j
  have hterm : ∀ n ∈ Finset.Icc (1 : ℕ+) j,
      AbsolutelyContinuousOnInterval
        (selectedFerrersAbelLogProductionTerm k n) a b := by
    intro n hn
    apply
      selectedFerrersAbelLogProductionTerm_absolutelyContinuousOnInterval_of_mapsToWindow
    exact selectedFerrersAbelLogCell_argument_mapsToWindow k hn
  have hsum : AbsolutelyContinuousOnInterval
      (fun x => ∑ n ∈ Finset.Icc (1 : ℕ+) j,
        selectedFerrersAbelLogProductionTerm k n x) a b := by
    have hsum_general : ∀ S : Finset ℕ+,
        (∀ n ∈ S, n ∈ Finset.Icc (1 : ℕ+) j) →
        AbsolutelyContinuousOnInterval
          (fun x => ∑ n ∈ S,
            selectedFerrersAbelLogProductionTerm k n x) a b := by
      intro S hS
      induction S using Finset.induction_on with
      | empty =>
          have hz : AbsolutelyContinuousOnInterval
              (fun _ : ℝ => (0 : ℂ)) a b :=
            (LipschitzWith.const (α := ℝ) (0 : ℂ)).lipschitzOnWith
              |>.absolutelyContinuousOnInterval
          simpa using hz
      | @insert n S hnS ih =>
          have hnmem := hS n (Finset.mem_insert_self n S)
          have hsub : ∀ m ∈ S, m ∈ Finset.Icc (1 : ℕ+) j := by
            intro m hm
            exact hS m (Finset.mem_insert_of_mem hm)
          simpa [Finset.sum_insert, hnS] using
            (hterm n hnmem).fun_add (ih hsub)
    exact hsum_general _ (fun n hn => hn)
  have hw := selectedFerrersAbelLogSqrtWeight_absolutelyContinuousOnInterval
    k a b
  have hshadow : AbsolutelyContinuousOnInterval
      (fun x =>
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (Real.sqrt
            (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)) a b := by
    simpa [smul_eq_mul, mul_assoc] using
      hw.const_smul ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0)
  simpa only [selectedFerrersAbelLogCellRepresentative, a, b] using
    hsum.fun_add hshadow

private theorem selectedFerrersAbelLogCellRepresentative_differentiableAt
    (k : ℕ) (j : ℕ+) {x : ℝ}
    (hx : x ∈ Set.Ioo
      (selectedFerrersAbelLogSeam k ⟨(j : ℕ) + 1, by omega⟩)
      (selectedFerrersAbelLogSeam k j)) :
    DifferentiableAt ℝ (selectedFerrersAbelLogCellRepresentative k j) x := by
  classical
  have hterm : ∀ n ∈ Finset.Icc (1 : ℕ+) j,
      DifferentiableAt ℝ (selectedFerrersAbelLogProductionTerm k n) x := by
    intro n hn
    obtain ⟨d, hd⟩ :=
      selectedFerrersAbelLogProductionTerm_hasDerivAt_of_argument_mem_Ioo
        k n (selectedFerrersAbelLogCell_argument_mem_Ioo k hn hx)
    exact hd.differentiableAt
  have hsum : DifferentiableAt ℝ
      (fun y => ∑ n ∈ Finset.Icc (1 : ℕ+) j,
        selectedFerrersAbelLogProductionTerm k n y) x :=
    DifferentiableAt.fun_sum hterm
  obtain ⟨dw, hw⟩ := selectedFerrersAbelLogSqrtWeight_hasDerivAt k x
  have hshadow : DifferentiableAt ℝ
      (fun y =>
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (Real.sqrt
            (Real.exp y /
              lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)) x := by
    exact (hw.const_mul
      ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0)).differentiableAt
  simpa only [selectedFerrersAbelLogCellRepresentative] using
    hsum.add hshadow

/-- The final repaired ledger summand is exactly the lower one-sided seam. -/
private theorem selectedFerrersAbelLogLowerEndpointSeam_eq_lastSummand
    (k : ℕ) :
    selectedFerrersAbelLogLowerEndpointSeam k =
      (((Real.sqrt
          (lambda_m (selectedFerrersPreAnchorIndex k) / (k + 2 : ℝ)) : ℝ) : ℂ) *
        selectedFerrersLemma73SourcePacket k
          (lambda_m (selectedFerrersPreAnchorIndex k))) := by
  have hlam := selectedFerrersW4_lambda_pos k
  have hsq := selectedFerrersW4_lambda_sq k
  have hsq' :
      lambda_m (selectedFerrersPreAnchorIndex k) *
          lambda_m (selectedFerrersPreAnchorIndex k) = (k : ℝ) + 2 := by
    exact_mod_cast hsq
  have hquot :
      lambda_m (selectedFerrersPreAnchorIndex k) / (k + 2 : ℝ) =
        (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ := by
    rw [← hsq']
    field_simp
  simp only [selectedFerrersAbelLogLowerEndpointSeam, hquot]

private theorem selectedFerrersAbelLogLowerRightValue_norm_le (k : ℕ) :
    ‖selectedFerrersAbelLogLowerRightValue k‖ ≤
      ‖selectedFerrersAbelLogRepresentative k 0‖ +
        ‖selectedFerrersAbelLogLowerEndpointSeam k‖ := by
  exact norm_sub_le _ _

#print axioms selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
#print axioms
  selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
#print axioms
  selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree

end Q3.RouteB.D0Pstar
