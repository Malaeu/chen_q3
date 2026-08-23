import Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate
import Mathlib.Analysis.BoundedVariation

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Filter MeasureTheory Set Polynomial
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.4.1b.3c.1.11 — the selected Ferrers packet variation certificate (W2)

Task `H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_LEAN`
of verdict `ea6f3109`.

The exact source-scaled selected Ferrers packet, with its production full
endpoint values, has bounded variation on the whole real line.

Route (as mandated):
1. a closed-unit-interval derivative majorant for the ordinary Legendre
   polynomials, polynomial in the degree: `|P_n'(x)| ≤ n(n+1)` on `[-1,1]`,
   obtained from the Legendre differential equation by integrating the exact
   flux identity `((1-x²)P_n')' = -n(n+1)·P_n` from the endpoint and using
   the already kernel-checked closed bound `|P_n| ≤ 1` — NOT by substituting
   `r = 1` into the interior `(1-r²)⁻¹` majorant (the mandatory plant records
   that blow-up);
2. the tail-splice weighted coefficient summability with weight `(q+1)²`;
3. mean value theorem on the open interval plus closed-window continuity
   gives a Lipschitz bound on the closed dimensionless interval;
4. transport through the physical scaling, the positive `L²` normalization,
   the exact mode-zero/mode-four combination and the exact complex source
   scale;
5. global bounded variation of the production zero extension, paying the two
   endpoint jumps explicitly through the exact variation additivity of
   adjacent windows.

LEDGER:
  CLOSES: [W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE]
  OPENS:  []
-/

/-! ## The mandatory plant -/

/-- **Plant.**  The interior derivative majorant factor `4/(1-r²)+1` blows
up as `r → 1⁻` along the exact arithmetic family `r_k = 1 - (k+2)⁻¹`:
plugging `r = 1` into the strict-subinterval bound is not a closed-endpoint
bound. -/
private theorem strict_compact_derivative_bound_does_not_supply_closed_endpoint_bound_plant :
    Tendsto
      (fun k : ℕ => 4 / (1 - (1 - ((k : ℝ) + 2)⁻¹) ^ 2) + 1)
      atTop atTop := by
  have hlower :
      ∀ k : ℕ,
        2 * ((k : ℝ) + 2) + 1 ≤
          4 / (1 - (1 - ((k : ℝ) + 2)⁻¹) ^ 2) + 1 := by
    intro k
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    set ε : ℝ := ((k : ℝ) + 2)⁻¹ with hε
    have hε0 : 0 < ε := inv_pos.mpr hk2
    have hε1 : ε ≤ 1 := by
      rw [hε]
      rw [inv_le_one₀ hk2]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hden : 1 - (1 - ε) ^ 2 = ε * (2 - ε) := by ring
    have hden_pos : 0 < ε * (2 - ε) := by nlinarith
    have hden_le : ε * (2 - ε) ≤ 2 * ε := by nlinarith
    have h1 : 4 / (2 * ε) ≤ 4 / (ε * (2 - ε)) := by
      apply div_le_div_of_nonneg_left (by norm_num) hden_pos hden_le
    have h2 : 4 / (2 * ε) = 2 * ((k : ℝ) + 2) := by
      rw [hε]
      field_simp
      ring
    rw [hden]
    linarith
  refine tendsto_atTop_mono hlower ?_
  apply tendsto_atTop_add_const_right
  apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

/-! ## Step 1 — the closed-interval Legendre derivative majorant -/

/-- The exact polynomial flux identity
`derivative ((1 - X²)·P_n') = -(n(n+1))·P_n`, a direct rearrangement of the
kernel-checked Legendre differential equation. -/
private theorem legendre_flux_derivative (n : ℕ) :
    Polynomial.derivative
        ((1 - X ^ 2) * (mode4OrdinaryLegendrePolynomial n).derivative) =
      -(C ((n : ℝ) * (n + 1)) * mode4OrdinaryLegendrePolynomial n) := by
  have hode := mode4OrdinaryLegendrePolynomial_differentialEquation n
  have hexp :
      Polynomial.derivative
          ((1 - X ^ 2) * (mode4OrdinaryLegendrePolynomial n).derivative) =
        (1 - X ^ 2) *
            (mode4OrdinaryLegendrePolynomial n).derivative.derivative -
          2 * X * (mode4OrdinaryLegendrePolynomial n).derivative := by
    rw [Polynomial.derivative_mul]
    have hd : Polynomial.derivative (1 - X ^ 2 : ℝ[X]) = -(2 * X) := by
      simp
      ring
    rw [hd]
    ring
  rw [hexp]
  linear_combination hode

/-- The flux function vanishes at the right endpoint. -/
private theorem legendre_flux_at_one (n : ℕ) :
    ((1 - X ^ 2) *
        (mode4OrdinaryLegendrePolynomial n).derivative).eval 1 = 0 := by
  simp

/-- Integrated flux bound: for `x ∈ [-1, 1]`,
`|(1-x²)·P_n'(x)| ≤ n(n+1)·(1-x)`. -/
private theorem legendre_flux_abs_le (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |((1 - X ^ 2) *
        (mode4OrdinaryLegendrePolynomial n).derivative).eval x| ≤
      (n : ℝ) * (n + 1) * (1 - x) := by
  set Q : ℝ[X] :=
    (1 - X ^ 2) * (mode4OrdinaryLegendrePolynomial n).derivative with hQ
  have hderiv :
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => Q.eval s)
        ((-(C ((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendrePolynomial n)).eval t) t := by
    intro t
    have h := Q.hasDerivAt t
    rw [hQ] at h ⊢
    rw [legendre_flux_derivative n] at h
    exact h
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Q.eval s)
      (f' := fun t : ℝ =>
        (-(C ((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendrePolynomial n)).eval t)
      (a := x) (b := 1)
      (fun t _ => hderiv t)
      ((Polynomial.continuous _).intervalIntegrable x 1)
  have hQ1 : Q.eval 1 = 0 := by
    rw [hQ]
    exact legendre_flux_at_one n
  have hFTC' :
      (∫ t in x..1,
        (-(C ((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendrePolynomial n)).eval t) =
        Q.eval 1 - Q.eval x := hFTC
  rw [hQ1] at hFTC'
  have hQx : Q.eval x =
      -∫ t in x..1,
        (-(C ((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendrePolynomial n)).eval t := by
    linarith [hFTC']
  rw [hQx, abs_neg]
  have hxle : x ≤ 1 := hx.2
  have hbound :
      ∀ t ∈ Set.Icc x 1,
        ‖(-(C ((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendrePolynomial n)).eval t‖ ≤
          (n : ℝ) * (n + 1) := by
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans hx.1 ht.1, ht.2⟩
    have hP := mode4OrdinaryLegendre_abs_le_one n t ht'
    rw [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C]
    rw [norm_neg, Real.norm_eq_abs, abs_mul]
    have hnn : |(n : ℝ) * (n + 1)| = (n : ℝ) * (n + 1) := by
      rw [abs_of_nonneg]
      positivity
    rw [hnn]
    calc
      (n : ℝ) * (n + 1) * |(mode4OrdinaryLegendrePolynomial n).eval t| ≤
          (n : ℝ) * (n + 1) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hP
      _ = (n : ℝ) * (n + 1) := mul_one _
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (n : ℝ) * (n + 1))
    (fun t ht => by
      apply hbound t
      rw [Set.uIoc_of_le hxle] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩)
  rw [Real.norm_eq_abs] at hle
  calc
    |∫ t in x..1,
        (-(C ((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendrePolynomial n)).eval t| ≤
        (n : ℝ) * (n + 1) * |1 - x| := hle
    _ = (n : ℝ) * (n + 1) * (1 - x) := by
      rw [abs_of_nonneg (by linarith)]

/-- **Step 1, closed form.**  The ordinary Legendre derivative satisfies the
closed-interval polynomial majorant `|P_n'(x)| ≤ n(n+1)` on all of
`[-1, 1]`. -/
theorem mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(mode4OrdinaryLegendrePolynomial n).derivative.eval x| ≤
      (n : ℝ) * (n + 1) := by
  -- first the nonnegative half, then parity.
  have hhalf :
      ∀ y : ℝ, 0 ≤ y → y ∈ Set.Icc (-1 : ℝ) 1 →
        |(mode4OrdinaryLegendrePolynomial n).derivative.eval y| ≤
          (n : ℝ) * (n + 1) := by
    intro y hy0 hy
    have hSclosed :
        IsClosed {t : ℝ |
          |(mode4OrdinaryLegendrePolynomial n).derivative.eval t| ≤
            (n : ℝ) * (n + 1)} := by
      apply isClosed_le
      · exact (Polynomial.continuous _).abs
      · exact continuous_const
    have hIco :
        Set.Ico (0 : ℝ) 1 ⊆
          {t : ℝ |
            |(mode4OrdinaryLegendrePolynomial n).derivative.eval t| ≤
              (n : ℝ) * (n + 1)} := by
      intro t ht
      have ht' : t ∈ Set.Icc (-1 : ℝ) 1 :=
        ⟨by linarith [ht.1], le_of_lt ht.2⟩
      have hflux := legendre_flux_abs_le n t ht'
      have hfactor : (1 - t ^ 2) > 0 := by nlinarith [ht.1, ht.2]
      have heval :
          ((1 - X ^ 2) *
              (mode4OrdinaryLegendrePolynomial n).derivative).eval t =
            (1 - t ^ 2) *
              (mode4OrdinaryLegendrePolynomial n).derivative.eval t := by
        simp
      rw [heval, abs_mul, abs_of_pos hfactor] at hflux
      have honeplus : (1 : ℝ) ≤ 1 + t := by linarith [ht.1]
      have hfsplit : (1 - t ^ 2) = (1 - t) * (1 + t) := by ring
      show |(mode4OrdinaryLegendrePolynomial n).derivative.eval t| ≤
        (n : ℝ) * (n + 1)
      have htlt : (0 : ℝ) < 1 - t := by linarith [ht.2]
      set A : ℝ :=
        |(mode4OrdinaryLegendrePolynomial n).derivative.eval t| with hA
      have hA0 : 0 ≤ A := abs_nonneg _
      have h3 : (1 - t) * ((1 + t) * A) ≤
          ((n : ℝ) * (n + 1)) * (1 - t) := by
        rw [hfsplit] at hflux
        nlinarith [hflux]
      have h4 : (1 + t) * A ≤ (n : ℝ) * (n + 1) := by
        by_contra hcon
        push_neg at hcon
        have := mul_lt_mul_of_pos_left hcon htlt
        nlinarith [h3]
      have h5 : A ≤ (1 + t) * A := by nlinarith
      linarith
    have hmem : y ∈ closure (Set.Ico (0 : ℝ) 1) := by
      rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨hy0, hy.2⟩
    have hsub := (closure_mono hIco).trans hSclosed.closure_eq.subset
    exact hsub hmem
  by_cases hy0 : 0 ≤ x
  · exact hhalf x hy0 hx
  · push_neg at hy0
    have hnx : 0 ≤ -x := by linarith
    have hnx1 : -x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hres := hhalf (-x) hnx hnx1
    have hpar := mode4OrdinaryLegendrePolynomial_derivative_eval_neg n x
    calc
      |(mode4OrdinaryLegendrePolynomial n).derivative.eval x| =
          |(mode4OrdinaryLegendrePolynomial n).derivative.eval (-x)| := by
        rw [hpar, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ (n : ℝ) * (n + 1) := hres

/-! ## Step 2 — closed-interval series derivative bound -/

/-- Closed-interval bound for one derivative term:
`‖(-1)^q a_q P_{2q}'(x)‖ ≤ 4 (q+1)² |a_q|` on `[-1, 1]`. -/
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

/-! ## The production packet -/

/-- The exact source-scaled selected Ferrers packet: the production
lemma-7.3 source object whose variation this file certifies. -/
noncomputable def selectedFerrersLemma73SourcePacket (k : ℕ) : ℝ → ℂ :=
  fun x => selectedFerrersLemma73SourceScale k *
    prolateCombination (selectedFerrersPreAnchorPair k) x

/-- Outside the closed physical window the packet vanishes exactly: both
selected modes are supported inside the window. -/
private theorem selectedPacket_zero_outside (k : ℕ) (x : ℝ)
    (hx : x ∉ Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda) :
    selectedFerrersLemma73SourcePacket k x = 0 := by
  have h0 : (selectedFerrersPreAnchorPair k).h0 x = 0 := by
    by_contra hne
    exact hx ((selectedFerrersPreAnchorPair k).h0_support hne)
  have h4 : (selectedFerrersPreAnchorPair k).h4 x = 0 := by
    by_contra hne
    exact hx ((selectedFerrersPreAnchorPair k).h4_support hne)
  simp [selectedFerrersLemma73SourcePacket, prolateCombination, h0, h4]

/-! ## Step 5 — exact variation ledger of the zero extension -/

/-- A function vanishing strictly left of `a` has variation at most the
single jump `edist (f a) 0` on `Iic a`: any monotone card pays at most one
crossing of `a`. -/
private theorem eVariationOn_Iic_le_edist_of_zero_on_Iio
    (f : ℝ → ℂ) (a : ℝ) (h0 : ∀ x : ℝ, x < a → f x = 0) :
    eVariationOn f (Set.Iic a) ≤ edist (f a) 0 := by
  classical
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  set S : Finset ℕ := (Finset.range n).filter
    (fun i => u i < a ∧ ¬ u (i + 1) < a) with hSdef
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [hSdef, Finset.mem_filter] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with hij | hij
    · have hstep : u (i + 1) ≤ u j := hu (Nat.succ_le_of_lt hij)
      exact hi.2.2 (lt_of_le_of_lt hstep hj.2.1)
    · have hij' : j < i := lt_of_le_of_ne hij fun h => hne h.symm
      have hstep : u (j + 1) ≤ u i := hu (Nat.succ_le_of_lt hij')
      exact hj.2.2 (lt_of_le_of_lt hstep hi.2.1)
  have hterm : ∀ i ∈ Finset.range n,
      edist (f (u (i + 1))) (f (u i)) ≤
        if i ∈ S then edist (f a) 0 else 0 := by
    intro i hi
    by_cases hc : u i < a ∧ ¬ u (i + 1) < a
    · rw [if_pos (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hi, hc⟩)]
      have h1 : u (i + 1) = a :=
        le_antisymm (Set.mem_Iic.mp (us (i + 1))) (not_lt.mp hc.2)
      rw [h1, h0 (u i) hc.1]
    · rw [if_neg (by
        rw [hSdef]
        intro hmm
        exact hc (Finset.mem_filter.mp hmm).2)]
      rcases not_and_or.mp hc with h1 | h2
      · have hia : u i = a :=
          le_antisymm (Set.mem_Iic.mp (us i)) (not_lt.mp h1)
        have h1a : u (i + 1) = a :=
          le_antisymm (Set.mem_Iic.mp (us (i + 1)))
            (hia ▸ hu (Nat.le_succ i))
        rw [hia, h1a]
        simp
      · rw [not_not] at h2
        rw [h0 (u (i + 1)) h2,
          h0 (u i) (lt_of_le_of_lt (hu (Nat.le_succ i)) h2)]
        simp
  calc
    ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
        ∑ i ∈ Finset.range n, (if i ∈ S then edist (f a) 0 else 0) :=
      Finset.sum_le_sum hterm
    _ = ∑ i ∈ S, edist (f a) 0 := by
      rw [Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
    _ = (S.card : ℝ≥0∞) * edist (f a) 0 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * edist (f a) 0 := by
      gcongr
      exact_mod_cast hcard
    _ = edist (f a) 0 := one_mul _

/-- Mirror ledger: a function vanishing strictly right of `a` has variation
at most the single jump `edist (f a) 0` on `Ici a`. -/
private theorem eVariationOn_Ici_le_edist_of_zero_on_Ioi
    (f : ℝ → ℂ) (a : ℝ) (h0 : ∀ x : ℝ, a < x → f x = 0) :
    eVariationOn f (Set.Ici a) ≤ edist (f a) 0 := by
  classical
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  set S : Finset ℕ := (Finset.range n).filter
    (fun i => ¬ a < u i ∧ a < u (i + 1)) with hSdef
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [hSdef, Finset.mem_filter] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with hij | hij
    · have hstep : u (i + 1) ≤ u j := hu (Nat.succ_le_of_lt hij)
      exact hj.2.1 (lt_of_lt_of_le hi.2.2 hstep)
    · have hij' : j < i := lt_of_le_of_ne hij fun h => hne h.symm
      have hstep : u (j + 1) ≤ u i := hu (Nat.succ_le_of_lt hij')
      exact hi.2.1 (lt_of_lt_of_le hj.2.2 hstep)
  have hterm : ∀ i ∈ Finset.range n,
      edist (f (u (i + 1))) (f (u i)) ≤
        if i ∈ S then edist (f a) 0 else 0 := by
    intro i hi
    by_cases hc : ¬ a < u i ∧ a < u (i + 1)
    · rw [if_pos (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hi, hc⟩)]
      have hia : u i = a :=
        le_antisymm (not_lt.mp hc.1) (Set.mem_Ici.mp (us i))
      rw [hia, h0 (u (i + 1)) hc.2, edist_comm]
    · rw [if_neg (by
        rw [hSdef]
        intro hmm
        exact hc (Finset.mem_filter.mp hmm).2)]
      rcases not_and_or.mp hc with h1 | h2
      · rw [not_not] at h1
        rw [h0 (u i) h1,
          h0 (u (i + 1)) (lt_of_lt_of_le h1 (hu (Nat.le_succ i)))]
        simp
      · have h1a : u (i + 1) = a :=
          le_antisymm (not_lt.mp h2) (Set.mem_Ici.mp (us (i + 1)))
        have hia : u i = a :=
          le_antisymm (h1a ▸ hu (Nat.le_succ i)) (Set.mem_Ici.mp (us i))
        rw [hia, h1a]
        simp
  calc
    ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
        ∑ i ∈ Finset.range n, (if i ∈ S then edist (f a) 0 else 0) :=
      Finset.sum_le_sum hterm
    _ = ∑ i ∈ S, edist (f a) 0 := by
      rw [Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
    _ = (S.card : ℝ≥0∞) * edist (f a) 0 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * edist (f a) 0 := by
      gcongr
      exact_mod_cast hcard
    _ = edist (f a) 0 := one_mul _

/-- The packet is Lipschitz on the closed physical window: the transported
window Lipschitz constants of both selected modes, combined through the
exact integrals, the exact normalizing denominator and the exact complex
source scale. -/
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

/-- **W2, the production theorem.**  The exact source-scaled selected
Ferrers packet, with its production full endpoint values, has bounded
variation on the whole real line.  The whole-line variation is the sum of
the two exact endpoint-jump ledgers and the Lipschitz variation of the
closed window. -/
theorem selectedFerrersLemma73SourcePacket_boundedVariationOn (k : ℕ) :
    BoundedVariationOn (selectedFerrersLemma73SourcePacket k) Set.univ := by
  set P := selectedFerrersPreAnchorPair k with hP
  set lam := P.pw.lambda with hlamdef
  have hlam := (selectedFerrersPreAnchorPair_spec k).1
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef, hP, hlam]
    exact Real.sqrt_nonneg _
  have hneg : -lam ≤ lam := by linarith
  have hzero_left : ∀ x : ℝ, x < -lam →
      selectedFerrersLemma73SourcePacket k x = 0 := by
    intro x hx
    apply selectedPacket_zero_outside
    intro hmem
    exact absurd hmem.1 (not_le.mpr hx)
  have hzero_right : ∀ x : ℝ, lam < x →
      selectedFerrersLemma73SourcePacket k x = 0 := by
    intro x hx
    apply selectedPacket_zero_outside
    intro hmem
    exact absurd hmem.2 (not_le.mpr hx)
  have hsplit2 : Set.Icc (-lam) lam ∪ Set.Ici lam = Set.Ici (-lam) :=
    Set.Icc_union_Ici_eq_Ici hneg
  have hsplit1 : Set.Iic (-lam) ∪ Set.Ici (-lam) = (Set.univ : Set ℝ) :=
    Set.Iic_union_Ici
  have hgr1 : IsGreatest (Set.Iic (-lam)) (-lam) := isGreatest_Iic
  have hle1 : IsLeast (Set.Icc (-lam) lam ∪ Set.Ici lam) (-lam) := by
    constructor
    · exact Or.inl ⟨le_refl _, hneg⟩
    · rintro y (hy | hy)
      · exact hy.1
      · linarith [Set.mem_Ici.mp hy]
  have hgr2 : IsGreatest (Set.Icc (-lam) lam) lam :=
    ⟨⟨hneg, le_refl _⟩, fun y hy => hy.2⟩
  have hle2 : IsLeast (Set.Ici lam) lam := isLeast_Ici
  have hBmid : BoundedVariationOn
      (selectedFerrersLemma73SourcePacket k) (Set.Icc (-lam) lam) := by
    obtain ⟨C, hC0, hlip⟩ := selectedPacket_lipschitz_on_window k
    have hlipOn : LipschitzOnWith (Real.toNNReal C)
        (selectedFerrersLemma73SourcePacket k) (Set.Icc (-lam) lam) := by
      apply LipschitzOnWith.of_dist_le'
      intro x hx y hy
      rw [dist_eq_norm, Real.dist_eq]
      exact hlip x hx y hy
    have hid : BoundedVariationOn (id : ℝ → ℝ) (Set.Icc (-lam) lam) := by
      have hmono : MonotoneOn (id : ℝ → ℝ) (Set.Icc (-lam) lam) :=
        monotone_id.monotoneOn _
      have h := hmono.eVariationOn_le
        (a := -lam) (b := lam) ⟨le_refl _, hneg⟩ ⟨hneg, le_refl _⟩
      rw [Set.inter_self] at h
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    have h := hlipOn.comp_boundedVariationOn (Set.mapsTo_id _) hid
    exact h
  show eVariationOn (selectedFerrersLemma73SourcePacket k) Set.univ ≠ ⊤
  rw [← hsplit1,
    eVariationOn.union (selectedFerrersLemma73SourcePacket k) hgr1
      (hsplit2 ▸ hle1 : IsLeast (Set.Ici (-lam)) (-lam)),
    ← hsplit2,
    eVariationOn.union (selectedFerrersLemma73SourcePacket k) hgr2 hle2]
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ne_top_of_le_ne_top (edist_ne_top _ _)
      (eVariationOn_Iic_le_edist_of_zero_on_Iio _ _ hzero_left)
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact hBmid
  · exact ne_top_of_le_ne_top (edist_ne_top _ _)
      (eVariationOn_Ici_le_edist_of_zero_on_Ioi _ _ hzero_right)

#print axioms selectedFerrersLemma73SourcePacket_boundedVariationOn
#print axioms
  strict_compact_derivative_bound_does_not_supply_closed_endpoint_bound_plant

end Q3.RouteB.D0Pstar
