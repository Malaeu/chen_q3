import Q3.Proofs.RouteB.G6N1SelectedFerrersW5RateAssembly
import Q3.Proofs.RouteB.G6N1SelectedFerrersCenterIntegralRate
import Q3.Proofs.RouteB.D0PstarGalerkinResidualDecay

/-!
# Goal 058 — selected Ferrers trial-normalizer closure (local-cell floor)

Verdict `82ac9628` (REQ-2026-08-26-H): the central `V₀` floor is killed by
zero-mass cancellation; the repaired route keeps sign location on the fixed
multiplicative cell `[1, 9/8]`, where every active explicit-`H` summand is
positive and the `n = 1` term supplies a fixed positive floor.

Route (five steps, all from the frozen production inputs):
1. eventual upper bound for `‖selectedFerrersLemma73SourceScale k‖` from the
   anchored `L²` rates, the χ-defect rates, the unit `L²` normalization of
   the two modes and the exact center-anchor locks;
2. positive floor for the scaled `E⋆` comb on the fixed cell `[1, 9/8]`:
   the `n = 1` explicit-`H` term is positive there, every other active term
   is positive, and the F72 packet error is `O(λ⁻¹)` after active-card
   counting;
3. dividing by the scale bound and integrating over the cell (fixed positive
   `dStar` mass `log (9/8)`) gives an eventual full-object `H_m` norm floor;
4. the family crosswalk transports the floor to the literal selected trial;
   the admitted `SelectedProjectionTailDecay` and the reverse triangle give
   an eventual projected-norm floor;
5. the selected trial normalizer is the inverse projected norm, hence
   eventually bounded; the existing two-premise receiver closes the literal
   normalized Galerkin residual.

No new analytic hypothesis; no subsequence; the literal moving carriers and
the literal normalized residual are kept.
-/

set_option maxHeartbeats 2000000

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Q3.RouteB.D0Pstar

/-! ## Step C: positivity of the explicit `H` profile at and beyond one -/

/-- The real `H` profile is strictly positive for `y ≥ 1`. -/
private theorem tnc_H_pos {y : ℝ} (hy : 1 ≤ y) : 0 < hbHRe y := by
  rw [hbHRe]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have h1 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
  have h2 : (3 : ℝ) < 2 * Real.pi * y ^ 2 := by nlinarith
  have hexp := Real.exp_pos (-Real.pi * y ^ 2)
  have hcoef : (0 : ℝ) < (Real.pi / 2) * y ^ 2 *
      (2 * Real.pi * y ^ 2 - 3) := by
    have := Real.pi_pos
    have h3 : (0 : ℝ) < 2 * Real.pi * y ^ 2 - 3 := by linarith
    positivity
  positivity

/-- Explicit positive floor for `4·H` on the fixed cell `[1, 9/8]`. -/
private noncomputable def tnc_cellFloor : ℝ :=
  4 * ((Real.pi / 2) * (2 * Real.pi - 3) *
    Real.exp (-Real.pi * (9 / 8 : ℝ) ^ 2))

private theorem tnc_cellFloor_pos : 0 < tnc_cellFloor := by
  rw [tnc_cellFloor]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hexp := Real.exp_pos (-Real.pi * (9 / 8 : ℝ) ^ 2)
  have h1 : (0 : ℝ) < 2 * Real.pi - 3 := by nlinarith
  positivity

/-- On the cell the `4·H` value dominates the explicit floor. -/
private theorem tnc_H_cell_floor {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) (9 / 8 : ℝ)) :
    tnc_cellFloor ≤ 4 * hbHRe u := by
  rw [tnc_cellFloor, hbHRe]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hu98 : u ≤ (9 / 8 : ℝ) := hu.2
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hsq1 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
  have hsq2 : u ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := by nlinarith
  have hexp_mono : Real.exp (-Real.pi * (9 / 8 : ℝ) ^ 2) ≤
      Real.exp (-Real.pi * u ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  have hcoef : (Real.pi / 2) * (2 * Real.pi - 3) ≤
      (Real.pi / 2) * u ^ 2 * (2 * Real.pi * u ^ 2 - 3) := by
    have h1 : (2 * Real.pi - 3) ≤ (2 * Real.pi * u ^ 2 - 3) := by
      nlinarith [Real.pi_pos]
    have h2 : (0 : ℝ) < 2 * Real.pi - 3 := by nlinarith
    nlinarith [Real.pi_pos]
  have hexp_pos := Real.exp_pos (-Real.pi * (9 / 8 : ℝ) ^ 2)
  have hcoef_pos : (0 : ℝ) < (Real.pi / 2) * (2 * Real.pi - 3) := by
    have h2 : (0 : ℝ) < 2 * Real.pi - 3 := by nlinarith
    positivity
  have hstep := mul_le_mul hcoef hexp_mono hexp_pos.le
    (by nlinarith [Real.pi_pos, hsq1] :
      (0 : ℝ) ≤ (Real.pi / 2) * u ^ 2 * (2 * Real.pi * u ^ 2 - 3))
  nlinarith [hstep]

/-! ## Step A: eventual anchored-scalar upper bounds from unit `L²` mass -/

/-- Square-integral of the mode-0 cylinder profile: `∫ ctW₀² ≤ 1`. -/
private theorem tnc_ctW0_sq_integral :
    (∫ y : ℝ, ctW0 y ^ 2) ≤ 1 := by
  have hrw : (fun y : ℝ => ctW0 y ^ 2) =
      fun y : ℝ => Real.exp (-(2 * Real.pi) * y ^ 2) := by
    funext y
    rw [ctW0, sq, ← Real.exp_add]
    congr 1
    ring
  rw [hrw, integral_gaussian]
  rw [show (2 * Real.pi) = Real.pi * 2 by ring]
  rw [show Real.pi / (Real.pi * 2) = 1 / 2 by
    field_simp]
  have h1 : Real.sqrt (1 / 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    norm_num
  simpa using h1

/-- Sub-exponential envelope for the mode-4 profile (local re-proof):
`|ctW₄ y| ≤ 355 e^{-π y²/2}`. -/
private theorem tnc_ctW4_envelope (y : ℝ) :
    |ctW4 y| ≤ 355 * Real.exp (-(Real.pi * y ^ 2) / 2) := by
  have hs : 0 ≤ Real.pi * y ^ 2 := by positivity
  set s : ℝ := Real.pi * y ^ 2 with hsdef
  have hlin : s ≤ 4 * Real.exp (s / 2) := by
    have h := Real.add_one_le_exp (s / 2)
    have hpos := Real.exp_pos (s / 2)
    nlinarith
  have hsq : s ^ 2 ≤ 16 * Real.exp (s / 2) := by
    have h := Real.add_one_le_exp (s / 4)
    have hpos := Real.exp_pos (s / 4)
    have hsq' : (s / 4 + 1) ^ 2 ≤ Real.exp (s / 4) ^ 2 := by
      have h0 : 0 ≤ s / 4 + 1 := by linarith
      exact pow_le_pow_left₀ h0 h 2
    have hexp2 : Real.exp (s / 4) ^ 2 = Real.exp (s / 2) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    nlinarith [hsq', hexp2]
  have habs : |ctW4 y| ≤
      (16 * s ^ 2 + 24 * s + 3) * Real.exp (-s) := by
    rw [ctW4]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexpeq : Real.exp (-Real.pi * y ^ 2) = Real.exp (-s) := by
      rw [hsdef]
      ring_nf
    rw [hexpeq]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 : 16 * Real.pi ^ 2 * y ^ 4 - 24 * Real.pi * y ^ 2 + 3 =
        16 * s ^ 2 - 24 * s + 3 := by
      rw [hsdef]; ring
    rw [h1]
    cases abs_cases (16 * s ^ 2 - 24 * s + 3) with
    | inl h => rw [h.1]; nlinarith
    | inr h => rw [h.1]; nlinarith
  have henv : (16 * s ^ 2 + 24 * s + 3) ≤ 355 * Real.exp (s / 2) := by
    have h3 : (1 : ℝ) ≤ Real.exp (s / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith
  calc |ctW4 y| ≤ (16 * s ^ 2 + 24 * s + 3) * Real.exp (-s) := habs
    _ ≤ (355 * Real.exp (s / 2)) * Real.exp (-s) := by
        apply mul_le_mul_of_nonneg_right henv (Real.exp_pos _).le
    _ = 355 * Real.exp (-s / 2) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ = 355 * Real.exp (-(Real.pi * y ^ 2) / 2) := by rw [hsdef]

/-- Square-integral of the mode-4 cylinder profile: `∫ ctW₄² ≤ 355²`. -/
private theorem tnc_ctW4_sq_integral :
    (∫ y : ℝ, ctW4 y ^ 2) ≤ 355 ^ 2 := by
  have hgauss_int : Integrable
      (fun y : ℝ => Real.exp (-Real.pi * y ^ 2)) volume :=
    integrable_exp_neg_mul_sq Real.pi_pos
  have hmaj : Integrable
      (fun y : ℝ => (355 : ℝ) ^ 2 * Real.exp (-Real.pi * y ^ 2)) volume :=
    hgauss_int.const_mul _
  have hptw : ∀ y : ℝ, ctW4 y ^ 2 ≤
      355 ^ 2 * Real.exp (-Real.pi * y ^ 2) := by
    intro y
    have henv := tnc_ctW4_envelope y
    have h1 : ctW4 y ^ 2 = |ctW4 y| ^ 2 := (sq_abs _).symm
    rw [h1]
    have h2 : |ctW4 y| ^ 2 ≤
        (355 * Real.exp (-(Real.pi * y ^ 2) / 2)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) henv 2
    have h3 : (355 * Real.exp (-(Real.pi * y ^ 2) / 2)) ^ 2 =
        355 ^ 2 * Real.exp (-Real.pi * y ^ 2) := by
      rw [mul_pow]
      congr 1
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    linarith
  have hint : Integrable (fun y : ℝ => ctW4 y ^ 2) volume := by
    apply hmaj.mono'
    · apply Continuous.aestronglyMeasurable
      have : Continuous ctW4 := by
        rw [show ctW4 = fun x : ℝ =>
          (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3) *
            Real.exp (-Real.pi * x ^ 2) from rfl]
        fun_prop
      fun_prop
    · filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hptw y
  calc (∫ y : ℝ, ctW4 y ^ 2) ≤
      ∫ y : ℝ, 355 ^ 2 * Real.exp (-Real.pi * y ^ 2) :=
      integral_mono hint hmaj hptw
    _ = 355 ^ 2 * ∫ y : ℝ, Real.exp (-Real.pi * y ^ 2) :=
      integral_const_mul _ _
    _ ≤ 355 ^ 2 * 1 := by
      rw [integral_gaussian]
      have h1 : Real.pi / Real.pi = 1 := div_self Real.pi_pos.ne'
      rw [h1, Real.sqrt_one]
    _ = 355 ^ 2 := by ring

/-- L¹ masses of the two profiles over the whole line (local re-proofs). -/
private theorem tnc_ctW0_abs_integral :
    (∫ y : ℝ, |ctW0 y|) ≤ 1 := by
  have habs : ∀ y : ℝ, |ctW0 y| = Real.exp (-Real.pi * y ^ 2) := by
    intro y
    rw [ctW0]
    exact abs_of_pos (Real.exp_pos _)
  have hrw : (fun y : ℝ => |ctW0 y|) =
      fun y : ℝ => Real.exp (-Real.pi * y ^ 2) := funext habs
  rw [hrw, integral_gaussian, div_self Real.pi_pos.ne', Real.sqrt_one]

private theorem tnc_halfgauss_integrable :
    Integrable (fun y : ℝ => Real.exp (-(Real.pi * y ^ 2) / 2)) volume := by
  have hrw : (fun y : ℝ => Real.exp (-(Real.pi * y ^ 2) / 2)) =
      fun y : ℝ => Real.exp (-(Real.pi / 2) * y ^ 2) := by
    funext y
    congr 1
    ring
  rw [hrw]
  exact integrable_exp_neg_mul_sq (by positivity)

private theorem tnc_ctW4_abs_integral :
    (∫ y : ℝ, |ctW4 y|) ≤ 533 := by
  have hmaj : Integrable
      (fun y : ℝ => 355 * Real.exp (-(Real.pi * y ^ 2) / 2)) volume :=
    tnc_halfgauss_integrable.const_mul 355
  have hint : Integrable (fun y : ℝ => |ctW4 y|) volume := by
    apply hmaj.mono'
    · apply Measurable.aestronglyMeasurable
      apply Measurable.abs
      have : Continuous ctW4 := by
        rw [show ctW4 = fun x : ℝ =>
          (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3) *
            Real.exp (-Real.pi * x ^ 2) from rfl]
        fun_prop
      exact this.measurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_abs]
      exact tnc_ctW4_envelope y
  have hval : (∫ y : ℝ, Real.exp (-(Real.pi * y ^ 2) / 2)) ≤ 3 / 2 := by
    have hrw : (fun y : ℝ => Real.exp (-(Real.pi * y ^ 2) / 2)) =
        fun y : ℝ => Real.exp (-(Real.pi / 2) * y ^ 2) := by
      funext y
      congr 1
      ring
    rw [hrw, integral_gaussian]
    have h2 : Real.pi / (Real.pi / 2) = 2 := by
      field_simp
    rw [h2]
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    norm_num
  calc (∫ y : ℝ, |ctW4 y|) ≤
      ∫ y : ℝ, 355 * Real.exp (-(Real.pi * y ^ 2) / 2) :=
      integral_mono hint hmaj (fun y => tnc_ctW4_envelope y)
    _ = 355 * ∫ y : ℝ, Real.exp (-(Real.pi * y ^ 2) / 2) :=
      integral_const_mul _ _
    _ ≤ 355 * (3 / 2) := by nlinarith [hval]
    _ ≤ 533 := by norm_num

/-- **Step A.** Eventual upper bounds for the two center-anchor scalars from
unit `L²` normalization and the anchored mode rates. -/
private theorem tnc_anchor_upper
    (C0 C4 : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop,
      ‖centerAnchorScalarZero k‖ ^ 2 ≤ 2 * 1 + 1 ∧
      ‖centerAnchorScalarFour k‖ ^ 2 ≤ 2 * 355 ^ 2 + 1 := by
  have hevC : ∀ᶠ k : ℕ in Filter.atTop,
      1100 * (C0 + C4) + 4 * (C0 + C4) ^ 2 + 4 ≤ ((k : ℕ) : ℝ) :=
    Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) _
  filter_upwards [hmode, hevC] with k hkmode hkC
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  set lamp : ℝ := selectedFerrersPaperLambda k with hlampdef
  have hlamp1 : (1 : ℝ) ≤ lamp := by
    rw [hlampdef, selectedFerrersPaperLambda]
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hlamp0 : (0 : ℝ) < lamp := by linarith
  have hlampsq : ((k + 2 : ℕ) : ℝ) = lamp ^ 2 := by
    rw [hlampdef, selectedFerrersPaperLambda]
    rw [Real.sq_sqrt (by positivity)]
  have hkk2 : ((k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (k : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hbig : 1100 * (C0 + C4) + 4 * (C0 + C4) ^ 2 + 4 ≤ lamp ^ 2 := by
    rw [← hlampsq]
    linarith [hkC, hkk2]
  -- generic per-mode bound
  have hgeneric : ∀ (a : ℂ) (h : ℝ → ℂ) (W : ℝ → ℝ) (Cj KD KW : ℝ),
      0 ≤ Cj → 0 ≤ KD → 0 ≤ KW → Cj ≤ C0 + C4 →
      (∫ u : ℝ, ‖h u‖ ^ 2) = 1 →
      Integrable (fun u : ℝ => ‖h u‖ ^ 2) volume →
      (∫ y : ℝ, W y ^ 2) ≤ KD →
      (∫ y : ℝ, |W y|) ≤ KW → KW ≤ 533 →
      Integrable (fun y : ℝ => W y ^ 2) volume →
      Integrable (fun y : ℝ => |W y|) volume →
      (∀ x ∈ Set.Icc (-lamp) lamp,
        ‖a * h x - ((W x : ℝ) : ℂ)‖ ≤ Cj / lamp ^ 2) →
      (∀ x ∉ Set.Icc (-lamp) lamp, h x = 0) →
      ‖a‖ ^ 2 ≤ 2 * KD + 1 := by
    intro a h W Cj KD KW hCj hKD hKW hCjle hunit hint hWsq hWabs hKW533
      hWsqInt hWabsInt hrate hsupp
    have hnormsq : ‖a‖ ^ 2 = ∫ u : ℝ, ‖a * h u‖ ^ 2 := by
      have hfun : (fun u : ℝ => ‖a * h u‖ ^ 2) =
          fun u : ℝ => ‖a‖ ^ 2 * ‖h u‖ ^ 2 := by
        funext u
        rw [norm_mul, mul_pow]
      rw [hfun, integral_const_mul, hunit, mul_one]
    set c : ℝ := Cj / lamp ^ 2 with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    have hptw : ∀ x : ℝ, ‖a * h x‖ ^ 2 ≤
        W x ^ 2 + 2 * c * |W x| +
          (Set.Icc (-lamp) lamp).indicator (fun _ => c ^ 2) x := by
      intro x
      by_cases hx : x ∈ Set.Icc (-lamp) lamp
      · have hr := hrate x hx
        have htri : ‖a * h x‖ ≤ |W x| + c := by
          calc ‖a * h x‖ =
              ‖(a * h x - ((W x : ℝ) : ℂ)) + ((W x : ℝ) : ℂ)‖ := by
                ring_nf
            _ ≤ ‖a * h x - ((W x : ℝ) : ℂ)‖ + ‖((W x : ℝ) : ℂ)‖ :=
              norm_add_le _ _
            _ ≤ c + |W x| := by
                rw [Complex.norm_real, Real.norm_eq_abs]
                exact add_le_add hr le_rfl
            _ = |W x| + c := by ring
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        rw [Set.indicator_of_mem hx]
        calc ‖a * h x‖ ^ 2 ≤ (|W x| + c) ^ 2 := hsq
          _ = |W x| ^ 2 + 2 * c * |W x| + c ^ 2 := by ring
          _ = W x ^ 2 + 2 * c * |W x| + c ^ 2 := by rw [sq_abs]
      · rw [hsupp x hx, mul_zero, norm_zero, Set.indicator_of_notMem hx]
        have h1 : (0 : ℝ) ≤ W x ^ 2 := sq_nonneg _
        have h2 : (0 : ℝ) ≤ 2 * c * |W x| := by positivity
        simpa using by nlinarith
    have hIndInt : Integrable (fun x : ℝ =>
        (Set.Icc (-lamp) lamp).indicator (fun _ => c ^ 2) x) volume := by
      apply MeasureTheory.IntegrableOn.integrable_indicator _
        measurableSet_Icc
      exact integrableOn_const (by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_lt_top.ne)
    have hmajInt : Integrable (fun x : ℝ =>
        W x ^ 2 + 2 * c * |W x| +
          (Set.Icc (-lamp) lamp).indicator (fun _ => c ^ 2) x) volume :=
      (hWsqInt.add (hWabsInt.const_mul _)).add hIndInt
    have hlhsInt : Integrable (fun u : ℝ => ‖a * h u‖ ^ 2) volume := by
      have hfun : (fun u : ℝ => ‖a * h u‖ ^ 2) =
          fun u : ℝ => ‖a‖ ^ 2 * ‖h u‖ ^ 2 := by
        funext u
        rw [norm_mul, mul_pow]
      rw [hfun]
      exact hint.const_mul _
    have hIco : (∫ x : ℝ, (Set.Icc (-lamp) lamp).indicator
        (fun _ => c ^ 2) x) = c ^ 2 * (2 * lamp) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
      rw [measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have hchain : (∫ u : ℝ, ‖a * h u‖ ^ 2) ≤
        KD + 2 * c * KW + c ^ 2 * (2 * lamp) := by
      calc (∫ u : ℝ, ‖a * h u‖ ^ 2) ≤
          ∫ x : ℝ, (W x ^ 2 + 2 * c * |W x| +
            (Set.Icc (-lamp) lamp).indicator (fun _ => c ^ 2) x) :=
          integral_mono hlhsInt hmajInt hptw
        _ = (∫ x : ℝ, (W x ^ 2 + 2 * c * |W x|)) +
            ∫ x : ℝ, (Set.Icc (-lamp) lamp).indicator
              (fun _ => c ^ 2) x :=
            MeasureTheory.integral_add
              (hWsqInt.add (hWabsInt.const_mul _)) hIndInt
        _ ≤ (KD + 2 * c * KW) + c ^ 2 * (2 * lamp) := by
            rw [hIco]
            have hsplit := MeasureTheory.integral_add hWsqInt
              (hWabsInt.const_mul (2 * c))
            rw [hsplit]
            have h2 : (∫ y : ℝ, 2 * c * |W y|) = 2 * c * ∫ y : ℝ, |W y| :=
              integral_const_mul _ _
            rw [h2]
            have h3 : 2 * c * (∫ y : ℝ, |W y|) ≤ 2 * c * KW := by
              apply mul_le_mul_of_nonneg_left hWabs (by positivity)
            linarith
    -- the two correction terms are eventually at most 1 in total
    have hcsmall : 2 * c * KW + c ^ 2 * (2 * lamp) ≤ 1 := by
      rw [hcdef]
      have hlam2 : (0 : ℝ) < lamp ^ 2 := by positivity
      have h1 : 2 * (Cj / lamp ^ 2) * KW ≤ 2 * 533 * (C0 + C4) / lamp ^ 2 := by
        have heq : 2 * (Cj / lamp ^ 2) * KW = (2 * Cj * KW) / lamp ^ 2 := by
          ring
        rw [heq]
        have hnum : 2 * Cj * KW ≤ 2 * 533 * (C0 + C4) := by nlinarith
        have hd := div_nonneg (sub_nonneg.2 hnum) hlam2.le
        have heq2 : (2 * 533 * (C0 + C4) - 2 * Cj * KW) / lamp ^ 2 =
            2 * 533 * (C0 + C4) / lamp ^ 2 -
              2 * Cj * KW / lamp ^ 2 := sub_div _ _ _
        linarith [hd, heq2.le, heq2.ge]
      have h2 : (Cj / lamp ^ 2) ^ 2 * (2 * lamp) ≤
          2 * (C0 + C4) ^ 2 / lamp ^ 2 := by
        rw [div_pow]
        have hl3 : lamp ^ 2 * lamp ≤ (lamp ^ 2) ^ 2 := by
          nlinarith
        calc (Cj ^ 2 / (lamp ^ 2) ^ 2) * (2 * lamp) =
            2 * Cj ^ 2 * lamp / (lamp ^ 2) ^ 2 := by ring
          _ ≤ 2 * (C0 + C4) ^ 2 * lamp / (lamp ^ 2) ^ 2 := by
              have hnum : 2 * Cj ^ 2 * lamp ≤ 2 * (C0 + C4) ^ 2 * lamp := by
                have hCj2 : Cj ^ 2 ≤ (C0 + C4) ^ 2 := by
                  apply pow_le_pow_left₀ hCj hCjle 2
                nlinarith [hlamp0]
              have hd := div_nonneg (sub_nonneg.2 hnum)
                (by positivity : (0:ℝ) ≤ (lamp ^ 2) ^ 2)
              have heq2 : (2 * (C0 + C4) ^ 2 * lamp - 2 * Cj ^ 2 * lamp) /
                  (lamp ^ 2) ^ 2 =
                  2 * (C0 + C4) ^ 2 * lamp / (lamp ^ 2) ^ 2 -
                    2 * Cj ^ 2 * lamp / (lamp ^ 2) ^ 2 := sub_div _ _ _
              linarith [hd, heq2.le, heq2.ge]
          _ ≤ 2 * (C0 + C4) ^ 2 / lamp ^ 2 := by
              rw [div_le_div_iff₀ (by positivity) hlam2]
              nlinarith
      have hbig' : (2 * 533 * (C0 + C4) + 2 * (C0 + C4) ^ 2) / lamp ^ 2 ≤
          1 := by
        rw [div_le_one hlam2]
        nlinarith [hbig, sq_nonneg (C0 + C4)]
      have hsum : 2 * 533 * (C0 + C4) / lamp ^ 2 +
          2 * (C0 + C4) ^ 2 / lamp ^ 2 =
          (2 * 533 * (C0 + C4) + 2 * (C0 + C4) ^ 2) / lamp ^ 2 := by
        ring
      linarith
    rw [hnormsq]
    calc (∫ u : ℝ, ‖a * h u‖ ^ 2) ≤
        KD + (2 * c * KW + c ^ 2 * (2 * lamp)) := by linarith [hchain]
      _ ≤ KD + 1 := by linarith
      _ ≤ 2 * KD + 1 := by linarith
  constructor
  · -- mode zero
    apply hgeneric (centerAnchorScalarZero k)
      (selectedFerrersPreAnchorPair k).h0 ctW0 C0 1 1
      hC0 (by norm_num) (by norm_num) (by linarith)
    · rw [hh0]
      exact (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode_normalized
        (by omega)
    · rw [hh0]
      exact (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode_sqNorm_integrable
        (by omega)
    · exact tnc_ctW0_sq_integral
    · exact tnc_ctW0_abs_integral
    · norm_num
    · have hcont : Continuous ctW0 := by
        rw [show ctW0 = fun x : ℝ => Real.exp (-Real.pi * x ^ 2) from rfl]
        fun_prop
      have hrw : (fun y : ℝ => ctW0 y ^ 2) =
          fun y : ℝ => Real.exp (-(2 * Real.pi) * y ^ 2) := by
        funext y
        rw [ctW0, sq, ← Real.exp_add]
        congr 1
        ring
      rw [hrw]
      exact integrable_exp_neg_mul_sq (by positivity)
    · have hrw : (fun y : ℝ => |ctW0 y|) =
          fun y : ℝ => Real.exp (-Real.pi * y ^ 2) := by
        funext y
        rw [ctW0]
        exact abs_of_pos (Real.exp_pos _)
      rw [hrw]
      exact integrable_exp_neg_mul_sq Real.pi_pos
    · intro x hx
      have h := (hkmode x hx).1
      have hcast : ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) :
          ℂ) = ((ctW0 x : ℝ) : ℂ) := by
        rw [ctW0_eq_cylinder]
      rw [← hcast]
      exact h
    · intro x hx
      by_contra hne
      apply hx
      have hmem := (selectedFerrersPreAnchorPair k).h0_support hne
      rwa [hlam] at hmem
  · -- mode four
    apply hgeneric (centerAnchorScalarFour k)
      (selectedFerrersPreAnchorPair k).h4 ctW4 C4 (355 ^ 2) 533
      hC4 (by norm_num) (by norm_num) (by linarith)
    · rw [hh4]
      exact (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode_normalized
        (by omega)
    · rw [hh4]
      exact (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode_sqNorm_integrable
        (by omega)
    · exact tnc_ctW4_sq_integral
    · exact tnc_ctW4_abs_integral
    · norm_num
    · have hgauss_int : Integrable
          (fun y : ℝ => Real.exp (-Real.pi * y ^ 2)) volume :=
        integrable_exp_neg_mul_sq Real.pi_pos
      apply (hgauss_int.const_mul ((355 : ℝ) ^ 2)).mono'
      · apply Continuous.aestronglyMeasurable
        have : Continuous ctW4 := by
          rw [show ctW4 = fun x : ℝ =>
            (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3) *
              Real.exp (-Real.pi * x ^ 2) from rfl]
          fun_prop
        fun_prop
      · filter_upwards [] with y
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have henv := tnc_ctW4_envelope y
        have h1 : ctW4 y ^ 2 = |ctW4 y| ^ 2 := (sq_abs _).symm
        rw [h1]
        have h2 := pow_le_pow_left₀ (abs_nonneg _) henv 2
        have h3 : (355 * Real.exp (-(Real.pi * y ^ 2) / 2)) ^ 2 =
            355 ^ 2 * Real.exp (-Real.pi * y ^ 2) := by
          rw [mul_pow]
          congr 1
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        linarith
    · apply tnc_halfgauss_integrable.const_mul 355 |>.mono'
      · apply Measurable.aestronglyMeasurable
        apply Measurable.abs
        have : Continuous ctW4 := by
          rw [show ctW4 = fun x : ℝ =>
            (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3) *
              Real.exp (-Real.pi * x ^ 2) from rfl]
          fun_prop
        exact this.measurable
      · filter_upwards [] with y
        rw [Real.norm_eq_abs, abs_abs]
        exact tnc_ctW4_envelope y
    · intro x hx
      have h := (hkmode x hx).2
      have hcast : ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) :
          ℂ) = ((ctW4 x : ℝ) : ℂ) := by
        rw [parabolicCylinderD_four_projectArgument, ctW4]
        norm_cast
        ring
      rw [← hcast]
      exact h
    · intro x hx
      by_contra hne
      apply hx
      have hmem := (selectedFerrersPreAnchorPair k).h4_support hne
      rwa [hlam] at hmem

/-! ## Step B: eventual upper bound for the Lemma-7.3 source scale -/

private theorem tnc_scale_upper
    (C0 C4 Cχ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ k in Filter.atTop,
      ‖selectedFerrersLemma73SourceScale k‖ ≤ M := by
  obtain ⟨CI, hCI0, hCIrate⟩ :=
    selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate Cχ hCχ hχ
  have hM0 : (0 : ℝ) < (Real.sqrt (2 * 355 ^ 2 + 1) * (1 + CI) +
      Real.sqrt 3 * (3 + CI)) / 4 + 1 := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (2 * 355 ^ 2 + 1) * (1 + CI) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    have h2 : (0 : ℝ) ≤ Real.sqrt 3 * (3 + CI) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    have h3 := div_nonneg (add_nonneg h1 h2)
      (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  refine ⟨(Real.sqrt (2 * 355 ^ 2 + 1) * (1 + CI) +
    Real.sqrt 3 * (3 + CI)) / 4 + 1, hM0, ?_⟩
  filter_upwards [tnc_anchor_upper C0 C4 hC0 hC4 hmode, hCIrate]
    with k hka hkI
  set a0 : ℂ := centerAnchorScalarZero k with ha0def
  set a4 : ℂ := centerAnchorScalarFour k with ha4def
  set I0 : ℝ := (selectedFerrersPreAnchorPair k).I0 with hI0def
  set I4 : ℝ := (selectedFerrersPreAnchorPair k).I4 with hI4def
  set D : ℝ := (selectedFerrersPreAnchorPair k).normalizingDenominator
    with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, ProlatePair.normalizingDenominator_eq]
    apply Real.sqrt_pos.mpr
    have hI0pos := (selectedFerrersPreAnchorPair_spec k).2.2.2.1
    nlinarith [sq_nonneg (selectedFerrersPreAnchorPair k).I4]
  have hlamp1 : (1 : ℝ) ≤ selectedFerrersPaperLambda k := by
    rw [selectedFerrersPaperLambda]
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hlampsq1 : (1 : ℝ) ≤ (selectedFerrersPaperLambda k) ^ 2 := by
    nlinarith
  have hCIdrop : CI / (selectedFerrersPaperLambda k) ^ 2 ≤ CI :=
    div_le_self hCI0 hlampsq1
  -- exact norm of the source scale
  have hval : ‖selectedFerrersLemma73SourceScale k‖ =
      ‖a0‖ * ‖a4‖ * D / 4 := by
    rw [selectedFerrersLemma73SourceScale, selectedFerrersLemma72Scale]
    rw [norm_mul, norm_mul, norm_neg, norm_div, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDpos]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    have h16 : ‖(16 : ℂ)‖ = 16 := by norm_num
    rw [h4, h16]
    rw [← ha0def, ← ha4def]
    ring
  -- inverse-norm anchored integral bounds
  have ha0I0 : ‖a0‖ * |I0| ≤ 1 + CI := by
    have h1 : ‖a0 * ((I0 : ℝ) : ℂ)‖ ≤
        ‖a0 * ((I0 : ℝ) : ℂ) - 1‖ + ‖(1 : ℂ)‖ := by
      calc ‖a0 * ((I0 : ℝ) : ℂ)‖ =
          ‖(a0 * ((I0 : ℝ) : ℂ) - 1) + 1‖ := by ring_nf
        _ ≤ ‖a0 * ((I0 : ℝ) : ℂ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    have h2 := hkI.1
    have h3 : ‖a0 * ((I0 : ℝ) : ℂ)‖ = ‖a0‖ * |I0| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4 : ‖(1 : ℂ)‖ = 1 := by norm_num
    rw [h3, h4] at h1
    linarith [hCIdrop, h2]
  have ha4I4 : ‖a4‖ * |I4| ≤ 3 + CI := by
    have h1 : ‖a4 * ((I4 : ℝ) : ℂ)‖ ≤
        ‖a4 * ((I4 : ℝ) : ℂ) - 3‖ + ‖(3 : ℂ)‖ := by
      calc ‖a4 * ((I4 : ℝ) : ℂ)‖ =
          ‖(a4 * ((I4 : ℝ) : ℂ) - 3) + 3‖ := by ring_nf
        _ ≤ ‖a4 * ((I4 : ℝ) : ℂ) - 3‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
    have h2 := hkI.2
    have h3 : ‖a4 * ((I4 : ℝ) : ℂ)‖ = ‖a4‖ * |I4| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [h3, h4] at h1
    linarith [hCIdrop, h2]
  -- anchored-scalar magnitudes
  have ha0n : ‖a0‖ ≤ Real.sqrt 3 := by
    have h := hka.1
    have h3 : ‖a0‖ ^ 2 ≤ 3 := by linarith
    have h4 : ‖a0‖ = Real.sqrt (‖a0‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h4]
    exact Real.sqrt_le_sqrt h3
  have ha4n : ‖a4‖ ≤ Real.sqrt (2 * 355 ^ 2 + 1) := by
    have h := hka.2
    have h4 : ‖a4‖ = Real.sqrt (‖a4‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h4]
    exact Real.sqrt_le_sqrt h
  -- denominator by the triangle
  have hD_le : D ≤ |I0| + |I4| := by
    rw [hDdef, ProlatePair.normalizingDenominator_eq]
    rw [← hI0def, ← hI4def]
    have hs1 : Real.sqrt (I0 ^ 2 + I4 ^ 2) ≤
        Real.sqrt ((|I0| + |I4|) ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_abs I0, sq_abs I4, abs_nonneg I0, abs_nonneg I4,
        mul_nonneg (abs_nonneg I0) (abs_nonneg I4)]
    have hs2 : Real.sqrt ((|I0| + |I4|) ^ 2) = |I0| + |I4| :=
      Real.sqrt_sq (by positivity)
    linarith
  -- final chain
  rw [hval]
  have hstep1 : ‖a0‖ * ‖a4‖ * D ≤ ‖a0‖ * ‖a4‖ * (|I0| + |I4|) := by
    apply mul_le_mul_of_nonneg_left hD_le (by positivity)
  have hsplit : ‖a0‖ * ‖a4‖ * (|I0| + |I4|) =
      ‖a4‖ * (‖a0‖ * |I0|) + ‖a0‖ * (‖a4‖ * |I4|) := by ring
  have h1 : ‖a4‖ * (‖a0‖ * |I0|) ≤
      Real.sqrt (2 * 355 ^ 2 + 1) * (1 + CI) := by
    apply mul_le_mul ha4n ha0I0 (by positivity) (Real.sqrt_nonneg _)
  have h2 : ‖a0‖ * (‖a4‖ * |I4|) ≤ Real.sqrt 3 * (3 + CI) := by
    apply mul_le_mul ha0n ha4I4 (by positivity) (Real.sqrt_nonneg _)
  have hstep1' : ‖a0‖ * ‖a4‖ * D ≤
      ‖a4‖ * (‖a0‖ * |I0|) + ‖a0‖ * (‖a4‖ * |I4|) := by
    rw [← hsplit]; exact hstep1
  have hsum : ‖a0‖ * ‖a4‖ * D ≤
      Real.sqrt (2 * 355 ^ 2 + 1) * (1 + CI) + Real.sqrt 3 * (3 + CI) :=
    hstep1'.trans (add_le_add h1 h2)
  have hq : ‖a0‖ * ‖a4‖ * D / 4 ≤
      (Real.sqrt (2 * 355 ^ 2 + 1) * (1 + CI) +
        Real.sqrt 3 * (3 + CI)) / 4 := by
    gcongr
  exact hq.trans (le_add_of_nonneg_right zero_le_one)

/-! ## Step D: the scaled local-cell `E⋆` floor -/

/-- The paper window scale `λ_k = √(k+2)` crosses any fixed threshold. -/
private theorem tnc_paperLambda_eventually_ge (T : ℝ) :
    ∀ᶠ k in Filter.atTop, T ≤ selectedFerrersPaperLambda k := by
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (T ^ 2))] with k hk
  rw [selectedFerrersPaperLambda]
  have h3 := Nat.le_ceil (T ^ 2)
  have h2 : ((Nat.ceil (T ^ 2) : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by
    exact_mod_cast hk
  have h1 : T ^ 2 ≤ ((k + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  calc T ≤ |T| := le_abs_self T
    _ = Real.sqrt (T ^ 2) := (Real.sqrt_sq_eq_abs T).symm
    _ ≤ Real.sqrt ((k + 2 : ℕ) : ℝ) := Real.sqrt_le_sqrt h1

/-- Active-card counting: on the cell (`u ≥ 1`) at most `λ` positive
integers stay inside the port window. -/
private theorem tnc_active_card_le
    (S0 : Finset ℕ+) {u lam : ℝ} (hu1 : 1 ≤ u) (hlam0 : 0 ≤ lam) :
    (((S0.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ lam)).card : ℕ) : ℝ) ≤
      lam := by
  classical
  have hsub : (S0.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ lam)).image
      (fun n : ℕ+ => (n : ℕ)) ⊆ Finset.Icc 1 (Nat.floor lam) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hnu : ((n : ℕ) : ℝ) * u ≤ lam := (Finset.mem_filter.mp hn).2
    have hp : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := by positivity
    have hn1 : ((n : ℕ) : ℝ) * 1 ≤ ((n : ℕ) : ℝ) * u :=
      mul_le_mul_of_nonneg_left hu1 hp
    have hnle : ((n : ℕ) : ℝ) ≤ lam := by linarith
    exact Finset.mem_Icc.mpr ⟨n.pos, Nat.le_floor hnle⟩
  have hinj : Function.Injective (fun n : ℕ+ => (n : ℕ)) :=
    fun a b h => PNat.coe_injective h
  have hcard :
      (S0.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ lam)).card =
        ((S0.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ lam)).image
          (fun n : ℕ+ => (n : ℕ))).card :=
    (Finset.card_image_of_injective _ hinj).symm
  have hle := Finset.card_le_card hsub
  have hIcc : (Finset.Icc 1 (Nat.floor lam)).card = Nat.floor lam := by
    rw [Nat.card_Icc]
    omega
  have hnat :
      (S0.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ lam)).card ≤
        Nat.floor lam := by
    rw [hcard]
    rw [hIcc] at hle
    exact hle
  have hfl : ((Nat.floor lam : ℕ) : ℝ) ≤ lam := Nat.floor_le hlam0
  have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
  linarith

set_option maxHeartbeats 8000000 in
/-- **Step D.**  The scaled `E⋆` comb keeps the fixed positive floor
`tnc_cellFloor / 2` on the whole cell `[1, 9/8]`, eventually in `k`:
the `n = 1` term supplies the floor, every other active term is positive
and the port packet error dies as `Cp/λ` after active-card counting. -/
private theorem tnc_scaled_cell_floor
    (C0 C4 Cχ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop, ∀ u ∈ Set.Icc (1 : ℝ) (9 / 8 : ℝ),
      tnc_cellFloor / 2 ≤
        ‖selectedFerrersLemma73SourceScale k *
          E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ := by
  classical
  obtain ⟨Cp, hCp0, hport⟩ :=
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hfl := tnc_cellFloor_pos
  filter_upwards [hport,
    tnc_paperLambda_eventually_ge (2 + 2 * Cp / tnc_cellFloor)] with k hkport hkthr
  intro u hu
  have hu1 : (1 : ℝ) ≤ u := hu.1
  have hu98 : u ≤ (9 / 8 : ℝ) := hu.2
  have hfrac0 : (0 : ℝ) ≤ 2 * Cp / tnc_cellFloor := by positivity
  have hlam2 : (2 : ℝ) ≤ selectedFerrersPaperLambda k := by linarith
  have hlam0 : (0 : ℝ) < selectedFerrersPaperLambda k := by linarith
  have hlameq : selectedFerrersPaperLambda k =
      lambda_m (selectedFerrersPreAnchorIndex k) :=
    selectedFerrersPaperLambda_eq_lambda_m k
  have hpwlam : (selectedFerrersPreAnchorPair k).pw.lambda =
      selectedFerrersPaperLambda k :=
    selectedFerrersPreAnchorPair_lambda_eq_paperLambda k
  have h2Cp : 2 * Cp ≤ tnc_cellFloor * selectedFerrersPaperLambda k := by
    have h1 : 2 * Cp / tnc_cellFloor ≤ selectedFerrersPaperLambda k := by
      linarith
    have h2 : tnc_cellFloor * (2 * Cp / tnc_cellFloor) = 2 * Cp := by
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hfl)]
    have h3 := mul_le_mul_of_nonneg_left h1 hfl.le
    linarith
  have hCplam : Cp / selectedFerrersPaperLambda k ≤ tnc_cellFloor / 2 := by
    have hnum : (0 : ℝ) ≤ tnc_cellFloor * selectedFerrersPaperLambda k - 2 * Cp := by
      linarith
    have hden : (0 : ℝ) < 2 * selectedFerrersPaperLambda k := by linarith
    have hquot := div_nonneg hnum hden.le
    have hkey : (tnc_cellFloor * selectedFerrersPaperLambda k - 2 * Cp) /
        (2 * selectedFerrersPaperLambda k) =
        tnc_cellFloor / 2 - Cp / selectedFerrersPaperLambda k := by
      field_simp
    rw [hkey] at hquot
    linarith
  have hwin : u ∈ sourceWindow (lambda_m (selectedFerrersPreAnchorIndex k)) := by
    rw [← hlameq, sourceWindow, Set.mem_Icc]
    constructor
    · have hinv : (selectedFerrersPaperLambda k)⁻¹ ≤ 1 := by
        rw [inv_eq_one_div, div_le_one hlam0]
        linarith
      linarith
    · linarith
  have hsupp := prolateCombination_windowFiniteSupport
    (selectedFerrersPreAnchorIndex k) (selectedFerrersPreAnchorPair k)
    (by rw [hpwlam, hlameq])
  rw [E_star_eq_finiteEStar_of_windowFiniteSupport hsupp hwin]
  rw [finiteEStar]
  have hrearr : selectedFerrersLemma73SourceScale k *
      ((Real.sqrt u : ℂ) *
        finiteEStarCore (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
          (prolateCombination (selectedFerrersPreAnchorPair k)) u) =
      (Real.sqrt u : ℂ) *
        (selectedFerrersLemma73SourceScale k *
          finiteEStarCore (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
            (prolateCombination (selectedFerrersPreAnchorPair k)) u) := by
    ring
  rw [hrearr, norm_mul]
  have hsq1 : (1 : ℝ) ≤ Real.sqrt u := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hu1
  have hnorm_sqrt : ‖((Real.sqrt u : ℝ) : ℂ)‖ = Real.sqrt u := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg u)]
  rw [hnorm_sqrt]
  have h4re : ∀ x : ℝ, ((4 : ℂ) * explicitCCMLimitH x).re = 4 * hbHRe x := by
    intro x
    rw [explicitCCMLimitH_eq_hbHRe,
      show ((4 : ℂ)) = (((4 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hcore : tnc_cellFloor / 2 ≤
      ‖selectedFerrersLemma73SourceScale k *
        finiteEStarCore (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
          (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ := by
    refine le_trans ?_
      (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
    have hexp : selectedFerrersLemma73SourceScale k *
        finiteEStarCore (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
          (prolateCombination (selectedFerrersPreAnchorPair k)) u =
        ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
          selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u) := by
      rw [finiteEStarCore, Finset.mul_sum]
    rw [hexp, Complex.re_sum]
    rw [← Finset.sum_filter_add_sum_filter_not
      (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
      (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k)
      (fun n : ℕ+ => (selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u)).re)]
    have hinactive : ∑ n ∈ Finset.filter (fun n : ℕ+ => ¬ ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)),
        (selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u)).re = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hgt : selectedFerrersPaperLambda k < ((n : ℕ) : ℝ) * u :=
        not_le.mp (Finset.mem_filter.mp hn).2
      have hzero : prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u) = 0 := by
        apply prolateCombination_eq_zero_outside
        intro hmem
        rw [Set.mem_Icc, hpwlam] at hmem
        linarith [hmem.2]
      rw [hzero, mul_zero, Complex.zero_re]
    have hterm : ∀ n ∈ Finset.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)),
        4 * hbHRe (((n : ℕ) : ℝ) * u) - Cp / selectedFerrersPaperLambda k ^ 2 ≤ (selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u)).re := by
      intro n hn
      have hnu_le : ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k :=
        (Finset.mem_filter.mp hn).2
      have hnu0 : (0 : ℝ) ≤ ((n : ℕ) : ℝ) * u := by positivity
      have hport_n := hkport (((n : ℕ) : ℝ) * u)
        (Set.mem_Icc.mpr ⟨by linarith, hnu_le⟩)
      have hdiff := Complex.abs_re_le_norm
        (selectedFerrersLemma73SourceScale k *
          prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u) -
          (4 : ℂ) * explicitCCMLimitH (((n : ℕ) : ℝ) * u))
      have hsub : (selectedFerrersLemma73SourceScale k *
          prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u) -
          (4 : ℂ) * explicitCCMLimitH (((n : ℕ) : ℝ) * u)).re =
          (selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u)).re -
            4 * hbHRe (((n : ℕ) : ℝ) * u) := by
        rw [Complex.sub_re, h4re]
      have habs : |(selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) (((n : ℕ) : ℝ) * u)).re -
          4 * hbHRe (((n : ℕ) : ℝ) * u)| ≤
          Cp / selectedFerrersPaperLambda k ^ 2 := by
        rw [← hsub]
        exact le_trans hdiff hport_n
      linarith [(abs_le.mp habs).1]
    have hsum1 := Finset.sum_le_sum hterm
    have hsplit : ∑ n ∈ Finset.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)),
        (4 * hbHRe (((n : ℕ) : ℝ) * u) - Cp / selectedFerrersPaperLambda k ^ 2) =
        (∑ n ∈ Finset.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)),
          4 * hbHRe (((n : ℕ) : ℝ) * u)) -
          (((Finset.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))).card : ℕ) : ℝ) * (Cp / selectedFerrersPaperLambda k ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1A : (1 : ℕ+) ∈ Finset.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)) := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [sourcePositiveIndexFinset]
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · exact_mod_cast (le_refl (1 : ℕ))
        · have hm : 2 ≤ (selectedFerrersPreAnchorIndex k).m :=
            (selectedFerrersPreAnchorIndex k).hm
          exact_mod_cast le_trans one_le_two hm
      · have hone : (((1 : ℕ+) : ℕ) : ℝ) = 1 := by norm_num
        rw [hone, one_mul]
        linarith
    have hposH : ∀ n ∈ Finset.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)),
        0 ≤ 4 * hbHRe (((n : ℕ) : ℝ) * u) := by
      intro n hn
      have hp := n.pos
      have hn1 : (1 : ℕ) ≤ (n : ℕ) := hp
      have hn1' : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn1
      have hmul := mul_le_mul hn1' hu1 zero_le_one
        (le_trans zero_le_one hn1')
      have hnu1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) * u := by linarith
      have := tnc_H_pos hnu1
      linarith
    have hsingle := Finset.single_le_sum hposH h1A
    have honeC : ((((1 : ℕ+) : ℕ) : ℝ)) * u = u := by norm_num
    rw [honeC] at hsingle
    have hHfl := tnc_H_cell_floor (Set.mem_Icc.mpr ⟨hu1, hu98⟩)
    have hcard := tnc_active_card_le
      (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)) hu1 hlam0.le
    have hcardmul : (((Finset.filter (fun n : ℕ+ => ((n : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k) (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))).card : ℕ) : ℝ) *
        (Cp / selectedFerrersPaperLambda k ^ 2) ≤
        Cp / selectedFerrersPaperLambda k := by
      have h2 : (0 : ℝ) ≤ Cp / selectedFerrersPaperLambda k ^ 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_right hcard h2
      have h4 : selectedFerrersPaperLambda k * (Cp / selectedFerrersPaperLambda k ^ 2) =
          Cp / selectedFerrersPaperLambda k := by
        rw [pow_two, ← div_div, mul_comm,
          div_mul_cancel₀ _ (ne_of_gt hlam0)]
      linarith
    rw [hinactive, add_zero]
    linarith [hsum1, hsplit, hsingle, hHfl, hcardmul, hCplam]
  have hmul := mul_le_mul_of_nonneg_right hsq1 (norm_nonneg
    (selectedFerrersLemma73SourceScale k *
      finiteEStarCore (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
        (prolateCombination (selectedFerrersPreAnchorPair k)) u))
  rw [one_mul] at hmul
  linarith

/-! ## Step E: the full-object `H_m` norm floor -/

/-- The `dStar` mass of the cell is at least `1/9`. -/
private theorem tnc_cell_dstar_mass_lb :
    ENNReal.ofReal (1 / 9 : ℝ) ≤ dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ)) := by
  rw [dStar, withDensity_apply _ measurableSet_Icc]
  have hmono : ∫⁻ _ in Set.Icc (1 : ℝ) (9 / 8 : ℝ), ENNReal.ofReal (8 / 9 : ℝ) ≤
      ∫⁻ x in Set.Icc (1 : ℝ) (9 / 8 : ℝ), ENNReal.ofReal x⁻¹ := by
    apply setLIntegral_mono' measurableSet_Icc
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    have h1 := one_div_le_one_div_of_le hx0 hx.2
    rw [inv_eq_one_div]
    calc (8 / 9 : ℝ) = 1 / (9 / 8 : ℝ) := by norm_num
      _ ≤ 1 / x := h1
  calc ENNReal.ofReal (1 / 9 : ℝ) =
      ENNReal.ofReal (8 / 9 : ℝ) * volume (Set.Icc (1 : ℝ) (9 / 8 : ℝ)) := by
        rw [Real.volume_Icc,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8 / 9)]
        norm_num
    _ = ∫⁻ _ in Set.Icc (1 : ℝ) (9 / 8 : ℝ), ENNReal.ofReal (8 / 9 : ℝ) := by
        rw [setLIntegral_const]
    _ ≤ _ := hmono

/-- The `dStar` mass of the cell is at most `1/8`. -/
private theorem tnc_cell_dstar_mass_ub :
    dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ)) ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
  rw [dStar, withDensity_apply _ measurableSet_Icc]
  have hmono : ∫⁻ x in Set.Icc (1 : ℝ) (9 / 8 : ℝ), ENNReal.ofReal x⁻¹ ≤
      ∫⁻ _ in Set.Icc (1 : ℝ) (9 / 8 : ℝ), ENNReal.ofReal (1 : ℝ) := by
    apply setLIntegral_mono' measurableSet_Icc
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    have h1 := one_div_le_one_div_of_le one_pos hx.1
    rw [inv_eq_one_div]
    calc 1 / x ≤ 1 / (1 : ℝ) := h1
      _ = 1 := by norm_num
  calc (∫⁻ x in Set.Icc (1 : ℝ) (9 / 8 : ℝ), ENNReal.ofReal x⁻¹) ≤
      ∫⁻ _ in Set.Icc (1 : ℝ) (9 / 8 : ℝ), ENNReal.ofReal (1 : ℝ) := hmono
    _ = ENNReal.ofReal (1 : ℝ) * volume (Set.Icc (1 : ℝ) (9 / 8 : ℝ)) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
        rw [Real.volume_Icc,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1)]
        apply ENNReal.ofReal_le_ofReal
        norm_num

set_option maxHeartbeats 8000000 in
/-- **Step E.**  Eventual full-object norm floor for the literal pre-anchor
trial: divide the scaled cell floor by the scale bound and integrate the
resulting pointwise floor over the cell of `dStar` mass at least `1/9`. -/
private theorem tnc_full_norm_floor
    (C0 C4 Cχ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
      c ≤ ‖gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k)‖ := by
  obtain ⟨M, hM0, hMev⟩ := tnc_scale_upper C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hcell := tnc_scaled_cell_floor C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hfl := tnc_cellFloor_pos
  refine ⟨tnc_cellFloor / 2 / M * (1 / 3), by positivity, ?_⟩
  filter_upwards [hMev, hcell, tnc_paperLambda_eventually_ge 2] with
    k hkM hkcell hklam
  have hb0 : (0 : ℝ) < tnc_cellFloor / 2 / M := by positivity
  have hpt : ∀ u ∈ Set.Icc (1 : ℝ) (9 / 8 : ℝ),
      tnc_cellFloor / 2 / M ≤
        ‖E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ := by
    intro u hu
    have h1 := hkcell u hu
    have h2 : ‖selectedFerrersLemma73SourceScale k *
        E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ ≤
        M * ‖E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hkM (norm_nonneg _)
    have h3 : tnc_cellFloor / 2 ≤ M * ‖E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ :=
      le_trans h1 h2
    have hkey : (M * ‖E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ - tnc_cellFloor / 2) / M =
        ‖E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ - tnc_cellFloor / 2 / M := by
      rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hM0)]
    have h5 : (0 : ℝ) ≤
        (M * ‖E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ - tnc_cellFloor / 2) / M :=
      div_nonneg (by linarith) hM0.le
    rw [hkey] at h5
    linarith
  have hlameq := selectedFerrersPaperLambda_eq_lambda_m k
  have hlam0 : (0 : ℝ) < selectedFerrersPaperLambda k := by linarith
  have hsub : Set.Icc (1 : ℝ) (9 / 8 : ℝ) ⊆ I_m (selectedFerrersPreAnchorIndex k) := by
    intro u hu
    rw [I_m, Set.mem_Icc]
    constructor
    · have hinv : (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ ≤ 1 := by
        rw [← hlameq, inv_eq_one_div, div_le_one hlam0]
        linarith
      linarith [hu.1]
    · rw [← hlameq]
      linarith [hu.2]
  have hmemLp := selectedFerrersPreAnchorPair_eStar_memLp k
  have hmass_lb := tnc_cell_dstar_mass_lb
  have hmass_ub := tnc_cell_dstar_mass_ub
  have hcellpos : dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ)) ≠ 0 := by
    intro hzero
    have h1 : (dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) Set.univ = 0 := by
      rw [hzero]
      simp
    rw [Measure.restrict_apply_univ] at h1
    rw [h1] at hmass_lb
    have h2 : ENNReal.ofReal (1 / 9 : ℝ) = 0 :=
      le_antisymm hmass_lb (zero_le _)
    rw [ENNReal.ofReal_eq_zero] at h2
    norm_num at h2
  have hae : ∀ᵐ u ∂(dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))),
      tnc_cellFloor / 2 / M ≤ ‖E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u‖ := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ hpt
  have h1 : eLpNorm (fun _ : ℝ => ((tnc_cellFloor / 2 / M : ℝ) : ℂ)) 2
      (dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) =
      ENNReal.ofReal (tnc_cellFloor / 2 / M) *
        (dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) ^ ((1 : ℝ) / (2 : ℝ)) := by
    rw [eLpNorm_const _ (by norm_num) hcellpos]
    have he : ‖((tnc_cellFloor / 2 / M : ℝ) : ℂ)‖ₑ =
        ENNReal.ofReal (tnc_cellFloor / 2 / M) := by
      rw [show ‖((tnc_cellFloor / 2 / M : ℝ) : ℂ)‖ₑ =
          ENNReal.ofReal ‖((tnc_cellFloor / 2 / M : ℝ) : ℂ)‖ from
        (ofReal_norm_eq_enorm _).symm]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
    rw [he, Measure.restrict_apply_univ]
    norm_num
  have h2 : eLpNorm (fun _ : ℝ => ((tnc_cellFloor / 2 / M : ℝ) : ℂ)) 2
      (dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) ≤
      eLpNorm (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
        (dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) := by
    apply eLpNorm_mono_ae
    filter_upwards [hae] with u hu
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
    exact hu
  have h3 : eLpNorm (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
      (dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) ≤
      eLpNorm (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
        (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
    apply eLpNorm_mono_measure
    exact Measure.restrict_mono hsub le_rfl
  have hmassfin : dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass_ub
  have hpow_lb : ENNReal.ofReal (1 / 3 : ℝ) ≤
      (dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) ^ ((1 : ℝ) / (2 : ℝ)) := by
    have hstep : ENNReal.ofReal (1 / 9 : ℝ) ^ ((1 : ℝ) / (2 : ℝ)) ≤
        (dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) ^ ((1 : ℝ) / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow hmass_lb (by norm_num)
    have hval : ENNReal.ofReal (1 / 9 : ℝ) ^ ((1 : ℝ) / (2 : ℝ)) =
        ENNReal.ofReal (1 / 3 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 9)]
      congr 1
      rw [← Real.sqrt_eq_rpow]
      rw [show (1 / 9 : ℝ) = (1 / 3 : ℝ) ^ 2 by norm_num]
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    rw [← hval]
    exact hstep
  have hfinal_lb : ENNReal.ofReal (tnc_cellFloor / 2 / M * (1 / 3)) ≤
      ENNReal.ofReal (tnc_cellFloor / 2 / M) *
        (dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) ^ ((1 : ℝ) / (2 : ℝ)) := by
    rw [ENNReal.ofReal_mul hb0.le]
    exact mul_le_mul_left' hpow_lb _
  have hchain : ENNReal.ofReal (tnc_cellFloor / 2 / M * (1 / 3)) ≤
      eLpNorm (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
        (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
    calc ENNReal.ofReal (tnc_cellFloor / 2 / M * (1 / 3)) ≤
        ENNReal.ofReal (tnc_cellFloor / 2 / M) *
          (dStar (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) ^ ((1 : ℝ) / (2 : ℝ)) := hfinal_lb
      _ = eLpNorm (fun _ : ℝ => ((tnc_cellFloor / 2 / M : ℝ) : ℂ)) 2
          (dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) := h1.symm
      _ ≤ eLpNorm (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
          (dStar.restrict (Set.Icc (1 : ℝ) (9 / 8 : ℝ))) := h2
      _ ≤ _ := h3
  have hnorm : ‖gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k)‖ =
      (eLpNorm (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
        (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k)))).toReal :=
    MeasureTheory.Lp.norm_toLp _ _
  rw [hnorm]
  have htoR : (ENNReal.ofReal (tnc_cellFloor / 2 / M * (1 / 3))).toReal =
      tnc_cellFloor / 2 / M * (1 / 3) :=
    ENNReal.toReal_ofReal (by positivity)
  calc tnc_cellFloor / 2 / M * (1 / 3) =
      (ENNReal.ofReal (tnc_cellFloor / 2 / M * (1 / 3))).toReal := htoR.symm
    _ ≤ (eLpNorm (E_star (prolateCombination (selectedFerrersPreAnchorPair k))) 2
        (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k)))).toReal :=
      ENNReal.toReal_mono hmemLp.2.ne hchain

/-! ## Step F: transport, reverse triangle and the public theorems -/

/-- Norms of the full trial transport across index/trial equalities. -/
private theorem tnc_gTrial_norm_transport
    {i i' : PairIndex} (hii : i = i') {h h' : ℝ → ℂ} (hhh : h = h')
    (w : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (w' : MemLp (E_star h') 2 (dStar.restrict (I_m i'))) :
    ‖gTrial_m i h w‖ = ‖gTrial_m i' h' w'‖ := by
  subst hii
  subst hhh
  rfl

/-- **The second W5 supplier** (verdict `82ac9628`,
GOAL058_SELECTED_FERRERS_LOCAL_CELL_NORMALIZER_CLOSURE).  The selected
trial normalizer is eventually bounded, from exactly the frozen inputs:
the local-cell floor bounds the full trial norm below, the admitted
projection tail decay and the reverse triangle bound the projected norm
below, and the normalizer is the inverse projected norm. -/
theorem selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
    (S : ProlateCanonicalSourceData)
    (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    SelectedTrialNormalizerBounded S := by
  have htail := selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
    S hFamily C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ
  obtain ⟨c, hc0, hcev⟩ := tnc_full_norm_floor C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hres : ∀ᶠ k in Filter.atTop,
      selectedUnnormalizedGalerkinResidualNorm S k < c / 2 :=
    htail.eventually_lt_const (by positivity)
  refine ⟨2 / c, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [hFamily, hcev, hres] with k hkF hkc hkres
  obtain ⟨hidx, htrial⟩ := hkF
  have hfullS : c ≤ ‖gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k))‖ := by
    rw [tnc_gTrial_norm_transport hidx htrial
      (S.source.eStar_memLp (selectedPairIndex S k))
      (selectedFerrersPreAnchorPair_eStar_memLp k)]
    exact hkc
  have hresid_eq : selectedUnnormalizedGalerkinResidualNorm S k =
      ‖(gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k)) -
        gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k))‖ := rfl
  have htri := abs_norm_sub_norm_le
    (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)))
    ((gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k)))
  have h2 : ‖gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k))‖ -
      ‖(gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k))‖ ≤
      ‖gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) -
        (gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k))‖ :=
    le_trans (le_abs_self _) htri
  have hswap : ‖gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) -
      (gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k))‖ =
      ‖(gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k)) -
        gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k))‖ := norm_sub_rev _ _
  have hgN : c / 2 ≤
      ‖(gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k))‖ := by
    rw [hswap, ← hresid_eq] at h2
    linarith
  have hcoe : ‖(gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k)) : H_m (selectedPairIndex S k))‖ =
      ‖gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k))‖ := rfl
  rw [hcoe] at hgN
  have hval : selectedTrialNormalizer S k =
      ‖gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k)
      (S.source.eStar_memLp (selectedPairIndex S k))‖⁻¹ := rfl
  rw [Complex.norm_real, Real.norm_eq_abs, hval, abs_inv, abs_norm,
    inv_eq_one_div]
  have h1d := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < c / 2) hgN
  calc 1 / ‖gTrial_m_N (selectedPairIndex S k) (selectedProlateTrial S k) (S.source.eStar_memLp (selectedPairIndex S k))‖ ≤ 1 / (c / 2) := h1d
    _ = 2 / c := one_div_div c 2

/-- **The closed normalized residual** (verdict `82ac9628`).  Both
suppliers of the exact two-premise receiver are now produced from the
frozen W5 ledger; the literal normalized Galerkin residual vanishes. -/
theorem
    selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger
    (S : ProlateCanonicalSourceData)
    (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    Tendsto
      (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
      atTop
      (𝓝 0) :=
  selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded S
    (selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
      S hFamily C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ)
    (selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
      S hFamily C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ)

#print axioms selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
#print axioms
  selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger

end Q3.RouteB.D0Pstar
