import Q3.Proofs.RouteB.G6N1SelectedFerrersPacketVariation
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Prod

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 2400000

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology FourierTransform ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.4.1b.3c.1.12 — selected Ferrers Abel–Poisson `L²` lock (W3)

For the exact complex-scaled production packet `f_k`, this file constructs

`u⁻¹ᐟ² ∑_{n≥1} rⁿ 𝓕(f_k)(n/u)`, `0 ≤ r < 1`,

and proves convergence in `L²(dStar|I_m)` to

`E_star(f_k)(u) + (1/2) f_k(0) √u`.

The proof uses a finite periodization and a positive unit-mass Poisson kernel.
The production endpoint values are not replaced pointwise by midpoint values:
the finitely many endpoint seams are removed only in the almost-everywhere
argument.  Exact evenness, rather than real-valuedness, identifies the positive
and negative Fourier coefficients.

SEARCH_FLAGS:
  - `./ask.sh "selectedFerrersLemma73SourcePacket prolateCombination even"`
  - `./ask.sh "selectedFerrersLemma73SourcePacket integral zero mass"`
  - `./ask.sh "dStar I_m measurableSet finite interval"`
  - `./ask.sh "finite support bound Int periodization Set.Icc"`
  - `./ask.sh "circle Fourier Poisson kernel geometric tsum intervalIntegral"`

LEDGER:
  CLOSES: [W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK]
  OPENS:  []
-/

private abbrev selectedPacket (k : ℕ) : ℝ → ℂ :=
  selectedFerrersLemma73SourcePacket k

/-! ## Mandatory falsifier plants -/

/-- A single full endpoint contribution and its midpoint replacement differ
pointwise, even though all non-seam terms agree. -/
private theorem full_endpoint_vs_midpoint_eStar_seam_plant :
    ∃ full midpoint : ℕ → ℂ,
      Summable full ∧ Summable midpoint ∧
      full 1 = 1 ∧ midpoint 1 = 1 / 2 ∧
      (∀ n : ℕ, n ≠ 1 → full n = midpoint n) ∧
      (∑' n : ℕ, full n) ≠ ∑' n : ℕ, midpoint n := by
  let full : ℕ → ℂ := fun n => if n = 1 then 1 else 0
  let midpoint : ℕ → ℂ := fun n => if n = 1 then 1 / 2 else 0
  have hfull : Summable full := summable_of_ne_finset_zero
    (s := {1}) (by intro n hn; simp [full] at hn ⊢; exact hn)
  have hmid : Summable midpoint := summable_of_ne_finset_zero
    (s := {1}) (by intro n hn; simp [midpoint] at hn ⊢; exact hn)
  refine ⟨full, midpoint, hfull, hmid, by simp [full], by simp [midpoint],
    ?_, ?_⟩
  · intro n hn
    simp [full, midpoint, hn]
  · rw [tsum_eq_single 1 (by intro b hb; simp [full, hb]),
      tsum_eq_single 1 (by intro b hb; simp [midpoint, hb])]
    norm_num [full, midpoint]

/-- Without zero mass, the omitted zero-frequency correction is nonzero on
every positive multiplicative scale. -/
private theorem zero_mass_is_load_bearing_plant
    {a : ℂ} (ha : a ≠ 0) {u : ℝ} (hu : 0 < u) :
    -(1 / 2 : ℂ) * a * (Real.sqrt u : ℂ)⁻¹ ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) ha)
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne'))

/-- Pointwise convergence alone does not imply `L²` convergence: the moving
unit vectors in counting measure converge pointwise to zero while retaining
squared norm one. -/
private theorem pointwise_without_domination_does_not_give_l2_plant :
    ∃ f : ℕ → ℕ → ℝ,
      (∀ x : ℕ, Tendsto (fun n : ℕ => f n x) atTop (𝓝 0)) ∧
      (∀ n : ℕ, (∫ x : ℕ, ‖f n x‖ ^ 2 ∂Measure.count) = 1) := by
  let f : ℕ → ℕ → ℝ := fun n x => if x = n then 1 else 0
  refine ⟨f, ?_, ?_⟩
  · intro x
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨x + 1, fun n hn => ?_⟩
    have hne : x ≠ n := by omega
    simp [f, hne, hε]
  · intro n
    have heq : (fun x : ℕ => ‖f n x‖ ^ 2) =
        ({n} : Set ℕ).indicator (fun _ : ℕ => (1 : ℝ)) := by
      funext x
      by_cases hx : x = n <;> simp [f, hx]
    rw [heq, integral_indicator (measurableSet_singleton n),
      integral_singleton]
    simp

/-- Compact support, integrability and exact evenness do not force a
complex-valued packet to be real-valued. -/
private theorem complex_even_packet_does_not_require_real_valuedness_plant :
    ∃ f : ℝ → ℂ,
      Integrable f volume ∧ Function.Even f ∧ f 0 = I := by
  let f : ℝ → ℂ :=
    (Set.Icc (-1 : ℝ) 1).indicator (fun _ => I)
  refine ⟨f, ?_, ?_, ?_⟩
  · have hconst : IntegrableOn (fun _ : ℝ => I)
        (Set.Icc (-1 : ℝ) 1) volume :=
      integrableOn_const (hs := by rw [Real.volume_Icc]; norm_num)
    exact hconst.integrable_indicator measurableSet_Icc
  · intro x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · have hneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith [hx.1, hx.2]
      simp [f, hx, hneg]
    · have hneg : -x ∉ Set.Icc (-1 : ℝ) 1 := by
        intro h
        apply hx
        constructor <;> linarith [h.1, h.2]
      simp [f, hx, hneg]
  · simp [f]

/-! ## Exact public objects -/

/-- The exact positive-frequency reflected Abel family. -/
noncomputable def selectedFerrersReflectedAbel
    (k : ℕ) (r u : ℝ) : ℂ :=
  (Real.sqrt u : ℂ)⁻¹ *
    ∑' n : ℕ+,
      (r : ℂ) ^ (n : ℕ) *
        𝓕 (selectedFerrersLemma73SourcePacket k)
          (((n : ℕ) : ℝ) / u)

/-- The production full-endpoint target.  Equality with the midpoint Poisson
limit is asserted only almost everywhere on the multiplicative window. -/
noncomputable def selectedFerrersAbelLimit
    (k : ℕ) (u : ℝ) : ℂ :=
  E_star (selectedFerrersLemma73SourcePacket k) u +
    (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
      (Real.sqrt u : ℂ)

/-! ## Exact packet locks -/

private theorem selectedPacket_even (k : ℕ) :
    Function.Even (selectedPacket k) := by
  intro x
  simp only [selectedPacket, selectedFerrersLemma73SourcePacket]
  rw [prolateCombination_even (selectedFerrersPreAnchorPair k) x]

private theorem selectedPacket_integrable (k : ℕ) :
    Integrable (selectedPacket k) volume := by
  simpa only [selectedPacket, selectedFerrersLemma73SourcePacket] using
    (prolateCombination_integrable (selectedFerrersPreAnchorPair k)).const_mul
      (selectedFerrersLemma73SourceScale k)

private theorem selectedPacket_zero_mass (k : ℕ) :
    (∫ x : ℝ, selectedPacket k x) = 0 := by
  simp only [selectedPacket, selectedFerrersLemma73SourcePacket]
  rw [integral_const_mul,
    integral_prolateCombination_eq_zero (selectedFerrersPreAnchorPair k),
    mul_zero]

private theorem selectedPacket_aestronglyMeasurable (k : ℕ) :
    AEStronglyMeasurable (selectedPacket k) volume :=
  (selectedPacket_integrable k).aestronglyMeasurable

private theorem selectedPacket_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖selectedPacket k x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    selectedFerrersPreAnchorPair_combination_bound k
  refine ⟨‖selectedFerrersLemma73SourceScale k‖ * C,
    mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro x
  simp only [selectedPacket, selectedFerrersLemma73SourcePacket, norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)

private theorem selectedPacket_zero_outside (k : ℕ) (x : ℝ)
    (hx : x ∉ Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda) :
    selectedPacket k x = 0 := by
  have h0 : (selectedFerrersPreAnchorPair k).h0 x = 0 := by
    by_contra hne
    exact hx ((selectedFerrersPreAnchorPair k).h0_support hne)
  have h4 : (selectedFerrersPreAnchorPair k).h4 x = 0 := by
    by_contra hne
    exact hx ((selectedFerrersPreAnchorPair k).h4_support hne)
  simp [selectedPacket, selectedFerrersLemma73SourcePacket,
    prolateCombination, h0, h4]

private theorem selectedPacket_lambda (k : ℕ) :
    (selectedFerrersPreAnchorPair k).pw.lambda =
      lambda_m (selectedFerrersPreAnchorIndex k) := by
  rw [(selectedFerrersPreAnchorPair_spec k).1]
  rfl

private theorem selectedIndex_m (k : ℕ) :
    (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl

private theorem selectedLambda_pos (k : ℕ) :
    0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
  rw [lambda_m, selectedIndex_m]
  positivity

private theorem selectedLambda_one_lt (k : ℕ) :
    1 < lambda_m (selectedFerrersPreAnchorIndex k) := by
  rw [lambda_m, selectedIndex_m]
  have h : (1 : ℝ) < (k + 2 : ℕ) := by exact_mod_cast (by omega : 1 < k + 2)
  simpa using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) h :
      Real.sqrt 1 < Real.sqrt (k + 2 : ℕ))

private lemma isFiniteMeasure_selectedWindow (k : ℕ) :
    IsFiniteMeasure
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  let i := selectedFerrersPreAnchorIndex k
  have hlam : 0 < lambda_m i := selectedLambda_pos k
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, dStar, I_m,
    withDensity_apply _ measurableSet_Icc]
  have hinv : IntegrableOn (fun u : ℝ => u⁻¹)
      (I_m i) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    exact ne_of_gt ((inv_pos.mpr hlam).trans_le hu.1)
  simpa [I_m] using hinv.setLIntegral_lt_top

private theorem selectedWindow_mem_pos (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) : 0 < u := by
  exact (inv_pos.mpr (selectedLambda_pos k)).trans_le hu.1

/-! ## Absolute convergence for `r < 1` -/

private theorem selectedPacket_fourier_bound (k : ℕ) (t : ℝ) :
    ‖𝓕 (selectedPacket k) t‖ ≤
      ∫ x : ℝ, ‖selectedPacket k x‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) (selectedPacket k) t

private theorem selectedReflectedAbel_summable (k : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    Summable (fun n : ℕ+ =>
      (r : ℂ) ^ (n : ℕ) *
        𝓕 (selectedPacket k) (((n : ℕ) : ℝ) / u)) := by
  let A : ℝ := ∫ x : ℝ, ‖selectedPacket k x‖
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  have hgeom : Summable (fun n : ℕ+ => r ^ (n : ℕ)) := by
    have hnat : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr0 hr1
    exact hnat.comp_injective Subtype.val_injective
  apply Summable.of_norm_bounded (hgeom.mul_left A)
  intro n
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0]
  calc
    r ^ (n : ℕ) * ‖𝓕 (selectedPacket k) (((n : ℕ) : ℝ) / u)‖ ≤
        r ^ (n : ℕ) * A :=
      mul_le_mul_of_nonneg_left (selectedPacket_fourier_bound k _)
        (pow_nonneg hr0 _)
    _ = A * r ^ (n : ℕ) := mul_comm _ _

/-! ## Finite periodization -/

/-- One fixed integer window suffices for every `u ∈ I_m` and every point of
one open period. -/
private def selectedPeriodizationIndices (k : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat (k + 2))) (Int.ofNat (k + 2))

private noncomputable def selectedPeriodization
    (k : ℕ) (u x : ℝ) : ℂ :=
  ∑ z ∈ selectedPeriodizationIndices k,
    selectedPacket k (u * ((z : ℝ) + x))

private theorem selectedLambda_sq (k : ℕ) :
    lambda_m (selectedFerrersPreAnchorIndex k) *
        lambda_m (selectedFerrersPreAnchorIndex k) = (k + 2 : ℕ) := by
  rw [lambda_m, selectedIndex_m, Real.mul_self_sqrt]
  positivity

private theorem selectedLambda_le_mul_index (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    lambda_m (selectedFerrersPreAnchorIndex k) ≤ u * (k + 2 : ℕ) := by
  let lam := lambda_m (selectedFerrersPreAnchorIndex k)
  have hlam : 0 < lam := selectedLambda_pos k
  have hsq : lam * lam = (k + 2 : ℕ) := selectedLambda_sq k
  change lam⁻¹ ≤ u ∧ u ≤ lam at hu
  have hmul := mul_le_mul_of_nonneg_left hu.1
    (by positivity : (0 : ℝ) ≤ (k + 2 : ℕ))
  have hrewrite : ((k + 2 : ℕ) : ℝ) * lam⁻¹ = lam := by
    rw [← hsq]
    field_simp
  rw [hrewrite, mul_comm ((k + 2 : ℕ) : ℝ) u] at hmul
  simpa only [lam] using hmul

/-- Outside the fixed index window every translate is zero on the open
fundamental period.  The endpoints are deliberately excluded here: their
duplication is the seam issue handled only almost everywhere below. -/
private theorem selectedPeriodization_term_zero_of_not_mem
    (k : ℕ) {u x : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) {z : ℤ}
    (hz : z ∉ selectedPeriodizationIndices k) :
    selectedPacket k (u * ((z : ℝ) + x)) = 0 := by
  apply selectedPacket_zero_outside
  rw [selectedPacket_lambda k]
  intro hcarrier
  have hu0 : 0 < u := selectedWindow_mem_pos k hu
  have hlamMul := selectedLambda_le_mul_index k hu
  rw [selectedPeriodizationIndices, Finset.mem_Icc] at hz
  rcases not_and_or.mp hz with hzleft | hzright
  · have hzlt : z < -(Int.ofNat (k + 2)) := lt_of_not_ge hzleft
    have hzle : z ≤ -(Int.ofNat (k + 2)) - 1 := by omega
    have hzleR : (z : ℝ) ≤ -(((k + 2 : ℕ) : ℝ)) - 1 := by
      exact_mod_cast hzle
    have hsum : (z : ℝ) + x < -(((k + 2 : ℕ) : ℝ)) := by
      linarith [hx.2]
    have hmul : u * ((z : ℝ) + x) <
        -u * (((k + 2 : ℕ) : ℝ)) := by
      nlinarith [mul_lt_mul_of_pos_left hsum hu0]
    have hlower : u * ((z : ℝ) + x) <
        -lambda_m (selectedFerrersPreAnchorIndex k) := by
      nlinarith
    exact (not_lt_of_ge hcarrier.1) hlower
  · have hzgt : Int.ofNat (k + 2) < z := lt_of_not_ge hzright
    have hzgtR : (((k + 2 : ℕ) : ℝ)) < (z : ℝ) := by
      exact_mod_cast hzgt
    have hsum : (((k + 2 : ℕ) : ℝ)) < (z : ℝ) + x := by
      linarith [hx.1]
    have hmul : u * (((k + 2 : ℕ) : ℝ)) <
        u * ((z : ℝ) + x) := mul_lt_mul_of_pos_left hsum hu0
    have hupper : lambda_m (selectedFerrersPreAnchorIndex k) <
        u * ((z : ℝ) + x) := lt_of_le_of_lt hlamMul hmul
    exact (not_lt_of_ge hcarrier.2) hupper

private theorem selectedPeriodization_eq_tsum (k : ℕ) {u x : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    selectedPeriodization k u x =
      ∑' z : ℤ, selectedPacket k (u * ((z : ℝ) + x)) := by
  rw [selectedPeriodization, tsum_eq_sum]
  intro z hz
  exact selectedPeriodization_term_zero_of_not_mem k hu hx hz

/-! ## Fourier coefficients of the finite periodization -/

private def selectedFourierPhase (n : ℤ) (x : ℝ) : ℂ :=
  (Real.fourierChar (-(x * (n : ℝ))) : ℂ)

private theorem selectedFourierPhase_add_int
    (n z : ℤ) (x : ℝ) :
    selectedFourierPhase n (x + z) = selectedFourierPhase n x := by
  rw [selectedFourierPhase, selectedFourierPhase]
  rw [show -((x + (z : ℝ)) * (n : ℝ)) =
      -(x * (n : ℝ)) + -((z : ℝ) * (n : ℝ)) by ring,
    Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
  have hz :
      ((Real.fourierChar (-((z : ℝ) * (n : ℝ))) : Circle) : ℂ) = 1 := by
    simp only [Real.fourierChar_apply]
    rw [show (((2 * Real.pi * -((z : ℝ) * (n : ℝ))) : ℝ) : ℂ) * I =
        ((-(z * n) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  rw [hz, mul_one]

private theorem selectedFourierPhase_aestronglyMeasurable (n : ℤ) :
    AEStronglyMeasurable (selectedFourierPhase n) volume := by
  apply Continuous.aestronglyMeasurable
  unfold selectedFourierPhase
  fun_prop

private theorem selectedFourierPhase_norm (n : ℤ) (x : ℝ) :
    ‖selectedFourierPhase n x‖ = 1 := by
  exact Circle.norm_coe _

private theorem selectedPhasePacket_integrable
    (k : ℕ) (n : ℤ) {u : ℝ} (hu : 0 < u) :
    Integrable (fun x : ℝ =>
      selectedFourierPhase n x * selectedPacket k (u * x)) volume := by
  apply ((selectedPacket_integrable k).comp_mul_left' hu.ne').bdd_mul
    (selectedFourierPhase_aestronglyMeasurable n)
  filter_upwards [] with x
  rw [selectedFourierPhase_norm]

private theorem selectedPacket_fourier_scale_pos
    (k : ℕ) {u : ℝ} (hu : 0 < u) (y : ℝ) :
    𝓕 (fun x => selectedPacket k (u * x)) y =
      (u⁻¹ : ℝ) • 𝓕 (selectedPacket k) (y / u) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let q : ℝ → ℂ := fun z =>
    Complex.exp (((-2 * Real.pi * (z / u) * y : ℝ) : ℂ) * I) •
      selectedPacket k z
  have hscale := Measure.integral_comp_mul_left q u
  rw [abs_of_pos (inv_pos.mpr hu)] at hscale
  calc
    _ = ∫ x : ℝ, q (u * x) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold q
      congr 2
      congr 2
      field_simp [hu.ne']
    _ = (u⁻¹ : ℝ) • ∫ z : ℝ, q z := hscale
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      unfold q
      congr 2
      congr 2
      field_simp [hu.ne']

private theorem selectedPeriodization_fourierCoeff
    (k : ℕ) (n : ℤ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    (∫ x : ℝ in (0 : ℝ)..1,
        selectedFourierPhase n x * selectedPeriodization k u x) =
      (u⁻¹ : ℝ) • 𝓕 (selectedPacket k) ((n : ℝ) / u) := by
  have hu0 : 0 < u := selectedWindow_mem_pos k hu
  let g : ℝ → ℂ := fun x =>
    selectedFourierPhase n x * selectedPacket k (u * x)
  have hg : Integrable g volume := selectedPhasePacket_integrable k n hu0
  calc
    (∫ x : ℝ in (0 : ℝ)..1,
        selectedFourierPhase n x * selectedPeriodization k u x) =
        ∫ x : ℝ in (0 : ℝ)..1,
          ∑ z ∈ selectedPeriodizationIndices k,
            selectedFourierPhase n x *
              selectedPacket k (u * ((z : ℝ) + x)) := by
      simp only [selectedPeriodization, Finset.mul_sum]
    _ = ∑ z ∈ selectedPeriodizationIndices k,
          ∫ x : ℝ in (0 : ℝ)..1,
            selectedFourierPhase n x *
              selectedPacket k (u * ((z : ℝ) + x)) := by
      apply intervalIntegral.integral_finset_sum
      intro z hz
      have hpacket : Integrable (fun x : ℝ =>
          selectedPacket k (u * ((z : ℝ) + x))) volume := by
        simpa only [add_comm] using
          (((selectedPacket_integrable k).comp_mul_left' hu0.ne').comp_add_left
            (z : ℝ))
      exact (hpacket.bdd_mul (selectedFourierPhase_aestronglyMeasurable n)
        (by filter_upwards [] with x; rw [selectedFourierPhase_norm])).intervalIntegrable
    _ = ∑ z ∈ selectedPeriodizationIndices k,
          ∫ x : ℝ in (0 : ℝ)..1, g (x + z) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply intervalIntegral.integral_congr
      intro x hx
      change selectedFourierPhase n x *
          selectedPacket k (u * ((z : ℝ) + x)) =
        selectedFourierPhase n (x + z) *
          selectedPacket k (u * (x + z))
      rw [selectedFourierPhase_add_int]
      congr 2
      ring
    _ = ∑' z : ℤ, ∫ x : ℝ in (0 : ℝ)..1, g (x + z) := by
      rw [tsum_eq_sum]
      intro z hz
      apply intervalIntegral.integral_zero_ae
      have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := Measure.ae_ne volume 1
      filter_upwards [hne] with x hx
      intro hxIoc
      unfold g
      rw [selectedFourierPhase_add_int]
      have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hxIoc
        exact ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx⟩
      rw [show u * (x + (z : ℝ)) = u * ((z : ℝ) + x) by ring,
        selectedPeriodization_term_zero_of_not_mem k hu hxIoo hz, mul_zero]
    _ = ∫ x : ℝ, g x := hg.hasSum_intervalIntegral_comp_add_int.tsum_eq
    _ = 𝓕 (fun x => selectedPacket k (u * x)) (n : ℝ) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with x
      unfold g selectedFourierPhase
      rw [Circle.smul_def]
      congr 2
      congr 1
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring
    _ = (u⁻¹ : ℝ) • 𝓕 (selectedPacket k) ((n : ℝ) / u) :=
      selectedPacket_fourier_scale_pos k hu0 (n : ℝ)

/-! ## The local Poisson kernel -/

private def selectedPoissonKernel (r x : ℝ) : ℝ :=
  (1 - r ^ 2) /
    (1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2)

private theorem selectedFourierPhase_ofNat (n : ℕ) (x : ℝ) :
    selectedFourierPhase (n : ℤ) x =
      ((Real.fourierChar (-x) : Circle) : ℂ) ^ n := by
  simp only [selectedFourierPhase, Real.fourierChar_apply]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem selectedFourierPhase_neg_ofNat (n : ℕ) (x : ℝ) :
    selectedFourierPhase (-(n : ℤ)) x =
      ((Real.fourierChar x : Circle) : ℂ) ^ n := by
  simp only [selectedFourierPhase, Real.fourierChar_apply]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem selectedPoissonKernel_series_eq {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    (((selectedPoissonKernel r x : ℝ) : ℂ)) =
      1 + ∑' n : ℕ+,
        (r : ℂ) ^ (n : ℕ) *
          (selectedFourierPhase (n : ℤ) x +
            selectedFourierPhase (-(n : ℤ)) x) := by
  let zp : ℂ := ((Real.fourierChar x : Circle) : ℂ)
  let zm : ℂ := ((Real.fourierChar (-x) : Circle) : ℂ)
  have hzp : ‖(r : ℂ) * zp‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Circle.norm_coe, mul_one]
    exact hr1
  have hzm : ‖(r : ℂ) * zm‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Circle.norm_coe, mul_one]
    exact hr1
  have hsumzp : Summable (fun n : ℕ+ => ((r : ℂ) * zp) ^ (n : ℕ)) :=
    (summable_geometric_of_norm_lt_one hzp).comp_injective Subtype.val_injective
  have hsumzm : Summable (fun n : ℕ+ => ((r : ℂ) * zm) ^ (n : ℕ)) :=
    (summable_geometric_of_norm_lt_one hzm).comp_injective Subtype.val_injective
  rw [show (∑' n : ℕ+,
      (r : ℂ) ^ (n : ℕ) *
        (selectedFourierPhase (n : ℤ) x +
          selectedFourierPhase (-(n : ℤ)) x)) =
      (∑' n : ℕ+, ((r : ℂ) * zm) ^ (n : ℕ)) +
      (∑' n : ℕ+, ((r : ℂ) * zp) ^ (n : ℕ)) by
    rw [← hsumzm.tsum_add hsumzp]
    congr 1
    funext n
    rw [selectedFourierPhase_ofNat, selectedFourierPhase_neg_ofNat]
    dsimp [zp, zm]
    rw [mul_add, mul_pow, mul_pow]]
  rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm
      (fun n : ℕ+ => ((r : ℂ) * zm) ^ (n : ℕ)),
    ← Equiv.tsum_eq Equiv.pnatEquivNat.symm
      (fun n : ℕ+ => ((r : ℂ) * zp) ^ (n : ℕ))]
  simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe]
  rw [geom_series_succ _ hzm, geom_series_succ _ hzp,
    tsum_geometric_of_norm_lt_one hzm, tsum_geometric_of_norm_lt_one hzp]
  have hzpform : ((Real.fourierChar x : Circle) : ℂ) =
      (Real.cos (2 * Real.pi * x) : ℂ) +
        (Real.sin (2 * Real.pi * x) : ℂ) * I := by
    rw [Real.fourierChar_apply, Complex.exp_mul_I]
    norm_num
  have hzmform : ((Real.fourierChar (-x) : Circle) : ℂ) =
      (Real.cos (2 * Real.pi * x) : ℂ) -
        (Real.sin (2 * Real.pi * x) : ℂ) * I := by
    rw [Real.fourierChar_apply]
    rw [show (((2 * Real.pi * -x : ℝ) : ℂ) * I) =
        (((-(2 * Real.pi * x) : ℝ) : ℂ) * I) by push_cast; ring,
      Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hsum : zp + zm = 2 * (Real.cos (2 * Real.pi * x) : ℂ) := by
    dsimp [zp, zm]
    rw [hzpform, hzmform]
    ring
  have hmul : zp * zm = 1 := by
    dsimp [zp, zm]
    rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul]
    simp
  have hnep : 1 - (r : ℂ) * zp ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hn := congrArg norm h
    rw [norm_one] at hn
    linarith [hzp]
  have hnem : 1 - (r : ℂ) * zm ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hn := congrArg norm h
    rw [norm_one] at hn
    linarith [hzm]
  have hkernelC : ((selectedPoissonKernel r x : ℝ) : ℂ) =
      (1 - (r : ℂ) ^ 2) /
        (1 - 2 * (r : ℂ) * (Real.cos (2 * Real.pi * x) : ℂ) +
          (r : ℂ) ^ 2) := by
    rw [selectedPoissonKernel]
    norm_cast
  have hdenfac :
      1 - 2 * (r : ℂ) * (Real.cos (2 * Real.pi * x) : ℂ) +
          (r : ℂ) ^ 2 =
        (1 - (r : ℂ) * zp) * (1 - (r : ℂ) * zm) := by
    rw [show (1 - (r : ℂ) * zp) * (1 - (r : ℂ) * zm) =
        1 - (r : ℂ) * (zp + zm) + (r : ℂ) ^ 2 * (zp * zm) by ring,
      hsum, hmul]
    ring
  rw [hkernelC, hdenfac]
  field_simp [hnep, hnem]
  ring_nf
  rw [mul_assoc, hmul, mul_one]

private theorem selectedFourierPhase_continuous (n : ℤ) :
    Continuous (selectedFourierPhase n) := by
  unfold selectedFourierPhase
  fun_prop

private theorem selectedFourierPhase_intervalIntegral (n : ℤ) (hn : n ≠ 0) :
    (∫ x : ℝ in (0 : ℝ)..1, selectedFourierPhase n x) = 0 := by
  let c : ℂ := ((-n : ℤ) : ℂ) * (2 * Real.pi * I)
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact_mod_cast (neg_ne_zero.mpr hn)
    · exact mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        I_ne_zero
  rw [show (∫ x : ℝ in (0 : ℝ)..1, selectedFourierPhase n x) =
      ∫ x : ℝ in (0 : ℝ)..1, Complex.exp (c * x) by
    apply intervalIntegral.integral_congr
    intro x hx
    unfold selectedFourierPhase
    simp only [Real.fourierChar_apply]
    congr 1
    dsimp [c]
    push_cast
    ring,
    integral_exp_mul_complex hc]
  dsimp [c]
  rw [mul_one, mul_zero, Complex.exp_zero,
    Complex.exp_int_mul_two_pi_mul_I]
  simp

private theorem selectedPoissonKernel_denominator_pos {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 < 1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2 := by
  rw [show 1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2 =
      (1 - r) ^ 2 + 2 * r * (1 - Real.cos (2 * Real.pi * x)) by ring]
  have hcos : 0 ≤ 1 - Real.cos (2 * Real.pi * x) := by
    linarith [Real.cos_le_one (2 * Real.pi * x)]
  have hsquare : 0 < (1 - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
  positivity

private theorem selectedPoissonKernel_nonneg {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 ≤ selectedPoissonKernel r x := by
  rw [selectedPoissonKernel]
  apply div_nonneg
  · nlinarith [sq_nonneg (1 - r)]
  · exact (selectedPoissonKernel_denominator_pos hr0 hr1 x).le

private theorem selectedPoissonKernel_continuous {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (selectedPoissonKernel r) := by
  unfold selectedPoissonKernel
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro x
    exact (selectedPoissonKernel_denominator_pos hr0 hr1 x).ne'

private theorem selectedPoissonKernel_tendstoUniformlyOn_zero_of_compact
    {s : Set ℝ} (hs : IsCompact s)
    (haway : ∀ x ∈ s, Real.cos (2 * Real.pi * x) ≠ 1) :
    TendstoUniformlyOn (fun r : ℝ => selectedPoissonKernel r) 0
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) s := by
  let d : ℝ → ℝ := fun x => 1 - Real.cos (2 * Real.pi * x)
  have hdcont : Continuous d := by
    dsimp [d]
    fun_prop
  have hdpos : ∀ x ∈ s, 0 < d x := by
    intro x hx
    have hnonneg : 0 ≤ d x := by
      dsimp [d]
      linarith [Real.cos_le_one (2 * Real.pi * x)]
    exact lt_of_le_of_ne hnonneg (by
      intro hzero
      apply haway x hx
      dsimp [d] at hzero
      linarith)
  obtain ⟨c, hc0, hc⟩ := hs.exists_forall_le' hdcont.continuousOn hdpos
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  have hnum : Tendsto (fun r : ℝ => 1 - r ^ 2)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
    have hfull : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝 1) (𝓝 0) := by
      have hcontinuous : ContinuousAt (fun r : ℝ => 1 - r ^ 2) 1 := by
        fun_prop
      change Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝 1)
        (𝓝 (1 - 1 ^ 2)) at hcontinuous
      norm_num at hcontinuous
      exact hcontinuous
    exact hfull.mono_left nhdsWithin_le_nhds
  have hnumSmall : ∀ᶠ r in 𝓝[Set.Ioo (0 : ℝ) 1] 1,
      1 - r ^ 2 < ε * c :=
    (tendsto_order.1 hnum).2 (ε * c) (mul_pos hε hc0)
  have hrHalf : ∀ᶠ r in 𝓝[Set.Ioo (0 : ℝ) 1] 1, (1 / 2 : ℝ) < r :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hnumSmall, hrHalf]
      with r hr hrnum hrhalf x hx
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r < 1 := hr.2
  have hd : c ≤ d x := hc x hx
  have hden : c ≤
      1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2 := by
    rw [show 1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2 =
        (1 - r) ^ 2 + 2 * r * d x by dsimp [d]; ring]
    nlinarith [sq_nonneg (1 - r)]
  have hnum0 : 0 ≤ 1 - r ^ 2 := by nlinarith
  simp only [Pi.zero_apply, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg (selectedPoissonKernel_nonneg hr0 hr1 x)]
  rw [selectedPoissonKernel]
  calc
    (1 - r ^ 2) /
        (1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2) ≤
        (1 - r ^ 2) / c :=
      div_le_div_of_nonneg_left hnum0 hc0 hden
    _ < ε := (div_lt_iff₀ hc0).2 (by simpa [mul_comm] using hrnum)

private theorem selectedPoissonKernel_unit_mass {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ x : ℝ in (0 : ℝ)..1, selectedPoissonKernel r x) = 1 := by
  let F : ℕ+ → ℝ → ℂ := fun n x =>
    (r : ℂ) ^ (n : ℕ) *
      (selectedFourierPhase (n : ℤ) x +
        selectedFourierPhase (-(n : ℤ)) x)
  let B : ℕ+ → ℝ → ℝ := fun n _ => 2 * r ^ (n : ℕ)
  have hgeom : Summable (fun n : ℕ+ => 2 * r ^ (n : ℕ)) := by
    exact ((summable_geometric_of_lt_one hr0 hr1).comp_injective
      Subtype.val_injective).mul_left 2
  have hFmeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro n
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    exact continuous_const.mul
      ((selectedFourierPhase_continuous (n : ℤ)).add
        (selectedFourierPhase_continuous (-(n : ℤ))))
  have hFbound (n : ℕ+) (x : ℝ) : ‖F n x‖ ≤ B n x := by
    dsimp [F, B]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    calc
      r ^ (n : ℕ) * ‖selectedFourierPhase (n : ℤ) x +
          selectedFourierPhase (-(n : ℤ)) x‖ ≤
          r ^ (n : ℕ) * (‖selectedFourierPhase (n : ℤ) x‖ +
            ‖selectedFourierPhase (-(n : ℤ)) x‖) := by
        gcongr
        exact norm_add_le _ _
      _ = 2 * r ^ (n : ℕ) := by
        rw [selectedFourierPhase_norm, selectedFourierPhase_norm]
        ring
  have hbound : ∀ n, ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖F n x‖ ≤ B n x := by
    intro n
    filter_upwards [] with x
    intro hx
    exact hFbound n x
  have hBsum : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Summable (fun n => B n x) := by
    filter_upwards [] with x
    intro hx
    exact hgeom
  have hBint : IntervalIntegrable (fun x => ∑' n, B n x) volume 0 1 := by
    have heq : (fun x : ℝ => ∑' n, B n x) =
        fun _ => ∑' n : ℕ+, 2 * r ^ (n : ℕ) := by
      funext x
      rfl
    rw [heq]
    exact intervalIntegrable_const
  have hFlim : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      HasSum (fun n => F n x)
        (((selectedPoissonKernel r x : ℝ) : ℂ) - 1) := by
    filter_upwards [] with x
    intro hx
    have hseries := selectedPoissonKernel_series_eq hr0 hr1 x
    have hs : Summable (fun n => F n x) :=
      Summable.of_norm_bounded hgeom (fun n => hFbound n x)
    rw [show (((selectedPoissonKernel r x : ℝ) : ℂ) - 1) =
        ∑' n, F n x by
      dsimp [F]
      rw [hseries]
      ring]
    exact hs.hasSum
  have hsumInt := intervalIntegral.hasSum_integral_of_dominated_convergence
    B hFmeas hbound hBsum hBint hFlim
  have htermzero : ∀ n : ℕ+,
      (∫ x : ℝ in (0 : ℝ)..1, F n x) = 0 := by
    intro n
    have hp : IntervalIntegrable (selectedFourierPhase (n : ℤ)) volume 0 1 :=
      (selectedFourierPhase_continuous (n : ℤ)).intervalIntegrable 0 1
    have hm : IntervalIntegrable (selectedFourierPhase (-(n : ℤ))) volume 0 1 :=
      (selectedFourierPhase_continuous (-(n : ℤ))).intervalIntegrable 0 1
    dsimp [F]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hp hm,
      selectedFourierPhase_intervalIntegral (n : ℤ)
        (by exact_mod_cast n.ne_zero),
      selectedFourierPhase_intervalIntegral (-(n : ℤ))
        (neg_ne_zero.mpr (by exact_mod_cast n.ne_zero))]
    simp
  have hzero : HasSum (fun n : ℕ+ => (0 : ℂ))
      (∫ x : ℝ in (0 : ℝ)..1,
        (((selectedPoissonKernel r x : ℝ) : ℂ) - 1)) := by
    simpa only [htermzero] using hsumInt
  have hmasszero : (∫ x : ℝ in (0 : ℝ)..1,
      (((selectedPoissonKernel r x : ℝ) : ℂ) - 1)) = 0 :=
    HasSum.unique hzero hasSum_zero
  have hkint : IntervalIntegrable
      (fun x : ℝ => ((selectedPoissonKernel r x : ℝ) : ℂ)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.comp
      (selectedPoissonKernel_continuous hr0 hr1)
  rw [intervalIntegral.integral_sub hkint intervalIntegrable_const,
    intervalIntegral.integral_const] at hmasszero
  norm_num at hmasszero
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  exact sub_eq_zero.mp hmasszero

private theorem selectedPoissonKernel_one_sub (r x : ℝ) :
    selectedPoissonKernel r (1 - x) = selectedPoissonKernel r x := by
  unfold selectedPoissonKernel
  rw [show 2 * Real.pi * (1 - x) = 2 * Real.pi - 2 * Real.pi * x by ring,
    Real.cos_two_pi_sub]

private theorem selectedPoissonKernel_half_mass {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ x : ℝ in Set.Icc 0 (1 / 2), selectedPoissonKernel r x) = 1 / 2 ∧
      (∫ x : ℝ in Set.Icc (1 / 2) 1, selectedPoissonKernel r x) = 1 / 2 := by
  have hleft : IntervalIntegrable (selectedPoissonKernel r) volume 0 (1 / 2) :=
    (selectedPoissonKernel_continuous hr0 hr1).intervalIntegrable 0 (1 / 2)
  have hright : IntervalIntegrable (selectedPoissonKernel r) volume (1 / 2) 1 :=
    (selectedPoissonKernel_continuous hr0 hr1).intervalIntegrable (1 / 2) 1
  have hsymm : (∫ x : ℝ in (0 : ℝ)..1 / 2, selectedPoissonKernel r x) =
      ∫ x : ℝ in (1 / 2 : ℝ)..1, selectedPoissonKernel r x := by
    calc
      (∫ x : ℝ in (0 : ℝ)..1 / 2, selectedPoissonKernel r x) =
          ∫ x : ℝ in (0 : ℝ)..1 / 2, selectedPoissonKernel r (1 - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact (selectedPoissonKernel_one_sub r x).symm
      _ = ∫ x : ℝ in (1 - 1 / 2 : ℝ)..1 - 0, selectedPoissonKernel r x := by
        rw [intervalIntegral.integral_comp_sub_left]
      _ = ∫ x : ℝ in (1 / 2 : ℝ)..1, selectedPoissonKernel r x := by
        norm_num
  have hsum : (∫ x : ℝ in (0 : ℝ)..1 / 2, selectedPoissonKernel r x) +
      (∫ x : ℝ in (1 / 2 : ℝ)..1, selectedPoissonKernel r x) = 1 := by
    rw [intervalIntegral.integral_add_adjacent_intervals hleft hright,
      selectedPoissonKernel_unit_mass hr0 hr1]
  have hleftValue :
      (∫ x : ℝ in (0 : ℝ)..1 / 2, selectedPoissonKernel r x) = 1 / 2 := by
    rw [hsymm] at hsum
    linarith
  have hrightValue :
      (∫ x : ℝ in (1 / 2 : ℝ)..1, selectedPoissonKernel r x) = 1 / 2 := by
    rw [← hsymm]
    exact hleftValue
  constructor
  · rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact hleftValue
  · rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact hrightValue

private theorem two_selectedPoissonKernel_tendstoUniformlyOn_zero_of_compact
    {s : Set ℝ} (hs : IsCompact s)
    (haway : ∀ x ∈ s, Real.cos (2 * Real.pi * x) ≠ 1) :
    TendstoUniformlyOn
      (fun r : ℝ => fun x => 2 * selectedPoissonKernel r x) 0
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) s := by
  have hbase := selectedPoissonKernel_tendstoUniformlyOn_zero_of_compact
    hs haway
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [
      (Metric.tendstoUniformlyOn_iff.1 hbase (ε / 2) (by positivity))]
      with r hr x hx
  have h := hr x hx
  simp only [Pi.zero_apply] at h ⊢
  rw [show dist (0 : ℝ) (2 * selectedPoissonKernel r x) =
      2 * dist (0 : ℝ) (selectedPoissonKernel r x) by
    simp [Real.dist_eq]]
  linarith

private theorem selectedCos_ne_one_on_left_away_zero
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) (hx0 : x ≠ 0) :
    Real.cos (2 * Real.pi * x) ≠ 1 := by
  intro hcos
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hangleNonneg : 0 ≤ 2 * Real.pi * x :=
    mul_nonneg htwoPi.le hx.1
  have hangleUpper : 2 * Real.pi * x < 2 * Real.pi := by
    have h := mul_le_mul_of_nonneg_left hx.2 htwoPi.le
    nlinarith [Real.pi_pos]
  have hangle : 2 * Real.pi * x = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt
      (lt_of_lt_of_le (neg_neg_of_pos htwoPi) hangleNonneg)
      hangleUpper).1 hcos
  apply hx0
  nlinarith [Real.pi_pos]

private theorem selectedCos_ne_one_on_right_away_one
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) (hx1 : x ≠ 1) :
    Real.cos (2 * Real.pi * x) ≠ 1 := by
  intro hcos
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hangleNonneg : 0 ≤ 2 * Real.pi * x :=
    mul_nonneg htwoPi.le (by linarith [hx.1])
  have hangleUpper : 2 * Real.pi * x < 2 * Real.pi := by
    simpa using mul_lt_mul_of_pos_left hxlt htwoPi
  have hangle : 2 * Real.pi * x = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt
      (lt_of_lt_of_le (neg_neg_of_pos htwoPi) hangleNonneg)
      hangleUpper).1 hcos
  nlinarith [Real.pi_pos, hx.1]

private theorem selectedPoissonKernel_left_peak
    {p : ℝ → ℂ} (hp : Integrable p volume) (hpc : ContinuousAt p 0) :
    Tendsto
      (fun r : ℝ => ∫ x : ℝ in (0 : ℝ)..1 / 2,
        (selectedPoissonKernel r x : ℂ) * p x)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 ((1 / 2 : ℂ) * p 0)) := by
  let s : Set ℝ := Set.Icc 0 (1 / 2)
  let g : ℝ → ℂ := fun x => (1 / 2 : ℝ) • p x
  let φ : ℝ → ℝ → ℝ := fun r x => 2 * selectedPoissonKernel r x
  have hpeak : Tendsto (fun r : ℝ => ∫ x in s, φ r x • g x)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 (g 0)) := by
    apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
        (s := s) (t := s) (x₀ := (0 : ℝ))
    · exact measurableSet_Icc
    · exact measurableSet_Icc
    · exact Subset.rfl
    · exact self_mem_nhdsWithin
    · exact isCompact_Icc.measure_ne_top
    · filter_upwards [self_mem_nhdsWithin] with r hr x hx
      exact mul_nonneg (by norm_num)
        (selectedPoissonKernel_nonneg hr.1.le hr.2 x)
    · intro v hvopen h0v
      apply two_selectedPoissonKernel_tendstoUniformlyOn_zero_of_compact
      · exact isCompact_Icc.diff hvopen
      · intro x hx
        exact selectedCos_ne_one_on_left_away_zero hx.1
          (fun hx0 => hx.2 (hx0 ▸ h0v))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      dsimp [φ, s]
      rw [integral_const_mul]
      norm_num [selectedPoissonKernel_half_mass hr.1.le hr.2]
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact ((continuous_const.mul
        (selectedPoissonKernel_continuous hr.1.le hr.2)).aestronglyMeasurable).restrict
    · exact (hp.smul (1 / 2 : ℝ)).integrableOn
    · exact (hpc.const_smul (1 / 2 : ℝ)).tendsto.mono_left
        nhdsWithin_le_nhds
  convert hpeak using 1
  · funext r
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp [φ, g, s]
    push_cast
    ring
  · dsimp [g]
    push_cast
    ring

private theorem selectedPoissonKernel_right_peak
    {p : ℝ → ℂ} (hp : Integrable p volume) (hpc : ContinuousAt p 1) :
    Tendsto
      (fun r : ℝ => ∫ x : ℝ in (1 / 2 : ℝ)..1,
        (selectedPoissonKernel r x : ℂ) * p x)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 ((1 / 2 : ℂ) * p 1)) := by
  let s : Set ℝ := Set.Icc (1 / 2) 1
  let g : ℝ → ℂ := fun x => (1 / 2 : ℝ) • p x
  let φ : ℝ → ℝ → ℝ := fun r x => 2 * selectedPoissonKernel r x
  have hpeak : Tendsto (fun r : ℝ => ∫ x in s, φ r x • g x)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 (g 1)) := by
    apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
        (s := s) (t := s) (x₀ := (1 : ℝ))
    · exact measurableSet_Icc
    · exact measurableSet_Icc
    · exact Subset.rfl
    · exact self_mem_nhdsWithin
    · exact isCompact_Icc.measure_ne_top
    · filter_upwards [self_mem_nhdsWithin] with r hr x hx
      exact mul_nonneg (by norm_num)
        (selectedPoissonKernel_nonneg hr.1.le hr.2 x)
    · intro v hvopen h1v
      apply two_selectedPoissonKernel_tendstoUniformlyOn_zero_of_compact
      · exact isCompact_Icc.diff hvopen
      · intro x hx
        exact selectedCos_ne_one_on_right_away_one hx.1
          (fun hx1 => hx.2 (hx1 ▸ h1v))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      dsimp [φ, s]
      rw [integral_const_mul]
      norm_num [selectedPoissonKernel_half_mass hr.1.le hr.2]
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact ((continuous_const.mul
        (selectedPoissonKernel_continuous hr.1.le hr.2)).aestronglyMeasurable).restrict
    · exact (hp.smul (1 / 2 : ℝ)).integrableOn
    · exact (hpc.const_smul (1 / 2 : ℝ)).tendsto.mono_left
        nhdsWithin_le_nhds
  convert hpeak using 1
  · funext r
    rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp [φ, g, s]
    push_cast
    ring
  · dsimp [g]
    push_cast
    ring

private theorem selectedPoissonKernel_peak
    {p : ℝ → ℂ} (hp : Integrable p volume)
    (hpc0 : ContinuousAt p 0) (hpc1 : ContinuousAt p 1)
    (hp10 : p 1 = p 0) :
    Tendsto
      (fun r : ℝ => ∫ x : ℝ in (0 : ℝ)..1,
        (selectedPoissonKernel r x : ℂ) * p x)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 (p 0)) := by
  have hleft := selectedPoissonKernel_left_peak hp hpc0
  have hright := selectedPoissonKernel_right_peak hp hpc1
  have hsum := hleft.add hright
  have hlimit : (1 / 2 : ℂ) * p 0 + (1 / 2 : ℂ) * p 1 = p 0 := by
    rw [hp10]
    ring
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hkC : ContinuousOn
      (fun x : ℝ => (selectedPoissonKernel r x : ℂ))
      (Set.Icc (0 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp
      (selectedPoissonKernel_continuous hr.1.le hr.2)).continuousOn
  have hleftI : IntervalIntegrable
      (fun x : ℝ => (selectedPoissonKernel r x : ℂ) * p x)
      volume 0 (1 / 2) :=
    hp.intervalIntegrable.continuousOn_mul (hkC.mono (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
      exact ⟨hx.1, hx.2.trans (by norm_num)⟩))
  have hrightI : IntervalIntegrable
      (fun x : ℝ => (selectedPoissonKernel r x : ℂ) * p x)
      volume (1 / 2) 1 :=
    hp.intervalIntegrable.continuousOn_mul (hkC.mono (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
      exact ⟨(by linarith [hx.1]), hx.2⟩))
  exact intervalIntegral.integral_add_adjacent_intervals hleftI hrightI

/-! ## Exact Abel/Poisson identity -/

private theorem selectedPacket_fourier_even (k : ℕ) :
    Function.Even (𝓕 (selectedPacket k)) := by
  intro t
  have h := Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ) (selectedPacket k) t
  have hcomp : selectedPacket k ∘ (LinearIsometryEquiv.neg ℝ) =
      selectedPacket k := by
    funext x
    exact selectedPacket_even k x
  rw [hcomp] at h
  change 𝓕 (selectedPacket k) (-t) = 𝓕 (selectedPacket k) t
  exact h.symm

private theorem selectedPeriodization_integrable
    (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (selectedPeriodization k u) volume := by
  have hsum := integrable_finset_sum (selectedPeriodizationIndices k)
    (fun z hz => by
      simpa only [add_comm] using
        (((selectedPacket_integrable k).comp_mul_left' hu.ne').comp_add_left
          (z : ℝ)))
  convert hsum using 1
  funext x
  apply Finset.sum_congr rfl
  intro z hz
  congr 2
  ring

private theorem selectedPeriodization_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u x : ℝ, ‖selectedPeriodization k u x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := selectedPacket_bound k
  refine ⟨((selectedPeriodizationIndices k).card : ℝ) * C,
    mul_nonneg (Nat.cast_nonneg _) hC0, ?_⟩
  intro u x
  rw [selectedPeriodization]
  calc
    ‖∑ z ∈ selectedPeriodizationIndices k,
        selectedPacket k (u * ((z : ℝ) + x))‖ ≤
        ∑ z ∈ selectedPeriodizationIndices k,
          ‖selectedPacket k (u * ((z : ℝ) + x))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ z ∈ selectedPeriodizationIndices k, C := by
      apply Finset.sum_le_sum
      intro z hz
      exact hC _
    _ = ((selectedPeriodizationIndices k).card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]

private noncomputable def selectedPoissonAverage
    (k : ℕ) (r u : ℝ) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..1,
    (selectedPoissonKernel r x : ℂ) * selectedPeriodization k u x

private theorem selectedPoissonAverage_series
    (k : ℕ) {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    selectedPoissonAverage k r u =
      (∫ x : ℝ in (0 : ℝ)..1, selectedPeriodization k u x) +
        ∑' n : ℕ+,
          (r : ℂ) ^ (n : ℕ) *
            ((∫ x : ℝ in (0 : ℝ)..1,
                selectedFourierPhase (n : ℤ) x *
                  selectedPeriodization k u x) +
              (∫ x : ℝ in (0 : ℝ)..1,
                selectedFourierPhase (-(n : ℤ)) x *
                  selectedPeriodization k u x)) := by
  let p : ℝ → ℂ := selectedPeriodization k u
  let F : ℕ+ → ℝ → ℂ := fun n x =>
    (r : ℂ) ^ (n : ℕ) *
      (selectedFourierPhase (n : ℤ) x +
        selectedFourierPhase (-(n : ℤ)) x) * p x
  let B : ℕ+ → ℝ → ℝ := fun n x =>
    2 * r ^ (n : ℕ) * ‖p x‖
  have hu0 : 0 < u := selectedWindow_mem_pos k hu
  have hpint : Integrable p volume := selectedPeriodization_integrable k hu0
  have hgeom : Summable (fun n : ℕ+ => 2 * r ^ (n : ℕ)) := by
    exact ((summable_geometric_of_lt_one hr0 hr1).comp_injective
      Subtype.val_injective).mul_left 2
  have hFmeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro n
    apply AEStronglyMeasurable.restrict
    exact (continuous_const.mul
      ((selectedFourierPhase_continuous (n : ℤ)).add
        (selectedFourierPhase_continuous (-(n : ℤ))))).aestronglyMeasurable.mul
      hpint.aestronglyMeasurable
  have hFbound (n : ℕ+) (x : ℝ) : ‖F n x‖ ≤ B n x := by
    dsimp [F, B]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    calc
      r ^ (n : ℕ) *
          ‖selectedFourierPhase (n : ℤ) x +
            selectedFourierPhase (-(n : ℤ)) x‖ * ‖p x‖ ≤
          r ^ (n : ℕ) * 2 * ‖p x‖ := by
        gcongr
        calc
          ‖selectedFourierPhase (n : ℤ) x +
              selectedFourierPhase (-(n : ℤ)) x‖ ≤
              ‖selectedFourierPhase (n : ℤ) x‖ +
                ‖selectedFourierPhase (-(n : ℤ)) x‖ := norm_add_le _ _
          _ = 2 := by
            rw [selectedFourierPhase_norm, selectedFourierPhase_norm]
            norm_num
      _ = 2 * r ^ (n : ℕ) * ‖p x‖ := by ring
  have hbound : ∀ n, ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖F n x‖ ≤ B n x := by
    intro n
    filter_upwards [] with x
    intro hx
    exact hFbound n x
  have hBsum : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Summable (fun n => B n x) := by
    filter_upwards [] with x
    intro hx
    exact hgeom.mul_right ‖p x‖
  have hBint : IntervalIntegrable (fun x => ∑' n, B n x) volume 0 1 := by
    have heq : (fun x : ℝ => ∑' n, B n x) =
        fun x => (∑' n : ℕ+, 2 * r ^ (n : ℕ)) * ‖p x‖ := by
      funext x
      dsimp [B]
      rw [tsum_mul_right]
    rw [heq]
    exact hpint.norm.const_mul _ |>.intervalIntegrable
  have hFlim : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      HasSum (fun n => F n x)
        ((((selectedPoissonKernel r x : ℝ) : ℂ) - 1) * p x) := by
    filter_upwards [] with x
    intro hx
    have hseries := selectedPoissonKernel_series_eq hr0 hr1 x
    have hs : Summable (fun n => F n x) :=
      Summable.of_norm_bounded (hgeom.mul_right ‖p x‖)
        (fun n => hFbound n x)
    have hbase : (∑' n : ℕ+,
        (r : ℂ) ^ (n : ℕ) *
          (selectedFourierPhase (n : ℤ) x +
            selectedFourierPhase (-(n : ℤ)) x)) =
        ((selectedPoissonKernel r x : ℝ) : ℂ) - 1 := by
      rw [hseries]
      ring
    change HasSum (fun n : ℕ+ =>
      ((r : ℂ) ^ (n : ℕ) *
        (selectedFourierPhase (n : ℤ) x +
          selectedFourierPhase (-(n : ℤ)) x)) * p x)
      ((((selectedPoissonKernel r x : ℝ) : ℂ) - 1) * p x)
    rw [← hbase]
    rw [← tsum_mul_right]
    exact hs.hasSum
  have hsumInt := intervalIntegral.hasSum_integral_of_dominated_convergence
    B hFmeas hbound hBsum hBint hFlim
  have hterm (n : ℕ+) :
      (∫ x : ℝ in (0 : ℝ)..1, F n x) =
        (r : ℂ) ^ (n : ℕ) *
          ((∫ x : ℝ in (0 : ℝ)..1,
              selectedFourierPhase (n : ℤ) x * p x) +
            (∫ x : ℝ in (0 : ℝ)..1,
              selectedFourierPhase (-(n : ℤ)) x * p x)) := by
    have hp : IntervalIntegrable p volume 0 1 := hpint.intervalIntegrable
    have hpos : IntervalIntegrable
        (fun x => selectedFourierPhase (n : ℤ) x * p x) volume 0 1 :=
      (hpint.bdd_mul (selectedFourierPhase_aestronglyMeasurable (n : ℤ))
        (by filter_upwards [] with x; rw [selectedFourierPhase_norm])).intervalIntegrable
    have hneg : IntervalIntegrable
        (fun x => selectedFourierPhase (-(n : ℤ)) x * p x) volume 0 1 :=
      (hpint.bdd_mul (selectedFourierPhase_aestronglyMeasurable (-(n : ℤ)))
        (by filter_upwards [] with x; rw [selectedFourierPhase_norm])).intervalIntegrable
    calc
      (∫ x : ℝ in (0 : ℝ)..1, F n x) =
          ∫ x : ℝ in (0 : ℝ)..1,
            (r : ℂ) ^ (n : ℕ) *
              (selectedFourierPhase (n : ℤ) x * p x +
                selectedFourierPhase (-(n : ℤ)) x * p x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [F]
        ring
      _ = (r : ℂ) ^ (n : ℕ) *
          ∫ x : ℝ in (0 : ℝ)..1,
            (selectedFourierPhase (n : ℤ) x * p x +
              selectedFourierPhase (-(n : ℤ)) x * p x) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add hpos hneg]
  have hseriesInt :
      (∫ x : ℝ in (0 : ℝ)..1,
        ((((selectedPoissonKernel r x : ℝ) : ℂ) - 1) * p x)) =
        ∑' n : ℕ+,
          (r : ℂ) ^ (n : ℕ) *
            ((∫ x : ℝ in (0 : ℝ)..1,
                selectedFourierPhase (n : ℤ) x * p x) +
              (∫ x : ℝ in (0 : ℝ)..1,
                selectedFourierPhase (-(n : ℤ)) x * p x)) := by
    rw [← hsumInt.tsum_eq]
    congr 1
    funext n
    exact hterm n
  have hkglobal : Integrable
      (fun x : ℝ => ((selectedPoissonKernel r x : ℝ) : ℂ) * p x)
      volume := by
    let C : ℝ := (1 - r ^ 2) / (1 - r) ^ 2
    have hC : ∀ x : ℝ,
        ‖((selectedPoissonKernel r x : ℝ) : ℂ)‖ ≤ C := by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (selectedPoissonKernel_nonneg hr0 hr1 x)]
      unfold selectedPoissonKernel C
      apply div_le_div_of_nonneg_left
      · nlinarith [sq_nonneg (1 - r)]
      · exact sq_pos_of_pos (sub_pos.mpr hr1)
      · rw [show 1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2 =
          (1 - r) ^ 2 + 2 * r *
            (1 - Real.cos (2 * Real.pi * x)) by ring]
        have hcos : 0 ≤ 1 - Real.cos (2 * Real.pi * x) := by
          linarith [Real.cos_le_one (2 * Real.pi * x)]
        nlinarith
    exact hpint.bdd_mul
      (Complex.continuous_ofReal.comp
        (selectedPoissonKernel_continuous hr0 hr1)).aestronglyMeasurable
      (by filter_upwards [] with x; exact hC x)
  have hkint : IntervalIntegrable
      (fun x : ℝ => ((selectedPoissonKernel r x : ℝ) : ℂ) * p x)
      volume 0 1 := hkglobal.intervalIntegrable
  have hpI : IntervalIntegrable p volume 0 1 := hpint.intervalIntegrable
  have hadd :
      (∫ x : ℝ in (0 : ℝ)..1,
        ((selectedPoissonKernel r x : ℝ) : ℂ) * p x) =
      (∫ x : ℝ in (0 : ℝ)..1, p x) +
        ∫ x : ℝ in (0 : ℝ)..1,
          ((((selectedPoissonKernel r x : ℝ) : ℂ) - 1) * p x) := by
    rw [show (fun x : ℝ => ((selectedPoissonKernel r x : ℝ) : ℂ) * p x) =
        fun x => p x +
          ((((selectedPoissonKernel r x : ℝ) : ℂ) - 1) * p x) by
      funext x
      ring,
      intervalIntegral.integral_add hpI
        (by simpa only [sub_mul, one_mul] using hkint.sub hpI)]
  rw [selectedPoissonAverage]
  simpa only [p, hseriesInt] using hadd

private theorem selectedPacket_fourier_zero (k : ℕ) :
    𝓕 (selectedPacket k) 0 = 0 := by
  rw [Real.fourier_eq]
  simpa using selectedPacket_zero_mass k

private theorem selectedPeriodization_integral_eq_zero
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    (∫ x : ℝ in (0 : ℝ)..1, selectedPeriodization k u x) = 0 := by
  have hcoeff := selectedPeriodization_fourierCoeff k 0 hu
  simpa [selectedFourierPhase, selectedPacket_fourier_zero k] using hcoeff

private theorem selectedPoissonAverage_eq_reflectedSeries
    (k : ℕ) {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    selectedPoissonAverage k r u =
      (2 * (u⁻¹ : ℝ) : ℂ) *
        ∑' n : ℕ+,
          (r : ℂ) ^ (n : ℕ) *
            𝓕 (selectedPacket k) (((n : ℕ) : ℝ) / u) := by
  rw [selectedPoissonAverage_series k hr0 hr1 hu,
    selectedPeriodization_integral_eq_zero k hu, zero_add]
  have hterm : ∀ n : ℕ+,
      (r : ℂ) ^ (n : ℕ) *
          ((∫ x : ℝ in (0 : ℝ)..1,
              selectedFourierPhase (n : ℤ) x *
                selectedPeriodization k u x) +
            (∫ x : ℝ in (0 : ℝ)..1,
              selectedFourierPhase (-(n : ℤ)) x *
                selectedPeriodization k u x)) =
        (2 * (u⁻¹ : ℝ) : ℂ) *
          ((r : ℂ) ^ (n : ℕ) *
            𝓕 (selectedPacket k) (((n : ℕ) : ℝ) / u)) := by
    intro n
    rw [selectedPeriodization_fourierCoeff k (n : ℤ) hu,
      selectedPeriodization_fourierCoeff k (-(n : ℤ)) hu]
    have harg : ((-(n : ℤ) : ℤ) : ℝ) / u =
        -(((n : ℕ) : ℝ) / u) := by
      push_cast
      ring
    rw [harg, selectedPacket_fourier_even k]
    simp only [Algebra.smul_def]
    push_cast
    ring_nf
    ac_rfl
  calc
    (∑' n : ℕ+,
        (r : ℂ) ^ (n : ℕ) *
          ((∫ x : ℝ in (0 : ℝ)..1,
              selectedFourierPhase (n : ℤ) x *
                selectedPeriodization k u x) +
            (∫ x : ℝ in (0 : ℝ)..1,
              selectedFourierPhase (-(n : ℤ)) x *
                selectedPeriodization k u x))) =
        ∑' n : ℕ+,
          (2 * (u⁻¹ : ℝ) : ℂ) *
            ((r : ℂ) ^ (n : ℕ) *
              𝓕 (selectedPacket k) (((n : ℕ) : ℝ) / u)) := by
      congr 1
      funext n
      exact hterm n
    _ = _ := tsum_mul_left

private theorem selectedReflectedAbel_eq_poissonAverage
    (k : ℕ) {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    selectedFerrersReflectedAbel k r u =
      ((Real.sqrt u : ℂ) / 2) * selectedPoissonAverage k r u := by
  rw [selectedPoissonAverage_eq_reflectedSeries k hr0 hr1 hu]
  have hu0 : 0 < u := selectedWindow_mem_pos k hu
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hsquare : Real.sqrt u * Real.sqrt u = u :=
    Real.mul_self_sqrt hu0.le
  have hscaleR : Real.sqrt u / 2 * (2 * u⁻¹) = (Real.sqrt u)⁻¹ := by
    field_simp [hsqrt.ne', hu0.ne']
    nlinarith
  rw [selectedFerrersReflectedAbel]
  simp only [selectedPacket]
  rw [← mul_assoc]
  congr 1
  exact_mod_cast hscaleR.symm

/-! ## The full-endpoint center value and its finite seam set -/

private theorem selectedPeriodization_term_zero_at_zero_of_not_mem
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) {z : ℤ}
    (hz : z ∉ selectedPeriodizationIndices k) :
    selectedPacket k (u * (z : ℝ)) = 0 := by
  apply selectedPacket_zero_outside
  rw [selectedPacket_lambda k]
  intro hcarrier
  have hu0 : 0 < u := selectedWindow_mem_pos k hu
  have hlamMul := selectedLambda_le_mul_index k hu
  rw [selectedPeriodizationIndices, Finset.mem_Icc] at hz
  rcases not_and_or.mp hz with hzleft | hzright
  · have hzlt : z < -(Int.ofNat (k + 2)) := lt_of_not_ge hzleft
    have hzle : z ≤ -(Int.ofNat (k + 2)) - 1 := by omega
    have hzleR : (z : ℝ) ≤ -(((k + 2 : ℕ) : ℝ)) - 1 := by
      exact_mod_cast hzle
    have hmul : u * (z : ℝ) < -u * (((k + 2 : ℕ) : ℝ)) := by
      nlinarith
    have hlower : u * (z : ℝ) <
        -lambda_m (selectedFerrersPreAnchorIndex k) := by
      nlinarith
    exact (not_lt_of_ge hcarrier.1) hlower
  · have hzgt : Int.ofNat (k + 2) < z := lt_of_not_ge hzright
    have hzgtR : (((k + 2 : ℕ) : ℝ)) < (z : ℝ) := by
      exact_mod_cast hzgt
    have hmul : u * (((k + 2 : ℕ) : ℝ)) < u * (z : ℝ) :=
      mul_lt_mul_of_pos_left hzgtR hu0
    have hupper : lambda_m (selectedFerrersPreAnchorIndex k) <
        u * (z : ℝ) := lt_of_le_of_lt hlamMul hmul
    exact (not_lt_of_ge hcarrier.2) hupper

private theorem selectedPeriodization_center_eq_tsum
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    selectedPeriodization k u 0 =
      ∑' z : ℤ, selectedPacket k (u * (z : ℝ)) := by
  rw [selectedPeriodization,
    tsum_eq_sum (s := selectedPeriodizationIndices k) (fun z hz => by
      simpa using
        selectedPeriodization_term_zero_at_zero_of_not_mem k hu hz)]
  simp

private theorem selectedPeriodization_center_eq_EStar
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k)) :
    ((Real.sqrt u : ℂ) / 2) * selectedPeriodization k u 0 =
      selectedFerrersAbelLimit k u := by
  let f : ℤ → ℂ := fun z => selectedPacket k (u * (z : ℝ))
  have hfinite : ∀ z ∉ selectedPeriodizationIndices k, f z = 0 := by
    intro z hz
    exact selectedPeriodization_term_zero_at_zero_of_not_mem k hu hz
  have hsum : Summable f := summable_of_ne_finset_zero hfinite
  have heven : ∀ z : ℤ, f (-z) = f z := by
    intro z
    dsimp [f]
    rw [Int.cast_neg, mul_neg, selectedPacket_even k]
  have hint := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum
  rw [selectedPeriodization_center_eq_tsum k hu, hint]
  have hu0 : 0 < u := selectedWindow_mem_pos k hu
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  rw [selectedFerrersAbelLimit, E_star]
  simp only [f, Int.cast_zero, mul_zero, selectedPacket,
    Int.cast_natCast, nsmul_eq_mul]
  ring

private theorem normalizedPhysicalMode_continuousOn_closed
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ContinuousOn S.normalizedPhysicalMode
      (Set.Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
  apply ((S.physicalComplex_continuousOn_closed hm).div_const
    (S.physicalL2Normalization : ℂ)).congr
  intro x hx
  simp [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension, hx]

private theorem selectedPacket_continuousOn_window (k : ℕ) :
    ContinuousOn (selectedPacket k)
      (Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda) := by
  let P := selectedFerrersPreAnchorPair k
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  have h0 : ContinuousOn P.h0 (Set.Icc (-P.pw.lambda) P.pw.lambda) := by
    rw [hh0, hlam]
    exact normalizedPhysicalMode_continuousOn_closed
      (selectedFerrersPreAnchorSolution0 k) (by omega)
  have h4 : ContinuousOn P.h4 (Set.Icc (-P.pw.lambda) P.pw.lambda) := by
    rw [hh4, hlam]
    exact normalizedPhysicalMode_continuousOn_closed
      (selectedFerrersPreAnchorSolution4 k) (by omega)
  have hcomb : ContinuousOn (prolateCombination P)
      (Set.Icc (-P.pw.lambda) P.pw.lambda) := by
    unfold prolateCombination
    exact ((continuousOn_const.mul h0).sub
      (continuousOn_const.mul h4)).div_const _
  simpa only [selectedPacket, selectedFerrersLemma73SourcePacket, P] using
    continuousOn_const.mul hcomb

private theorem selectedPacket_continuousAt_off_endpoints
    (k : ℕ) {y : ℝ}
    (hyneg : y ≠ -(selectedFerrersPreAnchorPair k).pw.lambda)
    (hypos : y ≠ (selectedFerrersPreAnchorPair k).pw.lambda) :
    ContinuousAt (selectedPacket k) y := by
  let lam := (selectedFerrersPreAnchorPair k).pw.lambda
  have hlam : 0 < lam := by
    rw [show lam = lambda_m (selectedFerrersPreAnchorIndex k) by
      exact selectedPacket_lambda k]
    exact selectedLambda_pos k
  by_cases hleft : y < -lam
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) y)
      |>.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hleft] with x hx
    apply selectedPacket_zero_outside
    intro hmem
    exact (not_lt_of_ge hmem.1) (by simpa only [lam] using hx)
  by_cases hright : lam < y
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) y)
      |>.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hright] with x hx
    apply selectedPacket_zero_outside
    intro hmem
    exact (not_lt_of_ge hmem.2) (by simpa only [lam] using hx)
  have hyin : y ∈ Set.Ioo (-lam) lam := by
    constructor
    · exact lt_of_le_of_ne (not_lt.mp hleft) (Ne.symm hyneg)
    · exact lt_of_le_of_ne (not_lt.mp hright) hypos
  exact (selectedPacket_continuousOn_window k y
    (Set.Ioo_subset_Icc_self hyin)).continuousAt
      (Icc_mem_nhds hyin.1 hyin.2)

private def selectedSeamIndices (k : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat (k + 3))) (Int.ofNat (k + 3))

private noncomputable def selectedSeamSet (k : ℕ) : Finset ℝ :=
  (selectedSeamIndices k).image (fun z : ℤ =>
      lambda_m (selectedFerrersPreAnchorIndex k) / (z : ℝ)) ∪
    (selectedSeamIndices k).image (fun z : ℤ =>
      -lambda_m (selectedFerrersPreAnchorIndex k) / (z : ℝ))

private theorem selectedSeam_off_endpoints
    (k : ℕ) {u : ℝ}
    (huseam : u ∉ (selectedSeamSet k : Set ℝ)) {z : ℤ}
    (hz : z ∈ selectedSeamIndices k) :
    u * (z : ℝ) ≠ -lambda_m (selectedFerrersPreAnchorIndex k) ∧
      u * (z : ℝ) ≠ lambda_m (selectedFerrersPreAnchorIndex k) := by
  classical
  let lam := lambda_m (selectedFerrersPreAnchorIndex k)
  have hlam : 0 < lam := selectedLambda_pos k
  constructor
  · intro heq
    have hz0 : (z : ℝ) ≠ 0 := by
      intro hz0
      rw [hz0, mul_zero] at heq
      linarith
    have hueq : u = -lam / (z : ℝ) := (eq_div_iff hz0).2 heq
    apply huseam
    rw [selectedSeamSet, Finset.coe_union, Set.mem_union]
    exact Or.inr (by
      rw [Finset.coe_image, Set.mem_image]
      exact ⟨z, hz, hueq.symm⟩)
  · intro heq
    have hz0 : (z : ℝ) ≠ 0 := by
      intro hz0
      rw [hz0, mul_zero] at heq
      linarith
    have hueq : u = lam / (z : ℝ) := (eq_div_iff hz0).2 heq
    apply huseam
    rw [selectedSeamSet, Finset.coe_union, Set.mem_union]
    exact Or.inl (by
      rw [Finset.coe_image, Set.mem_image]
      exact ⟨z, hz, hueq.symm⟩)

private theorem selectedPeriodization_continuousAt_zero_off_seams
    (k : ℕ) {u : ℝ}
    (huseam : u ∉ (selectedSeamSet k : Set ℝ)) :
    ContinuousAt (selectedPeriodization k u) 0 := by
  classical
  have hoff : ∀ z ∈ selectedPeriodizationIndices k,
      u * (z : ℝ) ≠ -lambda_m (selectedFerrersPreAnchorIndex k) ∧
        u * (z : ℝ) ≠ lambda_m (selectedFerrersPreAnchorIndex k) := by
    intro z hz
    apply selectedSeam_off_endpoints k huseam
    rw [selectedSeamIndices, Finset.mem_Icc]
    rw [selectedPeriodizationIndices, Finset.mem_Icc] at hz
    have hK : Int.ofNat (k + 2) ≤ Int.ofNat (k + 3) :=
      Int.ofNat_le.mpr (by omega)
    exact ⟨le_trans (neg_le_neg hK) hz.1, le_trans hz.2 hK⟩
  show Tendsto (selectedPeriodization k u) (𝓝 0)
    (𝓝 (selectedPeriodization k u 0))
  unfold selectedPeriodization
  apply tendsto_finset_sum
  intro z hz
  have hpacket := selectedPacket_continuousAt_off_endpoints k
    (by simpa only [selectedPacket_lambda k] using (hoff z hz).1)
    (by simpa only [selectedPacket_lambda k] using (hoff z hz).2)
  have harg : ContinuousAt (fun x : ℝ => u * ((z : ℝ) + x)) 0 := by
    fun_prop
  exact hpacket.comp_of_eq harg (by simp)

private theorem selectedPeriodization_continuousAt_one_off_seams
    (k : ℕ) {u : ℝ}
    (huseam : u ∉ (selectedSeamSet k : Set ℝ)) :
    ContinuousAt (selectedPeriodization k u) 1 := by
  classical
  have hoff : ∀ z ∈ selectedPeriodizationIndices k,
      u * ((z : ℝ) + 1) ≠
          -lambda_m (selectedFerrersPreAnchorIndex k) ∧
        u * ((z : ℝ) + 1) ≠
          lambda_m (selectedFerrersPreAnchorIndex k) := by
    intro z hz
    have hzw : z + 1 ∈ selectedSeamIndices k := by
      rw [selectedSeamIndices, Finset.mem_Icc]
      rw [selectedPeriodizationIndices, Finset.mem_Icc] at hz
      have hK : Int.ofNat (k + 2) ≤ Int.ofNat (k + 3) :=
        Int.ofNat_le.mpr (by omega)
      have hKplus : Int.ofNat (k + 2) + 1 ≤ Int.ofNat (k + 3) := by
        norm_cast
      exact ⟨le_trans (neg_le_neg hK) (le_trans hz.1 (Int.le_add_of_nonneg_right
        (by norm_num))), le_trans (by simpa [add_comm] using add_le_add_right hz.2 1) hKplus⟩
    simpa only [Int.cast_add, Int.cast_one] using
      selectedSeam_off_endpoints k huseam hzw
  show Tendsto (selectedPeriodization k u) (𝓝 1)
    (𝓝 (selectedPeriodization k u 1))
  unfold selectedPeriodization
  apply tendsto_finset_sum
  intro z hz
  have hpacket := selectedPacket_continuousAt_off_endpoints k
    (by simpa only [selectedPacket_lambda k] using (hoff z hz).1)
    (by simpa only [selectedPacket_lambda k] using (hoff z hz).2)
  have harg : ContinuousAt (fun x : ℝ => u * ((z : ℝ) + x)) 1 := by
    fun_prop
  exact hpacket.comp_of_eq harg (by simp)

private theorem selectedPeriodization_term_zero_at_one_of_not_mem
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (huseam : u ∉ (selectedSeamSet k : Set ℝ)) {z : ℤ}
    (hz : z ∉ selectedPeriodizationIndices k) :
    selectedPacket k (u * ((z : ℝ) + 1)) = 0 := by
  apply selectedPacket_zero_outside
  rw [selectedPacket_lambda k]
  intro hcarrier
  have hu0 : 0 < u := selectedWindow_mem_pos k hu
  have hlamMul := selectedLambda_le_mul_index k hu
  have hlamMulExpanded := hlamMul
  norm_num at hlamMulExpanded
  have hnegMul :
      -(u * ((k : ℝ) + 2)) ≤
        -lambda_m (selectedFerrersPreAnchorIndex k) := by
    exact neg_le_neg hlamMulExpanded
  rw [selectedPeriodizationIndices, Finset.mem_Icc] at hz
  rcases not_and_or.mp hz with hzleft | hzright
  · have hzlt : z < -(Int.ofNat (k + 2)) := lt_of_not_ge hzleft
    have hzwle : z + 1 ≤ -(Int.ofNat (k + 2)) := by omega
    have hzwleR : ((z + 1 : ℤ) : ℝ) ≤ -(((k + 2 : ℕ) : ℝ)) := by
      exact_mod_cast hzwle
    have hvalue : u * ((z : ℝ) + 1) ≤
        -lambda_m (selectedFerrersPreAnchorIndex k) := by
      have hmul : u * (((z + 1 : ℤ) : ℝ)) ≤
          -u * (((k + 2 : ℕ) : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hzwleR hu0.le]
      norm_num at hmul
      exact le_trans hmul hnegMul
    have heq : u * ((z : ℝ) + 1) =
        -lambda_m (selectedFerrersPreAnchorIndex k) :=
      le_antisymm hvalue hcarrier.1
    have hzwge : -(Int.ofNat (k + 2)) ≤ z + 1 := by
      by_contra hcontra
      have hstrict : z + 1 < -(Int.ofNat (k + 2)) := lt_of_not_ge hcontra
      have hstrictR : ((z + 1 : ℤ) : ℝ) < -(((k + 2 : ℕ) : ℝ)) := by
        exact_mod_cast hstrict
      have hmul : u * (((z + 1 : ℤ) : ℝ)) <
          -u * (((k + 2 : ℕ) : ℝ)) := by
        nlinarith [mul_lt_mul_of_pos_left hstrictR hu0]
      norm_num at hmul
      exact (not_lt_of_ge hcarrier.1) (lt_of_lt_of_le hmul hnegMul)
    have hzw : z + 1 ∈ selectedSeamIndices k := by
      rw [selectedSeamIndices, Finset.mem_Icc]
      have hK : Int.ofNat (k + 2) ≤ Int.ofNat (k + 3) :=
        Int.ofNat_le.mpr (by omega)
      have hK3nonneg : (0 : ℤ) ≤ Int.ofNat (k + 3) :=
        Int.natCast_nonneg _
      have hminusK_le_K3 :
          -(Int.ofNat (k + 2)) ≤ Int.ofNat (k + 3) :=
        le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) hK3nonneg
      exact ⟨le_trans (neg_le_neg hK) hzwge,
        le_trans hzwle hminusK_le_K3⟩
    exact (selectedSeam_off_endpoints k huseam hzw).1 (by
      simpa only [Int.cast_add, Int.cast_one] using heq)
  · have hzgt : Int.ofNat (k + 2) < z := lt_of_not_ge hzright
    have hzgtR : (((k + 2 : ℕ) : ℝ)) < (z : ℝ) := by
      exact_mod_cast hzgt
    have hmul : u * (((k + 2 : ℕ) : ℝ)) <
        u * ((z : ℝ) + 1) := by
      nlinarith [mul_lt_mul_of_pos_left hzgtR hu0]
    have hupper : lambda_m (selectedFerrersPreAnchorIndex k) <
        u * ((z : ℝ) + 1) := lt_of_le_of_lt hlamMul hmul
    exact (not_lt_of_ge hcarrier.2) hupper

private theorem selectedPeriodization_one_eq_zero_off_seams
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (huseam : u ∉ (selectedSeamSet k : Set ℝ)) :
    selectedPeriodization k u 1 = selectedPeriodization k u 0 := by
  let f : ℤ → ℂ := fun z => selectedPacket k (u * (z : ℝ))
  calc
    selectedPeriodization k u 1 = ∑' z : ℤ, f (z + 1) := by
      rw [selectedPeriodization,
        tsum_eq_sum (s := selectedPeriodizationIndices k) (fun z hz => by
          simpa only [f, Int.cast_add, Int.cast_one] using
            selectedPeriodization_term_zero_at_one_of_not_mem
              k hu huseam hz)]
      simp only [f, Int.cast_add, Int.cast_one]
    _ = ∑' z : ℤ, f z := Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) f
    _ = selectedPeriodization k u 0 := by
      rw [selectedPeriodization_center_eq_tsum k hu]

private theorem selectedPoissonAverage_tendsto_center_off_seams
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (huseam : u ∉ (selectedSeamSet k : Set ℝ)) :
    Tendsto (fun r : ℝ => selectedPoissonAverage k r u)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1)
      (𝓝 (selectedPeriodization k u 0)) := by
  apply selectedPoissonKernel_peak
  · exact selectedPeriodization_integrable k (selectedWindow_mem_pos k hu)
  · exact selectedPeriodization_continuousAt_zero_off_seams k huseam
  · exact selectedPeriodization_continuousAt_one_off_seams k huseam
  · exact selectedPeriodization_one_eq_zero_off_seams k hu huseam

private theorem selectedFerrersReflectedAbel_tendsto_pointwise_off_seams
    (k : ℕ) {u : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (huseam : u ∉ (selectedSeamSet k : Set ℝ)) :
    Tendsto (fun r : ℝ => selectedFerrersReflectedAbel k r u)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1)
      (𝓝 (selectedFerrersAbelLimit k u)) := by
  have haverage : Tendsto
      (fun r : ℝ => ((Real.sqrt u : ℂ) / 2) *
        selectedPoissonAverage k r u)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1)
      (𝓝 (((Real.sqrt u : ℂ) / 2) *
        selectedPeriodization k u 0)) :=
    tendsto_const_nhds.mul
      (selectedPoissonAverage_tendsto_center_off_seams k hu huseam)
  rw [selectedPeriodization_center_eq_EStar k hu] at haverage
  refine haverage.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (selectedReflectedAbel_eq_poissonAverage k hr.1.le hr.2 hu).symm

/-! ## Measurability and uniform domination on the selected window -/

private theorem selectedPacket_measurable (k : ℕ) :
    Measurable (selectedPacket k) := by
  let carrier := Set.Icc
    (-(selectedFerrersPreAnchorPair k).pw.lambda)
    (selectedFerrersPreAnchorPair k).pw.lambda
  have hpiece : Measurable
      (carrier.piecewise (selectedPacket k) (fun _ => 0)) :=
    (selectedPacket_continuousOn_window k).measurable_piecewise
      continuousOn_const measurableSet_Icc
  convert hpiece using 1
  funext x
  by_cases hx : x ∈ carrier
  · simp [carrier, hx]
  · simp [carrier, hx, selectedPacket_zero_outside k x hx]

private theorem selectedPeriodization_stronglyMeasurable_prod (k : ℕ) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      selectedPeriodization k p.1 p.2) := by
  apply Measurable.stronglyMeasurable
  unfold selectedPeriodization
  apply Finset.measurable_sum
  intro z hz
  exact (selectedPacket_measurable k).comp
    (measurable_fst.mul (measurable_const.add measurable_snd))

private theorem selectedPoissonKernel_measurable (r : ℝ) :
    Measurable (selectedPoissonKernel r) := by
  unfold selectedPoissonKernel
  fun_prop

private theorem selectedPoissonAverage_stronglyMeasurable
    (k : ℕ) (r : ℝ) :
    StronglyMeasurable (selectedPoissonAverage k r) := by
  have hintegrand : StronglyMeasurable (fun p : ℝ × ℝ =>
      (selectedPoissonKernel r p.2 : ℂ) *
        selectedPeriodization k p.1 p.2) := by
    apply Measurable.stronglyMeasurable
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp
        ((selectedPoissonKernel_measurable r).comp measurable_snd)
    · exact (selectedPeriodization_stronglyMeasurable_prod k).measurable
  have hint := hintegrand.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
  rw [show selectedPoissonAverage k r = fun u : ℝ =>
      ∫ x : ℝ in Set.Ioc (0 : ℝ) 1,
        (selectedPoissonKernel r x : ℂ) *
          selectedPeriodization k u x by
    funext u
    rw [selectedPoissonAverage,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]]
  exact hint

private theorem selectedPoissonAverage_bound
    (k : ℕ) {r u C : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (hC : ∀ v x : ℝ, ‖selectedPeriodization k v x‖ ≤ C) :
    ‖selectedPoissonAverage k r u‖ ≤ C := by
  let p : ℝ → ℂ := selectedPeriodization k u
  let D : ℝ := (1 - r ^ 2) / (1 - r) ^ 2
  have hp : Integrable p volume :=
    selectedPeriodization_integrable k (selectedWindow_mem_pos k hu)
  have hkernelBound : ∀ x : ℝ,
      ‖(selectedPoissonKernel r x : ℂ)‖ ≤ D := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (selectedPoissonKernel_nonneg hr0 hr1 x)]
    unfold selectedPoissonKernel D
    apply div_le_div_of_nonneg_left
    · nlinarith [sq_nonneg (1 - r)]
    · exact sq_pos_of_pos (sub_pos.mpr hr1)
    · rw [show 1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ 2 =
        (1 - r) ^ 2 + 2 * r *
          (1 - Real.cos (2 * Real.pi * x)) by ring]
      have hcos : 0 ≤ 1 - Real.cos (2 * Real.pi * x) := by
        linarith [Real.cos_le_one (2 * Real.pi * x)]
      nlinarith
  have hprod : Integrable
      (fun x : ℝ => (selectedPoissonKernel r x : ℂ) * p x) volume :=
    hp.bdd_mul
      (Complex.continuous_ofReal.comp
        (selectedPoissonKernel_continuous hr0 hr1)).aestronglyMeasurable
      (by filter_upwards [] with x; exact hkernelBound x)
  have hnorm : IntervalIntegrable
      (fun x : ℝ => ‖(selectedPoissonKernel r x : ℂ) * p x‖)
      volume 0 1 := hprod.norm.intervalIntegrable
  have hmajorant : IntervalIntegrable
      (fun x : ℝ => C * selectedPoissonKernel r x) volume 0 1 :=
    ((selectedPoissonKernel_continuous hr0 hr1).intervalIntegrable 0 1).const_mul C
  rw [selectedPoissonAverage]
  calc
    ‖∫ x : ℝ in (0 : ℝ)..1,
        (selectedPoissonKernel r x : ℂ) * p x‖ ≤
        ∫ x : ℝ in (0 : ℝ)..1,
          ‖(selectedPoissonKernel r x : ℂ) * p x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x : ℝ in (0 : ℝ)..1,
        C * selectedPoissonKernel r x := by
      apply intervalIntegral.integral_mono_on (by norm_num) hnorm hmajorant
      intro x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (selectedPoissonKernel_nonneg hr0 hr1 x)]
      calc
        selectedPoissonKernel r x * ‖p x‖ ≤
            selectedPoissonKernel r x * C :=
          mul_le_mul_of_nonneg_left (hC u x)
            (selectedPoissonKernel_nonneg hr0 hr1 x)
        _ = C * selectedPoissonKernel r x := mul_comm _ _
    _ = C := by
      rw [intervalIntegral.integral_const_mul,
        selectedPoissonKernel_unit_mass hr0 hr1, mul_one]

private theorem selectedPoissonScale_stronglyMeasurable :
    StronglyMeasurable (fun u : ℝ => (Real.sqrt u : ℂ) / 2) := by
  exact ((Complex.continuous_ofReal.comp Real.continuous_sqrt).div_const 2)
    |>.stronglyMeasurable

private theorem selectedFerrersReflectedAbel_aestronglyMeasurable
    (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    AEStronglyMeasurable (selectedFerrersReflectedAbel k r)
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  have hrepresentative : StronglyMeasurable (fun u : ℝ =>
      ((Real.sqrt u : ℂ) / 2) * selectedPoissonAverage k r u) :=
    selectedPoissonScale_stronglyMeasurable.mul
      (selectedPoissonAverage_stronglyMeasurable k r)
  apply hrepresentative.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc :
      MeasurableSet (I_m (selectedFerrersPreAnchorIndex k)))] with u hu
  exact (selectedReflectedAbel_eq_poissonAverage k hr0 hr1 hu).symm

private theorem selectedFerrersAbelLimit_aestronglyMeasurable (k : ℕ) :
    AEStronglyMeasurable (selectedFerrersAbelLimit k)
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  have hcenter : StronglyMeasurable
      (fun u : ℝ => selectedPeriodization k u 0) := by
    apply Measurable.stronglyMeasurable
    unfold selectedPeriodization
    apply Finset.measurable_sum
    intro z hz
    exact (selectedPacket_measurable k).comp
      (measurable_id.mul (measurable_const.add measurable_const))
  have hrepresentative : StronglyMeasurable (fun u : ℝ =>
      ((Real.sqrt u : ℂ) / 2) * selectedPeriodization k u 0) :=
    selectedPoissonScale_stronglyMeasurable.mul hcenter
  apply hrepresentative.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc :
      MeasurableSet (I_m (selectedFerrersPreAnchorIndex k)))] with u hu
  exact selectedPeriodization_center_eq_EStar k hu

private theorem selectedFerrersReflectedAbel_bound
    (k : ℕ) {r u C : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (hC : ∀ v x : ℝ, ‖selectedPeriodization k v x‖ ≤ C) :
    ‖selectedFerrersReflectedAbel k r u‖ ≤
      (Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) / 2) * C := by
  rw [selectedReflectedAbel_eq_poissonAverage k hr0 hr1 hu, norm_mul,
    norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr (selectedWindow_mem_pos k hu))]
  norm_num
  have hsqrt : Real.sqrt u ≤
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) :=
    Real.sqrt_le_sqrt hu.2
  have hscale : Real.sqrt u / 2 ≤
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) / 2 := by
    linarith
  exact mul_le_mul hscale
    (selectedPoissonAverage_bound k hr0 hr1 hu hC)
    (norm_nonneg _) (by positivity)

private theorem selectedFerrersAbelLimit_bound
    (k : ℕ) {u C : ℝ}
    (hu : u ∈ I_m (selectedFerrersPreAnchorIndex k))
    (hC : ∀ v x : ℝ, ‖selectedPeriodization k v x‖ ≤ C) :
    ‖selectedFerrersAbelLimit k u‖ ≤
      (Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) / 2) * C := by
  rw [← selectedPeriodization_center_eq_EStar k hu, norm_mul,
    norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr (selectedWindow_mem_pos k hu))]
  norm_num
  have hsqrt : Real.sqrt u ≤
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) :=
    Real.sqrt_le_sqrt hu.2
  have hscale : Real.sqrt u / 2 ≤
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) / 2 := by
    linarith
  exact mul_le_mul hscale (hC u 0) (norm_nonneg _) (by positivity)

theorem selectedFerrersReflectedAbel_memLp
    (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    MemLp (selectedFerrersReflectedAbel k r) 2
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  letI : IsFiniteMeasure
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) :=
    isFiniteMeasure_selectedWindow k
  obtain ⟨C, _hC0, hC⟩ := selectedPeriodization_bound k
  apply MemLp.of_bound
    (selectedFerrersReflectedAbel_aestronglyMeasurable k hr0 hr1)
    ((Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) / 2) * C)
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc :
      MeasurableSet (I_m (selectedFerrersPreAnchorIndex k)))] with u hu
  exact selectedFerrersReflectedAbel_bound k hr0 hr1 hu hC

theorem selectedFerrersAbelLimit_memLp (k : ℕ) :
    MemLp (selectedFerrersAbelLimit k) 2
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  letI : IsFiniteMeasure
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) :=
    isFiniteMeasure_selectedWindow k
  obtain ⟨C, _hC0, hC⟩ := selectedPeriodization_bound k
  apply MemLp.of_bound (selectedFerrersAbelLimit_aestronglyMeasurable k)
    ((Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) / 2) * C)
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc :
      MeasurableSet (I_m (selectedFerrersPreAnchorIndex k)))] with u hu
  exact selectedFerrersAbelLimit_bound k hu hC

private theorem selectedSeamSet_dStar_measure_zero (k : ℕ) :
    dStar (selectedSeamSet k : Set ℝ) = 0 := by
  rw [dStar, withDensity_apply _ (selectedSeamSet k).measurableSet]
  exact setLIntegral_measure_zero _ _
    ((selectedSeamSet k).measure_zero volume)

private theorem selectedOffSeam_ae (k : ℕ) :
    ∀ᵐ u : ℝ ∂(dStar.restrict
      (I_m (selectedFerrersPreAnchorIndex k))),
      u ∉ (selectedSeamSet k : Set ℝ) := by
  have hrestrict : (dStar.restrict
      (I_m (selectedFerrersPreAnchorIndex k)))
      (selectedSeamSet k : Set ℝ) = 0 := by
    rw [Measure.restrict_apply (selectedSeamSet k).measurableSet]
    exact measure_mono_null inter_subset_left
      (selectedSeamSet_dStar_measure_zero k)
  rw [ae_iff]
  simpa using hrestrict

theorem selectedFerrersReflectedAbel_tendsto_L2 (k : ℕ) :
    Tendsto
      (fun r : ℝ =>
        ∫ u : ℝ,
          ‖selectedFerrersReflectedAbel k r u -
            selectedFerrersAbelLimit k u‖ ^ 2
          ∂(dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))))
      (𝓝[Set.Ioo (0 : ℝ) 1] 1)
      (𝓝 0) := by
  let μ := dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))
  letI : IsFiniteMeasure μ := isFiniteMeasure_selectedWindow k
  obtain ⟨C, hC0, hC⟩ := selectedPeriodization_bound k
  let B : ℝ :=
    (Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) / 2) * C
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  let D : ℝ := (2 * B) ^ 2
  have hFmeas : ∀ᶠ r in 𝓝[Set.Ioo (0 : ℝ) 1] 1,
      AEStronglyMeasurable
        (fun u : ℝ =>
          ‖selectedFerrersReflectedAbel k r u -
            selectedFerrersAbelLimit k u‖ ^ 2) μ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ((selectedFerrersReflectedAbel_aestronglyMeasurable
      k hr.1.le hr.2).sub
        (selectedFerrersAbelLimit_aestronglyMeasurable k)).norm.pow 2
  have hbound : ∀ᶠ r in 𝓝[Set.Ioo (0 : ℝ) 1] 1,
      ∀ᵐ u : ℝ ∂μ,
        ‖‖selectedFerrersReflectedAbel k r u -
          selectedFerrersAbelLimit k u‖ ^ 2‖ ≤ D := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc :
        MeasurableSet (I_m (selectedFerrersPreAnchorIndex k)))] with u hu
    have hreflected : ‖selectedFerrersReflectedAbel k r u‖ ≤ B := by
      exact selectedFerrersReflectedAbel_bound k hr.1.le hr.2 hu hC
    have hlimit : ‖selectedFerrersAbelLimit k u‖ ≤ B := by
      exact selectedFerrersAbelLimit_bound k hu hC
    have hdiff : ‖selectedFerrersReflectedAbel k r u -
        selectedFerrersAbelLimit k u‖ ≤ 2 * B := by
      calc
        ‖selectedFerrersReflectedAbel k r u -
            selectedFerrersAbelLimit k u‖ ≤
            ‖selectedFerrersReflectedAbel k r u‖ +
              ‖selectedFerrersAbelLimit k u‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add hreflected hlimit
        _ = 2 * B := by ring
    rw [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
    exact pow_le_pow_left₀ (norm_nonneg _) hdiff 2
  have hDint : Integrable (fun _ : ℝ => D) μ := integrable_const D
  have hpointwise : ∀ᵐ u : ℝ ∂μ,
      Tendsto
        (fun r : ℝ =>
          ‖selectedFerrersReflectedAbel k r u -
            selectedFerrersAbelLimit k u‖ ^ 2)
        (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc :
        MeasurableSet (I_m (selectedFerrersPreAnchorIndex k))),
      selectedOffSeam_ae k] with u hu huseam
    have hdiff : Tendsto
        (fun r : ℝ => selectedFerrersReflectedAbel k r u -
          selectedFerrersAbelLimit k u)
        (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 0) :=
      by
        simpa using
          (selectedFerrersReflectedAbel_tendsto_pointwise_off_seams
            k hu huseam).sub
              (tendsto_const_nhds : Tendsto
                (fun _ : ℝ => selectedFerrersAbelLimit k u)
                (𝓝[Set.Ioo (0 : ℝ) 1] 1)
                (𝓝 (selectedFerrersAbelLimit k u)))
    simpa using hdiff.norm.pow 2
  simpa only [μ, integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => D) hFmeas hbound hDint hpointwise)

#print axioms selectedFerrersReflectedAbel_memLp
#print axioms selectedFerrersAbelLimit_memLp
#print axioms selectedFerrersReflectedAbel_tendsto_L2
#print axioms full_endpoint_vs_midpoint_eStar_seam_plant
#print axioms zero_mass_is_load_bearing_plant
#print axioms pointwise_without_domination_does_not_give_l2_plant
#print axioms complex_even_packet_does_not_require_real_valuedness_plant

end Q3.RouteB.D0Pstar
