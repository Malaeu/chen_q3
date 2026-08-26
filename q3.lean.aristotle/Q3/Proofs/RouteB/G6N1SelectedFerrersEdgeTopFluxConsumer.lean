import Q3.Proofs.RouteB.G6N1SelectedFerrersOuterPolynomialDecay
import Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate
import Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
import Q3.Proofs.RouteB.G6N1SelectedFerrersPacketVariation
import Q3.Proofs.RouteB.D0PstarPhysicalFourierEnergyControl

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Edge-top flux consumer, stage A (verdict ed7c8f7d, REQ-2026-08-26-E)

The exact object locks for the top-lattice transaction:

* the source packet is EXACTLY the two-mode anchored combination
  `¼(χ₀·(a₄h₄) − 3χ₂·(a₀h₀))` — two DISTINCT eigenmodes, never one;
* the cylinder target is EXACTLY `4H = ¼(D₄ − 3D₀)`;
* the lattice boundary has THREE classes — non-top `(n+1)u ≤ λ`,
  strict top `nu < λ < (n+1)u`, physical seam `nu = λ` — with the
  strict-top index unique and its point strictly inside the outer half.
-/

/-! ## The exact packet identity -/

/-- **Exact source-packet identity**: the literal Lemma-7.3 source packet is
the two-mode anchored combination `¼(χ₀·(a₄h₄) − 3χ₂·(a₀h₀))`. -/
theorem selectedFerrersLemma73SourcePacket_eq_anchored_combination
    (k : ℕ) (x : ℝ) :
    selectedFerrersLemma73SourcePacket k x =
      (1 / 4 : ℂ) *
        (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x) -
        3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x)) := by
  set P := selectedFerrersPreAnchorPair k with hP
  have hspec := selectedFerrersPreAnchorPair_spec k
  have hI0 := hspec.2.2.2.1
  have hI4 := hspec.2.2.2.2.1
  have hDpos : (0 : ℝ) < P.normalizingDenominator := by
    rw [ProlatePair.normalizingDenominator_eq]
    have h2 : (0 : ℝ) < P.I0 ^ 2 + P.I4 ^ 2 := by positivity
    exact Real.sqrt_pos.2 h2
  have hDc : ((P.normalizingDenominator : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hDpos.ne'
  have hcancel : selectedFerrersLemma73SourcePacket k x =
      -((centerAnchorScalarZero k * centerAnchorScalarFour k) / 4) *
        (((P.I4 : ℝ) : ℂ) * P.h0 x - ((P.I0 : ℝ) : ℂ) * P.h4 x) := by
    rw [selectedFerrersLemma73SourcePacket, selectedFerrersLemma73SourceScale,
      selectedFerrersLemma72Scale, prolateCombination]
    rw [← hP]
    field_simp
    ring
  have e1 := P.h0_fourier_center
  have e2 := P.h4_fourier_center
  have lock1 : centerAnchorScalarZero k * P.h0 0 = 1 := by
    have := centerAnchorScalarZero_mul_center k
    simpa [selectedFerrersCenterZero, ← hP] using this
  have lock2 : centerAnchorScalarFour k * P.h4 0 = 3 := by
    have := centerAnchorScalarFour_mul_center k
    simpa [selectedFerrersCenterFour, ← hP] using this
  rw [hcancel, e1, e2]
  linear_combination
    ((1 / 4 : ℂ) * (P.chi0 : ℂ) * P.h4 x * centerAnchorScalarFour k) *
      lock1 -
    ((1 / 4 : ℂ) * (P.chi2 : ℂ) * P.h0 x * centerAnchorScalarZero k) *
      lock2

/-- **Exact target identity**: `4H = ¼(D₄ − 3D₀)` at the project argument. -/
theorem four_mul_explicitCCMLimitH_eq_cylinder (x : ℝ) :
    (4 : ℂ) * explicitCCMLimitH x =
      (1 / 4 : ℂ) *
        (((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ) -
          3 * ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)) := by
  rw [explicitCCMLimitH_eq_cylinder_combination]
  push_cast
  ring

/-! ## The three-way lattice boundary partition -/

/-- **Exact boundary partition**: every lattice point with `n·u ≤ λ` or a
straddle is in exactly one of the three classes — non-top `(n+1)u ≤ λ`,
strict top `nu < λ < (n+1)u`, or physical seam `nu = λ`.  (Points with
`nu > λ` lie beyond the window and are outside the boundary classes.) -/
theorem edgeTop_boundary_trichotomy (u lam : ℝ) (hu : 0 < u) (n : ℝ)
    (hn : n * u ≤ lam) :
    ((n + 1) * u ≤ lam ∧ ¬(n * u < lam ∧ lam < (n + 1) * u) ∧ n * u ≠ lam) ∨
    ((n * u < lam ∧ lam < (n + 1) * u) ∧ ¬((n + 1) * u ≤ lam) ∧
      n * u ≠ lam) ∨
    (n * u = lam ∧ ¬((n + 1) * u ≤ lam ∧ n * u < lam) ∧
      ¬(n * u < lam ∧ lam < (n + 1) * u ∧ (n + 1) * u ≤ lam)) := by
  rcases eq_or_lt_of_le hn with heq | hlt
  · right; right
    refine ⟨heq, ?_, ?_⟩
    · rintro ⟨_, h2⟩
      linarith
    · rintro ⟨h1, _, _⟩
      linarith
  · rcases le_or_lt ((n + 1) * u) lam with hle | hgt
    · left
      refine ⟨hle, ?_, hlt.ne⟩
      rintro ⟨_, h2⟩
      linarith
    · right; left
      exact ⟨⟨hlt, hgt⟩, by intro h; linarith, hlt.ne⟩

/-- **Uniqueness of the strict-top index**: two strict-top indices at the
same spacing coincide. -/
theorem edgeTop_strictTop_unique (u lam : ℝ) (hu : 0 < u)
    (n₁ n₂ : ℕ)
    (h₁ : (n₁ : ℝ) * u < lam ∧ lam < ((n₁ : ℝ) + 1) * u)
    (h₂ : (n₂ : ℝ) * u < lam ∧ lam < ((n₂ : ℝ) + 1) * u) : n₁ = n₂ := by
  by_contra hne
  rcases Nat.lt_or_ge n₁ n₂ with hlt | hge
  · have hc : ((n₁ : ℝ) + 1) ≤ (n₂ : ℝ) := by exact_mod_cast hlt
    nlinarith [h₁.2, h₂.1, hu]
  · have hlt2 : n₂ < n₁ := by omega
    have hc : ((n₂ : ℝ) + 1) ≤ (n₁ : ℝ) := by exact_mod_cast hlt2
    nlinarith [h₂.2, h₁.1, hu]

/-- **The strict-top point sits in the outer half**: `nu > λ/2`. -/
theorem edgeTop_strictTop_outer (u lam : ℝ) (hu : 0 < u) (n : ℕ)
    (hn1 : 1 ≤ n)
    (h : (n : ℝ) * u < lam ∧ lam < ((n : ℝ) + 1) * u) :
    lam / 2 < (n : ℝ) * u := by
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  nlinarith [h.1, h.2, hu, hn1R]

/-! ## Stage B: the per-mode outer flux derivative bound

One mode, its OWN differential eigenvalue.  The exact distance factor
`(λ−y)` cancels between the flux numerator and the degenerate weight —
no average, no sup-norm hypothesis, no `δ″`. -/

variable {mProject K : ℕ} {Λ : ℝ}

/-- **Outer flux derivative bound** for the raw committed series: if the
mode is `≤ A/λ⁶` on the outer half, its derivative is `≤ 41·A/λ³` strictly
inside the outer half.  Uses only the committed ODE and zero flux. -/
theorem sturm_outer_flux_derivative_bound
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hθabs : |Λ + mode4JacobiG mProject| ≤ (Real.sqrt mProject) ^ 4)
    (A : ℝ) (hA : 0 ≤ A)
    (houter : ∀ t ∈ Icc (Real.sqrt mProject / 2) (Real.sqrt mProject),
      |mode4PhysicalFerrersSeries mProject S.coefficients t| ≤
        A / (Real.sqrt mProject) ^ 6) :
    ∀ y ∈ Ico (Real.sqrt mProject / 2) (Real.sqrt mProject),
      |mode4PhysicalFerrersFirstDerivativeSeries mProject
        S.coefficients y| ≤ 41 * A / (Real.sqrt mProject) ^ 3 := by
  set lam := Real.sqrt (mProject : ℝ) with hlamdef
  set φ : ℝ → ℝ := mode4PhysicalFerrersSeries mProject S.coefficients
    with hφdef
  set φd : ℝ → ℝ :=
    mode4PhysicalFerrersFirstDerivativeSeries mProject S.coefficients
    with hφddef
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hm2 : (2 : ℝ) ≤ (mProject : ℝ) := by exact_mod_cast hm
  have hlam0 : (0 : ℝ) < lam := Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef]
    exact Real.one_le_sqrt.mpr (by linarith)
  have hsq : lam ^ 2 = (mProject : ℝ) := Real.sq_sqrt hmR.le
  have hpi2 : Real.pi ^ 2 ≤ 10 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  intro y hy
  have hy0 : (0 : ℝ) < y := by nlinarith [hy.1, hlam0]
  set F : ℝ → ℝ := fun t => (lam ^ 2 - t ^ 2) * φd t with hF
  -- pointwise bound on the flux derivative over the outer region
  have hFd_bound : ∀ t ∈ Icc y lam,
      |((2 * Real.pi * lam * t) ^ 2 * φ t -
        (Λ + mode4JacobiG mProject) * φ t)| ≤ 41 * A / lam ^ 2 := by
    intro t ht
    have htO : t ∈ Icc (lam / 2) lam := ⟨le_trans hy.1 ht.1, ht.2⟩
    have hφt := houter t htO
    have hcoef : |(2 * Real.pi * lam * t) ^ 2 -
        (Λ + mode4JacobiG mProject)| ≤ 41 * lam ^ 4 := by
      have h1 : (2 * Real.pi * lam * t) ^ 2 ≤ 4 * Real.pi ^ 2 * lam ^ 4 := by
        have ht2 : t ^ 2 ≤ lam ^ 2 := by nlinarith [ht.2, ht.1, hy.1, hlam0]
        nlinarith [mul_le_mul_of_nonneg_left ht2
          (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2 * lam ^ 2)]
      have h2 := abs_le.1 hθabs
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg (2 * Real.pi * lam * t), h2.2, hlam0,
          pow_pos hlam0 4]
      · nlinarith [h1, h2.1, hpi2, pow_pos hlam0 4]
    calc |(2 * Real.pi * lam * t) ^ 2 * φ t -
        (Λ + mode4JacobiG mProject) * φ t| =
        |((2 * Real.pi * lam * t) ^ 2 -
          (Λ + mode4JacobiG mProject))| * |φ t| := by
          rw [← abs_mul]
          congr 1
          ring
      _ ≤ (41 * lam ^ 4) * (A / lam ^ 6) := by
          apply mul_le_mul hcoef hφt (abs_nonneg _) (by positivity)
      _ = 41 * A / lam ^ 2 := by
          field_simp
  -- FTC on truncations, then the zero-flux limit
  have hFbound : |F y| ≤ (lam - y) * (41 * A / lam ^ 2) := by
    have hlim := sturm_mode_flux_tendsto_zero_top S hm hK hsep hΛ
    have hFdiff : ∀ z ∈ Ico y lam, |F z - F y| ≤
        (lam - y) * (41 * A / lam ^ 2) := by
      intro z hz
      have hyz : y ≤ z := hz.1
      have hsubIoo : Icc y z ⊆ Ioo (-lam) lam := by
        intro t ht
        exact ⟨by nlinarith [ht.1, hy.1, hlam0],
          lt_of_le_of_lt ht.2 hz.2⟩
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := F)
        (f' := fun t => (2 * Real.pi * lam * t) ^ 2 * φ t -
          (Λ + mode4JacobiG mProject) * φ t)
        (a := y) (b := z)
        (fun t ht => by
          rw [uIcc_of_le hyz] at ht
          exact sturm_mode_flux_hasDerivAt S hm (hsubIoo ht))
        (by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hyz]
          have hφc : ContinuousOn φ (Icc y z) :=
            (sturm_physSeries_continuousOn_closed S hm).mono
              (fun t ht => Ioo_subset_Icc_self (hsubIoo ht))
          apply ContinuousOn.sub
          · apply ContinuousOn.mul _ hφc
            fun_prop
          · exact continuousOn_const.mul hφc)
      rw [← hftc]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 41 * A / lam ^ 2)
        (f := fun t => (2 * Real.pi * lam * t) ^ 2 * φ t -
          (Λ + mode4JacobiG mProject) * φ t)
        (a := y) (b := z)
        (by
          intro t ht
          rw [uIoc_of_le hyz] at ht
          rw [Real.norm_eq_abs]
          exact hFd_bound t ⟨ht.1.le, le_trans ht.2 hz.2.le⟩)
      rw [Real.norm_eq_abs] at hnorm
      calc |∫ t in y..z, ((2 * Real.pi * lam * t) ^ 2 * φ t -
          (Λ + mode4JacobiG mProject) * φ t)| ≤
          (41 * A / lam ^ 2) * |z - y| := hnorm
        _ ≤ (lam - y) * (41 * A / lam ^ 2) := by
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z - y)]
            have : z - y ≤ lam - y := by linarith [hz.2.le]
            nlinarith [this, hA, pow_pos hlam0 2,
              div_nonneg (by linarith : (0:ℝ) ≤ 41 * A)
                (pow_pos hlam0 2).le]
    -- pass to the limit z → λ⁻ along the zero flux
    have hT : Tendsto (fun z => |F z - F y|)
        (nhdsWithin lam (Iio lam)) (𝓝 |0 - F y|) := by
      have h1 : Tendsto F (nhdsWithin lam (Iio lam)) (𝓝 0) := by
        simp only [hF, hφddef]
        exact sturm_mode_flux_tendsto_zero_top S hm hK hsep hΛ
      exact (h1.sub_const _).abs
    have hev : ∀ᶠ z in nhdsWithin lam (Iio lam),
        |F z - F y| ≤ (lam - y) * (41 * A / lam ^ 2) := by
      have hyMem : Ioo y lam ∈ nhdsWithin lam (Iio lam) := by
        apply mem_nhdsWithin.mpr
        exact ⟨Ioi y, isOpen_Ioi, hy.2, fun t ht => ⟨ht.1, ht.2⟩⟩
      filter_upwards [hyMem] with z hz
      exact hFdiff z ⟨hz.1.le, hz.2⟩
    have := le_of_tendsto hT hev
    rwa [zero_sub, abs_neg] at this
  -- divide by the weight; the distance factor cancels exactly
  have hw : (0 : ℝ) < lam ^ 2 - y ^ 2 := by nlinarith [hy.2, hy0]
  have hwge : lam * (lam - y) ≤ lam ^ 2 - y ^ 2 := by nlinarith [hy0]
  have hFy : |φd y| = |F y| / (lam ^ 2 - y ^ 2) := by
    rw [hF]
    simp only
    rw [abs_mul, abs_of_pos hw]
    field_simp
  rw [hFy]
  rw [div_le_div_iff₀ hw (by positivity : (0:ℝ) < lam ^ 3)]
  calc |F y| * lam ^ 3 ≤
      ((lam - y) * (41 * A / lam ^ 2)) * lam ^ 3 :=
        mul_le_mul_of_nonneg_right hFbound (by positivity)
    _ = (41 * A) * (lam * (lam - y)) := by
        field_simp
    _ ≤ (41 * A) * (lam ^ 2 - y ^ 2) := by
        apply mul_le_mul_of_nonneg_left hwge (by positivity)
    _ = 41 * A * (lam ^ 2 - y ^ 2) := by ring

/-! ## Stage C-i: explicit derivatives of the target and the anchored modes -/

/-- The explicit real derivative of the `H`-profile. -/
private theorem etc_hbHRe_hasDerivAt (y : ℝ) :
    HasDerivAt hbHRe
      ((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
        3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2)) y := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * t ^ 2))
      ((-Real.pi * (2 * y)) * Real.exp (-Real.pi * y ^ 2)) y := by
    have hin : HasDerivAt (fun t : ℝ => -Real.pi * t ^ 2)
        (-Real.pi * (2 * y)) y := by
      have := (hasDerivAt_pow 2 y).const_mul (-Real.pi)
      exact this.congr_deriv (by push_cast; ring)
    exact hin.exp.congr_deriv (by ring)
  have hpoly : HasDerivAt
      (fun t : ℝ => (Real.pi / 2) * t ^ 2 * (2 * Real.pi * t ^ 2 - 3))
      (Real.pi * y * (2 * Real.pi * y ^ 2 - 3) +
        (Real.pi / 2) * y ^ 2 * (4 * Real.pi * y)) y := by
    have h2 := (hasDerivAt_pow 2 y).const_mul (Real.pi / 2)
    have h4 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t ^ 2 - 3)
        (2 * Real.pi * (2 * y)) y := by
      have := (hasDerivAt_pow 2 y).const_mul (2 * Real.pi)
      exact (this.sub_const 3).congr_deriv (by push_cast; ring)
    have := (h2.congr_deriv (show (Real.pi / 2) * ((2:ℕ) * y ^ 1) =
        Real.pi * y by push_cast; ring)).mul h4
    exact this.congr_deriv (by ring)
  have hprod : HasDerivAt (fun t : ℝ =>
      (Real.pi / 2) * t ^ 2 * (2 * Real.pi * t ^ 2 - 3) *
        Real.exp (-Real.pi * t ^ 2))
      ((Real.pi * y * (2 * Real.pi * y ^ 2 - 3) +
        (Real.pi / 2) * y ^ 2 * (4 * Real.pi * y)) *
          Real.exp (-Real.pi * y ^ 2) +
        (Real.pi / 2) * y ^ 2 * (2 * Real.pi * y ^ 2 - 3) *
          ((-Real.pi * (2 * y)) * Real.exp (-Real.pi * y ^ 2))) y :=
    hpoly.mul hexp
  have hfun : (fun t : ℝ =>
      (Real.pi / 2) * t ^ 2 * (2 * Real.pi * t ^ 2 - 3) *
        Real.exp (-Real.pi * t ^ 2)) = hbHRe := by
    funext t
    rw [hbHRe]
  rw [hfun] at hprod
  exact hprod.congr_deriv (by ring)

/-- The complex target `H` has the same explicit derivative. -/
private theorem etc_H_hasDerivAt (y : ℝ) :
    HasDerivAt explicitCCMLimitH
      ((((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
        3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2) : ℝ)) : ℂ) y := by
  have h := (etc_hbHRe_hasDerivAt y).ofReal_comp
  have hfun : (fun t : ℝ => ((hbHRe t : ℝ) : ℂ)) = explicitCCMLimitH := by
    funext t
    rw [explicitCCMLimitH_eq_hbHRe]
  rwa [hfun] at h

/-- Crude global bound: `4·|H′(y)| ≤ 1536·λ⁵·e^{−πλ²/4}` on the outer half. -/
private theorem etc_Hderiv_outer_bound (lam : ℝ) (hlam1 : 1 ≤ lam)
    (y : ℝ) (hy : y ∈ Icc (lam / 2) lam) :
    ‖(((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
      3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2) : ℝ) : ℂ)‖ ≤
      384 * lam ^ 5 * Real.exp (-Real.pi * lam ^ 2 / 4) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hy0 : (0 : ℝ) < y := by nlinarith [hy.1, hlam1]
  have hylam : y ≤ lam := hy.2
  have hpoly : |(-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
      3 * Real.pi * y)| ≤ 384 * lam ^ 5 := by
    have hy5 : y ^ 5 ≤ lam ^ 5 := by
      apply pow_le_pow_left₀ hy0.le hylam
    have hy3 : y ^ 3 ≤ lam ^ 3 := by
      apply pow_le_pow_left₀ hy0.le hylam
    have hl35 : lam ^ 3 ≤ lam ^ 5 :=
      pow_le_pow_right₀ hlam1 (by norm_num)
    have hl15 : lam ≤ lam ^ 5 := by
      have := pow_le_pow_right₀ hlam1 (show 1 ≤ 5 by norm_num)
      simpa using this
    have hpi2 : Real.pi ^ 2 ≤ 10 := by nlinarith [hpi, hpi0]
    have hpi3 : Real.pi ^ 3 ≤ 32 := by
      nlinarith [hpi, hpi0, hpi2,
        mul_le_mul_of_nonneg_left hpi2 hpi0.le]
    have h1 := abs_add_le (-(2 * Real.pi ^ 3) * y ^ 5 +
      7 * Real.pi ^ 2 * y ^ 3) (-(3 * Real.pi * y))
    have h2 := abs_add_le (-(2 * Real.pi ^ 3) * y ^ 5)
      (7 * Real.pi ^ 2 * y ^ 3)
    have e1 : |(-(2 * Real.pi ^ 3) * y ^ 5)| = 2 * Real.pi ^ 3 * y ^ 5 := by
      rw [abs_of_nonpos (by
        nlinarith [mul_pos (pow_pos hpi0 3) (pow_pos hy0 5)])]
      ring
    have e2 : |7 * Real.pi ^ 2 * y ^ 3| = 7 * Real.pi ^ 2 * y ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
    have e3 : |(-(3 * Real.pi * y))| = 3 * Real.pi * y := by
      rw [abs_of_nonpos (by nlinarith [mul_pos hpi0 hy0])]
      ring
    calc |(-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
        3 * Real.pi * y)| = |(-(2 * Real.pi ^ 3) * y ^ 5 +
          7 * Real.pi ^ 2 * y ^ 3) + (-(3 * Real.pi * y))| := by
          rw [sub_eq_add_neg]
      _ ≤ |(-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3)| +
          |(-(3 * Real.pi * y))| := h1
      _ ≤ (|(-(2 * Real.pi ^ 3) * y ^ 5)| + |7 * Real.pi ^ 2 * y ^ 3|) +
          |(-(3 * Real.pi * y))| := by linarith [h2]
      _ = 2 * Real.pi ^ 3 * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 +
          3 * Real.pi * y := by rw [e1, e2, e3]
      _ ≤ 384 * lam ^ 5 := by
          nlinarith [hy5, hy3, hl35, hl15, hpi3, hpi2, hpi0,
            mul_le_mul_of_nonneg_left hy5
              (by positivity : (0:ℝ) ≤ 2 * Real.pi ^ 3),
            mul_le_mul_of_nonneg_left hy3
              (by positivity : (0:ℝ) ≤ 7 * Real.pi ^ 2),
            mul_le_mul_of_nonneg_left hylam
              (by positivity : (0:ℝ) ≤ 3 * Real.pi)]
  have hexp : Real.exp (-Real.pi * y ^ 2) ≤
      Real.exp (-Real.pi * lam ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    have hy2 : lam ^ 2 / 4 ≤ y ^ 2 := by nlinarith [hy.1, hy0]
    nlinarith [hy2, hpi0]
  calc |(-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
      3 * Real.pi * y)| * Real.exp (-Real.pi * y ^ 2) ≤
      (384 * lam ^ 5) * Real.exp (-Real.pi * lam ^ 2 / 4) := by
        apply mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = 384 * lam ^ 5 * Real.exp (-Real.pi * lam ^ 2 / 4) := by ring

/-- Interior derivative of a normalized zero-extended anchored mode. -/
private theorem etc_anchored_hasDerivAt
    {mProject K' : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K' Λ)
    (hm : 2 ≤ mProject) (a : ℂ) {y : ℝ}
    (hy : y ∈ Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject)) :
    HasDerivAt (fun t => a * S.normalizedPhysicalMode t)
      (a * (((mode4PhysicalFerrersFirstDerivativeSeries mProject
          S.coefficients y : ℝ) : ℂ) /
        ((S.physicalL2Normalization : ℝ) : ℂ))) y := by
  have hseries : HasDerivAt
      (fun t => mode4PhysicalFerrersSeriesComplex mProject S.coefficients t)
      ((mode4PhysicalFerrersFirstDerivativeSeries mProject
        S.coefficients y : ℝ) : ℂ) y := by
    have h := (S.physicalFerrersSeries_hasDerivAt_firstDerivativeSeries
      hm hy).ofReal_comp
    exact h
  have hdiv := hseries.div_const ((S.physicalL2Normalization : ℝ) : ℂ)
  have hlocal : (fun t => S.normalizedPhysicalMode t) =ᶠ[𝓝 y]
      (fun t => mode4PhysicalFerrersSeriesComplex mProject S.coefficients t /
        ((S.physicalL2Normalization : ℝ) : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      Set.indicator_of_mem (Ioo_subset_Icc_self ht)]
  have hmode : HasDerivAt (fun t => S.normalizedPhysicalMode t)
      (((mode4PhysicalFerrersFirstDerivativeSeries mProject
        S.coefficients y : ℝ) : ℂ) /
        ((S.physicalL2Normalization : ℝ) : ℂ)) y :=
    hdiv.congr_of_eventuallyEq hlocal
  exact hmode.const_mul a

/-! ## Stage C-ii: the literal strict-top budget -/

/-- **The literal defect edge-top budget**: the `√u`-weighted log-window
integral of the derivative-defect comb restricted to the strict-top class
`nu < λ < (n+1)u` — the unique seam-free uppermost lattice cell.  The
non-top class `(n+1)u ≤ λ` is closed by nodes 3A/3B; the physical seam
`nu = λ` belongs to the committed W4 jump ledger. -/
noncomputable def selectedFerrersDefectEdgeTopBudget (k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.log ((k + 2 : ℕ) : ℝ),
    Real.sqrt (Real.exp x / selectedFerrersPaperLambda k) *
      ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
          (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
            selectedFerrersPaperLambda k ∧
          selectedFerrersPaperLambda k <
            ((n : ℝ) + 1) * (Real.exp x / selectedFerrersPaperLambda k)),
        (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) : ℝ) : ℂ) *
          deriv (fun t => selectedFerrersLemma73SourcePacket k t -
            (4 : ℂ) * explicitCCMLimitH t)
            ((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k))‖

/-- The explicit continuous expression for the defect derivative on the
open half-window. -/
private noncomputable def etc_Dexpr (k : ℕ) (y : ℝ) : ℂ :=
  (1 / 4 : ℂ) *
    (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
      (centerAnchorScalarFour k *
        (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution4 k).coefficients y : ℝ) : ℂ) /
        (((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
          ℝ) : ℂ))) -
    3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
      (centerAnchorScalarZero k *
        (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution0 k).coefficients y : ℝ) : ℂ) /
        (((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :
          ℝ) : ℂ)))) -
  (4 : ℂ) * (((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
    3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2) : ℝ) : ℂ)

/-- The defect function in its two-mode anchored form. -/
private theorem etc_defect_funext (k : ℕ) :
    (fun t => selectedFerrersLemma73SourcePacket k t -
      (4 : ℂ) * explicitCCMLimitH t) =
    (fun t => (1 / 4 : ℂ) *
      (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
        (centerAnchorScalarFour k *
          (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode t) -
      3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
        (centerAnchorScalarZero k *
          (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode t)) -
      (4 : ℂ) * explicitCCMLimitH t) := by
  funext t
  have h := selectedFerrersLemma73SourcePacket_eq_anchored_combination k t
  have hspec := selectedFerrersPreAnchorPair_spec k
  rw [h, hspec.2.1, hspec.2.2.1]

/-- The defect derivative agrees with the explicit expression on the open
half-window. -/
private theorem etc_derivDfn_eq (k : ℕ) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) (selectedFerrersPaperLambda k)) :
    deriv (fun t => selectedFerrersLemma73SourcePacket k t -
      (4 : ℂ) * explicitCCMLimitH t) y = etc_Dexpr k y := by
  have hyIoo : y ∈ Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
    have h1 := hy.1
    have h2 := hy.2
    rw [selectedFerrersPaperLambda] at h2
    constructor
    · have : (0 : ℝ) ≤ Real.sqrt ((k + 2 : ℕ) : ℝ) := Real.sqrt_nonneg _
      linarith
    · exact h2
  have hd4 := etc_anchored_hasDerivAt (selectedFerrersPreAnchorSolution4 k)
    (by omega) (centerAnchorScalarFour k) hyIoo
  have hd0 := etc_anchored_hasDerivAt (selectedFerrersPreAnchorSolution0 k)
    (by omega) (centerAnchorScalarZero k) hyIoo
  have hH := etc_H_hasDerivAt y
  have hcomb : HasDerivAt
      (fun t => (1 / 4 : ℂ) *
        (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (centerAnchorScalarFour k *
            (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode t) -
        3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (centerAnchorScalarZero k *
            (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode
              t)) -
        (4 : ℂ) * explicitCCMLimitH t)
      (etc_Dexpr k y) y := by
    have h1 := ((hd4.const_mul
      (((selectedFerrersPreAnchorPair k).chi0 : ℂ))).sub
      (hd0.const_mul
        (3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ)))).const_mul
      (1 / 4 : ℂ)
    have h2 := hH.const_mul (4 : ℂ)
    exact (h1.sub h2).congr_deriv (by rw [etc_Dexpr])
  rw [etc_defect_funext k]
  exact hcomb.deriv

/-- The explicit expression is continuous on the open half-window. -/
private theorem etc_Dexpr_continuousOn (k : ℕ) :
    ContinuousOn (etc_Dexpr k)
      (Ioo (0 : ℝ) (selectedFerrersPaperLambda k)) := by
  have hsub : Ioo (0 : ℝ) (selectedFerrersPaperLambda k) ⊆
      Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
        (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
    intro t ht
    rw [selectedFerrersPaperLambda] at ht
    constructor
    · have : (0 : ℝ) ≤ Real.sqrt ((k + 2 : ℕ) : ℝ) := Real.sqrt_nonneg _
      linarith [ht.1]
    · exact ht.2
  have hφd4 : ContinuousOn (fun y : ℝ =>
      ((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y : ℝ) : ℂ))
      (Ioo (0 : ℝ) (selectedFerrersPaperLambda k)) := by
    apply Continuous.comp_continuousOn Complex.continuous_ofReal
    intro t ht
    exact (((selectedFerrersPreAnchorSolution4
      k).physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
      (by omega) (hsub ht)).continuousAt).continuousWithinAt
  have hφd0 : ContinuousOn (fun y : ℝ =>
      ((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y : ℝ) : ℂ))
      (Ioo (0 : ℝ) (selectedFerrersPaperLambda k)) := by
    apply Continuous.comp_continuousOn Complex.continuous_ofReal
    intro t ht
    exact (((selectedFerrersPreAnchorSolution0
      k).physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
      (by omega) (hsub ht)).continuousAt).continuousWithinAt
  have hH : Continuous (fun y : ℝ =>
      (((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
        3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2) : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    fun_prop
  unfold etc_Dexpr
  apply ContinuousOn.sub
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub
    · exact continuousOn_const.mul
        (continuousOn_const.mul (hφd4.div_const _))
    · exact continuousOn_const.mul
        (continuousOn_const.mul (hφd0.div_const _))
  · exact (continuous_const.mul hH).continuousOn

/-- The integral bound: a pointwise strict-top derivative-defect rate
`CT/λ³` integrates to the budget rate `2·CT/(λ·√λ)`. -/
private theorem etc_budget_bound (k : ℕ) (CT : ℝ) (hCT : 0 ≤ CT)
    (hDb : ∀ y ∈ Ico (selectedFerrersPaperLambda k / 2)
        (selectedFerrersPaperLambda k),
      ‖deriv (fun t => selectedFerrersLemma73SourcePacket k t -
        (4 : ℂ) * explicitCCMLimitH t) y‖ ≤
        CT / (selectedFerrersPaperLambda k) ^ 3) :
    selectedFerrersDefectEdgeTopBudget k ≤
      2 * CT / (selectedFerrersPaperLambda k *
        Real.sqrt (selectedFerrersPaperLambda k)) := by
  set lam := selectedFerrersPaperLambda k with hlamdef
  set m : ℕ := k + 2 with hmdef
  have hmR : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : (1 : ℕ) ≤ m := by omega
    exact_mod_cast this
  have hlam_eq : lam = Real.sqrt ((m : ℕ) : ℝ) := by
    rw [hlamdef, selectedFerrersPaperLambda, hmdef]
  have hlam0 : (0 : ℝ) < lam := by
    rw [hlam_eq]
    exact Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlam_eq]
    exact Real.one_le_sqrt.mpr hm1
  have hsq : lam ^ 2 = (m : ℝ) := by
    rw [hlam_eq]
    exact Real.sq_sqrt hmR.le
  have hL0 : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  set Dfn : ℝ → ℂ := fun t => selectedFerrersLemma73SourcePacket k t -
    (4 : ℂ) * explicitCCMLimitH t with hDfn
  set Fc : ℕ → ℝ → ℂ := fun n x =>
    if ((n : ℝ) * (Real.exp x / lam) < lam ∧
        lam < ((n : ℝ) + 1) * (Real.exp x / lam)) then
      (((Real.sqrt (Real.exp x / lam) *
        ((n : ℝ) * (Real.exp x / lam)) : ℝ)) : ℂ) *
        deriv Dfn ((n : ℝ) * (Real.exp x / lam))
    else 0 with hFc
  -- the integrand is the norm of the finite Fc-sum
  have heq : ∀ x : ℝ,
      Real.sqrt (Real.exp x / lam) *
        ‖∑ n ∈ (Finset.Icc 1 m).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam)),
          (((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
            deriv Dfn ((n : ℝ) * (Real.exp x / lam))‖ =
      ‖∑ n ∈ Finset.Icc 1 m, Fc n x‖ := by
    intro x
    rw [Finset.sum_filter]
    have hpull : Real.sqrt (Real.exp x / lam) *
        ‖∑ n ∈ Finset.Icc 1 m, (if ((n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam)) then
          (((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
            deriv Dfn ((n : ℝ) * (Real.exp x / lam)) else 0)‖ =
        ‖((Real.sqrt (Real.exp x / lam) : ℝ) : ℂ) *
          ∑ n ∈ Finset.Icc 1 m, (if ((n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam)) then
          (((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
            deriv Dfn ((n : ℝ) * (Real.exp x / lam)) else 0)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hpull, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    simp only [hFc]
    rw [mul_ite, mul_zero]
    congr 1
    · rw [← mul_assoc]
      congr 1
      push_cast
      ring
  -- each Fc n is integrable on the window
  have hFc_int : ∀ n ∈ Finset.Icc 1 m,
      IntegrableOn (Fc n) (Ioc (0 : ℝ) (Real.log (m : ℝ))) volume := by
    intro n hn
    obtain ⟨hn1, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    -- the strict-top condition is the open x-interval
    have hcond : ∀ x : ℝ,
        (((n : ℝ) * (Real.exp x / lam) < lam ∧
          lam < ((n : ℝ) + 1) * (Real.exp x / lam)) ↔
        x ∈ Ioo (Real.log ((m : ℝ) / ((n : ℝ) + 1)))
          (Real.log ((m : ℝ) / (n : ℝ)))) := by
      intro x
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · rw [Real.log_lt_iff_lt_exp (by positivity),
            div_lt_iff₀ (by positivity)]
          have heq : ((n : ℝ) + 1) * (Real.exp x / lam) =
              (((n : ℝ) + 1) * Real.exp x) / lam := by ring
          rw [heq, lt_div_iff₀ hlam0] at h2
          nlinarith [h2, hsq]
        · rw [Real.lt_log_iff_exp_lt (by positivity), lt_div_iff₀ hn0]
          have heq : (n : ℝ) * (Real.exp x / lam) =
              ((n : ℝ) * Real.exp x) / lam := by ring
          rw [heq, div_lt_iff₀ hlam0] at h1
          nlinarith [h1, hsq]
      · rintro ⟨h1, h2⟩
        rw [Real.log_lt_iff_lt_exp (by positivity),
          div_lt_iff₀ (by positivity)] at h1
        rw [Real.lt_log_iff_exp_lt (by positivity), lt_div_iff₀ hn0] at h2
        constructor
        · have heq : (n : ℝ) * (Real.exp x / lam) =
              ((n : ℝ) * Real.exp x) / lam := by ring
          rw [heq, div_lt_iff₀ hlam0]
          nlinarith [h2, hsq]
        · have heq : ((n : ℝ) + 1) * (Real.exp x / lam) =
              (((n : ℝ) + 1) * Real.exp x) / lam := by ring
          rw [heq, lt_div_iff₀ hlam0]
          nlinarith [h1, hsq]
    have hind : Fc n = Set.indicator
        (Ioo (Real.log ((m : ℝ) / ((n : ℝ) + 1)))
          (Real.log ((m : ℝ) / (n : ℝ))))
        (fun x => (((Real.sqrt (Real.exp x / lam) *
          ((n : ℝ) * (Real.exp x / lam)) : ℝ)) : ℂ) *
          deriv Dfn ((n : ℝ) * (Real.exp x / lam))) := by
      funext x
      simp only [hFc]
      by_cases hc : ((n : ℝ) * (Real.exp x / lam) < lam ∧
          lam < ((n : ℝ) + 1) * (Real.exp x / lam))
      · rw [if_pos hc, Set.indicator_of_mem ((hcond x).1 hc)]
      · rw [if_neg hc, Set.indicator_of_notMem
          (fun hmem => hc ((hcond x).2 hmem))]
    -- measurability from continuity on the open interval
    have hasm : AEStronglyMeasurable (Fc n) volume := by
      rw [hind]
      rw [aestronglyMeasurable_indicator_iff measurableSet_Ioo]
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
      apply ContinuousOn.congr
        (f := fun x => (((Real.sqrt (Real.exp x / lam) *
          ((n : ℝ) * (Real.exp x / lam)) : ℝ)) : ℂ) *
          etc_Dexpr k ((n : ℝ) * (Real.exp x / lam)))
      · apply ContinuousOn.mul
        · apply Continuous.continuousOn
          apply Complex.continuous_ofReal.comp
          fun_prop
        · apply ContinuousOn.comp (etc_Dexpr_continuousOn k)
          · apply Continuous.continuousOn
            fun_prop
          · intro x hx
            have hcnd := (hcond x).2 hx
            exact ⟨by positivity, hcnd.1⟩
      · intro x hx
        have hcnd := (hcond x).2 hx
        have hy : (n : ℝ) * (Real.exp x / lam) ∈
            Ioo (0 : ℝ) (selectedFerrersPaperLambda k) :=
          ⟨by positivity, hcnd.1⟩
        simp only
        rw [etc_derivDfn_eq k hy]
    -- boundedness on the window
    have hbdd : ∀ x : ℝ, ‖Fc n x‖ ≤ Real.sqrt lam * CT / lam ^ 2 := by
      intro x
      simp only [hFc]
      by_cases hc : ((n : ℝ) * (Real.exp x / lam) < lam ∧
          lam < ((n : ℝ) + 1) * (Real.exp x / lam))
      · rw [if_pos hc]
        have hu0 : (0 : ℝ) < Real.exp x / lam := by positivity
        have hnu0 : (0 : ℝ) < (n : ℝ) * (Real.exp x / lam) := by positivity
        have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hulam : Real.exp x / lam ≤ lam := by
          nlinarith [hc.1, hn1R, hu0]
        have houter := edgeTop_strictTop_outer (Real.exp x / lam) lam
          hu0 n hn1 hc
        have hDbd := hDb ((n : ℝ) * (Real.exp x / lam))
          ⟨houter.le, hc.1⟩
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        calc Real.sqrt (Real.exp x / lam) *
            ((n : ℝ) * (Real.exp x / lam)) *
            ‖deriv Dfn ((n : ℝ) * (Real.exp x / lam))‖ ≤
            Real.sqrt lam * lam * (CT / lam ^ 3) := by
              apply mul_le_mul
              · apply mul_le_mul
                  (Real.sqrt_le_sqrt hulam) hc.1.le hnu0.le
                  (Real.sqrt_nonneg _)
              · rw [hDfn] at hDbd ⊢
                exact hDbd
              · exact norm_nonneg _
              · positivity
          _ = Real.sqrt lam * CT / lam ^ 2 := by
              field_simp
      · rw [if_neg hc]
        simp only [norm_zero]
        positivity
    -- integrability from the bound
    apply MeasureTheory.Integrable.mono'
      (g := fun _ : ℝ => Real.sqrt lam * CT / lam ^ 2)
    · exact MeasureTheory.integrableOn_const
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    · exact hasm.restrict
    · filter_upwards with x
      exact hbdd x
  -- the summed integrand and the budget
  have hsum_int : IntegrableOn (fun x => ∑ n ∈ Finset.Icc 1 m, Fc n x)
      (Ioc (0 : ℝ) (Real.log (m : ℝ))) volume :=
    MeasureTheory.integrable_finset_sum _ hFc_int
  have hpoint_le : ∀ x : ℝ, ‖∑ n ∈ Finset.Icc 1 m, Fc n x‖ ≤
      Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) := by
    intro x
    have h1 : ‖∑ n ∈ Finset.Icc 1 m, Fc n x‖ ≤
        ∑ n ∈ Finset.Icc 1 m, ‖Fc n x‖ := norm_sum_le _ _
    have h2 : ∀ n ∈ Finset.Icc 1 m, ‖Fc n x‖ ≤
        (if ((n : ℝ) * (Real.exp x / lam) < lam ∧
          lam < ((n : ℝ) + 1) * (Real.exp x / lam)) then
          Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) else 0) := by
      intro n hn
      obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
      simp only [hFc]
      by_cases hc : ((n : ℝ) * (Real.exp x / lam) < lam ∧
          lam < ((n : ℝ) + 1) * (Real.exp x / lam))
      · rw [if_pos hc, if_pos hc]
        have hu0 : (0 : ℝ) < Real.exp x / lam := by positivity
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have houter := edgeTop_strictTop_outer (Real.exp x / lam) lam
          hu0 n hn1 hc
        have hDbd := hDb ((n : ℝ) * (Real.exp x / lam))
          ⟨houter.le, hc.1⟩
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        calc Real.sqrt (Real.exp x / lam) *
            ((n : ℝ) * (Real.exp x / lam)) *
            ‖deriv Dfn ((n : ℝ) * (Real.exp x / lam))‖ ≤
            Real.sqrt (Real.exp x / lam) * lam * (CT / lam ^ 3) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hc.1.le
                  (Real.sqrt_nonneg _)
              · rw [hDfn] at hDbd ⊢
                exact hDbd
              · exact norm_nonneg _
              · positivity
          _ = Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) := by
              field_simp
      · rw [if_neg hc, if_neg hc, norm_zero]
    -- at most one strict-top index
    have hcard : ((Finset.Icc 1 m).filter (fun n : ℕ =>
        (n : ℝ) * (Real.exp x / lam) < lam ∧
        lam < ((n : ℝ) + 1) * (Real.exp x / lam))).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact edgeTop_strictTop_unique (Real.exp x / lam) lam
        (by positivity) a b ha' hb'
    calc ‖∑ n ∈ Finset.Icc 1 m, Fc n x‖ ≤
        ∑ n ∈ Finset.Icc 1 m, ‖Fc n x‖ := h1
      _ ≤ ∑ n ∈ Finset.Icc 1 m,
          (if ((n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam)) then
            Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) else 0) :=
          Finset.sum_le_sum h2
      _ = ∑ _n ∈ (Finset.Icc 1 m).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam)),
          Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) :=
          (Finset.sum_filter _ _).symm
      _ ≤ 1 * (Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2)) := by
          rw [Finset.sum_const]
          have hb0 : (0 : ℝ) ≤
              Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) := by
            positivity
          calc _ ≤ (1 : ℕ) • (Real.sqrt (Real.exp x / lam) *
              (CT / lam ^ 2)) := by
                apply smul_le_smul_of_nonneg_right hcard hb0
            _ = 1 * (Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2)) := by
                simp
      _ = Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) := by ring
  -- rewrite the budget through the Fc-sum and compare
  have hbudget_eq : selectedFerrersDefectEdgeTopBudget k =
      ∫ x in Ioc (0 : ℝ) (Real.log (m : ℝ)),
        ‖∑ n ∈ Finset.Icc 1 m, Fc n x‖ := by
    rw [selectedFerrersDefectEdgeTopBudget]
    rw [show Real.log ((k + 2 : ℕ) : ℝ) = Real.log (m : ℝ) by rw [hmdef]]
    rw [intervalIntegral.integral_of_le hL0]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro x _
    exact heq x
  have hg_int : IntegrableOn
      (fun x => Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2))
      (Ioc (0 : ℝ) (Real.log (m : ℝ))) volume := by
    apply MeasureTheory.IntegrableOn.mono_set
      (t := Icc (0 : ℝ) (Real.log (m : ℝ)))
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply Continuous.continuousOn
      fun_prop
    · exact Ioc_subset_Icc_self
  have hmono := MeasureTheory.setIntegral_mono_on
    (hsum_int.norm) hg_int measurableSet_Ioc
    (fun x _ => hpoint_le x)
  -- evaluate the majorant integral by the exact antiderivative
  have hFTC : (∫ x in (0 : ℝ)..Real.log (m : ℝ),
      Real.sqrt (Real.exp x / lam)) =
      2 * Real.sqrt ((m : ℝ) / lam) - 2 * Real.sqrt (1 / lam) := by
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) (Real.log (m : ℝ)),
        HasDerivAt (fun t => 2 * Real.sqrt (Real.exp t / lam))
          (Real.sqrt (Real.exp x / lam)) x := by
      intro x _
      have hpos : (0 : ℝ) < Real.exp x / lam := by positivity
      have hin : HasDerivAt (fun t : ℝ => Real.exp t / lam)
          (Real.exp x / lam) x := (Real.hasDerivAt_exp x).div_const lam
      have hs := hin.sqrt hpos.ne'
      have h2 := hs.const_mul (2 : ℝ)
      apply h2.congr_deriv
      rw [show (2 : ℝ) * (Real.exp x / lam /
          (2 * Real.sqrt (Real.exp x / lam))) =
        (Real.exp x / lam) / Real.sqrt (Real.exp x / lam) from by ring,
        Real.div_sqrt]
    have hint : IntervalIntegrable
        (fun x => Real.sqrt (Real.exp x / lam)) volume 0
        (Real.log (m : ℝ)) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [h, Real.exp_log hmR, Real.exp_zero]
  have hss : Real.sqrt lam * Real.sqrt lam = lam :=
    Real.mul_self_sqrt hlam0.le
  have hmlam : ((m : ℝ) : ℝ) / lam = lam := by
    rw [← hsq]
    field_simp
  calc selectedFerrersDefectEdgeTopBudget k =
      ∫ x in Ioc (0 : ℝ) (Real.log (m : ℝ)),
        ‖∑ n ∈ Finset.Icc 1 m, Fc n x‖ := hbudget_eq
    _ ≤ ∫ x in Ioc (0 : ℝ) (Real.log (m : ℝ)),
        Real.sqrt (Real.exp x / lam) * (CT / lam ^ 2) := hmono
    _ = (CT / lam ^ 2) * ∫ x in Ioc (0 : ℝ) (Real.log (m : ℝ)),
        Real.sqrt (Real.exp x / lam) := by
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro x _
        ring
    _ = (CT / lam ^ 2) *
        (2 * Real.sqrt ((m : ℝ) / lam) - 2 * Real.sqrt (1 / lam)) := by
        rw [← intervalIntegral.integral_of_le hL0, hFTC]
    _ ≤ (CT / lam ^ 2) * (2 * Real.sqrt lam) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hmlam]
        have : (0 : ℝ) ≤ Real.sqrt (1 / lam) := Real.sqrt_nonneg _
        linarith
    _ = 2 * CT / (lam * Real.sqrt lam) := by
        field_simp
        rw [Real.sq_sqrt hlam0.le]



/-! ## Stage C-iii: the public consumer theorems -/

/-- The anchored norm is the scaled raw series on the window. -/
private theorem etc_anchored_norm
    {mProject K' : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K' Λ)
    (hm : 2 ≤ mProject) (a : ℂ) {y : ℝ}
    (hy : y ∈ Icc (-(Real.sqrt mProject)) (Real.sqrt mProject)) :
    ‖a * S.normalizedPhysicalMode y‖ =
      (‖a‖ / S.physicalL2Normalization) *
        |mode4PhysicalFerrersSeries mProject S.coefficients y| := by
  have hN : (0 : ℝ) < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  have hind : S.physicalZeroExtension y =
      mode4PhysicalFerrersSeriesComplex mProject S.coefficients y := by
    rw [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      Set.indicator_of_mem hy]
  rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    hind, mode4PhysicalFerrersSeriesComplex]
  rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN]
  field_simp

/-- Eventually `1536·λ⁸ ≤ e^{πλ²/4}` on the selected schedule. -/
private theorem etc_exp_dominates :
    ∀ᶠ k : ℕ in Filter.atTop,
      1536 * (selectedFerrersPaperLambda k) ^ 8 ≤
        Real.exp (Real.pi * (selectedFerrersPaperLambda k) ^ 2 / 4) := by
  have hev := Filter.Tendsto.eventually_ge_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ)) (777216 : ℝ)
  filter_upwards [hev] with k hk
  set lam := selectedFerrersPaperLambda k with hlamdef
  have hmR : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hlam0 : (0 : ℝ) < lam := by
    rw [hlamdef, selectedFerrersPaperLambda]
    exact Real.sqrt_pos.2 hmR
  have hsq : lam ^ 2 = ((k + 2 : ℕ) : ℝ) := by
    rw [hlamdef, selectedFerrersPaperLambda]
    exact Real.sq_sqrt hmR.le
  have hbig : (777216 : ℝ) ≤ lam ^ 2 := by
    rw [hsq]
    push_cast
    push_cast at hk
    linarith
  have hx : (0 : ℝ) ≤ Real.pi * lam ^ 2 / 4 := by positivity
  have h5 := Real.pow_div_factorial_le_exp (x := Real.pi * lam ^ 2 / 4)
    hx 5
  have h5' : Real.pi ^ 5 * lam ^ 10 / 122880 ≤
      Real.exp (Real.pi * lam ^ 2 / 4) := by
    have heq : (Real.pi * lam ^ 2 / 4) ^ 5 / (Nat.factorial 5 : ℝ) =
        Real.pi ^ 5 * lam ^ 10 / 122880 := by
      norm_num [Nat.factorial]
      ring
    rwa [heq] at h5
  have hpi5 : (243 : ℝ) ≤ Real.pi ^ 5 := by
    have p1 := Real.pi_gt_three
    have p2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [p1]
    have p4 : (81 : ℝ) ≤ Real.pi ^ 4 := by
      nlinarith [mul_le_mul p2 p2 (by norm_num) (by positivity)]
    nlinarith [mul_le_mul p1.le p4 (by norm_num) Real.pi_pos.le]
  have c1 : 243 * lam ^ 10 ≤ Real.pi ^ 5 * lam ^ 10 :=
    mul_le_mul_of_nonneg_right hpi5 (by positivity)
  have c2 : 777216 * lam ^ 8 ≤ lam ^ 2 * lam ^ 8 :=
    mul_le_mul_of_nonneg_right hbig (by positivity)
  have c3 : lam ^ 2 * lam ^ 8 = lam ^ 10 := by ring
  have c5 : 243 * 777216 * lam ^ 8 ≤ Real.pi ^ 5 * lam ^ 10 := by
    nlinarith [c1, c2, c3]
  have c6 : 243 * 777216 * lam ^ 8 / 122880 ≤
      Real.pi ^ 5 * lam ^ 10 / 122880 :=
    div_le_div_of_nonneg_right c5 (by norm_num)
  nlinarith [h5', c6, pow_nonneg hlam0.le 8]

/--
**The exact strict-top budget rate** (verdict ed7c8f7d).  From the F72
mode rate, the χ-defect rate, and the differential eigenvalue rate, the
literal strict-top defect budget is eventually bounded by
`2·(5373952·√2032129 + 1)/(λ·√λ)` — the `λ^{-3/2}` rate with the exact
constant produced by the complete algebra.
-/
theorem selectedFerrersDefectEdgeTopBudget_bound_of_modeChiThetaRates
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
    (hmode :
      ∀ᶠ k in Filter.atTop,
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
    (hchi :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ :
      ∀ᶠ k in Filter.atTop,
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
            mode4JacobiG (k + 2)| ≤ Cθ * ((k + 2 : ℕ) : ℝ) ∧
          |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
            mode4JacobiG (k + 2)| ≤ Cθ * ((k + 2 : ℕ) : ℝ)) :
    ∀ᶠ k in Filter.atTop,
      selectedFerrersDefectEdgeTopBudget k ≤
        2 * (5373952 * Real.sqrt 2032129 + 1) /
          (selectedFerrersPaperLambda k *
            Real.sqrt (selectedFerrersPaperLambda k)) := by
  -- the one-sided eigenvalue window for the decay supplier
  have hθ1 : ∀ᶠ k in Filter.atTop,
      mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) ≤ Cθ * ((k + 2 : ℕ) : ℝ) ∧
        mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) ≤ Cθ * ((k + 2 : ℕ) : ℝ) := by
    filter_upwards [hθ] with k hk
    exact ⟨(abs_le.1 hk.1).2, (abs_le.1 hk.2).2⟩
  have houter := selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates
    C0 C4 Cθ hC0 hC4 hmode hθ1
  obtain ⟨Cdummy, _, houter_ev⟩ := houter
  have hevχ : ∀ᶠ k : ℕ in Filter.atTop,
      Cχ ≤ ((k + 2 : ℕ) : ℝ) := by
    have := Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) Cχ
    filter_upwards [this] with k hk
    push_cast
    push_cast at hk
    linarith
  have hevθ : ∀ᶠ k : ℕ in Filter.atTop,
      Cθ ≤ ((k + 2 : ℕ) : ℝ) := by
    have := Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) Cθ
    filter_upwards [this] with k hk
    push_cast
    push_cast at hk
    linarith
  filter_upwards [houter_ev, hchi, hθ, hevχ, hevθ, etc_exp_dominates]
    with k houterk hchik hθk hχk hθsk hexpk
  apply etc_budget_bound k _ (by positivity)
  -- the pointwise strict-top defect-derivative rate
  intro y hy
  set lam := selectedFerrersPaperLambda k with hlamdef
  have hmR : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hlam0 : (0 : ℝ) < lam := by
    rw [hlamdef, selectedFerrersPaperLambda]
    exact Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef, selectedFerrersPaperLambda]
    apply Real.one_le_sqrt.mpr
    push_cast
    linarith
  have hsq : lam ^ 2 = ((k + 2 : ℕ) : ℝ) := by
    rw [hlamdef, selectedFerrersPaperLambda]
    exact Real.sq_sqrt hmR.le
  have hyIoo : y ∈ Ioo (0 : ℝ) lam :=
    ⟨by nlinarith [hy.1, hlam0], hy.2⟩
  rw [etc_derivDfn_eq k (by rw [← hlamdef]; exact hyIoo)]
  -- the eigenvalue windows for the two exact modes
  have hlam4 : ∀ Λv : ℝ, |Λv + mode4JacobiG (k + 2)| ≤
      Cθ * ((k + 2 : ℕ) : ℝ) →
      |Λv + mode4JacobiG (k + 2)| ≤ (Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 4 := by
    intro Λv hv
    have hsq4 : (Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 4 =
        ((k + 2 : ℕ) : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hmR.le]
    rw [hsq4]
    calc |Λv + mode4JacobiG (k + 2)| ≤ Cθ * ((k + 2 : ℕ) : ℝ) := hv
      _ ≤ ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hθsk hmR.le
      _ = ((k + 2 : ℕ) : ℝ) ^ 2 := by ring
  have hG : (0 : ℝ) < mode4JacobiG (k + 2) := by
    rw [mode4JacobiG]; positivity
  have hspec := selectedFerrersPreAnchorPair_spec k
  set B65 : ℝ := 65536 * Real.sqrt 2032129 with hB65
  have hB65pos : (0 : ℝ) < B65 := by rw [hB65]; positivity
  -- per-mode data
  have hN0 : (0 : ℝ) <
      (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :=
    (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization_pos
      (by omega)
  have hN4 : (0 : ℝ) <
      (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :=
    (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization_pos
      (by omega)
  have ha0 : (0 : ℝ) < ‖centerAnchorScalarZero k‖ :=
    norm_pos_iff.mpr (centerAnchorScalarZero_ne k)
  have ha4 : (0 : ℝ) < ‖centerAnchorScalarFour k‖ :=
    norm_pos_iff.mpr (centerAnchorScalarFour_ne k)
  -- raw outer value bounds from the semantically ratified decay supplier
  have hlameq : lam = Real.sqrt ((k + 2 : ℕ) : ℝ) := by
    rw [hlamdef, selectedFerrersPaperLambda]
  have hraw0 : ∀ t ∈ Icc (lam / 2) lam,
      (‖centerAnchorScalarZero k‖ /
        (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization) *
      |mode4PhysicalFerrersSeries (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients t| ≤
      B65 / lam ^ 6 := by
    intro t ht
    have htIcc : t ∈ Icc (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
        (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
      constructor
      · rw [← hlameq]
        nlinarith [ht.1, hlam0]
      · rw [← hlameq]
        exact ht.2
    have hout := (houterk t ht).1
    rw [hspec.2.1] at hout
    rw [etc_anchored_norm (selectedFerrersPreAnchorSolution0 k)
      (by omega) _ htIcc] at hout
    rw [hB65]
    exact hout
  have hraw4 : ∀ t ∈ Icc (lam / 2) lam,
      (‖centerAnchorScalarFour k‖ /
        (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization) *
      |mode4PhysicalFerrersSeries (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients t| ≤
      B65 / lam ^ 6 := by
    intro t ht
    have htIcc : t ∈ Icc (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
        (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
      constructor
      · rw [← hlameq]
        nlinarith [ht.1, hlam0]
      · rw [← hlameq]
        exact ht.2
    have hout := (houterk t ht).2
    rw [hspec.2.2.1] at hout
    rw [etc_anchored_norm (selectedFerrersPreAnchorSolution4 k)
      (by omega) _ htIcc] at hout
    rw [hB65]
    exact hout
  -- flux derivative bounds for the raw series
  set A0 : ℝ := B65 *
    (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization /
      ‖centerAnchorScalarZero k‖ with hA0
  set A4 : ℝ := B65 *
    (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization /
      ‖centerAnchorScalarFour k‖ with hA4
  have hA0pos : (0 : ℝ) < A0 := by rw [hA0]; positivity
  have hA4pos : (0 : ℝ) < A4 := by rw [hA4]; positivity
  have hflux0 := sturm_outer_flux_derivative_bound
    (selectedFerrersPreAnchorSolution0 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k)
    (mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three _ hG 0
      (by norm_num)).le
    (hlam4 _ hθk.1) A0 hA0pos.le
    (by
      intro t ht
      rw [← hlameq] at ht
      have h := hraw0 t ht
      rw [← hlameq]
      have h2 := mul_le_mul_of_nonneg_left h
        (show (0:ℝ) ≤ (selectedFerrersPreAnchorSolution0
          k).physicalL2Normalization / ‖centerAnchorScalarZero k‖ by
            positivity)
      have hid : ((selectedFerrersPreAnchorSolution0
          k).physicalL2Normalization / ‖centerAnchorScalarZero k‖) *
          ((‖centerAnchorScalarZero k‖ /
            (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization) *
          |mode4PhysicalFerrersSeries (k + 2)
            (selectedFerrersPreAnchorSolution0 k).coefficients t|) =
          |mode4PhysicalFerrersSeries (k + 2)
            (selectedFerrersPreAnchorSolution0 k).coefficients t| := by
        field_simp
      have hid2 : ((selectedFerrersPreAnchorSolution0
          k).physicalL2Normalization / ‖centerAnchorScalarZero k‖) *
          (B65 / lam ^ 6) = A0 / lam ^ 6 := by
        rw [hA0]
        field_simp
      rw [hid, hid2] at h2
      exact h2)
  have hflux4 := sturm_outer_flux_derivative_bound
    (selectedFerrersPreAnchorSolution4 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k)
    (mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three _ hG 2
      (by norm_num)).le
    (hlam4 _ hθk.2) A4 hA4pos.le
    (by
      intro t ht
      rw [← hlameq] at ht
      have h := hraw4 t ht
      rw [← hlameq]
      have h2 := mul_le_mul_of_nonneg_left h
        (show (0:ℝ) ≤ (selectedFerrersPreAnchorSolution4
          k).physicalL2Normalization / ‖centerAnchorScalarFour k‖ by
            positivity)
      have hid : ((selectedFerrersPreAnchorSolution4
          k).physicalL2Normalization / ‖centerAnchorScalarFour k‖) *
          ((‖centerAnchorScalarFour k‖ /
            (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization) *
          |mode4PhysicalFerrersSeries (k + 2)
            (selectedFerrersPreAnchorSolution4 k).coefficients t|) =
          |mode4PhysicalFerrersSeries (k + 2)
            (selectedFerrersPreAnchorSolution4 k).coefficients t| := by
        field_simp
      have hid2 : ((selectedFerrersPreAnchorSolution4
          k).physicalL2Normalization / ‖centerAnchorScalarFour k‖) *
          (B65 / lam ^ 6) = A4 / lam ^ 6 := by
        rw [hA4]
        field_simp
      rw [hid, hid2] at h2
      exact h2)
  -- the derivative values at the strict-top point
  have hyIco : y ∈ Ico (Real.sqrt ((k + 2 : ℕ) : ℝ) / 2)
      (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
    constructor
    · rw [← hlameq]; exact hy.1
    · rw [← hlameq]; exact hy.2
  have hd0 := hflux0 y hyIco
  have hd4 := hflux4 y hyIco
  rw [← hlameq] at hd0 hd4
  -- chi bounds
  have hχ0 : |(selectedFerrersPreAnchorPair k).chi0| ≤ 2 := by
    have h1 := hchik.1
    have h2 : Cχ / lam ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      rw [hsq]
      exact hχk
    calc |(selectedFerrersPreAnchorPair k).chi0| =
        |(1 : ℝ) - (1 - (selectedFerrersPreAnchorPair k).chi0)| := by
          congr 1
          ring
      _ ≤ |(1 : ℝ)| + |1 - (selectedFerrersPreAnchorPair k).chi0| :=
          abs_sub _ _
      _ ≤ 1 + Cχ / lam ^ 2 := by
          rw [abs_one]
          linarith [h1]
      _ ≤ 2 := by linarith [h2]
  have hχ2 : |(selectedFerrersPreAnchorPair k).chi2| ≤ 2 := by
    have h1 := hchik.2
    have h2 : Cχ / lam ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      rw [hsq]
      exact hχk
    calc |(selectedFerrersPreAnchorPair k).chi2| =
        |(1 : ℝ) - (1 - (selectedFerrersPreAnchorPair k).chi2)| := by
          congr 1
          ring
      _ ≤ |(1 : ℝ)| + |1 - (selectedFerrersPreAnchorPair k).chi2| :=
          abs_sub _ _
      _ ≤ 1 + Cχ / lam ^ 2 := by
          rw [abs_one]
          linarith [h1]
      _ ≤ 2 := by linarith [h2]
  -- the H-part
  have hH := etc_Hderiv_outer_bound lam hlam1 y ⟨hy.1, hy.2.le⟩
  have hHsmall : 4 * (384 * lam ^ 5 * Real.exp (-Real.pi * lam ^ 2 / 4)) ≤
      1 / lam ^ 3 := by
    have hE := hexpk
    have hepos := Real.exp_pos (-Real.pi * lam ^ 2 / 4)
    rw [le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 3)]
    have hkey : 1536 * lam ^ 8 * Real.exp (-Real.pi * lam ^ 2 / 4) ≤ 1 := by
      have h2 := mul_le_mul_of_nonneg_right hE hepos.le
      rw [← Real.exp_add] at h2
      rw [show Real.pi * lam ^ 2 / 4 + -Real.pi * lam ^ 2 / 4 = 0 from
        by ring, Real.exp_zero] at h2
      linarith [h2]
    nlinarith [hkey]
  -- assemble the norm chain
  rw [etc_Dexpr]
  have hnorm4 : ‖((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
      (centerAnchorScalarFour k *
        (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution4 k).coefficients y : ℝ) : ℂ) /
        (((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
          ℝ) : ℂ)))‖ ≤ 2 * (41 * B65 / lam ^ 3) := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN4]
    calc |(selectedFerrersPreAnchorPair k).chi0| *
        (‖centerAnchorScalarFour k‖ *
          (|mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution4 k).coefficients y| /
          (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization)) ≤
        2 * (‖centerAnchorScalarFour k‖ *
          ((41 * A4 / lam ^ 3) /
          (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization)) := by
          apply mul_le_mul hχ0 _ (by positivity) (by norm_num)
          apply mul_le_mul_of_nonneg_left _ ha4.le
          exact div_le_div_of_nonneg_right hd4 hN4.le
      _ = 2 * (41 * B65 / lam ^ 3) := by
          rw [hA4]
          field_simp
  have hnorm0 : ‖(3 : ℂ) * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
      (centerAnchorScalarZero k *
        (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution0 k).coefficients y : ℝ) : ℂ) /
        (((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :
          ℝ) : ℂ)))‖ ≤ 6 * (41 * B65 / lam ^ 3) := by
    rw [norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN0]
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [h3]
    calc 3 * |(selectedFerrersPreAnchorPair k).chi2| *
        (‖centerAnchorScalarZero k‖ *
          (|mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution0 k).coefficients y| /
          (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization)) ≤
        (3 * 2) * (‖centerAnchorScalarZero k‖ *
          ((41 * A0 / lam ^ 3) /
          (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization)) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left hχ2 (by norm_num)
          · apply mul_le_mul_of_nonneg_left _ ha0.le
            exact div_le_div_of_nonneg_right hd0 hN0.le
          · positivity
          · positivity
      _ = 6 * (41 * B65 / lam ^ 3) := by
          rw [hA0]
          field_simp
          norm_num
  have hHn : ‖(4 : ℂ) * (((-(2 * Real.pi ^ 3) * y ^ 5 +
      7 * Real.pi ^ 2 * y ^ 3 - 3 * Real.pi * y) *
      Real.exp (-Real.pi * y ^ 2) : ℝ) : ℂ)‖ ≤ 1 / lam ^ 3 := by
    rw [norm_mul]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    calc 4 * ‖(((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
        3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2) : ℝ) : ℂ)‖ ≤
        4 * (384 * lam ^ 5 * Real.exp (-Real.pi * lam ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left hH (by norm_num)
      _ ≤ 1 / lam ^ 3 := hHsmall
  calc ‖(1 / 4 : ℂ) *
      (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
        (centerAnchorScalarFour k *
          (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution4 k).coefficients y : ℝ) : ℂ) /
          (((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
            ℝ) : ℂ))) -
      3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
        (centerAnchorScalarZero k *
          (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution0 k).coefficients y : ℝ) : ℂ) /
          (((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :
            ℝ) : ℂ)))) -
      (4 : ℂ) * (((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
        3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2) : ℝ) : ℂ)‖ ≤
      ‖(1 / 4 : ℂ) *
        (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (centerAnchorScalarFour k *
            (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
              (selectedFerrersPreAnchorSolution4 k).coefficients y : ℝ) : ℂ) /
            (((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
              ℝ) : ℂ))) -
        3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (centerAnchorScalarZero k *
            (((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
              (selectedFerrersPreAnchorSolution0 k).coefficients y : ℝ) : ℂ) /
            (((selectedFerrersPreAnchorSolution0
              k).physicalL2Normalization : ℝ) : ℂ))))‖ +
      ‖(4 : ℂ) * (((-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
        3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2) : ℝ) : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ (1 / 4) * (2 * (41 * B65 / lam ^ 3) + 6 * (41 * B65 / lam ^ 3)) +
        1 / lam ^ 3 := by
        apply add_le_add _ hHn
        rw [norm_mul]
        have hq : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
        rw [hq]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc ‖_ - _‖ ≤ _ + _ := norm_sub_le _ _
          _ ≤ 2 * (41 * B65 / lam ^ 3) + 6 * (41 * B65 / lam ^ 3) :=
              add_le_add hnorm4 hnorm0
    _ = (82 * B65 + 1) / lam ^ 3 := by
        field_simp
        ring
    _ = (5373952 * Real.sqrt 2032129 + 1) / lam ^ 3 := by
        rw [hB65]
        ring_nf


/--
**W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE** (verdict
ed7c8f7d).  The squared strict-top defect budget over the physical
bandwidth tends to zero on the selected schedule: the derivative wall's
last named gap closes at rate `O(λ⁻⁴)`.
-/
theorem selectedFerrersDefectEdgeTopBudget_bandwidthNegligible_of_modeChiThetaRates
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
    (hmode :
      ∀ᶠ k in Filter.atTop,
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
    (hchi :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ :
      ∀ᶠ k in Filter.atTop,
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
            mode4JacobiG (k + 2)| ≤ Cθ * ((k + 2 : ℕ) : ℝ) ∧
          |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
            mode4JacobiG (k + 2)| ≤ Cθ * ((k + 2 : ℕ) : ℝ)) :
    Filter.Tendsto (fun k : ℕ =>
      (selectedFerrersDefectEdgeTopBudget k) ^ 2 *
        (physicalFourierBandwidth (selectedFerrersPreAnchorIndex k))⁻¹)
      Filter.atTop (𝓝 0) := by
  set CB : ℝ := 2 * (5373952 * Real.sqrt 2032129 + 1) with hCB
  have hCB0 : (0 : ℝ) < CB := by rw [hCB]; positivity
  have hrate := selectedFerrersDefectEdgeTopBudget_bound_of_modeChiThetaRates
    C0 C4 Cχ Cθ hC0 hC4 hmode hchi hθ
  apply squeeze_zero'
    (g := fun k : ℕ => (CB ^ 2 / Real.pi) * ((((k + 2 : ℕ) : ℝ)) ^ 2)⁻¹)
  · filter_upwards with k
    have hbw : (0 : ℝ) < physicalFourierBandwidth
        (selectedFerrersPreAnchorIndex k) := by
      rw [physicalFourierBandwidth]
      have hL : (0 : ℝ) < L_m (selectedFerrersPreAnchorIndex k) := by
        rw [L_m, logLength]
        apply Real.log_pos
        have : (2 : ℕ) ≤ k + 2 := by omega
        exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) this
      positivity
    positivity
  · filter_upwards [hrate] with k hk
    set lam := selectedFerrersPaperLambda k with hlamdef
    have hmR : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hlam0 : (0 : ℝ) < lam := by
      rw [hlamdef, selectedFerrersPaperLambda]
      exact Real.sqrt_pos.2 hmR
    have hlam1 : (1 : ℝ) ≤ lam := by
      rw [hlamdef, selectedFerrersPaperLambda]
      apply Real.one_le_sqrt.mpr
      push_cast
      linarith
    have hsq : lam ^ 2 = ((k + 2 : ℕ) : ℝ) := by
      rw [hlamdef, selectedFerrersPaperLambda]
      exact Real.sq_sqrt hmR.le
    have hss : Real.sqrt lam * Real.sqrt lam = lam :=
      Real.mul_self_sqrt hlam0.le
    have hbudget_nn : (0 : ℝ) ≤ selectedFerrersDefectEdgeTopBudget k := by
      rw [selectedFerrersDefectEdgeTopBudget]
      apply intervalIntegral.integral_nonneg
      · apply Real.log_nonneg
        have : (1 : ℕ) ≤ k + 2 := by omega
        exact_mod_cast this
      · intro x _
        positivity
    -- bandwidth computation on the selected index
    have hLval : L_m (selectedFerrersPreAnchorIndex k) =
        Real.log ((k + 2 : ℕ) : ℝ) := by
      rw [L_m, logLength, selectedFerrersPreAnchorIndex]
    have hNval : ((selectedFerrersPreAnchorIndex k).N + 1 : ℕ) = k + 3 := by
      rw [selectedFerrersPreAnchorIndex]
    have hlog_pos : (0 : ℝ) < Real.log ((k + 2 : ℕ) : ℝ) := by
      apply Real.log_pos
      have : (2 : ℕ) ≤ k + 2 := by omega
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) this
    have hbw_inv : (physicalFourierBandwidth
        (selectedFerrersPreAnchorIndex k))⁻¹ =
        Real.log ((k + 2 : ℕ) : ℝ) / (2 * Real.pi * ((k + 3 : ℕ) : ℝ)) := by
      rw [physicalFourierBandwidth, hLval, hNval]
      rw [inv_div]
    -- the log is at most 2λ
    have hlog_le : Real.log ((k + 2 : ℕ) : ℝ) ≤ 2 * lam := by
      have h1 : Real.log ((k + 2 : ℕ) : ℝ) = 2 * Real.log lam := by
        rw [← hsq]
        rw [show lam ^ 2 = lam * lam by ring]
        rw [Real.log_mul hlam0.ne' hlam0.ne']
        ring
      rw [h1]
      have h2 := Real.log_le_sub_one_of_pos hlam0
      linarith
    -- assemble the squeeze bound
    have hratio : (selectedFerrersDefectEdgeTopBudget k) ^ 2 *
        (physicalFourierBandwidth (selectedFerrersPreAnchorIndex k))⁻¹ ≤
        (CB ^ 2 / Real.pi) * (((k + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
      rw [hbw_inv]
      have hsq_budget : (selectedFerrersDefectEdgeTopBudget k) ^ 2 ≤
          (CB / (lam * Real.sqrt lam)) ^ 2 := by
        apply pow_le_pow_left₀ hbudget_nn
        rw [hCB]
        exact hk
      have hb2 : (CB / (lam * Real.sqrt lam)) ^ 2 =
          CB ^ 2 / (lam ^ 2 * lam) := by
        have hmm : (lam * Real.sqrt lam) ^ 2 = lam ^ 2 * lam := by
          rw [mul_pow, Real.sq_sqrt hlam0.le]
        rw [div_pow, hmm]
      have hk3 : (0 : ℝ) < ((k + 3 : ℕ) : ℝ) := by positivity
      calc (selectedFerrersDefectEdgeTopBudget k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ) /
            (2 * Real.pi * ((k + 3 : ℕ) : ℝ))) ≤
          (CB ^ 2 / (lam ^ 2 * lam)) *
            ((2 * lam) / (2 * Real.pi * ((k + 3 : ℕ) : ℝ))) := by
            apply mul_le_mul
            · rw [← hb2]; exact hsq_budget
            · exact div_le_div_of_nonneg_right hlog_le (by positivity)
            · positivity
            · positivity
        _ = CB ^ 2 / (Real.pi * lam ^ 2 * ((k + 3 : ℕ) : ℝ)) := by
            field_simp
        _ ≤ (CB ^ 2 / Real.pi) * (((k + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
            rw [hsq]
            rw [show (CB ^ 2 / Real.pi) * ((((k + 2 : ℕ) : ℝ)) ^ 2)⁻¹ =
              CB ^ 2 / (Real.pi * ((k + 2 : ℕ) : ℝ) ^ 2) from by
                field_simp]
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            have hle : ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by
              push_cast
              linarith
            nlinarith [mul_le_mul_of_nonneg_left hle
              (show (0:ℝ) ≤ Real.pi * ((k + 2 : ℕ) : ℝ) by positivity)]
    exact hratio
  · have h0 : Filter.Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have := tendsto_natCast_atTop_atTop (R := ℝ)
      apply Filter.tendsto_atTop_mono _ this
      intro k
      push_cast
      linarith
    have h1 : Filter.Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ 2))
        Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h0
    have h2 : Filter.Tendsto (fun k : ℕ => ((((k + 2 : ℕ) : ℝ) ^ 2))⁻¹)
        Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (CB ^ 2 / Real.pi)
    simpa using h3


#print axioms selectedFerrersLemma73SourcePacket_eq_anchored_combination
#print axioms four_mul_explicitCCMLimitH_eq_cylinder
#print axioms edgeTop_boundary_trichotomy
#print axioms edgeTop_strictTop_unique
#print axioms edgeTop_strictTop_outer
#print axioms sturm_outer_flux_derivative_bound
#print axioms selectedFerrersDefectEdgeTopBudget_bound_of_modeChiThetaRates
#print axioms selectedFerrersDefectEdgeTopBudget_bandwidthNegligible_of_modeChiThetaRates

end Q3.RouteB.D0Pstar
