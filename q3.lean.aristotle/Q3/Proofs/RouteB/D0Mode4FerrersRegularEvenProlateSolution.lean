import Q3.Proofs.RouteB.D0Mode4FerrersEndpointFlux

/-!
# Goal 058 G3: regular even mode-four Ferrers solution assembly

This file packages the existing source-row conclusions into one public object.
The object remains conditional on a zero of the committed matching function.
It does not identify the series with the ordered degree-four PSWF, rescale it to
the physical window, or supply a finite-Fourier eigenrelation.
-/

namespace Q3.RouteB

/-- The exact properties currently constructed for the dimensionless
mode-four Ferrers series.  Nontriviality is retained at the normalized
coefficient-row boundary; no ordered-mode identification is part of this
structure. -/
structure Mode4FerrersRegularEvenProlateSolution
    (mProject K : ℕ) (Λ : ℝ) where
  coefficients : ℕ → ℝ
  coefficient_zero_pos : 0 < coefficients 0
  coefficients_ne_zero : coefficients ≠ 0
  coefficients_abs_summable : Summable (fun q : ℕ => |coefficients q|)
  coefficients_sq_summable : Summable (fun q : ℕ => (coefficients q) ^ 2)
  normalized :
    HasSum
      (fun q : ℕ =>
        (coefficients q) ^ 2 / (4 * (q : ℝ) + 1))
      1
  recurrence :
    ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal
            (mode4JacobiG mProject) q * coefficients (q - 1) +
        (mode4PSWFLegendreDiagonal
              (mode4JacobiG mProject) q -
            (Λ + mode4JacobiG mProject)) * coefficients q +
        mode4PSWFLegendreSuperdiagonal
            (mode4JacobiG mProject) q * coefficients (q + 1) = 0
  splice_anchor_ne_zero : coefficients (K - 1) ≠ 0
  tail_splice :
    ∀ n : ℕ,
      coefficients (K - 1 + n) =
        coefficients (K - 1) *
          mode4TailCoefficientRow mProject Λ K n
  even : Function.Even (mode4FerrersSeries coefficients)
  continuousOn_closed :
    ContinuousOn
      (mode4FerrersSeries coefficients)
      (Set.Icc (-1 : ℝ) 1)
  contDiffOn_two_open :
    ContDiffOn ℝ 2
      (mode4FerrersSeries coefficients)
      (Set.Ioo (-1 : ℝ) 1)
  ferrersSeries_hasDerivAt_firstDerivativeSeries :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt
        (mode4FerrersSeries coefficients)
        (mode4FerrersFirstDerivativeSeries coefficients x)
        x
  firstDerivativeSeries_hasDerivAt_secondDerivativeSeries :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt
        (mode4FerrersFirstDerivativeSeries coefficients)
        (mode4FerrersSecondDerivativeSeries coefficients x)
        x
  prolateDifferentialEquation :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) *
            mode4FerrersSecondDerivativeSeries coefficients x +
          2 * x *
            mode4FerrersFirstDerivativeSeries coefficients x +
          mode4JacobiG mProject * x ^ 2 *
            mode4FerrersSeries coefficients x =
        (Λ + mode4JacobiG mProject) *
          mode4FerrersSeries coefficients x
  zeroFlux_at_endpoints :
    Filter.Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) *
            mode4FerrersFirstDerivativeSeries coefficients x)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) *
            mode4FerrersFirstDerivativeSeries coefficients x)
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        (nhds (0 : ℝ))

/-- A matching root assembles the normalized nonzero coefficient row, even
closed-window Ferrers series, interior `C²` prolate ODE, and both natural
zero-flux endpoint conditions into one public source object.

This remains conditional on `hroot`; it is not the ordered degree-four
selection theorem. -/
theorem exists_mode4FerrersRegularEvenProlateSolution_of_root
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
    (hroot : mode4RootFunction mProject K Λ = 0) :
    Nonempty (Mode4FerrersRegularEvenProlateSolution mProject K Λ) := by
  obtain ⟨a, ha0, haAbs, haSq, haNorm, haRec, haSpliceNe,
      haSplice, hC2, hODE⟩ :=
    exists_mode4MatchedNormalizedProlateFerrersRow_of_root
      mProject K Λ hm hK hsep hΛ hroot
  have haNe : a ≠ (0 : ℕ → ℝ) := by
    intro hzero
    have hzero0 : a 0 = 0 := by
      rw [hzero]
      rfl
    linarith
  have hEven : Function.Even (mode4FerrersSeries a) :=
    mode4FerrersSeries_even a
  have hContinuous :
      ContinuousOn (mode4FerrersSeries a) (Set.Icc (-1 : ℝ) 1) :=
    mode4FerrersSeries_continuousOn a haAbs
  have haWeightedTwo :
      Summable (fun q : ℕ =>
        (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|) :=
    mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
      mProject K Λ hm hK hsep hΛ a haSplice 2
  have hFirstDerivative :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        HasDerivAt
          (mode4FerrersSeries a)
          (mode4FerrersFirstDerivativeSeries a x)
          x := by
    intro x hx
    let r : ℝ := (|x| + 1) / 2
    have hAbs : |x| < 1 := abs_lt.mpr hx
    have hrPos : 0 < r := by
      dsimp [r]
      nlinarith [abs_nonneg x]
    have hrLt : r < 1 := by
      dsimp [r]
      nlinarith
    have hxInterior : x ∈ Set.Ioo (-r) r := by
      constructor
      · dsimp [r]
        nlinarith [neg_abs_le x]
      · dsimp [r]
        nlinarith [le_abs_self x]
    exact mode4FerrersSeries_hasDerivAt_of_mem_Ioo
      a r hrPos hrLt haAbs haWeightedTwo x hxInterior
  have hSecondDerivative :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        HasDerivAt
          (mode4FerrersFirstDerivativeSeries a)
          (mode4FerrersSecondDerivativeSeries a x)
          x := by
    intro x hx
    let r : ℝ := (|x| + 1) / 2
    have hAbs : |x| < 1 := abs_lt.mpr hx
    have hrPos : 0 < r := by
      dsimp [r]
      nlinarith [abs_nonneg x]
    have hrLt : r < 1 := by
      dsimp [r]
      nlinarith
    have hxInterior : x ∈ Set.Ioo (-r) r := by
      constructor
      · dsimp [r]
        nlinarith [neg_abs_le x]
      · dsimp [r]
        nlinarith [le_abs_self x]
    exact mode4FerrersFirstDerivativeSeries_hasDerivAt_of_mem_Ioo
      a r hrPos hrLt haWeightedTwo x hxInterior
  have hFlux :=
    mode4Ferrers_zeroFlux_at_endpoints_of_tail_splice
      mProject K Λ hm hK hsep hΛ a haSplice
  exact ⟨{
    coefficients := a
    coefficient_zero_pos := ha0
    coefficients_ne_zero := haNe
    coefficients_abs_summable := haAbs
    coefficients_sq_summable := haSq
    normalized := haNorm
    recurrence := haRec
    splice_anchor_ne_zero := haSpliceNe
    tail_splice := haSplice
    even := hEven
    continuousOn_closed := hContinuous
    contDiffOn_two_open := hC2
    ferrersSeries_hasDerivAt_firstDerivativeSeries := hFirstDerivative
    firstDerivativeSeries_hasDerivAt_secondDerivativeSeries := hSecondDerivative
    prolateDifferentialEquation := hODE
    zeroFlux_at_endpoints := hFlux
  }⟩

#print axioms exists_mode4FerrersRegularEvenProlateSolution_of_root

end Q3.RouteB
