import Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate
import Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# L73.3 — the selected Ferrers E-star window main error

Floor `L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR` of verdict `19ee838c`.

Finite-sum assembly over the **dynamic** main count: for `u` in the source
window, the number of active positive dilation indices is exactly
`floor(lambda_k / u)` — every included point `(n+1)*u` stays inside the
certified window `[-lambda_k, lambda_k]`, so the F72.6 pointwise packet rate
applies term by term.  The count is load-bearing (the private plant records
that a one-term bound cannot cover a comb of four); summing over a static
range `n ≤ k+2` instead would overcount near the upper window edge by a
factor of order `lambda_k` and destroy the sharp `u^(-1/2)` behaviour.

The result is the exact CCM Lemma-7.3 main-sum estimate
`sqrt u * (lambda/u) * (C/lambda^2) = C / (lambda * sqrt u)`.

Deliberately NOT here: the infinite Gaussian target tail beyond `lambda_k`
(that is L73.4) and any Mellin integration (L73.5).

LEDGER:
  CLOSES: [SELECTED_FERRERS_ESTAR_FINITE_SUM_ERROR]
  OPENS:  []
-/

/-- **The plant.**  The cardinality factor is load-bearing: a comb of four
unit terms has norm four, not one. -/
private theorem eStarMainSum_cardinalityFactor_plant :
    ‖∑ _n ∈ Finset.range 4, (1 : ℂ)‖ = 4 ∧
      ¬ ‖∑ _n ∈ Finset.range 4, (1 : ℂ)‖ ≤ 1 := by
  norm_num

/-- **The dynamic main count**: the number of positive integers `n` with
`n * u ≤ lambda_k`. -/
noncomputable def selectedFerrersEStarMainCount (k : ℕ) (u : ℝ) : ℕ :=
  Nat.floor (selectedFerrersPaperLambda k / u)

/-- **The E-star window main error**: the `sqrt u`-weighted finite sum of the
scaled-packet-minus-target differences over the active dilation points. -/
noncomputable def selectedFerrersEStarWindowMainError
    (k : ℕ) (u : ℝ) : ℂ :=
  ((Real.sqrt u : ℝ) : ℂ) *
    ∑ n ∈ Finset.range (selectedFerrersEStarMainCount k u),
      (selectedFerrersLemma73SourceScale k *
          prolateCombination (selectedFerrersPreAnchorPair k)
            (((n + 1 : ℕ) : ℝ) * u)
        - (4 : ℂ) *
          explicitCCMLimitH (((n + 1 : ℕ) : ℝ) * u))

/-- **L73.3.**  The mode and chi rates bound the E-star window main error by
`C / (lambda * sqrt u)`, uniformly over the source window, eventually in the
schedule. -/
theorem selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
    (C0 C4 Cχ : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ)
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
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        ∀ u ∈ sourceWindow (selectedFerrersPaperLambda k),
          ‖selectedFerrersEStarWindowMainError k u‖ ≤
            C / (selectedFerrersPaperLambda k * Real.sqrt u) := by
  obtain ⟨C, hCnn, hrate⟩ :=
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  refine ⟨C, hCnn, ?_⟩
  filter_upwards [hrate] with k hk
  intro u hu
  have hlam : 0 < selectedFerrersPaperLambda k := by
    rw [selectedFerrersPaperLambda]
    apply Real.sqrt_pos.mpr
    positivity
  have hu0 : 0 < u := by
    have h1 : (selectedFerrersPaperLambda k)⁻¹ ≤ u := hu.1
    have h2 : 0 < (selectedFerrersPaperLambda k)⁻¹ := by positivity
    linarith
  set s : ℝ := Real.sqrt u with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu0
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
  set M : ℕ := selectedFerrersEStarMainCount k u with hM
  have hMle : (M : ℝ) ≤ selectedFerrersPaperLambda k / u := by
    rw [hM, selectedFerrersEStarMainCount]
    exact Nat.floor_le (by positivity)
  -- every included point stays in the certified window
  have hmem : ∀ n ∈ Finset.range M,
      ((n + 1 : ℕ) : ℝ) * u ∈ Set.Icc (-(selectedFerrersPaperLambda k))
        (selectedFerrersPaperLambda k) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hn1 : ((n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hn
    have hup : ((n + 1 : ℕ) : ℝ) * u ≤ selectedFerrersPaperLambda k := by
      have h1 : ((n + 1 : ℕ) : ℝ) * u ≤ (selectedFerrersPaperLambda k / u) * u :=
        mul_le_mul_of_nonneg_right (le_trans hn1 hMle) hu0.le
      rwa [div_mul_cancel₀ _ hu0.ne'] at h1
    have hlow : -(selectedFerrersPaperLambda k) ≤ ((n + 1 : ℕ) : ℝ) * u := by
      have hpos : 0 ≤ ((n + 1 : ℕ) : ℝ) * u := by positivity
      linarith
    exact ⟨hlow, hup⟩
  -- termwise packet rate and the finite-sum triangle
  have hsum : ‖∑ n ∈ Finset.range M,
      (selectedFerrersLemma73SourceScale k *
          prolateCombination (selectedFerrersPreAnchorPair k)
            (((n + 1 : ℕ) : ℝ) * u)
        - (4 : ℂ) * explicitCCMLimitH (((n + 1 : ℕ) : ℝ) * u))‖
      ≤ (M : ℝ) * (C / (selectedFerrersPaperLambda k) ^ 2) := by
    calc ‖∑ n ∈ Finset.range M, _‖
        ≤ ∑ n ∈ Finset.range M,
          ‖selectedFerrersLemma73SourceScale k *
              prolateCombination (selectedFerrersPreAnchorPair k)
                (((n + 1 : ℕ) : ℝ) * u)
            - (4 : ℂ) * explicitCCMLimitH (((n + 1 : ℕ) : ℝ) * u)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range M, (C / (selectedFerrersPaperLambda k) ^ 2) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hk (((n + 1 : ℕ) : ℝ) * u) (hmem n hn)
      _ = (M : ℝ) * (C / (selectedFerrersPaperLambda k) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- assemble the sqrt-u weight
  rw [selectedFerrersEStarWindowMainError]
  rw [norm_mul]
  have hsnorm : ‖((Real.sqrt u : ℝ) : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_eq_abs, hsdef,
      abs_of_nonneg (Real.sqrt_nonneg u)]
  rw [hsnorm]
  have hchain : s * ((M : ℝ) * (C / (selectedFerrersPaperLambda k) ^ 2))
      ≤ s * ((selectedFerrersPaperLambda k / u) *
          (C / (selectedFerrersPaperLambda k) ^ 2)) := by
    apply mul_le_mul_of_nonneg_left ?_ hs0.le
    apply mul_le_mul_of_nonneg_right hMle (by positivity)
  have hexact : s * ((selectedFerrersPaperLambda k / u) *
      (C / (selectedFerrersPaperLambda k) ^ 2))
      = C / (selectedFerrersPaperLambda k * s) := by
    rw [← hs2]
    field_simp
  calc s * ‖∑ n ∈ Finset.range M,
      (selectedFerrersLemma73SourceScale k *
          prolateCombination (selectedFerrersPreAnchorPair k)
            (((n + 1 : ℕ) : ℝ) * u)
        - (4 : ℂ) * explicitCCMLimitH (((n + 1 : ℕ) : ℝ) * u))‖
      ≤ s * ((M : ℝ) * (C / (selectedFerrersPaperLambda k) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum hs0.le
    _ ≤ s * ((selectedFerrersPaperLambda k / u) *
          (C / (selectedFerrersPaperLambda k) ^ 2)) := hchain
    _ = C / (selectedFerrersPaperLambda k * s) := hexact
    _ = C / (selectedFerrersPaperLambda k * Real.sqrt u) := by rw [hsdef]

#print axioms selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates

end Q3.RouteB.D0Pstar

end
