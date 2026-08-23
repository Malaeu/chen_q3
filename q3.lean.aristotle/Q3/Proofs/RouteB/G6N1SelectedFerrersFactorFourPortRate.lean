import Q3.Proofs.RouteB.G6N1SelectedFerrersZeroMassCylinderPacket

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.6 — the factor-four port source scale and final packet rate

Floor `F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE` of verdict
`f9623d8b`.

The factor four enters exactly once, and only at the port boundary: the
unscaled literal packet has Mellin transform `(1/4) * centeredXi` (the
REQ-E quarter-centered-Xi normalization audit), so multiplication by four is
the unique fixed port normalization targeting the production `centeredXi`.
It is not a fitted convention: the scale and the target change together,
`selectedFerrersLemma73SourceScale = 4 * selectedFerrersLemma72Scale` against
`4 * explicitCCMLimitH`, and the rate constant scales by the same exact
factor.  The private plant distinguishes omission (`1/4 ≠ 1`), the mandated
single occurrence (`4 * (1/4) = 1`), and duplication (`16 * (1/4) ≠ 1`).

No new analysis: the theorem calls the F72.5 packet rate and multiplies the
pointwise error by four.

LEDGER:
  CLOSES: [F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE,
           F72_6_FACTOR_FOUR_PORT_PACKET_RATE]
  OPENS:  []
-/

/-- **The plant.**  The factor four must occur exactly once: omission leaves
the quarter, duplication overshoots. -/
private theorem factorFour_occurs_exactly_once_plant :
    ((1 : ℂ) / 4 ≠ 1) ∧
      (4 : ℂ) * ((1 : ℂ) / 4) = 1 ∧
      (16 : ℂ) * ((1 : ℂ) / 4) ≠ 1 := by
  norm_num

/-- **The port source scale.**  The factor four enters here and nowhere
else. -/
noncomputable def selectedFerrersLemma73SourceScale (k : ℕ) : ℂ :=
  (4 : ℂ) * selectedFerrersLemma72Scale k

/-- The port scale never vanishes. -/
theorem selectedFerrersLemma73SourceScale_ne (k : ℕ) :
    selectedFerrersLemma73SourceScale k ≠ 0 := by
  rw [selectedFerrersLemma73SourceScale]
  exact mul_ne_zero (by norm_num) (selectedFerrersLemma72Scale_ne k)

/-- **F72.6.**  The mode and chi rates produce the factor-four port packet
rate to `4 * explicitCCMLimitH`, with the a-priori constant `4 * C`. -/
theorem selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
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
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖selectedFerrersLemma73SourceScale k *
              prolateCombination (selectedFerrersPreAnchorPair k) x -
            (4 : ℂ) * explicitCCMLimitH x‖ ≤
              C / (selectedFerrersPaperLambda k) ^ 2 := by
  obtain ⟨C, hC0', hCrate⟩ :=
    selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  refine ⟨4 * C, by linarith, ?_⟩
  filter_upwards [hCrate] with k hk
  intro x hx
  have hinner := hk x hx
  have hport : selectedFerrersLemma73SourceScale k *
      prolateCombination (selectedFerrersPreAnchorPair k) x -
        (4 : ℂ) * explicitCCMLimitH x
      = (4 : ℂ) * (selectedFerrersLemma72Scale k *
          prolateCombination (selectedFerrersPreAnchorPair k) x -
            explicitCCMLimitH x) := by
    rw [selectedFerrersLemma73SourceScale]
    ring
  rw [hport, norm_mul]
  have hnorm4 : ‖(4 : ℂ)‖ = 4 := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  rw [hnorm4]
  calc 4 * ‖selectedFerrersLemma72Scale k *
      prolateCombination (selectedFerrersPreAnchorPair k) x -
        explicitCCMLimitH x‖
      ≤ 4 * (C / (selectedFerrersPaperLambda k) ^ 2) :=
        mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = (4 * C) / (selectedFerrersPaperLambda k) ^ 2 := by ring

#print axioms selectedFerrersLemma73SourceScale_ne
#print axioms selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates

end Q3.RouteB.D0Pstar

end
