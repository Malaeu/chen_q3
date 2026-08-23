import Q3.Proofs.RouteB.G6N1SelectedFerrersClosedSubstripMellinConvergence
import Q3.Proofs.RouteB.D0CriticalStripCompactBound

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# L73.8 — the conditional selected Ferrers CCM Lemma 7.3 pre-anchor port

Floor `L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL` of
verdict `6e10d992`.

The **conditional port constructor**: given the exact existing mode and chi
rate contracts, it produces an actual inhabitant of
`CCMLemma73PreAnchorPort selectedFerrersPreAnchorData`.

The declaration is deliberately conditional.  The source tree proves the
selected closed-substrip convergence (L73.7) only from the explicit `hmode`
and `hχ` rate inputs; an unqualified global port value would silently assert
that the external Satz-9 and Fuchs inputs are already discharged.  A
structure field is not a place to hide unresolved analytic hypotheses, so
the weakest correct statement is this constructor: supply the rate
contracts, receive the port.  No additional analytic assumption is
introduced anywhere.

The topological content is the compact-local promotion: every compact
subset of the open centered critical strip lies inside one strict closed
substrip (`D0CriticalStripCompactBound`), and on each such substrip the
L73.7 uniform theorem applies.  The private plant records that no single
fixed closed substrip contains the whole open strip, so the promotion is
genuinely per-compact and cannot be collapsed to one `σ`.

Deliberately NOT here: the cofinal source shell bind, Theorem 5.10, H2a,
H2b, any roof.

LEDGER:
  CLOSES: [CCM_LEMMA_7_3_PREANCHOR_PORT_FROM_MODE_AND_CHI_RATES]
  OPENS:  []
-/

/-! ## The mandatory plant -/

/-- **The plant** (verbatim from the verdict).  For every fixed
`0 ≤ σ < 1/2` the open centered strip contains a point strictly beyond the
closed substrip `|z.im| ≤ σ`.  Compact-local promotion therefore cannot be
replaced by one fixed closed substrip for the entire open strip. -/
private theorem openStrip_not_contained_in_fixed_closedSubstrip_plant
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    ∃ z : ℂ, z ∈ centeredCriticalStrip ∧ σ < |z.im| := by
  let y : ℝ := (σ + 1 / 2) / 2
  have hσy : σ < y := by
    dsimp [y]
    linarith
  have hyhalf : y < 1 / 2 := by
    dsimp [y]
    linarith
  have hy0 : 0 ≤ y := le_trans hσ0 hσy.le
  refine ⟨(⟨0, y⟩ : ℂ), ?_, ?_⟩
  · change |y| < 1 / 2
    rw [abs_of_nonneg hy0]
    exact hyhalf
  · change σ < |y|
    rw [abs_of_nonneg hy0]
    exact hσy

/-! ## The conditional port constructor -/

/-- **L73.8.**  The conditional selected Ferrers pre-anchor port: from the
exact existing mode and chi rate contracts, an inhabitant of
`CCMLemma73PreAnchorPort selectedFerrersPreAnchorData`.  The source scale is
the existing factor-four scale, its nonvanishing is the existing supplier,
and the convergence field is the L73.7 closed-substrip theorem promoted to
local uniform convergence through the compact-substrip helper.  The exact
data record, schedule, pair, scale, coordinate and target are untouched. -/
noncomputable def selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
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
            ((parabolicCylinderD 0
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    CCMLemma73PreAnchorPort selectedFerrersPreAnchorData where
  sourceScale := selectedFerrersLemma73SourceScale
  sourceScale_ne := selectedFerrersLemma73SourceScale_ne
  convergence := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
      CanonicalRHRoute.isOpen_centeredCriticalStrip]
    intro K hKsub hK
    obtain ⟨σ, hσ0, hσ, hKσ⟩ :=
      compact_subset_centeredCriticalStrip_contained_in_closed_substrip
        hK hKsub
    have hclosed :=
      selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates
        σ C0 C4 Cχ hσ0 hσ hC0 hC4 hCχ hmode hχ
    have hKconv : TendstoUniformlyOn
        (fun k z =>
          selectedFerrersLemma73SourceScale k *
            preAnchorGwinTransformCoordinate
              (selectedFerrersPreAnchorIndex k)
              (prolateCombination (selectedFerrersPreAnchorPair k)) z)
        centeredXi Filter.atTop K := by
      rw [Metric.tendstoUniformlyOn_iff] at hclosed ⊢
      intro ε hε
      filter_upwards [hclosed ε hε] with k hk
      intro z hz
      exact hk z (hKσ z hz)
    simpa only [selectedFerrersPreAnchorData_index,
      selectedFerrersPreAnchorData_pair] using hKconv

#print axioms selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates

end Q3.RouteB.D0Pstar

end
