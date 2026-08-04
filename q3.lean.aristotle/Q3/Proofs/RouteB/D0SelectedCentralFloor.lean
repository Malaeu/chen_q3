import Q3.Proofs.RouteB.D0PostAnchorMontel
import Q3.Proofs.RouteB.D0AnchorFloor

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- Exact selected-sequence source data for a single uniform relative central
mass floor.  The positive constant is outside the quantifier over the selected
index and every dependent carrier is literally `D.parent (D.extract k)`. -/
structure SelectedAnchorRatioData
    (D : CanonicalData) where
  delta : ℝ
  delta_pos : 0 < delta

  hTrial : (k : ℕ) → ℝ → ℂ

  hEStar :
    ∀ k,
      MemLp
        (E_star (hTrial k)) 2
        (dStar.restrict
          (I_m (D.parent (D.extract k)).1))

  bind :
    ∀ k,
      ∀ hTrialNonzero :
        TrialNonzero
          (D.parent (D.extract k)).1
          (hTrial k)
          (hEStar k),
      ∀ n : ℤ,
        D.kTrial.kTrial
            (D.parent (D.extract k)).1 n =
          c_n
            (D.parent (D.extract k)).1
            (hTrial k)
            (hEStar k)
            hTrialNonzero n

  mass_pos :
    ∀ k,
      0 <
        Real.sqrt
            (L_m (D.parent (D.extract k)).1) *
          ‖inner ℂ
            (V_n_m (D.parent (D.extract k)).1 0)
            (gTrial_m
              (D.parent (D.extract k)).1
              (hTrial k)
              (hEStar k))‖

  ratio :
    ∀ k,
      delta *
          ‖gTrial_m
            (D.parent (D.extract k)).1
            (hTrial k)
            (hEStar k)‖
        ≤
      Real.sqrt
          (L_m (D.parent (D.extract k)).1) *
        ‖inner ℂ
          (V_n_m (D.parent (D.extract k)).1 0)
          (gTrial_m
            (D.parent (D.extract k)).1
            (hTrial k)
            (hEStar k))‖

/-- Aggregate the existing per-index relative central-mass receiver into the
uniform raw-transform denominator floor required by the post-anchor Montel
gate. -/
theorem selectedCentralFloor_of_anchorRatioData
    (D : CanonicalData)
    (S : SelectedAnchorRatioData D) :
    SelectedCentralFloor D := by
  refine ⟨S.delta, S.delta_pos, ?_⟩
  intro k
  have hpacket :=
    D0AnchorFloorFromUnprojectedMassNormRatio
      D.kTrial
      (D.parent (D.extract k)).1
      (S.hTrial k)
      (S.hEStar k)
      (S.bind k)
      S.delta
      S.delta_pos
      (S.mass_pos k)
      (S.ratio k)
  exact hpacket.2.2.2

#print axioms SelectedAnchorRatioData
#print axioms selectedCentralFloor_of_anchorRatioData

end Q3.RouteB.D0Pstar
