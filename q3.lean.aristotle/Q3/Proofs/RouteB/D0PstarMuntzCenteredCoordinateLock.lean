import Q3.Proofs.RouteB.D0ProlateKTrialSource
import Q3.Proofs.RouteB.MuntzV3.ProlateCombinationReceiver

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# Exact D0 Pstar to Müntz centered-coordinate lock

This module closes only the XW.6 type/orientation discriminator.  It places
the production `rawFplus ... (-z)` coordinate and the Müntz
`Gwin ... (-i*z)` coordinate on the same literal
`canonical.parent (canonical.extract k)` source object supplied by XW.8.

The finite Galerkin coordinate defect is deliberately retained as a named
term.  No theorem below says that it is zero, tends to zero, or supplies
`SlotS2`.
-/

/-- The exact `CentralIndex` consumed by the production selected family. -/
def selectedCentralIndex
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    CentralIndex S.canonical.kTrial :=
  S.canonical.parent (S.canonical.extract k)

/-- The underlying independent `(m,N)` index on the same selected sequence. -/
def selectedPairIndex
    (S : ProlateCanonicalSourceData) (k : ℕ) : PairIndex :=
  (selectedCentralIndex S k).1

/-- The exact source pair stored by XW.8 at the selected production index. -/
def selectedProlatePair
    (S : ProlateCanonicalSourceData) (k : ℕ) : ProlatePair :=
  S.source.pair (selectedPairIndex S k)

/-- The exact two-mode source trial used to construct the selected row. -/
def selectedProlateTrial
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ → ℂ :=
  prolateCombination (selectedProlatePair S k)

/-- The Müntz window coordinate corresponding to the multiplicative Fourier
kernel `u^(-i*z)`: its Mellin exponent is `s = -i*z`. -/
def selectedGwinTransformCoordinate
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  EStarMuntzZeroMassContinuation.Gwin
    (selectedProlateTrial S k)
    (lambda_m (selectedPairIndex S k))
    (-Complex.I * z)

/-- The production D0 coordinate with the source-locked reflection. -/
def selectedRawTransformCoordinate
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  rawFplus S.canonical.kTrial (selectedPairIndex S k) (-z)

/-- The exact positive normalization used inside the selected `kTrial_m_N`.
All carrier and nonzero witnesses are the ones stored by XW.8. -/
def selectedTrialNormalizer
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ :=
  sTrial_m_N
    (selectedPairIndex S k)
    (selectedProlateTrial S k)
    (S.source.eStar_memLp (selectedPairIndex S k))
    (S.source.trialNonzero (selectedPairIndex S k))

/-- The scaled full-window Müntz coordinate before central normalization. -/
def selectedScaledGwinTransformCoordinate
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  (selectedTrialNormalizer S k : ℂ) *
    selectedGwinTransformCoordinate S k z

/-- The exact finite-coordinate defect.  Phase 4A records the difference but
does not identify it with an object-first projection residual or bound it. -/
def selectedGalerkinCoordinateDefect
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  selectedRawTransformCoordinate S k z -
    selectedScaledGwinTransformCoordinate S k z

/-- The production central normalizer on the exact selected index. -/
def selectedCenteringFactor
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℂ :=
  centeredXi 0 /
    rawFplus S.canonical.kTrial (selectedPairIndex S k) 0

/-- The single centered Müntz main coordinate at transform variable `z`.
Its argument convention is `Gwin ... (-i*z)`. -/
def selectedMuntzCenteredTransformCoordinate
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  selectedCenteringFactor S k *
    selectedScaledGwinTransformCoordinate S k z

/-- The same main coordinate in the literal `selectedFamily ... z` variable.
Substituting `-z` into the transform coordinate changes `Gwin(-i*w)` to
`Gwin(i*z)`, exactly as forced by `rawFplus D i z = T_i(kTrial)(-z)`. -/
def selectedMuntzApproximation
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  selectedMuntzCenteredTransformCoordinate S k (-z)

/-- The selected index is literally `parent (extract k)`; no second schedule
is present. -/
@[simp] theorem selectedCentralIndex_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    selectedCentralIndex S k =
      S.canonical.parent (S.canonical.extract k) :=
  rfl

@[simp] theorem selectedPairIndex_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    selectedPairIndex S k =
      (S.canonical.parent (S.canonical.extract k)).1 :=
  rfl

@[simp] theorem selectedProlatePair_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    selectedProlatePair S k =
      S.source.pair
        (S.canonical.parent (S.canonical.extract k)).1 :=
  rfl

@[simp] theorem selectedProlateTrial_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    selectedProlateTrial S k =
      prolateCombination
        (S.source.pair
          (S.canonical.parent (S.canonical.extract k)).1) :=
  rfl

/-- The source pair's stored bandwidth is the production D0 window parameter
at the same selected index. -/
theorem selectedProlatePair_lambda_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    (selectedProlatePair S k).pw.lambda =
      lambda_m (selectedPairIndex S k) := by
  simpa [selectedProlatePair] using
    S.source.lambda_eq (selectedPairIndex S k)

/-- The selected coefficient row is still the exact normalized, projected
source trial at the selected pair index. -/
@[simp] theorem selectedCanonical_kTrial
    (S : ProlateCanonicalSourceData) (k : ℕ) (n : ℤ) :
    S.canonical.kTrial.kTrial (selectedPairIndex S k) n =
      c_n
        (selectedPairIndex S k)
        (selectedProlateTrial S k)
        (S.source.eStar_memLp (selectedPairIndex S k))
        (S.source.trialNonzero (selectedPairIndex S k)) n := by
  unfold selectedProlateTrial selectedProlatePair
  exact S.canonical_kTrial (selectedPairIndex S k) n

/-- Exact sign/orientation expansion of the production selected family. -/
theorem selectedFamily_neg_eq_centeredRawCoordinate
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) :
    selectedFamily (canonicalApproximation S.canonical) k (-z) =
      selectedCenteringFactor S k *
        selectedRawTransformCoordinate S k z :=
  rfl

/-- Algebraic reconstruction retaining the finite-coordinate defect. -/
theorem selectedRawCoordinate_eq_scaledGwin_add_defect
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) :
    selectedRawTransformCoordinate S k z =
      selectedScaledGwinTransformCoordinate S k z +
        selectedGalerkinCoordinateDefect S k z := by
  simp only [selectedGalerkinCoordinateDefect]
  ring

/-- The exact selected-family decomposition in the original family variable.
The second summand is intentionally left open for the Phase-4B projection
residual and compact-open decay proof. -/
theorem selectedFamily_eq_muntzApproximation_add_defect
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) :
    selectedFamily (canonicalApproximation S.canonical) k z =
      selectedMuntzApproximation S k z +
        selectedCenteringFactor S k *
          selectedGalerkinCoordinateDefect S k (-z) := by
  rw [show z = -(-z) by ring]
  rw [selectedFamily_neg_eq_centeredRawCoordinate]
  rw [selectedRawCoordinate_eq_scaledGwin_add_defect]
  simp only [selectedMuntzApproximation,
    selectedMuntzCenteredTransformCoordinate]
  ring_nf

#print axioms selectedProlatePair_lambda_eq
#print axioms selectedCanonical_kTrial
#print axioms selectedFamily_neg_eq_centeredRawCoordinate
#print axioms selectedRawCoordinate_eq_scaledGwin_add_defect
#print axioms selectedFamily_eq_muntzApproximation_add_defect

end Q3.RouteB.D0Pstar
