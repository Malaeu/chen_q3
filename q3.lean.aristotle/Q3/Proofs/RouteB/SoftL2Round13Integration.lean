import Mathlib

set_option linter.mathlibStandardSet false

open Filter

noncomputable section

namespace Q3.RouteB

/-- Typed form of the Round-13 quantifier guard.  `S2` is allowed to pass to
the nested sequence `parent (extract k)` only; it cannot introduce an
independent cofinal carrier. -/
structure SoftSameCofinalSubsequence
    (Index : Type*) (H2a S1 : Index → Prop) where
  parent : ℕ → Index
  parentCofinal : Prop
  h2aOnParent : ∀ k, H2a (parent k)
  s1OnParent : ∀ k, S1 (parent k)
  extract : ℕ → ℕ
  extractStrictMono : StrictMono extract

/-- The actual sequence consumed by `S2` after the Round-13 guard. -/
def SoftSameCofinalSubsequence.s2Sequence
    {Index : Type*} {H2a S1 : Index → Prop}
    (G : SoftSameCofinalSubsequence Index H2a S1) : ℕ → Index :=
  fun k => G.parent (G.extract k)

/-- Autocorrelation in an abstract complex Hilbert carrier. -/
def HilbertAutocorrelation
    {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : T → H →L[ℂ] H) (q : H) (t : T) : ℂ :=
  inner ℂ (U t q) q

/-- A typed abstraction of one-dimensional normalized ground-space
uniqueness: any two normalized ground representatives differ by a unit
complex scalar. -/
def SimpleNormalizedGroundPhaseUnique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ground : H → Prop) : Prop :=
  ∀ p q, Ground p → Ground q →
    ∃ c : ℂ, starRingEnd ℂ c * c = 1 ∧ p = c • q

/-- Round-13 derived corollary: a simple normalized complex ground space has
one canonical phase-independent autocorrelation.  Isolation is not consumed
by this short corollary. -/
theorem simpleGround_canonicalPhaseIndependentAutocorrelation
    {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ground : H → Prop) (U : T → H →L[ℂ] H)
    (hsimple : SimpleNormalizedGroundPhaseUnique Ground)
    {p q : H} (hp : Ground p) (hq : Ground q) (t : T) :
    HilbertAutocorrelation U p t = HilbertAutocorrelation U q t := by
  rcases hsimple p q hp hq with ⟨c, hc, rfl⟩
  simp only [HilbertAutocorrelation, map_smul, inner_smul_left,
    inner_smul_right]
  calc
    c * (starRingEnd ℂ c * inner ℂ (U t q) q) =
        (starRingEnd ℂ c * c) * inner ℂ (U t q) q := by ring
    _ = inner ℂ (U t q) q := by rw [hc, one_mul]

/-- The five input slots of the frozen L2.2 contract.  The distribution type
is abstract here: analytic realization in `D'(ℝ)` is a downstream
instantiation, not an assumption hidden in this interface. -/
structure GlobalPositiveDefiniteUniquenessInputs
    (Index Dist : Type*) [SMul ℝ Dist] (A APhi : Dist) where
  diagonal : ℕ → Index
  scale : ℝ
  oneDiagonalSubsequenceOnEveryCompact : Prop
  convergenceInDPrime : Prop
  positiveDefiniteLimit : Prop
  limitingEquationInDPrime : Prop

/-- Typed, deliberately unproved L2.2 statement from Round 13.

The output is exactly `A = c • AΦ` in the eventual distribution instance. -/
def GlobalPositiveDefiniteUniqueness
    (Index Dist : Type*) [SMul ℝ Dist] (A APhi : Dist) : Prop :=
  ∀ input : GlobalPositiveDefiniteUniquenessInputs Index Dist A APhi,
    input.oneDiagonalSubsequenceOnEveryCompact →
    input.convergenceInDPrime →
    input.positiveDefiniteLimit →
    input.limitingEquationInDPrime →
    0 < input.scale →
    A = input.scale • APhi

/-- The two inputs of the optional source-level compactness leaf. -/
structure SourceCompactnessInputs (Source : Type*) where
  family : ℕ → Source
  spatialTightness : Prop
  uniformTranslationContinuity : Prop

/-- Output carrier of the optional source reconstruction leaf. -/
structure SourceCompactnessOutput (Source : Type*) where
  limitSource : Source
  subsequence : ℕ → ℕ
  subsequenceStrictMono : StrictMono subsequence
  strongL2Convergence : Prop
  uniformFullAutocorrelationConvergence : Prop

/-- Optional Round-13 theorem type.  It is not an input to L2.2. -/
def SourceCompactnessToFullAutocorrelation (Source : Type*) : Prop :=
  ∀ input : SourceCompactnessInputs Source,
    input.spatialTightness →
    input.uniformTranslationContinuity →
    Nonempty (SourceCompactnessOutput Source)

#check SoftSameCofinalSubsequence
#check simpleGround_canonicalPhaseIndependentAutocorrelation
#check GlobalPositiveDefiniteUniqueness
#check SourceCompactnessToFullAutocorrelation

#print axioms simpleGround_canonicalPhaseIndependentAutocorrelation

end Q3.RouteB
