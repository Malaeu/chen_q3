import Q3.Basic.Defs

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3

/-!
# Exact Weil square-class interface

This file is an interface layer only.  It records the corrected
Hermitian-square test class needed by Weil positivity and deliberately does not
claim density, positivity, or RH.

The broad legacy exports `Weil_cone` and `W_K` in `Q3.Basic.Defs` are
pointwise-nonnegative cones.  They are useful for background lemmas but are not
the exact Weil-square target.
-/

/-- Reflected conjugate involution: `g^sharp(x) = conjugate(g(-x))`. -/
def sharp (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => conj (g (-x))

/-- Complex Hermitian square before taking the real-valued test-function view. -/
noncomputable def hermitianSquareC (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ y : ℝ, g y * sharp g (x - y)

/-- Real-valued test function associated to a Hermitian square. -/
noncomputable def hermitianSquare (g : ℝ → ℂ) : ℝ → ℝ :=
  fun x => (hermitianSquareC g x).re

/-- Exact Hermitian-square structure for a real-valued test function. -/
def IsHermitianSquareOf (Φ : ℝ → ℝ) (g : ℝ → ℂ) : Prop :=
  (∀ x, (hermitianSquareC g x).im = 0) ∧ Φ = hermitianSquare g

/-- The additive boundary transform used to state the Weil boundary-null
conditions.  This is the `H`-side interface; downstream normalization must be
matched with the exact T0/explicit-formula convention before consumption. -/
noncomputable def boundaryTransform (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, g x * Complex.exp (s * (x : ℂ))

/-- The boundary-side `H` transform used in the square-class interface. -/
abbrev WeilBoundaryH (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  boundaryTransform g s

/-- Boundary-null conditions at the two pole-cancelling boundary values. -/
def HasWeilBoundaryNull (g : ℝ → ℂ) : Prop :=
  WeilBoundaryH g (1 / 2 : ℂ) = 0 ∧
    WeilBoundaryH g (-(1 / 2 : ℂ)) = 0

/-- Smooth compactly supported generator condition for the square class. -/
def SmoothCompactGenerator (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ g ∧ HasCompactSupport g

/-- Explicit compact support condition for the produced Hermitian square. -/
def SupportedInWindow (K : ℝ) (Φ : ℝ → ℝ) : Prop :=
  Function.support Φ ⊆ Set.Icc (-K) K

/-- A witness that `Φ` is an admissible compactly supported Weil Hermitian
square in the window `[-K,K]`. -/
structure WeilSquareWitness (K : ℝ) (Φ : ℝ → ℝ) where
  g : ℝ → ℂ
  smooth_compact_generator : SmoothCompactGenerator g
  square_structure : IsHermitianSquareOf Φ g
  square_support : SupportedInWindow K Φ
  boundary_null : HasWeilBoundaryNull g

/-- Corrected local Weil square class. -/
def W_sq_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | Nonempty (WeilSquareWitness K Φ)}

/-- Corrected global Weil square class, as a union over compact windows. -/
def W_sq : Set (ℝ → ℝ) :=
  {Φ | ∃ K > 0, Φ ∈ W_sq_K K}

/-- Name the Weil functional on the corrected square interface. -/
abbrev WeilForm (Φ : ℝ → ℝ) : ℝ :=
  Q Φ

/-- Uniform convergence on the compact window `[-K,K]`.

This is only the topology selected for the first continuity interface; the
actual continuity theorem is not asserted here. -/
def UniformOnWindowTendsto (K : ℝ) (Φn : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc (-K) K,
    |Φn n x - Φ x| < ε

/-- Statement shape for continuity of the Weil form on the corrected local
square class.  This is a proposition, not a claimed theorem. -/
def WeilFormContinuous (K : ℝ) : Prop :=
  ∀ (Φn : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ),
    (∀ n, Φn n ∈ W_sq_K K) →
      Φ ∈ W_sq_K K →
        UniformOnWindowTendsto K Φn Φ →
          Filter.Tendsto (fun n => WeilForm (Φn n)) Filter.atTop (nhds (WeilForm Φ))

/-- Exact Weil criterion statement over the corrected Hermitian-square class.

This is a proposition recording the intended external criterion.  It is not
used to prove RH here. -/
def ExactWeilCriterion : Prop :=
  RH ↔ ∀ Φ ∈ W_sq, 0 ≤ WeilForm Φ

#check sharp
#check hermitianSquareC
#check hermitianSquare
#check IsHermitianSquareOf
#check boundaryTransform
#check WeilBoundaryH
#check HasWeilBoundaryNull
#check SmoothCompactGenerator
#check SupportedInWindow
#check WeilSquareWitness
#check W_sq_K
#check W_sq
#check WeilForm
#check UniformOnWindowTendsto
#check WeilFormContinuous
#check ExactWeilCriterion

end Q3

end
