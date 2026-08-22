import Mathlib
import RequestProject.Defs
import RequestProject.Main

/-!
# The even-only source spectrum package, inhabited

Step two of the integration order fixed by verdict `f414829c`, in the shape
verdict `7c232019` (REQ-R) prescribed: an even-only structure carrying exactly
what the downstream consumers use — the strictly increasing branch, its
regularity, and exhaustiveness — with no odd cargo and no DLMF or project
adapter field. Mixing those into one object was killed as a category failure
when the direct submission was refused; they stay a separate, later
transaction.

The structure is source-pure: every field speaks only of
`RegularEvenSpheroidalEigenvalue`. And it is **inhabited without any axiom**:
the ratified main theorem `spheroidal_even_spectrum` supplies precisely the
four fields, so the constructor below is a proof, not a hole. This is the
supplier the book route was waiting for, at order `m = 0` and fixed parameter.
-/

open Set

/-- The even-only source spectrum package at a fixed parameter.

`evenBranch r` is the `r`-th regular even spheroidal eigenvalue in increasing
order. No odd branch, no DLMF field, no project object. -/
structure BookRegularEvenSpectrumEven (G : ℝ) where
  /-- The ordered even branch. -/
  evenBranch : ℕ → ℝ
  /-- Reality and simplicity, in the form the enumeration lock consumes. -/
  evenBranch_strictMono : StrictMono evenBranch
  /-- Every branch value is a regular even spheroidal eigenvalue. -/
  evenBranch_regular : ∀ r, RegularEvenSpheroidalEigenvalue G (evenBranch r)
  /-- Exhaustiveness: every regular even spheroidal eigenvalue is a branch
  value. This is the direction the reference states with the definite article
  and the paid target could not finish; it is now carried by the ratified
  spectrum theorem. -/
  regular_evenBranch : ∀ Λ, RegularEvenSpheroidalEigenvalue G Λ →
    ∃ r, evenBranch r = Λ

/-- **The inhabitant.**  The ratified spectrum theorem supplies all four
fields: the strictly monotone enumeration whose range is exactly the regular
even spectrum. -/
theorem bookRegularEvenSpectrumEven_exists (G : ℝ) :
    Nonempty (BookRegularEvenSpectrumEven G) := by
  obtain ⟨μ, hmono, hrange⟩ := spheroidal_even_spectrum G
  refine ⟨⟨μ, hmono, ?_, ?_⟩⟩
  · intro r
    have : μ r ∈ range μ := mem_range_self r
    rw [hrange] at this
    exact this
  · intro Λ hΛ
    have : Λ ∈ range μ := by rw [hrange]; exact hΛ
    exact this

#print axioms bookRegularEvenSpectrumEven_exists
