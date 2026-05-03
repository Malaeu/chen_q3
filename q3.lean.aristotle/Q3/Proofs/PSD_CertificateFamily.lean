import Q3.Proofs.PSD_PenaltyCertificate

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
Directed finite-certificate family skeleton for the PSD-pd fallback lane.

This file intentionally does not prove analytic exhaustion.  It provides the
formal carrier objects needed after Step 26:

`FinitePenaltyCert` rows can be packaged as certified finite blocks, certified
finite blocks can be organized into a directed family, and a later analytic
closure package can expose global boundary-null positivity.

There are no new axioms and no unfinished proof placeholders here.
-/

/-- A finite test-space label.

The fields are strings because this layer is a theorem-facing registry shell;
the numeric interpretation lives in the interval certificate artifacts and the
future analytic realization layer. -/
structure FiniteSpaceLabel where
  id : String
  L : String
  ell : String
  delta : String
  kSpline : String
deriving Repr

/-- A finite certified block is a finite space label together with concrete
finite matrices and a `FinitePenaltyCert` for those matrices. -/
structure CertifiedFiniteBlock where
  label : FiniteSpaceLabel
  rho : Type
  iota : Type
  [rhoFinite : Fintype rho]
  [iotaFinite : Fintype iota]
  D : Matrix iota iota ℝ
  R : Matrix iota iota ℝ
  Q : Matrix rho iota ℝ
  cert : Q3.Proofs.FinitePenaltyCert D R Q

/-- Abstract refinement relation between finite blocks.

`Refines A B` means that `B` is at least as rich as `A`: for example a larger
window, smaller bump scale, denser grid, or stronger certified coverage.  The
analytic meaning is supplied later. -/
class HasRefinement (α : Type) where
  Refines : α → α → Prop

/-- Abstract directed family of finite certified blocks.

This is only the order-theoretic shell.  It does not assert density or
boundary-null exhaustion. -/
structure DirectedCertFamily where
  Block : Type
  [refinement : HasRefinement Block]
  certBlock : Block → CertifiedFiniteBlock
  nonempty : Nonempty Block
  directed :
    ∀ b₁ b₂ : Block,
      ∃ b₃ : Block,
        HasRefinement.Refines b₁ b₃ ∧ HasRefinement.Refines b₂ b₃

/-- Future analytic exhaustion package.

The `statement` field will eventually be the real boundary-null density theorem
for the finite spaces in `F`; Step 27 only records the interface. -/
structure BoundaryNullExhaustive (F : DirectedCertFamily) where
  statement : Prop
  proof : statement

/-- Future analytic positivity output.

The `statement` field will eventually say that the Weil/PSD form is
nonnegative on all compactly supported boundary-null tests. -/
structure BoundaryNullGlobalPositivity where
  statement : Prop
  proof : statement

/-- The closure package connecting a directed finite certificate family to the
future global boundary-null positivity statement. -/
structure DirectedFamilyClosure (F : DirectedCertFamily) where
  exhaustive : BoundaryNullExhaustive F
  positivity : BoundaryNullGlobalPositivity

/-- Consumer function: a closure package exposes its positivity payload. -/
def boundaryNull_global_positivity_of_closure
    (F : DirectedCertFamily)
    (H : DirectedFamilyClosure F) :
    BoundaryNullGlobalPositivity :=
  H.positivity

/-- Proposition-level consumer theorem for the positivity payload. -/
theorem boundaryNull_global_positivity_statement_of_closure
    (F : DirectedCertFamily)
    (H : DirectedFamilyClosure F) :
    H.positivity.statement :=
  H.positivity.proof

end PSDpd
end Q3
