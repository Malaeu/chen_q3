import Q3.Proofs.PSD_MatrixIdentification

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
B-spline packet matrix-identification receiver.

Step 31 introduced the abstract `FiniteWeilMatrixModel` port.  This file gives
the next layer down: a concrete receiver for B-spline packet entry identities.

It still does not prove the B-spline transform, autocorrelation, Arch integral,
or prime-shift formulas.  Instead, it records the exact hypotheses those
formulas must provide and packages them into the Step 31 model.
-/

/--
Entry-level data for one B-spline packet finite block.

The intended concrete meaning is:

* `synth v = sum_j v_j psi_j`;
* `A` is the Arch matrix;
* `P` is the Prime matrix;
* `C` is the full Weil matrix, intended as `A - P`;
* `Q` is the two-row boundary matrix, up to the harmless nonzero row scalings.

The fields are theorem-facing hypotheses.  The hard analytic work of proving
them for the actual B-spline formulas belongs to Step 32B and later.
-/
structure BSplinePacketEntryData
    (ρ ι V : Type*) [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V] where
  A : Matrix ι ι ℝ
  P : Matrix ι ι ℝ
  C : Matrix ι ι ℝ
  Q : Matrix ρ ι ℝ
  synth : (ι → ℝ) → V
  archForm : V → ℝ
  primeForm : V → ℝ
  weilForm : V → ℝ
  boundary : BoundaryPair V

  /-- Arch entry identity: `A` represents the Arch form on synthesized packets. -/
  arch_ident :
    ∀ v : ι → ℝ,
      archForm (synth v) = Q3.Proofs.quadForm A v

  /-- Prime entry identity: `P` represents the prime form on synthesized packets. -/
  prime_ident :
    ∀ v : ι → ℝ,
      primeForm (synth v) = Q3.Proofs.quadForm P v

  /-- Weil split on synthesized packets. -/
  weil_split :
    ∀ v : ι → ℝ,
      weilForm (synth v) = archForm (synth v) - primeForm (synth v)

  /-- Full finite matrix identity, normally `C = A - P` as quadratic forms. -/
  C_ident :
    ∀ v : ι → ℝ,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm A v - Q3.Proofs.quadForm P v

  /--
  Analytic boundary-null packets land in the finite matrix boundary kernel.

  The concrete B-spline proof may use nonzero row scalings in
  `H_j(±1/2)=const_± Q_{±,j}`; after the row scalings are discharged, this is
  the exact implication needed by `FiniteWeilMatrixModel`.
  -/
  analyticBoundary_to_matrixBoundary :
    ∀ v : ι → ℝ,
      boundary.evalPlus (synth v) = 0 →
      boundary.evalMinus (synth v) = 0 →
        Q3.Proofs.BoundaryNull Q v

namespace BSplinePacketEntryData

/-- The B-spline entry identities identify the analytic Weil form with the
finite matrix `C` on synthesized packets. -/
theorem weil_ident
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (B : BSplinePacketEntryData ρ ι V) :
    ∀ v : ι → ℝ,
      B.weilForm (B.synth v) = Q3.Proofs.quadForm B.C v := by
  intro v
  calc
    B.weilForm (B.synth v)
        = B.archForm (B.synth v) - B.primeForm (B.synth v) := B.weil_split v
    _ = Q3.Proofs.quadForm B.A v - Q3.Proofs.quadForm B.P v := by
          rw [B.arch_ident v, B.prime_ident v]
    _ = Q3.Proofs.quadForm B.C v := by
          exact (B.C_ident v).symm

/-- Convert B-spline packet entry identities into the Step 31
`FiniteWeilMatrixModel`. -/
def toFiniteWeilMatrixModel
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (B : BSplinePacketEntryData ρ ι V) :
    FiniteWeilMatrixModel (V := V) B.C B.Q where
  synth := B.synth
  weilForm := B.weilForm
  boundary := B.boundary
  weil_ident := B.weil_ident
  analyticBoundary_to_matrixBoundary := B.analyticBoundary_to_matrixBoundary

end BSplinePacketEntryData

/--
Certified B-spline packet block.

This packages the B-spline entry receiver together with the kappa-split finite
penalty certificate from Steps 18--26.
-/
structure CertifiedBSplinePacketBlock
    (ρ ι V : Type*) [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V] where
  entry : BSplinePacketEntryData ρ ι V
  D : Matrix ι ι ℝ
  R : Matrix ι ι ℝ
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  cert : Q3.Proofs.FinitePenaltyCert D R entry.Q
  split :
    ∀ v : ι → ℝ,
      Q3.Proofs.quadForm entry.C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v

namespace CertifiedBSplinePacketBlock

/-- Convert a certified B-spline packet block into the packaged Step 31
`CertifiedFiniteWeilModel`. -/
def toCertifiedFiniteWeilModel
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplinePacketBlock ρ ι V) :
    CertifiedFiniteWeilModel ρ ι V where
  C := B.entry.C
  D := B.D
  R := B.R
  Q := B.entry.Q
  theta := B.theta
  theta_nonneg := B.theta_nonneg
  cert := B.cert
  split := B.split
  model := B.entry.toFiniteWeilMatrixModel

/-- A certified B-spline packet block proves finite analytic Weil positivity on
its synthesized analytic boundary-null packets. -/
theorem weil_nonneg_on_analyticBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplinePacketBlock ρ ι V) :
    ∀ v : ι → ℝ,
      B.entry.boundary.evalPlus (B.entry.synth v) = 0 →
      B.entry.boundary.evalMinus (B.entry.synth v) = 0 →
        0 ≤ B.entry.weilForm (B.entry.synth v) :=
  (B.toCertifiedFiniteWeilModel).weil_nonneg_on_analyticBoundary

/-- The strengthened lower bound from the finite kappa certificate transfers to
the B-spline packet analytic form. -/
theorem weil_ge_theta_R_on_analyticBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplinePacketBlock ρ ι V) :
    ∀ v : ι → ℝ,
      B.entry.boundary.evalPlus (B.entry.synth v) = 0 →
      B.entry.boundary.evalMinus (B.entry.synth v) = 0 →
        B.theta * Q3.Proofs.quadForm B.R v ≤
          B.entry.weilForm (B.entry.synth v) :=
  (B.toCertifiedFiniteWeilModel).weil_ge_theta_R_on_analyticBoundary

end CertifiedBSplinePacketBlock

end PSDpd
end Q3
