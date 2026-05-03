import Q3.Proofs.PSD_PenaltyCertificate
import Q3.Proofs.PSD_BoundaryNullExhaustion

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
Matrix identification shell for the PSD-pd finite-certificate lane.

Steps 18--22 produce interval-backed finite matrices.  Steps 24--30 give the
finite penalty certificate and the boundary-null exhaustion machinery.  This
file is the missing theorem-facing port between them and the analytic form:

* a synthesis map sends coefficient vectors to test functions;
* the analytic Weil/PSD form on synthesized tests is identified with the
  finite quadratic form `vᵀ C v`;
* analytic boundary vanishing implies the coefficient vector lies in the
  finite constraint kernel `ker Q`.

The concrete B-spline / Arch / prime integral formulas are not proved here.
They should instantiate `FiniteWeilMatrixModel` in a later file.
-/

/-- Analytic-to-matrix model for one finite block.

`C` is the matrix for the full Weil/PSD form on the finite packet space and
`Q` is the boundary constraint matrix.  The model records exactly the two
identifications needed by the finite certificate consumer:

1. `weilForm (synth v) = quadForm C v`;
2. analytic boundary vanishing of `synth v` implies `BoundaryNull Q v`.
-/
structure FiniteWeilMatrixModel
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (C : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) where
  synth : (ι → ℝ) → V
  weilForm : V → ℝ
  boundary : BoundaryPair V
  weil_ident :
    ∀ v : ι → ℝ,
      weilForm (synth v) = Q3.Proofs.quadForm C v
  analyticBoundary_to_matrixBoundary :
    ∀ v : ι → ℝ,
      boundary.evalPlus (synth v) = 0 →
      boundary.evalMinus (synth v) = 0 →
        Q3.Proofs.BoundaryNull Q v

namespace FiniteWeilMatrixModel

/-- Matrix-boundary version: a finite penalty certificate proves analytic
nonnegativity on synthesized vectors whose coefficient vector is in `ker Q`. -/
theorem weil_nonneg_on_matrixBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (M : FiniteWeilMatrixModel (V := V) C Q)
    (cert : Q3.Proofs.FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v)
    (htheta : 0 ≤ theta) :
    ∀ v : ι → ℝ,
      Q3.Proofs.BoundaryNull Q v →
        0 ≤ M.weilForm (M.synth v) := by
  intro v hv
  by_cases hzero : v = 0
  · subst v
    rw [M.weil_ident]
    simp [Q3.Proofs.quadForm]
  · rw [M.weil_ident]
    exact
      Q3.Proofs.FinitePenaltyCert.C_nonneg_on_boundaryNull
        (C := C) (D := D) (R := R) (Q := Q) (theta := theta)
        cert hC htheta v hv hzero

/-- Analytic-boundary version: if synthesized vector has both analytic boundary
values zero, the same finite certificate proves analytic nonnegativity. -/
theorem weil_nonneg_on_analyticBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (M : FiniteWeilMatrixModel (V := V) C Q)
    (cert : Q3.Proofs.FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v)
    (htheta : 0 ≤ theta) :
    ∀ v : ι → ℝ,
      M.boundary.evalPlus (M.synth v) = 0 →
      M.boundary.evalMinus (M.synth v) = 0 →
        0 ≤ M.weilForm (M.synth v) := by
  intro v hplus hminus
  exact
    M.weil_nonneg_on_matrixBoundary cert hC htheta v
      (M.analyticBoundary_to_matrixBoundary v hplus hminus)

/-- Strengthened matrix-boundary version:
`C >= theta R` is transferred to the analytic form on synthesized vectors. -/
theorem weil_ge_theta_R_on_matrixBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (M : FiniteWeilMatrixModel (V := V) C Q)
    (cert : Q3.Proofs.FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v) :
    ∀ v : ι → ℝ,
      Q3.Proofs.BoundaryNull Q v →
        theta * Q3.Proofs.quadForm R v ≤ M.weilForm (M.synth v) := by
  intro v hv
  by_cases hzero : v = 0
  · subst v
    rw [M.weil_ident]
    simp [Q3.Proofs.quadForm]
  · rw [M.weil_ident]
    exact
      Q3.Proofs.FinitePenaltyCert.C_ge_theta_R_on_boundaryNull
        (C := C) (D := D) (R := R) (Q := Q) (theta := theta)
        cert hC v hv hzero

/-- Strengthened analytic-boundary version. -/
theorem weil_ge_theta_R_on_analyticBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (M : FiniteWeilMatrixModel (V := V) C Q)
    (cert : Q3.Proofs.FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v) :
    ∀ v : ι → ℝ,
      M.boundary.evalPlus (M.synth v) = 0 →
      M.boundary.evalMinus (M.synth v) = 0 →
        theta * Q3.Proofs.quadForm R v ≤ M.weilForm (M.synth v) := by
  intro v hplus hminus
  exact
    M.weil_ge_theta_R_on_matrixBoundary cert hC v
      (M.analyticBoundary_to_matrixBoundary v hplus hminus)

end FiniteWeilMatrixModel

/-- Packaged finite Weil positivity model.

This is the theorem-facing object that a concrete B-spline finite block should
eventually instantiate: matrices, kappa-split certificate, synthesis map, and
matrix-identification laws all in one record.
-/
structure CertifiedFiniteWeilModel
    (ρ ι V : Type*) [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V] where
  C : Matrix ι ι ℝ
  D : Matrix ι ι ℝ
  R : Matrix ι ι ℝ
  Q : Matrix ρ ι ℝ
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  cert : Q3.Proofs.FinitePenaltyCert D R Q
  split :
    ∀ v : ι → ℝ,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v
  model : FiniteWeilMatrixModel (V := V) C Q

namespace CertifiedFiniteWeilModel

/-- A packaged finite Weil model proves analytic nonnegativity on its
synthesized analytic boundary-null vectors. -/
theorem weil_nonneg_on_analyticBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (B : CertifiedFiniteWeilModel ρ ι V) :
    ∀ v : ι → ℝ,
      B.model.boundary.evalPlus (B.model.synth v) = 0 →
      B.model.boundary.evalMinus (B.model.synth v) = 0 →
        0 ≤ B.model.weilForm (B.model.synth v) :=
  B.model.weil_nonneg_on_analyticBoundary B.cert B.split B.theta_nonneg

/-- A packaged finite Weil model also exposes the strengthened
`C >= theta R` analytic inequality. -/
theorem weil_ge_theta_R_on_analyticBoundary
    {ρ ι V : Type*} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (B : CertifiedFiniteWeilModel ρ ι V) :
    ∀ v : ι → ℝ,
      B.model.boundary.evalPlus (B.model.synth v) = 0 →
      B.model.boundary.evalMinus (B.model.synth v) = 0 →
        B.theta * Q3.Proofs.quadForm B.R v ≤
          B.model.weilForm (B.model.synth v) :=
  B.model.weil_ge_theta_R_on_analyticBoundary B.cert B.split

end CertifiedFiniteWeilModel

end PSDpd
end Q3
