import Q3.Proofs.PSD_BSplineTranslationIdentities
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd

/-!
B-spline matrix-identification instance.

This file closes the Step 32 Lean-side matrix-identification chain.

Steps 32A--32E built the proof port:

* finite penalty certificate;
* boundary rows;
* basis expansion;
* translated-packet boundary covariance;
* translated-packet difference-kernel entries.

This file packages those concrete B-spline identity data together with a finite
penalty certificate and exposes the final Step 31 object:
`CertifiedFiniteWeilModel`.

The remaining non-bookkeeping mathematics is not another receiver layer: it is
to instantiate `BSplineTranslatedAnalyticContract` from the actual centered
B-spline bump, its transform, and its autocorrelation profile.
-/

/--
Certified concrete B-spline packet block.

`identities` is the concrete analytic content for one translated B-spline
packet block: boundary transform covariance and Arch/prime difference-kernel
pairings.  `cert` is the interval-backed finite penalty certificate for the
resulting matrices.
-/
structure CertifiedBSplineConcreteBlock
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  identities : BSplineTranslatedAnalyticContract ι V
  D : Matrix ι ι ℝ
  R : Matrix ι ι ℝ
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  cert :
    Q3.Proofs.FinitePenaltyCert
      D
      R
      identities.toAnalyticKernelContract.toFormulaContract.boundaryRows.Q
  split :
    ∀ v : ι → ℝ,
      Q3.Proofs.quadForm identities.toAnalyticKernelContract.toFormulaContract.C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v

namespace CertifiedBSplineConcreteBlock

/-- The finite matrix-to-Weil model supplied by the concrete B-spline
identities. -/
def finiteWeilMatrixModel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplineConcreteBlock ι V) :
    FiniteWeilMatrixModel
      (V := V)
      B.identities.toAnalyticKernelContract.toFormulaContract.C
      B.identities.toAnalyticKernelContract.toFormulaContract.boundaryRows.Q :=
  B.identities.toFiniteWeilMatrixModel

/--
Concrete B-spline identity data plus the interval-backed finite penalty
certificate produce the packaged Step 31 finite analytic model.
-/
def toCertifiedFiniteWeilModel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplineConcreteBlock ι V) :
    CertifiedFiniteWeilModel (Fin 2) ι V where
  C := B.identities.toAnalyticKernelContract.toFormulaContract.C
  D := B.D
  R := B.R
  Q := B.identities.toAnalyticKernelContract.toFormulaContract.boundaryRows.Q
  theta := B.theta
  theta_nonneg := B.theta_nonneg
  cert := B.cert
  split := B.split
  model := B.finiteWeilMatrixModel

/--
Final Step 32 consumer theorem: a certified concrete B-spline packet block
proves finite analytic Weil nonnegativity on analytic boundary-null packet
vectors.
-/
theorem weil_nonneg_on_analyticBoundary
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplineConcreteBlock ι V) :
    ∀ v : ι → ℝ,
      B.finiteWeilMatrixModel.boundary.evalPlus
          (B.finiteWeilMatrixModel.synth v) = 0 →
      B.finiteWeilMatrixModel.boundary.evalMinus
          (B.finiteWeilMatrixModel.synth v) = 0 →
        0 ≤ B.finiteWeilMatrixModel.weilForm
          (B.finiteWeilMatrixModel.synth v) :=
  B.toCertifiedFiniteWeilModel.weil_nonneg_on_analyticBoundary

/--
The strengthened Step 32 consumer theorem: the same block exposes the
coercive-style lower bound against the certified base matrix `R`.
-/
theorem weil_ge_theta_R_on_analyticBoundary
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplineConcreteBlock ι V) :
    ∀ v : ι → ℝ,
      B.finiteWeilMatrixModel.boundary.evalPlus
          (B.finiteWeilMatrixModel.synth v) = 0 →
      B.finiteWeilMatrixModel.boundary.evalMinus
          (B.finiteWeilMatrixModel.synth v) = 0 →
        B.theta * Q3.Proofs.quadForm B.R v ≤
          B.finiteWeilMatrixModel.weilForm
            (B.finiteWeilMatrixModel.synth v) :=
  B.toCertifiedFiniteWeilModel.weil_ge_theta_R_on_analyticBoundary

end CertifiedBSplineConcreteBlock

/--
Named Step 32F theorem.

Once the concrete B-spline transform, correlation, Arch-entry, and prime-entry
identities instantiate `BSplineTranslatedAnalyticContract`, the interval-backed
finite penalty certificate becomes a certified finite analytic Weil model.
-/
def bspline_packet_certifiedFiniteWeilModel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : CertifiedBSplineConcreteBlock ι V) :
    CertifiedFiniteWeilModel (Fin 2) ι V :=
  B.toCertifiedFiniteWeilModel

end PSDpd
end Q3
