import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource
import Mathlib.Data.Nat.Choose.Cast

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Source-model bridge scaffolding for the Step33A.1-A sub0 combined-cancellation
high-order Taylor route.

This file deliberately does not emit generated center-jet rows, order-16 rows,
or a `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid` payload.  It
records the first structural analytic bridge that is currently local: the whole
combined expression is `C^16` once the base Step22 Omega weight is available as
`C^16`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Cauchy-style convolution for normalized center jets.  The payload generator
may use this as the exact shape for component-product jets; it is only a
definition here, not a proof that any generated row is valid. -/
def primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution
    (n : Nat) (a b : Nat -> Real) : Real :=
  (Finset.range (n + 1)).sum (fun k => a k * b (n - k))

/-- The active center for the zero-cell combined-cancellation Taylor bridge. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter : Real :=
  (1 : Real) / 20

/-- Factorial-normalized center jet in the convention consumed by the
degree-15 combined-cancellation Taylor receiver. -/
def primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
    (f : Real -> Real) (n : Nat) : Real :=
  iteratedDeriv n f
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
    (Nat.factorial n : Real)

/-- Local all-order product rule for scalar iterated derivatives.  Mathlib in
this repo has no `iteratedDeriv_mul`; this is the exact finite substitute used
by the Step33A.1-A center-jet bridge. -/
theorem primaryFiniteRow0Parent0Split100Sub0_iterate_deriv_mul
    (n : Nat) (f g : Real -> Real)
    (hf : ContDiff Real n f) (hg : ContDiff Real n g) :
    deriv^[n] (fun x => f x * g x) =
      fun x => ∑ k ∈ Finset.range n.succ,
        n.choose k • ((deriv^[n - k] f x) * (deriv^[k] g x)) := by
  induction n with
  | zero =>
      ext x
      simp [Finset.range]
  | succ n IH =>
      have hf_n : ContDiff Real n f := hf.of_le (by norm_num)
      have hg_n : ContDiff Real n g := hg.of_le (by norm_num)
      calc
        deriv^[n + 1] (fun x => f x * g x) =
            deriv (fun x => ∑ k ∈ Finset.range n.succ,
              n.choose k • ((deriv^[n - k] f x) * (deriv^[k] g x))) := by
          rw [Function.iterate_succ_apply', IH hf_n hg_n]
        _ = (fun x =>
              (∑ k ∈ Finset.range n.succ,
                n.choose k • ((deriv^[n - k + 1] f x) * (deriv^[k] g x))) +
              ∑ k ∈ Finset.range n.succ,
                n.choose k • ((deriv^[n - k] f x) * (deriv^[k + 1] g x))) := by
          ext x
          rw [deriv_fun_sum]
          · rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro k hkMem
            rw [Finset.mem_range] at hkMem
            have hLeft :
                DifferentiableAt Real (deriv^[n - k] f) x := by
              simpa [iteratedDeriv_eq_iterate] using
                (hf.differentiable_iteratedDeriv (n - k) (by
                  exact_mod_cast (Nat.sub_lt_succ n k))).differentiableAt
            have hRight :
                DifferentiableAt Real (deriv^[k] g) x := by
              simpa [iteratedDeriv_eq_iterate] using
                (hg.differentiable_iteratedDeriv k (by
                  exact_mod_cast hkMem)).differentiableAt
            change
              deriv
                  (fun y =>
                    n.choose k • (((deriv^[n - k] f) * (deriv^[k] g)) y)) x =
                n.choose k • (deriv^[n - k + 1] f x * deriv^[k] g x) +
                  n.choose k • (deriv^[n - k] f x * deriv^[k + 1] g x)
            rw [deriv_fun_const_smul (n.choose k) (DifferentiableAt.mul hLeft hRight)]
            rw [deriv_mul hLeft hRight]
            simp_rw [Function.iterate_succ_apply', smul_add]
          · intro k hk
            rw [Finset.mem_range] at hk
            change
              DifferentiableAt Real
                ((n.choose k) •
                  (fun x => (deriv^[n - k] f x) * (deriv^[k] g x))) x
            apply DifferentiableAt.const_smul
            apply DifferentiableAt.mul
            · simpa [iteratedDeriv_eq_iterate] using
                (hf.differentiable_iteratedDeriv (n - k) (by
                  exact_mod_cast (Nat.sub_lt_succ n k))).differentiableAt
            · simpa [iteratedDeriv_eq_iterate] using
                (hg.differentiable_iteratedDeriv k (by
                  exact_mod_cast hk)).differentiableAt
        _ = fun x => ∑ k ∈ Finset.range (n + 1).succ,
              (n + 1).choose k •
                ((deriv^[n + 1 - k] f x) * (deriv^[k] g x)) := by
          ext x
          calc
            (∑ k ∈ Finset.range n.succ,
                n.choose k • (deriv^[n - k + 1] f x * deriv^[k] g x)) +
                ∑ k ∈ Finset.range n.succ,
                  n.choose k • (deriv^[n - k] f x * deriv^[k + 1] g x)
                = (∑ k ∈ Finset.range n.succ,
                    n.choose k.succ •
                      (deriv^[n - k] f x * deriv^[k + 1] g x)) +
                  1 • (deriv^[n + 1] f x * deriv^[0] g x) +
                    ∑ k ∈ Finset.range n.succ,
                      n.choose k • (deriv^[n - k] f x * deriv^[k + 1] g x) := ?_
            _ = ((∑ k ∈ Finset.range n.succ,
                    n.choose k • (deriv^[n - k] f x * deriv^[k + 1] g x)) +
                  ∑ k ∈ Finset.range n.succ,
                    n.choose k.succ •
                      (deriv^[n - k] f x * deriv^[k + 1] g x)) +
                  1 • (deriv^[n + 1] f x * deriv^[0] g x) := by
              rw [add_comm, add_assoc]
            _ = (∑ i ∈ Finset.range n.succ,
                  (n + 1).choose (i + 1) •
                    (deriv^[n + 1 - (i + 1)] f x * deriv^[i + 1] g x)) +
                1 • (deriv^[n + 1] f x * deriv^[0] g x) := by
              simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ,
                add_smul, Finset.sum_add_distrib]
            _ = ∑ k ∈ Finset.range (n + 1).succ,
                  (n + 1).choose k •
                    (deriv^[n + 1 - k] f x * deriv^[k] g x) := by
              rw [Finset.sum_range_succ' _ (n + 1), Nat.choose_zero_right,
                tsub_zero]
          congr
          refine (Finset.sum_range_succ' _ _).trans (congr_arg₂ (· + ·) ?_ ?_)
          · rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_smul,
              add_zero]
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [Finset.mem_range] at hk
            congr
            lia
          · rw [Nat.choose_zero_right, tsub_zero]

/-- Product bridge for the repository's factorial-normalized center-jet
convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    (n : Nat) (f g : Real -> Real)
    (hf : ContDiff Real n f) (hg : ContDiff Real n g) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun x => f x * g x) n =
      primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
        (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet f)
        (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet g) := by
  unfold primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
  unfold primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution
  rw [show (iteratedDeriv n (fun x => f x * g x)
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter) =
      iteratedDeriv n (fun x => g x * f x)
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter by
        congr 1
        ext x
        ring]
  have hprod :
      iteratedDeriv n (fun x => g x * f x)
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter =
        ∑ k ∈ Finset.range n.succ,
          n.choose k •
            (iteratedDeriv (n - k) g
                primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter *
              iteratedDeriv k f
                primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter) := by
    have h :=
      congrFun
        (primaryFiniteRow0Parent0Split100Sub0_iterate_deriv_mul n g f hg hf)
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
    simpa [iteratedDeriv_eq_iterate] using h
  rw [hprod]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mem_range] at hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ hk
  rw [nsmul_eq_mul]
  change
    ((n.choose k : Real) *
        (iteratedDeriv (n - k) g
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter *
          iteratedDeriv k f
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter)) /
        (Nat.factorial n : Real) =
      (iteratedDeriv k f
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
        (Nat.factorial k : Real)) *
        (iteratedDeriv (n - k) g
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
          (Nat.factorial (n - k) : Real))
  rw [Nat.cast_choose Real hk_le]
  field_simp [Nat.cast_ne_zero]

/-- Additivity bridge for the repository's factorial-normalized center-jet
convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    (n : Nat) (f g : Real -> Real)
    (hf : ContDiff Real n f) (hg : ContDiff Real n g) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun x => f x + g x) n =
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet f n +
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet g n := by
  unfold primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
  change
    iteratedDeriv n (f + g)
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
        (Nat.factorial n : Real) =
      iteratedDeriv n f
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
          (Nat.factorial n : Real) +
        iteratedDeriv n g
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
          (Nat.factorial n : Real)
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt]
  ring

/-- Subtraction bridge for the repository's factorial-normalized center-jet
convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_sub
    (n : Nat) (f g : Real -> Real)
    (hf : ContDiff Real n f) (hg : ContDiff Real n g) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun x => f x - g x) n =
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet f n -
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet g n := by
  unfold primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
  change
    iteratedDeriv n (f - g)
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
        (Nat.factorial n : Real) =
      iteratedDeriv n f
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
          (Nat.factorial n : Real) -
        iteratedDeriv n g
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
          (Nat.factorial n : Real)
  rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt]
  ring

/-- Constant-scaling bridge for the repository's factorial-normalized center-jet
convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_const_mul
    (n : Nat) (c : Real) (f : Real -> Real)
    (hf : ContDiff Real n f) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun x => c * f x) n =
      c * primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet f n := by
  unfold primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
  rw [iteratedDeriv_const_mul hf.contDiffAt c]
  ring

/-- Residual Taylor polynomial as a named source for component-level center
jets. -/
def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta

/-- Cauchy-source center jet for the actual component product.  This is the
generator-facing convention; all-order equality is the later product-Leibniz
obligation. -/
def primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaActual)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual)

/-- Cauchy-source center jet for the nominal polynomial component product. -/
def primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly)

/-- Cauchy-source center jet for the cancellation residual component product. -/
def primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta -
            primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta))
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta -
            primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta)) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaActual eta -
            primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta))
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta -
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta))

/-- Component-source center jet for the full combined-cancellation expression.
For `n = 0` this is Lean-checked below; for all rows this is the exact source
the later product-Leibniz bridge must justify. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly n +
    primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        n +
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
        n

/-- First exact component Cauchy row for the actual component product. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_centerJet0_eq_cauchy :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual 0 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual]

/-- First exact component Cauchy row for the nominal polynomial component
product. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_centerJet0_eq_cauchy :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal 0 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal]

/-- First exact component Cauchy row for the cancellation-residual component
product. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_centerJet0_eq_cauchy :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        0 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual]

/-- First exact center-jet row of the whole combined-cancellation expression in
the component-source convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet0_eq_componentSource :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
        0 =
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr,
    primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal]
  ring

/-- Local smoothness helper for the rational Taylor-polynomial surface used by
the combined source model. -/
theorem rawOmegaATaylorPolynomial_contDiff16
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat) :
    ContDiff Real 16 (rawOmegaATaylorPolynomial degree center coeff) := by
  unfold rawOmegaATaylorPolynomial
  fun_prop

/-- The base Step22 Omega weight is `C^16`, obtained from its differentiability
and the existing closed-form derivative smoothness certificate. -/
theorem step22OmegaArchWeight_contDiff16 :
    ContDiff Real 16
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight := by
  rw [show (16 : WithTop ENat) = (15 : WithTop ENat) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  constructor
  · exact fun eta =>
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt eta
  · constructor
    · intro h
      norm_num at h
    · have hDeriv :
          deriv CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight =
            step22OmegaArchWeightDerivClosedForm := by
        funext eta
        exact step22OmegaArchWeight_deriv_eq_closedForm eta
      have hClosed :
          ContDiff Real 15 step22OmegaArchWeightDerivClosedForm :=
        step22OmegaArchWeightDerivClosedForm_contDiff16.of_le (by norm_num)
      rw [hDeriv]
      exact hClosed

/--
The whole combined-cancellation expression is `C^16` once the base
`step22OmegaArchWeight` source is available as `C^16`.

This closes only the structural smoothness sub-obligation of
`Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid`; it does not provide
the center-jet rows or the uniform order-16 bound.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16_of_omega
    (hOmega :
      ContDiff Real 16
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight) :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr := by
  change
    ContDiff Real 16
      (fun eta : Real =>
        rawOmegaATaylorPolynomial
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta +
          primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta)
  simp only [
    primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs,
    primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly]
  have hResidualPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
  have hOmegaPrimePoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
  have hOmegaPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
  have hShapeSqPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff
  have hShapeSqDerivPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff
  have hOmegaPrime :
      ContDiff Real 16 step22OmegaArchWeightDerivClosedForm :=
    step22OmegaArchWeightDerivClosedForm_contDiff16
  have hShapeSqDeriv :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10))
  fun_prop

/--
Unconditional structural smoothness bridge for the whole combined-cancellation
expression. This still does not provide the center-jet rows or uniform order-16
bound required for a concrete `Valid` payload.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16 :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr :=
  primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16_of_omega
    step22OmegaArchWeight_contDiff16

/-- All center-jet rows for the actual component product in the Cauchy-source
convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_centerJet_eq_cauchy
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual j.1 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
        j.1 := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hOmegaPrime :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16.of_le hj16
  have hOmega :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16.of_le hj16
  have hShapeSq :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hShapeSqDeriv :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)).of_le hj16
  have hProductLeft :
      ContDiff Real j.1
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta) :=
    hOmegaPrime.mul hShapeSq
  have hProductRight :
      ContDiff Real j.1
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta) :=
    hOmega.mul hShapeSqDeriv
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    j.1
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta)
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta)
    hProductLeft hProductRight]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual hOmegaPrime hShapeSq]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual hOmega hShapeSqDeriv]

/-- All center-jet rows for the nominal polynomial component product in the
Cauchy-source convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_centerJet_eq_cauchy
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal j.1 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
        j.1 := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hOmegaPrimePoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff).of_le hj16
  have hOmegaPoly :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff).of_le hj16
  have hShapeSqPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff).of_le hj16
  have hShapeSqDerivPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff).of_le hj16
  have hProductLeft :
      ContDiff Real j.1
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta) :=
    hOmegaPrimePoly.mul hShapeSqPoly
  have hProductRight :
      ContDiff Real j.1
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta) :=
    hOmegaPoly.mul hShapeSqDerivPoly
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    j.1
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta)
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta)
    hProductLeft hProductRight]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly hOmegaPrimePoly
    hShapeSqPoly]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly hOmegaPoly
    hShapeSqDerivPoly]

/-- All center-jet rows for the cancellation-residual component product in the
Cauchy-source convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_centerJet_eq_cauchy
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        j.1 := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hOmegaPrime :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16.of_le hj16
  have hOmega :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16.of_le hj16
  have hShapeSq :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hShapeSqDeriv :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)).of_le hj16
  have hOmegaPrimePoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff).of_le hj16
  have hOmegaPoly :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff).of_le hj16
  have hShapeSqPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff).of_le hj16
  have hShapeSqDerivPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff).of_le hj16
  let t1 : Real -> Real := fun eta =>
    (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta -
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta) *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta
  let t2 : Real -> Real := fun eta =>
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta *
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta -
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta)
  let t3 : Real -> Real := fun eta =>
    (primaryFiniteRow0Parent0Split100Sub0OmegaActual eta -
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta) *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta
  let t4 : Real -> Real := fun eta =>
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta *
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta -
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta)
  have ht1 : ContDiff Real j.1 t1 := by
    dsimp [t1]
    exact (hOmegaPrime.sub hOmegaPrimePoly).mul hShapeSq
  have ht2 : ContDiff Real j.1 t2 := by
    dsimp [t2]
    exact hOmegaPrimePoly.mul (hShapeSq.sub hShapeSqPoly)
  have ht3 : ContDiff Real j.1 t3 := by
    dsimp [t3]
    exact (hOmega.sub hOmegaPoly).mul hShapeSqDeriv
  have ht4 : ContDiff Real j.1 t4 := by
    dsimp [t4]
    exact hOmegaPoly.mul (hShapeSqDeriv.sub hShapeSqDerivPoly)
  have ht12 : ContDiff Real j.1 (fun eta => t1 eta + t2 eta) :=
    ht1.add ht2
  have ht123 :
      ContDiff Real j.1 (fun eta => (t1 eta + t2 eta) + t3 eta) :=
    ht12.add ht3
  change
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta => ((t1 eta + t2 eta) + t3 eta) + t4 eta) j.1 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        j.1
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    j.1 (fun eta => (t1 eta + t2 eta) + t3 eta) t4 ht123 ht4]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    j.1 (fun eta => t1 eta + t2 eta) t3 ht12 ht3]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    j.1 t1 t2 ht1 ht2]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta -
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta)
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    (hOmegaPrime.sub hOmegaPrimePoly) hShapeSq]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta -
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta)
    hOmegaPrimePoly (hShapeSq.sub hShapeSqPoly)]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0OmegaActual eta -
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta)
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
    (hOmega.sub hOmegaPoly) hShapeSqDeriv]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_mul
    j.1 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta -
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta)
    hOmegaPoly (hShapeSqDeriv.sub hShapeSqDerivPoly)]

/-- All center-jet rows of the whole combined-cancellation expression in the
component-source convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_componentSource
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
        j.1 := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hResidualPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff).of_le hj16
  have hOmegaPrime :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16.of_le hj16
  have hOmega :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16.of_le hj16
  have hShapeSq :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hShapeSqDeriv :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)).of_le hj16
  have hOmegaPrimePoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff).of_le hj16
  have hOmegaPoly :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff).of_le hj16
  have hShapeSqPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff).of_le hj16
  have hShapeSqDerivPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff).of_le hj16
  have hNominal :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal := by
    unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
    exact
      (hOmegaPrimePoly.mul hShapeSqPoly).add
        (hOmegaPoly.mul hShapeSqDerivPoly)
  have hResidual :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
    exact
      ((((hOmegaPrime.sub hOmegaPrimePoly).mul hShapeSq).add
        (hOmegaPrimePoly.mul (hShapeSq.sub hShapeSqPoly))).add
        ((hOmega.sub hOmegaPoly).mul hShapeSqDeriv)).add
        (hOmegaPoly.mul (hShapeSqDeriv.sub hShapeSqDerivPoly))
  have hScaledResidual :
      ContDiff Real j.1
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
              eta) := by
    simpa using
      (ContDiff.const_smul
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff hResidual)
  have hScaledNominal :
      ContDiff Real j.1
        (fun eta : Real =>
          (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta) := by
    simpa using
      (ContDiff.const_smul
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real))
        hNominal)
  have hScaledRhs :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs := by
    unfold primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs
    exact hScaledResidual.add hScaledNominal
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    j.1
    (rawOmegaATaylorPolynomial
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff)
    primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs
    hResidualPoly hScaledRhs]
  unfold primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_add
    j.1
    (fun eta : Real =>
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
          eta)
    (fun eta : Real =>
      (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta)
    hScaledResidual hScaledNominal]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_const_mul
    j.1 primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
    hResidual]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_const_mul
    j.1
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real))
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal hNominal]
  rw [primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_centerJet_eq_cauchy j]
  rw [primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_centerJet_eq_cauchy j]
  unfold primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly
  ring_nf

end Step33
end PSDpd
end Q3
