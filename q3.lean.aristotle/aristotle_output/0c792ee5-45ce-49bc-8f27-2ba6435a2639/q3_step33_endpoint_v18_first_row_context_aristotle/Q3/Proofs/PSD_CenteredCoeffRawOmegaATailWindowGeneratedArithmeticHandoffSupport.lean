import Q3.Proofs.PSD_CenteredCoeffRawOmegaATailWindowArithmeticImport
import Q3.Proofs.PSD_CenteredCoeffRawOmegaATailWindowPayloadSupport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0
set_option autoImplicit false

/-!
Raw-Omega Step33 `A` generated-arithmetic handoff support.

This module is the lightweight landing surface for the future analytic
comparison import.  It imports the checked generated arithmetic payloads and
the generator-facing payload structures, but deliberately avoids the heavy
prime/live/P0 Step33 support graph.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport

/-- Finite-measure helper for generated constant comparison functions on a
closed-open analytic window. -/
lemma volume_Ioc_ne_top_real (a b : Real) : volume (Set.Ioc a b) ≠ ⊤ := by
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

lemma integrableOn_const_Ioc_real (a b c : Real) :
    IntegrableOn (fun _ : Real => c) (Set.Ioc a b) := by
  exact MeasureTheory.integrableOn_const (hs := volume_Ioc_ne_top_real a b)

lemma integrableOn_quadratic_Ioc_real (a b c0 c1 c2 : Real) :
    IntegrableOn (fun x : Real => c0 + c1 * x + c2 * x ^ 2) (Set.Ioc a b) := by
  have hcont : Continuous (fun x : Real => c0 + c1 * x + c2 * x ^ 2) := by
    fun_prop
  exact (hcont.integrableOn_Icc (a := a) (b := b)).mono_set Set.Ioc_subset_Icc_self

structure RawOmegaAQuadraticComparison where
  c0 : CoeffIndex23 → Real
  c1 : CoeffIndex23 → Real
  c2 : CoeffIndex23 → Real

def RawOmegaAQuadraticComparison.eval
    (q : RawOmegaAQuadraticComparison) (n : CoeffIndex23) (eta : Real) : Real :=
  q.c0 n + q.c1 n * eta + q.c2 n * eta ^ 2

lemma RawOmegaAQuadraticComparison.integrableOn_Ioc
    (q : RawOmegaAQuadraticComparison) (n : CoeffIndex23) (a b : Real) :
    IntegrableOn (q.eval n) (Set.Ioc a b) := by
  simpa [RawOmegaAQuadraticComparison.eval] using
    integrableOn_quadratic_Ioc_real a b (q.c0 n) (q.c1 n) (q.c2 n)

lemma setIntegral_const_Ioc_real (a b c : Real) :
    (∫ (_ : Real) in Set.Ioc a b, c) = (volume.real (Set.Ioc a b)) * c := by
  rw [MeasureTheory.setIntegral_const]
  simp [smul_eq_mul]

lemma setIntegral_const_Ioc_real_of_le {a b c : Real} (hab : a <= b) :
    (∫ (_ : Real) in Set.Ioc a b, c) = (b - a) * c := by
  calc
    (∫ (_ : Real) in Set.Ioc a b, c) = (∫ _ in a..b, c) := by
      rw [intervalIntegral.integral_of_le hab]
    _ = (b - a) * c := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]

def primaryK11RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n)
        (Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n)
        (Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteUpperF n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n)
        (Set.Ioc primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n)
        (Set.Ioc primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailUpperF n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  { finiteLowerF := finiteLowerF
    finiteUpperF := finiteUpperF
    tailLowerF := tailLowerF
    tailUpperF := tailUpperF
    hProfileInt := hProfileInt
    hFiniteLowerInt := hFiniteLowerInt
    hFiniteUpperInt := hFiniteUpperInt
    hFiniteLower := hFiniteLower
    hFiniteUpper := hFiniteUpper
    hFiniteLowerBound := hFiniteLowerBound
    hFiniteUpperBound := hFiniteUpperBound
    hTailLowerInt := hTailLowerInt
    hTailUpperInt := hTailUpperInt
    hTailLower := hTailLower
    hTailUpper := hTailUpper
    hTailWindowLower := hTailWindowLower
    hTailWindowUpper := hTailWindowUpper
    hTailRemainder := hTailRemainder }

def controlK9RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n)
        (Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n)
        (Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteUpperF n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n)
        (Set.Ioc controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n)
        (Set.Ioc controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailUpperF n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  { finiteLowerF := finiteLowerF
    finiteUpperF := finiteUpperF
    tailLowerF := tailLowerF
    tailUpperF := tailUpperF
    hProfileInt := hProfileInt
    hFiniteLowerInt := hFiniteLowerInt
    hFiniteUpperInt := hFiniteUpperInt
    hFiniteLower := hFiniteLower
    hFiniteUpper := hFiniteUpper
    hFiniteLowerBound := hFiniteLowerBound
    hFiniteUpperBound := hFiniteUpperBound
    hTailLowerInt := hTailLowerInt
    hTailUpperInt := hTailUpperInt
    hTailLower := hTailLower
    hTailUpper := hTailUpper
    hTailWindowLower := hTailWindowLower
    hTailWindowUpper := hTailWindowUpper
    hTailRemainder := hTailRemainder }

def primaryK11RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_const_comparison
    (finiteLower finiteUpper tailLower tailUpper : CoeffIndex23 → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          finiteUpper n)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteLower n)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          tailUpper n)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailLower n)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  primaryK11RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison
    (fun n _ => finiteLower n) (fun n _ => finiteUpper n)
    (fun n _ => tailLower n) (fun n _ => tailUpper n)
    hProfileInt
    (fun n =>
      integrableOn_const_Ioc_real (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        (finiteLower n))
    (fun n =>
      integrableOn_const_Ioc_real (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        (finiteUpper n))
    hFiniteLower hFiniteUpper
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg]
      simpa using hFiniteLowerBound n)
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg]
      simpa using hFiniteUpperBound n)
    (fun n =>
      integrableOn_const_Ioc_real
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd
        (tailLower n))
    (fun n =>
      integrableOn_const_Ioc_real
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd
        (tailUpper n))
    hTailLower hTailUpper
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.hTailWindow]
      simpa using hTailWindowLower n)
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.hTailWindow]
      simpa using hTailWindowUpper n)
    hTailRemainder

def controlK9RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_const_comparison
    (finiteLower finiteUpper tailLower tailUpper : CoeffIndex23 → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          finiteUpper n)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteLower n)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          tailUpper n)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailLower n)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  controlK9RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison
    (fun n _ => finiteLower n) (fun n _ => finiteUpper n)
    (fun n _ => tailLower n) (fun n _ => tailUpper n)
    hProfileInt
    (fun n =>
      integrableOn_const_Ioc_real (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        (finiteLower n))
    (fun n =>
      integrableOn_const_Ioc_real (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        (finiteUpper n))
    hFiniteLower hFiniteUpper
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg]
      simpa using hFiniteLowerBound n)
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg]
      simpa using hFiniteUpperBound n)
    (fun n =>
      integrableOn_const_Ioc_real
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd
        (tailLower n))
    (fun n =>
      integrableOn_const_Ioc_real
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd
        (tailUpper n))
    hTailLower hTailUpper
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.hTailWindow]
      simpa using hTailWindowLower n)
    (fun n => by
      rw [setIntegral_const_Ioc_real_of_le
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.hTailWindow]
      simpa using hTailWindowUpper n)
    hTailRemainder

def primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
    (analytic :
      PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload :=
  primaryK11RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_analytic
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated
    analytic

def controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
    (analytic :
      ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated) :
    ControlK9RawOmegaAComparisonTailWindowPayload :=
  controlK9RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_analytic
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated
    analytic

def rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_analytic
    (primaryAnalytic :
      PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated)
    (controlAnalytic :
      ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload ×
      ControlK9RawOmegaAComparisonTailWindowPayload :=
  ( primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
      primaryAnalytic
  , controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
      controlAnalytic )

def primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_const_comparison
    (finiteLower finiteUpper tailLower tailUpper : CoeffIndex23 → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          finiteUpper n)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteLower n)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          tailUpper n)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailLower n)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload :=
  primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
    (primaryK11RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_const_comparison
      finiteLower finiteUpper tailLower tailUpper
      hProfileInt
      hFiniteLower hFiniteUpper
      hFiniteLowerBound hFiniteUpperBound
      hTailLower hTailUpper
      hTailWindowLower hTailWindowUpper
      hTailRemainder)

def controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_const_comparison
    (finiteLower finiteUpper tailLower tailUpper : CoeffIndex23 → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          finiteUpper n)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteLower n)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          finiteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          tailUpper n)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailLower n)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          tailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    ControlK9RawOmegaAComparisonTailWindowPayload :=
  controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
    (controlK9RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_const_comparison
      finiteLower finiteUpper tailLower tailUpper
      hProfileInt
      hFiniteLower hFiniteUpper
      hFiniteLowerBound hFiniteUpperBound
      hTailLower hTailUpper
      hTailWindowLower hTailWindowUpper
      hTailRemainder)

def rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison
    (primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper :
      CoeffIndex23 → Real)
    (controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper :
      CoeffIndex23 → Real)
    (hPrimaryProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpper n)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteLower n)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpper n)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailLower n)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpper n)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteLower n)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpper n)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailLower n)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload ×
      ControlK9RawOmegaAComparisonTailWindowPayload :=
  ( primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_const_comparison
      primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
      hPrimaryProfileInt
      hPrimaryFiniteLower hPrimaryFiniteUpper
      hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
      hPrimaryTailLower hPrimaryTailUpper
      hPrimaryTailWindowLower hPrimaryTailWindowUpper
      hPrimaryTailRemainder
  , controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_const_comparison
      controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
      hControlProfileInt
      hControlFiniteLower hControlFiniteUpper
      hControlFiniteLowerBound hControlFiniteUpperBound
      hControlTailLower hControlTailUpper
      hControlTailWindowLower hControlTailWindowUpper
      hControlTailRemainder )

def rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability
    (primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper :
      CoeffIndex23 → Real)
    (controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper :
      CoeffIndex23 → Real)
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpper n)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteLower n)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpper n)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailLower n)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpper n)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteLower n)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpper n)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailLower n)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload ×
      ControlK9RawOmegaAComparisonTailWindowPayload :=
  rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison
    primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
    controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi
    hPrimaryFiniteLower hPrimaryFiniteUpper
    hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
    hPrimaryTailLower hPrimaryTailUpper
    hPrimaryTailWindowLower hPrimaryTailWindowUpper
    hPrimaryTailRemainder
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi
    hControlFiniteLower hControlFiniteUpper
    hControlFiniteLowerBound hControlFiniteUpperBound
    hControlTailLower hControlTailUpper
    hControlTailWindowLower hControlTailWindowUpper
    hControlTailRemainder

/-- Generator-facing constant-comparison payload constructor where positive-axis
integrability and the `(U,∞)` raw-Omega tail remainders are discharged by the
shared structural linear-growth majorant.  The generator only has to supply the
finite/tail-window comparison inequalities and arithmetic checks that the
generated remainder radii dominate the explicit `U^{-2}` majorants. -/
def rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability_and_tail_growth
    (primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper :
      CoeffIndex23 → Real)
    (controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper :
      CoeffIndex23 → Real)
    (C0 C1 : Real)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ eta : Real,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| <=
        C0 + C1 * |eta|)
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpper n)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteLower n)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpper n)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailLower n)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainderRadius : ∀ n : CoeffIndex23,
      (|primaryK11Ell / Real.pi| *
        ((C0 + C1) *
          |(Real.sqrt (Q3.PSDpd.bsplineScale 11 *
            Q3.PSDpd.bsplineAutocorrNorm 11))⁻¹| ^ 2 *
          (|(primaryK11Ell /
            (2 * Q3.PSDpd.bsplineScale 11))|⁻¹) ^ 4)) *
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd ^
          (-2 : ℝ) / 2) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpper n)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteLower n)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpper n)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailLower n)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainderRadius : ∀ n : CoeffIndex23,
      (|controlK9Ell / Real.pi| *
        ((C0 + C1) *
          |(Real.sqrt (Q3.PSDpd.bsplineScale 9 *
            Q3.PSDpd.bsplineAutocorrNorm 9))⁻¹| ^ 2 *
          (|(controlK9Ell /
            (2 * Q3.PSDpd.bsplineScale 9))|⁻¹) ^ 4)) *
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd ^
          (-2 : ℝ) / 2) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload ×
      ControlK9RawOmegaAComparisonTailWindowPayload := by
  have hPrimaryTailEnd :
      (1 : Real) <= primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd := by
    change (1 : Real) <= rawOmegaATailWindowEnd
    norm_num [rawOmegaATailWindowEnd]
  have hControlTailEnd :
      (1 : Real) <= controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd := by
    change (1 : Real) <= rawOmegaATailWindowEnd
    norm_num [rawOmegaATailWindowEnd]
  exact
    rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability
      primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
      controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
      hPrimaryFiniteLower hPrimaryFiniteUpper
      hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
      hPrimaryTailLower hPrimaryTailUpper
      hPrimaryTailWindowLower hPrimaryTailWindowUpper
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaATailRemainder_abs_le_of_linear_growth
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd C0 C1
        hC0 hC1 hgrowth hPrimaryTailEnd
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius
        hPrimaryTailRemainderRadius)
      hControlFiniteLower hControlFiniteUpper
      hControlFiniteLowerBound hControlFiniteUpperBound
      hControlTailLower hControlTailUpper
      hControlTailWindowLower hControlTailWindowUpper
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaATailRemainder_abs_le_of_linear_growth
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd C0 C1
        hC0 hC1 hgrowth hControlTailEnd
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius
        hControlTailRemainderRadius)

/-- Single generated-import target for the direct analytic raw-Omega
tail-window route.  This keeps the generator target compact when the tail
remainder is proved directly rather than through a shared global linear-growth
witness. -/
structure RawOmegaAAnalyticTailWindowInputs where
  primaryAnalytic :
    PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated
  controlAnalytic :
    ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated

def RawOmegaAAnalyticTailWindowInputs.toPayloads
    (inputs : RawOmegaAAnalyticTailWindowInputs) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload ×
      ControlK9RawOmegaAComparisonTailWindowPayload :=
  rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_analytic
    inputs.primaryAnalytic inputs.controlAnalytic

/-- Single generated-import target for direct raw-Omega finite/tail window
integral certificates.

Unlike `RawOmegaAAnalyticTailWindowInputs`, this surface does not ask the
generator for pointwise lower/upper comparison functions.  It asks for direct
finite-window and tail-window integral bounds against the raw-Omega analytic
parts, plus the tail remainder.  This is the intended landing surface for a
future Arb-backed chunk-integral certificate generator. -/
structure RawOmegaADirectTailWindowInputs where
  primaryAnalytic :
    PrimaryK11RawOmegaADirectTailWindowAnalyticPayload
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated
  controlAnalytic :
    ControlK9RawOmegaADirectTailWindowAnalyticPayload
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated

theorem RawOmegaADirectTailWindowInputs.toFiniteTailBoundsCerts
    (inputs : RawOmegaADirectTailWindowInputs) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRadius ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRadius := by
  exact ⟨
    primaryK11RawOmegaAFiniteTailBoundsCert_of_arithmetic_and_directTailWindow
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated
      inputs.primaryAnalytic,
    controlK9RawOmegaAFiniteTailBoundsCert_of_arithmetic_and_directTailWindow
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated
      inputs.controlAnalytic⟩

theorem primaryK11RawOmegaATailLogMajorant_integral_le_tailRemainderRadius_after_520
    (n : CoeffIndex23) :
    ∫ eta in Set.Ioi (520 : Real),
      |primaryK11Ell / Real.pi| * ((10 : Real) * Real.log (3 * eta)) *
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          11 primaryK11Ell eta <=
      primaryK11RawOmegaATailRemainderRadius n := by
  let C : Real :=
    |(Real.sqrt (bsplineScale 11 * bsplineAutocorrNorm 11))⁻¹| ^ 2 *
      (|(primaryK11Ell / (2 * bsplineScale 11))|⁻¹) ^ (2 * (11 + 1))
  have hC_nonneg : 0 <= C := by
    dsimp [C]
    positivity
  have hmaj_eq : ∀ eta : Real,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          11 primaryK11Ell eta = C * eta ^ (-24 : Real) := by
    intro eta
    dsimp [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant, C]
    norm_num
  have hfun :
      (fun eta : Real =>
        |primaryK11Ell / Real.pi| * ((10 : Real) * Real.log (3 * eta)) *
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            11 primaryK11Ell eta) =
      (fun eta : Real =>
        (|primaryK11Ell / Real.pi| * (10 : Real) * C) *
          (Real.log (3 * eta) * eta ^ (-24 : Real))) := by
    funext eta
    rw [hmaj_eq]
    ring
  rw [hfun]
  rw [integral_const_mul]
  rw [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmega_integral_Ioi_log_three_mul_rpow_neg24_after_520]
  have hpi_lower_pos : 0 < Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower := by
    norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower]
  have hpi_bound :
      |primaryK11Ell / Real.pi| <=
        ((3 : Real) / 10) / Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower := by
    have hpi_lb := Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower_le_pi
    have hinv :
        Real.pi⁻¹ <= Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hpi_lower_pos hpi_lb
    calc
      |primaryK11Ell / Real.pi| = |primaryK11Ell| * Real.pi⁻¹ := by
        rw [abs_div, abs_of_pos Real.pi_pos]
        rw [div_eq_mul_inv]
      _ <= |primaryK11Ell| * Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = ((3 : Real) / 10) / Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower := by
        rw [show |primaryK11Ell| = ((3 : Real) / 10) by
          norm_num [primaryK11Ell, primaryK11EllRat]]
        ring
  have hlog_bound :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmega_log_1560_le_upper
  have hI_le :
      (520 : Real) ^ (-23 : Real) *
          (Real.log (1560 : Real) / 23 + 1 / ((23 : Real) ^ 2)) <=
      (520 : Real) ^ (-23 : Real) *
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaLog1560Upper / 23 +
            1 / ((23 : Real) ^ 2)) := by
    gcongr
  have hcoef_nonneg :
      0 <= (((3 : Real) / 10) /
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower) * 10 * C := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) hpi_lower_pos.le) (by norm_num))
      hC_nonneg
  have hbound :
      |primaryK11Ell / Real.pi| * 10 * C *
          ((520 : Real) ^ (-23 : Real) *
            (Real.log (1560 : Real) / 23 + 1 / ((23 : Real) ^ 2))) <=
      (((3 : Real) / 10) /
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower) *
          10 * C *
          ((520 : Real) ^ (-23 : Real) *
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaLog1560Upper / 23 +
              1 / ((23 : Real) ^ 2))) := by
    gcongr
  refine le_trans hbound ?_
  dsimp [C]
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr
    (mul_pos (bsplineScale_pos 11) (bsplineAutocorrNorm_pos 11))))]
  rw [inv_pow]
  rw [Real.sq_sqrt (le_of_lt
    (mul_pos (bsplineScale_pos 11) (bsplineAutocorrNorm_pos 11)))]
  fin_cases n <;>
    norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaLog1560Upper,
      primaryK11RawOmegaATailRemainderRadius,
      primaryK11RawOmegaATailRemainderRadiusRat,
      primaryK11Ell, primaryK11EllRat,
      bsplineScale,
      bsplineAutocorrNorm,
      bsplineAutocorrDegree,
      centeredCardinalBSpline,
      positivePartPower,
      Finset.sum_range_succ,
      Nat.choose]

theorem controlK9RawOmegaATailLogMajorant_integral_le_tailRemainderRadius_after_520
    (n : CoeffIndex23) :
    ∫ eta in Set.Ioi (520 : Real),
      |controlK9Ell / Real.pi| * ((10 : Real) * Real.log (3 * eta)) *
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          9 controlK9Ell eta <=
      controlK9RawOmegaATailRemainderRadius n := by
  let C : Real :=
    |(Real.sqrt (bsplineScale 9 * bsplineAutocorrNorm 9))⁻¹| ^ 2 *
      (|(controlK9Ell / (2 * bsplineScale 9))|⁻¹) ^ (2 * (9 + 1))
  have hC_nonneg : 0 <= C := by
    dsimp [C]
    positivity
  have hmaj_eq : ∀ eta : Real,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          9 controlK9Ell eta = C * eta ^ (-20 : Real) := by
    intro eta
    dsimp [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant, C]
    norm_num
  have hfun :
      (fun eta : Real =>
        |controlK9Ell / Real.pi| * ((10 : Real) * Real.log (3 * eta)) *
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            9 controlK9Ell eta) =
      (fun eta : Real =>
        (|controlK9Ell / Real.pi| * (10 : Real) * C) *
          (Real.log (3 * eta) * eta ^ (-20 : Real))) := by
    funext eta
    rw [hmaj_eq]
    ring
  rw [hfun]
  rw [integral_const_mul]
  rw [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmega_integral_Ioi_log_three_mul_rpow_neg20_after_520]
  have hpi_lower_pos : 0 < Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower := by
    norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower]
  have hpi_bound :
      |controlK9Ell / Real.pi| <=
        ((3 : Real) / 10) / Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower := by
    have hpi_lb := Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower_le_pi
    have hinv :
        Real.pi⁻¹ <= Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hpi_lower_pos hpi_lb
    calc
      |controlK9Ell / Real.pi| = |controlK9Ell| * Real.pi⁻¹ := by
        rw [abs_div, abs_of_pos Real.pi_pos]
        rw [div_eq_mul_inv]
      _ <= |controlK9Ell| * Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = ((3 : Real) / 10) / Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower := by
        rw [show |controlK9Ell| = ((3 : Real) / 10) by
          norm_num [controlK9Ell, controlK9EllRat]]
        ring
  have hlog_bound :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmega_log_1560_le_upper
  have hI_le :
      (520 : Real) ^ (-19 : Real) *
          (Real.log (1560 : Real) / 19 + 1 / ((19 : Real) ^ 2)) <=
      (520 : Real) ^ (-19 : Real) *
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaLog1560Upper / 19 +
            1 / ((19 : Real) ^ 2)) := by
    gcongr
  have hcoef_nonneg :
      0 <= (((3 : Real) / 10) /
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower) * 10 * C := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) hpi_lower_pos.le) (by norm_num))
      hC_nonneg
  have hbound :
      |controlK9Ell / Real.pi| * 10 * C *
          ((520 : Real) ^ (-19 : Real) *
            (Real.log (1560 : Real) / 19 + 1 / ((19 : Real) ^ 2))) <=
      (((3 : Real) / 10) /
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower) *
          10 * C *
          ((520 : Real) ^ (-19 : Real) *
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaLog1560Upper / 19 +
              1 / ((19 : Real) ^ 2))) := by
    gcongr
  refine le_trans hbound ?_
  dsimp [C]
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr
    (mul_pos (bsplineScale_pos 9) (bsplineAutocorrNorm_pos 9))))]
  rw [inv_pow]
  rw [Real.sq_sqrt (le_of_lt
    (mul_pos (bsplineScale_pos 9) (bsplineAutocorrNorm_pos 9)))]
  fin_cases n <;>
    norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaPiLower,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.rawOmegaLog1560Upper,
      controlK9RawOmegaATailRemainderRadius,
      controlK9RawOmegaATailRemainderRadiusRat,
      controlK9Ell, controlK9EllRat,
      bsplineScale,
      bsplineAutocorrNorm,
      bsplineAutocorrDegree,
      centeredCardinalBSpline,
      positivePartPower,
      Finset.sum_range_succ,
      Nat.choose]

theorem primaryK11RawOmegaATailRemainder_abs_le_generated :
    ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n := by
  intro n
  change
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      11 primaryK11Ell ((n.1 : Real) / 4) rawOmegaATailWindowEnd| <=
      primaryK11RawOmegaATailRemainderRadius n
  exact
    (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant
      (U := rawOmegaATailWindowEnd) (omegaFactor := 10)
      (remainderRadius := primaryK11RawOmegaATailRemainderRadius)
      (by norm_num [rawOmegaATailWindowEnd])
      (by
        simpa [rawOmegaATailWindowEnd] using
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaATailLogMajorant_integrable_after_520)
      (by
        intro eta heta
        exact
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_abs_le_ten_logOmega_after_520
            eta (by simpa [rawOmegaATailWindowEnd] using heta))
      (by
        intro n
        simpa [rawOmegaATailWindowEnd] using
          primaryK11RawOmegaATailLogMajorant_integral_le_tailRemainderRadius_after_520 n)) n

theorem controlK9RawOmegaATailRemainder_abs_le_generated :
    ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n := by
  intro n
  change
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      9 controlK9Ell ((n.1 : Real) / 4) rawOmegaATailWindowEnd| <=
      controlK9RawOmegaATailRemainderRadius n
  exact
    (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant
      (U := rawOmegaATailWindowEnd) (omegaFactor := 10)
      (remainderRadius := controlK9RawOmegaATailRemainderRadius)
      (by norm_num [rawOmegaATailWindowEnd])
      (by
        simpa [rawOmegaATailWindowEnd] using
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaATailLogMajorant_integrable_after_520)
      (by
        intro eta heta
        exact
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_abs_le_ten_logOmega_after_520
            eta (by simpa [rawOmegaATailWindowEnd] using heta))
      (by
        intro n
        simpa [rawOmegaATailWindowEnd] using
          controlK9RawOmegaATailLogMajorant_integral_le_tailRemainderRadius_after_520 n)) n

/-- Primary direct analytic raw-Omega input constructor with profile
integrability discharged by the shared raw-Omega integrability theorem. -/
def primaryK11RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison_builtin_integrability
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n)
        (Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n)
        (Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteUpperF n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n)
        (Set.Ioc primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n)
        (Set.Ioc primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailUpperF n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  primaryK11RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison
    finiteLowerF finiteUpperF tailLowerF tailUpperF
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi
    hFiniteLowerInt hFiniteUpperInt
    hFiniteLower hFiniteUpper
    hFiniteLowerBound hFiniteUpperBound
    hTailLowerInt hTailUpperInt
    hTailLower hTailUpper
    hTailWindowLower hTailWindowUpper
    hTailRemainder

/-- Control direct analytic raw-Omega input constructor with profile
integrability discharged by the shared raw-Omega integrability theorem. -/
def controlK9RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison_builtin_integrability
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n)
        (Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n)
        (Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        finiteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          finiteUpperF n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n)
        (Set.Ioc controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n)
        (Set.Ioc controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        tailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          tailUpperF n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated :=
  controlK9RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison
    finiteLowerF finiteUpperF tailLowerF tailUpperF
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi
    hFiniteLowerInt hFiniteUpperInt
    hFiniteLower hFiniteUpper
    hFiniteLowerBound hFiniteUpperBound
    hTailLowerInt hTailUpperInt
    hTailLower hTailUpper
    hTailWindowLower hTailWindowUpper
    hTailRemainder

/-- Generator-facing constructor for the active direct analytic route.  The
profile integrability facts are filled from checked raw-Omega support, leaving
the generated import to provide only comparison functions, their window
integrability, pointwise bounds, scalar window containments, and direct tail
remainders. -/
def rawOmegaAAnalyticTailWindowInputs_of_generated_comparison_builtin_integrability
    (primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF :
      CoeffIndex23 → Real → Real)
    (controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF :
      CoeffIndex23 → Real → Real)
    (hPrimaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n)
        (Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hPrimaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n)
        (Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpperF n eta)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          primaryFiniteLowerF n eta)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          primaryFiniteUpperF n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailLowerF n)
        (Set.Ioc primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hPrimaryTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailUpperF n)
        (Set.Ioc primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpperF n eta)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          primaryTailLowerF n eta)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          primaryTailUpperF n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n)
        (Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hControlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n)
        (Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff))
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpperF n eta)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          controlFiniteLowerF n eta)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          controlFiniteUpperF n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailLowerF n)
        (Set.Ioc controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hControlTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailUpperF n)
        (Set.Ioc controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd))
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpperF n eta)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          controlTailLowerF n eta)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          controlTailUpperF n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    RawOmegaAAnalyticTailWindowInputs :=
  { primaryAnalytic :=
      primaryK11RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison_builtin_integrability
        primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF
        hPrimaryFiniteLowerInt hPrimaryFiniteUpperInt
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLowerInt hPrimaryTailUpperInt
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder
    controlAnalytic :=
      controlK9RawOmegaAComparisonTailWindowAnalyticPayload_generated_of_comparison_builtin_integrability
        controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF
        hControlFiniteLowerInt hControlFiniteUpperInt
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLowerInt hControlTailUpperInt
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder }

/-- Generator-facing constructor for quadratic comparison families.  The
generated import still has to prove the pointwise enclosures, scalar integral
containments, and tail remainders, but it no longer has to carry separate
integrability facts for each quadratic lower/upper comparison function. -/
def rawOmegaAAnalyticTailWindowInputs_of_generated_quadratic_comparison_builtin_integrability
    (primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper :
      RawOmegaAQuadraticComparison)
    (controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper :
      RawOmegaAQuadraticComparison)
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLower.eval n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpper.eval n eta)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          primaryFiniteLower.eval n eta)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          primaryFiniteUpper.eval n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLower.eval n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpper.eval n eta)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          primaryTailLower.eval n eta)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          primaryTailUpper.eval n eta) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLower.eval n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpper.eval n eta)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          controlFiniteLower.eval n eta)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real)
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
          controlFiniteUpper.eval n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLower.eval n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpper.eval n eta)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        ∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          controlTailLower.eval n eta)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
            controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
          controlTailUpper.eval n eta) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    RawOmegaAAnalyticTailWindowInputs :=
  rawOmegaAAnalyticTailWindowInputs_of_generated_comparison_builtin_integrability
    primaryFiniteLower.eval primaryFiniteUpper.eval primaryTailLower.eval primaryTailUpper.eval
    controlFiniteLower.eval controlFiniteUpper.eval controlTailLower.eval controlTailUpper.eval
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc primaryFiniteLower n (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff)
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc primaryFiniteUpper n (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff)
    hPrimaryFiniteLower hPrimaryFiniteUpper
    hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc primaryTailLower n
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd)
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc primaryTailUpper n
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd)
    hPrimaryTailLower hPrimaryTailUpper
    hPrimaryTailWindowLower hPrimaryTailWindowUpper
    hPrimaryTailRemainder
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc controlFiniteLower n (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff)
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc controlFiniteUpper n (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff)
    hControlFiniteLower hControlFiniteUpper
    hControlFiniteLowerBound hControlFiniteUpperBound
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc controlTailLower n
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd)
    (fun n =>
      RawOmegaAQuadraticComparison.integrableOn_Ioc controlTailUpper n
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd)
    hControlTailLower hControlTailUpper
    hControlTailWindowLower hControlTailWindowUpper
    hControlTailRemainder

/-- Single generated-import target for constant finite/tail comparison
functions plus direct tail-remainder bounds.  This route uses the structural
raw-Omega integrability theorems, but does not require a shared global
linear-growth witness for the tail remainders. -/
structure RawOmegaAConstComparisonDirectTailInputs where
  primaryFiniteLower : CoeffIndex23 → Real
  primaryFiniteUpper : CoeffIndex23 → Real
  primaryTailLower : CoeffIndex23 → Real
  primaryTailUpper : CoeffIndex23 → Real
  controlFiniteLower : CoeffIndex23 → Real
  controlFiniteUpper : CoeffIndex23 → Real
  controlTailLower : CoeffIndex23 → Real
  controlTailUpper : CoeffIndex23 → Real
  hPrimaryFiniteLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      primaryFiniteLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta
  hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        primaryFiniteUpper n
  hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        primaryFiniteLower n
  hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        primaryFiniteUpper n <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n
  hPrimaryTailLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      primaryTailLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta
  hPrimaryTailUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        primaryTailUpper n
  hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        primaryTailLower n
  hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
    (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        primaryTailUpper n <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hPrimaryTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      11 primaryK11Ell ((n.1 : Real) / 4)
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n
  hControlFiniteLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      controlFiniteLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta
  hControlFiniteUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        controlFiniteUpper n
  hControlFiniteLowerBound : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        controlFiniteLower n
  hControlFiniteUpperBound : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        controlFiniteUpper n <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n
  hControlTailLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      controlTailLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta
  hControlTailUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        controlTailUpper n
  hControlTailWindowLower : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        controlTailLower n
  hControlTailWindowUpper : ∀ n : CoeffIndex23,
    (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        controlTailUpper n <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hControlTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      9 controlK9Ell ((n.1 : Real) / 4)
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n

def RawOmegaAConstComparisonDirectTailInputs.toPayloads
    (inputs : RawOmegaAConstComparisonDirectTailInputs) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload ×
      ControlK9RawOmegaAComparisonTailWindowPayload :=
  rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability
    inputs.primaryFiniteLower inputs.primaryFiniteUpper
    inputs.primaryTailLower inputs.primaryTailUpper
    inputs.controlFiniteLower inputs.controlFiniteUpper
    inputs.controlTailLower inputs.controlTailUpper
    inputs.hPrimaryFiniteLower inputs.hPrimaryFiniteUpper
    inputs.hPrimaryFiniteLowerBound inputs.hPrimaryFiniteUpperBound
    inputs.hPrimaryTailLower inputs.hPrimaryTailUpper
    inputs.hPrimaryTailWindowLower inputs.hPrimaryTailWindowUpper
    inputs.hPrimaryTailRemainder
    inputs.hControlFiniteLower inputs.hControlFiniteUpper
    inputs.hControlFiniteLowerBound inputs.hControlFiniteUpperBound
    inputs.hControlTailLower inputs.hControlTailUpper
    inputs.hControlTailWindowLower inputs.hControlTailWindowUpper
    inputs.hControlTailRemainder

/-- Single generated-import target for the raw-Omega constant-comparison
tail-window route.  It bundles the comparison constants, pointwise window
bounds, scalar window containments, a shared growth witness for
`step22OmegaArchWeight`, and the generated radius domination checks for the
structural `U^-2` tail majorants. -/
structure RawOmegaAConstComparisonTailGrowthInputs where
  primaryFiniteLower : CoeffIndex23 → Real
  primaryFiniteUpper : CoeffIndex23 → Real
  primaryTailLower : CoeffIndex23 → Real
  primaryTailUpper : CoeffIndex23 → Real
  controlFiniteLower : CoeffIndex23 → Real
  controlFiniteUpper : CoeffIndex23 → Real
  controlTailLower : CoeffIndex23 → Real
  controlTailUpper : CoeffIndex23 → Real
  C0 : Real
  C1 : Real
  hC0 : 0 <= C0
  hC1 : 0 <= C1
  hgrowth : ∀ eta : Real,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| <=
      C0 + C1 * |eta|
  hPrimaryFiniteLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      primaryFiniteLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta
  hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        primaryFiniteUpper n
  hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        primaryFiniteLower n
  hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        primaryFiniteUpper n <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n
  hPrimaryTailLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      primaryTailLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta
  hPrimaryTailUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        primaryTailUpper n
  hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        primaryTailLower n
  hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
    (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        primaryTailUpper n <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hPrimaryTailRemainderRadius : ∀ n : CoeffIndex23,
    (|primaryK11Ell / Real.pi| *
      ((C0 + C1) *
        |(Real.sqrt (Q3.PSDpd.bsplineScale 11 *
          Q3.PSDpd.bsplineAutocorrNorm 11))⁻¹| ^ 2 *
        (|(primaryK11Ell /
          (2 * Q3.PSDpd.bsplineScale 11))|⁻¹) ^ 4)) *
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd ^
        (-2 : ℝ) / 2) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n
  hControlFiniteLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      controlFiniteLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta
  hControlFiniteUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc (0 : Real)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        controlFiniteUpper n
  hControlFiniteLowerBound : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        controlFiniteLower n
  hControlFiniteUpperBound : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
        controlFiniteUpper n <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n
  hControlTailLower : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      controlTailLower n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta
  hControlTailUpper : ∀ n : CoeffIndex23,
    ∀ eta ∈ Set.Ioc
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        controlTailUpper n
  hControlTailWindowLower : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        controlTailLower n
  hControlTailWindowUpper : ∀ n : CoeffIndex23,
    (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
        controlTailUpper n <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n
  hControlTailRemainderRadius : ∀ n : CoeffIndex23,
    (|controlK9Ell / Real.pi| *
      ((C0 + C1) *
        |(Real.sqrt (Q3.PSDpd.bsplineScale 9 *
          Q3.PSDpd.bsplineAutocorrNorm 9))⁻¹| ^ 2 *
        (|(controlK9Ell /
          (2 * Q3.PSDpd.bsplineScale 9))|⁻¹) ^ 4)) *
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd ^
        (-2 : ℝ) / 2) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n

def RawOmegaAConstComparisonTailGrowthInputs.toPayloads
    (inputs : RawOmegaAConstComparisonTailGrowthInputs) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload ×
      ControlK9RawOmegaAComparisonTailWindowPayload :=
  rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability_and_tail_growth
    inputs.primaryFiniteLower inputs.primaryFiniteUpper
    inputs.primaryTailLower inputs.primaryTailUpper
    inputs.controlFiniteLower inputs.controlFiniteUpper
    inputs.controlTailLower inputs.controlTailUpper
    inputs.C0 inputs.C1 inputs.hC0 inputs.hC1 inputs.hgrowth
    inputs.hPrimaryFiniteLower inputs.hPrimaryFiniteUpper
    inputs.hPrimaryFiniteLowerBound inputs.hPrimaryFiniteUpperBound
    inputs.hPrimaryTailLower inputs.hPrimaryTailUpper
    inputs.hPrimaryTailWindowLower inputs.hPrimaryTailWindowUpper
    inputs.hPrimaryTailRemainderRadius
    inputs.hControlFiniteLower inputs.hControlFiniteUpper
    inputs.hControlFiniteLowerBound inputs.hControlFiniteUpperBound
    inputs.hControlTailLower inputs.hControlTailUpper
    inputs.hControlTailWindowLower inputs.hControlTailWindowUpper
    inputs.hControlTailRemainderRadius

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
