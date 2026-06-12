import Q3.Proofs.PSD_CenteredCoeffRawOmegaATailWindowArithmeticSupport

set_option linter.mathlibStandardSet false
set_option autoImplicit false

/-!
Raw-Omega Step33 `A` tail-window full payload interfaces.

This module keeps the generator-facing analytic comparison payload surface out
of the prime/live generated support graph.  Generated comparison-integral code
can import this file together with the arithmetic payload import and assemble
the full raw-Omega `A` payload without rebuilding the downstream Step33 P/P0
receivers.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport

/-- Generator-facing primary raw-Omega `A` payload bundle for the finite-window
and tail-window comparison route. -/
structure PrimaryK11RawOmegaAComparisonTailWindowPayload where
  cutoff : Real
  tailEnd : Real
  finiteLower : CoeffIndex23 → Real
  finiteUpper : CoeffIndex23 → Real
  tailWindowLower : CoeffIndex23 → Real
  tailWindowUpper : CoeffIndex23 → Real
  tailRemainderRadius : CoeffIndex23 → Real
  tailRadius : CoeffIndex23 → Real
  finiteLowerF : CoeffIndex23 → Real → Real
  finiteUpperF : CoeffIndex23 → Real → Real
  tailLowerF : CoeffIndex23 → Real → Real
  tailUpperF : CoeffIndex23 → Real → Real
  hCutoff_nonneg : 0 <= cutoff
  hTailWindow : cutoff <= tailEnd
  hProfileInt : ∀ n : CoeffIndex23,
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4))
      (Set.Ioi (0 : Real))
  hFiniteLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) cutoff)
  hFiniteUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) cutoff)
  hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) cutoff,
    finiteLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta
  hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) cutoff,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta <=
      finiteUpperF n eta
  hFiniteLowerBound : ∀ n : CoeffIndex23,
    finiteLower n <= ∫ eta in Set.Ioc (0 : Real) cutoff, finiteLowerF n eta
  hFiniteUpperBound : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc (0 : Real) cutoff, finiteUpperF n eta) <= finiteUpper n
  hTailLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailLowerF n) (Set.Ioc cutoff tailEnd)
  hTailUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailUpperF n) (Set.Ioc cutoff tailEnd)
  hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc cutoff tailEnd,
    tailLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta
  hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc cutoff tailEnd,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta <=
      tailUpperF n eta
  hTailWindowLower : ∀ n : CoeffIndex23,
    tailWindowLower n <= ∫ eta in Set.Ioc cutoff tailEnd, tailLowerF n eta
  hTailWindowUpper : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc cutoff tailEnd, tailUpperF n eta) <= tailWindowUpper n
  hTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      11 primaryK11Ell ((n.1 : Real) / 4) tailEnd| <= tailRemainderRadius n
  hTailLowerArith : ∀ n : CoeffIndex23,
    -tailRadius n <= tailWindowLower n - tailRemainderRadius n
  hTailUpperArith : ∀ n : CoeffIndex23,
    tailWindowUpper n + tailRemainderRadius n <= tailRadius n
  hPayloadLowerArith : ∀ n : CoeffIndex23,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceLower n <=
      finiteLower n - tailRadius n
  hPayloadUpperArith : ∀ n : CoeffIndex23,
    finiteUpper n + tailRadius n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceUpper n

/-- Generator-facing control raw-Omega `A` payload bundle for the finite-window
and tail-window comparison route. -/
structure ControlK9RawOmegaAComparisonTailWindowPayload where
  cutoff : Real
  tailEnd : Real
  finiteLower : CoeffIndex23 → Real
  finiteUpper : CoeffIndex23 → Real
  tailWindowLower : CoeffIndex23 → Real
  tailWindowUpper : CoeffIndex23 → Real
  tailRemainderRadius : CoeffIndex23 → Real
  tailRadius : CoeffIndex23 → Real
  finiteLowerF : CoeffIndex23 → Real → Real
  finiteUpperF : CoeffIndex23 → Real → Real
  tailLowerF : CoeffIndex23 → Real → Real
  tailUpperF : CoeffIndex23 → Real → Real
  hCutoff_nonneg : 0 <= cutoff
  hTailWindow : cutoff <= tailEnd
  hProfileInt : ∀ n : CoeffIndex23,
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4))
      (Set.Ioi (0 : Real))
  hFiniteLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) cutoff)
  hFiniteUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) cutoff)
  hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) cutoff,
    finiteLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta
  hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) cutoff,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta <=
      finiteUpperF n eta
  hFiniteLowerBound : ∀ n : CoeffIndex23,
    finiteLower n <= ∫ eta in Set.Ioc (0 : Real) cutoff, finiteLowerF n eta
  hFiniteUpperBound : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc (0 : Real) cutoff, finiteUpperF n eta) <= finiteUpper n
  hTailLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailLowerF n) (Set.Ioc cutoff tailEnd)
  hTailUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailUpperF n) (Set.Ioc cutoff tailEnd)
  hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc cutoff tailEnd,
    tailLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta
  hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc cutoff tailEnd,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta <=
      tailUpperF n eta
  hTailWindowLower : ∀ n : CoeffIndex23,
    tailWindowLower n <= ∫ eta in Set.Ioc cutoff tailEnd, tailLowerF n eta
  hTailWindowUpper : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc cutoff tailEnd, tailUpperF n eta) <= tailWindowUpper n
  hTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      9 controlK9Ell ((n.1 : Real) / 4) tailEnd| <= tailRemainderRadius n
  hTailLowerArith : ∀ n : CoeffIndex23,
    -tailRadius n <= tailWindowLower n - tailRemainderRadius n
  hTailUpperArith : ∀ n : CoeffIndex23,
    tailWindowUpper n + tailRemainderRadius n <= tailRadius n
  hPayloadLowerArith : ∀ n : CoeffIndex23,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceLower n <=
      finiteLower n - tailRadius n
  hPayloadUpperArith : ∀ n : CoeffIndex23,
    finiteUpper n + tailRadius n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceUpper n

/-- Analytic-only primary raw-Omega comparison payload, parameterized by the
already checked arithmetic payload.  Generated comparison-integral imports
should target this structure before assembling the full payload. -/
structure PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
    (arith : PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload) where
  finiteLowerF : CoeffIndex23 → Real → Real
  finiteUpperF : CoeffIndex23 → Real → Real
  tailLowerF : CoeffIndex23 → Real → Real
  tailUpperF : CoeffIndex23 → Real → Real
  hProfileInt : ∀ n : CoeffIndex23,
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4))
      (Set.Ioi (0 : Real))
  hFiniteLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) arith.cutoff)
  hFiniteUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) arith.cutoff)
  hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
    finiteLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta
  hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta <=
      finiteUpperF n eta
  hFiniteLowerBound : ∀ n : CoeffIndex23,
    arith.finiteLower n <=
      ∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteLowerF n eta
  hFiniteUpperBound : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteUpperF n eta) <=
      arith.finiteUpper n
  hTailLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailLowerF n) (Set.Ioc arith.cutoff arith.tailEnd)
  hTailUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailUpperF n) (Set.Ioc arith.cutoff arith.tailEnd)
  hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
    tailLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta
  hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4) eta <=
      tailUpperF n eta
  hTailWindowLower : ∀ n : CoeffIndex23,
    arith.tailWindowLower n <=
      ∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailLowerF n eta
  hTailWindowUpper : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailUpperF n eta) <=
      arith.tailWindowUpper n
  hTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      11 primaryK11Ell ((n.1 : Real) / 4) arith.tailEnd| <=
      arith.tailRemainderRadius n

/-- Analytic-only control raw-Omega comparison payload, parameterized by the
already checked arithmetic payload. -/
structure ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
    (arith : ControlK9RawOmegaAComparisonTailWindowArithmeticPayload) where
  finiteLowerF : CoeffIndex23 → Real → Real
  finiteUpperF : CoeffIndex23 → Real → Real
  tailLowerF : CoeffIndex23 → Real → Real
  tailUpperF : CoeffIndex23 → Real → Real
  hProfileInt : ∀ n : CoeffIndex23,
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4))
      (Set.Ioi (0 : Real))
  hFiniteLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) arith.cutoff)
  hFiniteUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) arith.cutoff)
  hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
    finiteLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta
  hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta <=
      finiteUpperF n eta
  hFiniteLowerBound : ∀ n : CoeffIndex23,
    arith.finiteLower n <=
      ∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteLowerF n eta
  hFiniteUpperBound : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteUpperF n eta) <=
      arith.finiteUpper n
  hTailLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailLowerF n) (Set.Ioc arith.cutoff arith.tailEnd)
  hTailUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (tailUpperF n) (Set.Ioc arith.cutoff arith.tailEnd)
  hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
    tailLowerF n eta <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta
  hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4) eta <=
      tailUpperF n eta
  hTailWindowLower : ∀ n : CoeffIndex23,
    arith.tailWindowLower n <=
      ∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailLowerF n eta
  hTailWindowUpper : ∀ n : CoeffIndex23,
    (∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailUpperF n eta) <=
      arith.tailWindowUpper n
  hTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      9 controlK9Ell ((n.1 : Real) / 4) arith.tailEnd| <=
      arith.tailRemainderRadius n

def primaryK11RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
    (arith : PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload)
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) arith.cutoff))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) arith.cutoff))
    (hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
      finiteLowerF n eta <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      arith.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteUpperF n eta) <=
        arith.finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n) (Set.Ioc arith.cutoff arith.tailEnd))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n) (Set.Ioc arith.cutoff arith.tailEnd))
    (hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
      tailLowerF n eta <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      arith.tailWindowLower n <=
        ∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailUpperF n eta) <=
        arith.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) arith.tailEnd| <=
        arith.tailRemainderRadius n) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload := by
  exact
    { cutoff := arith.cutoff
      tailEnd := arith.tailEnd
      finiteLower := arith.finiteLower
      finiteUpper := arith.finiteUpper
      tailWindowLower := arith.tailWindowLower
      tailWindowUpper := arith.tailWindowUpper
      tailRemainderRadius := arith.tailRemainderRadius
      tailRadius := arith.tailRadius
      finiteLowerF := finiteLowerF
      finiteUpperF := finiteUpperF
      tailLowerF := tailLowerF
      tailUpperF := tailUpperF
      hCutoff_nonneg := arith.hCutoff_nonneg
      hTailWindow := arith.hTailWindow
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
      hTailRemainder := hTailRemainder
      hTailLowerArith := arith.hTailLowerArith
      hTailUpperArith := arith.hTailUpperArith
      hPayloadLowerArith := arith.hPayloadLowerArith
      hPayloadUpperArith := arith.hPayloadUpperArith }

def primaryK11RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_analytic
    (arith : PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload)
    (analytic : PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload arith) :
    PrimaryK11RawOmegaAComparisonTailWindowPayload := by
  exact
    primaryK11RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
      arith
      analytic.finiteLowerF analytic.finiteUpperF
      analytic.tailLowerF analytic.tailUpperF
      analytic.hProfileInt
      analytic.hFiniteLowerInt analytic.hFiniteUpperInt
      analytic.hFiniteLower analytic.hFiniteUpper
      analytic.hFiniteLowerBound analytic.hFiniteUpperBound
      analytic.hTailLowerInt analytic.hTailUpperInt
      analytic.hTailLower analytic.hTailUpper
      analytic.hTailWindowLower analytic.hTailWindowUpper
      analytic.hTailRemainder

def controlK9RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
    (arith : ControlK9RawOmegaAComparisonTailWindowArithmeticPayload)
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) arith.cutoff))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) arith.cutoff))
    (hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
      finiteLowerF n eta <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) arith.cutoff,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      arith.finiteLower n <=
        ∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) arith.cutoff, finiteUpperF n eta) <=
        arith.finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n) (Set.Ioc arith.cutoff arith.tailEnd))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n) (Set.Ioc arith.cutoff arith.tailEnd))
    (hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
      tailLowerF n eta <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc arith.cutoff arith.tailEnd,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      arith.tailWindowLower n <=
        ∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc arith.cutoff arith.tailEnd, tailUpperF n eta) <=
        arith.tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) arith.tailEnd| <=
        arith.tailRemainderRadius n) :
    ControlK9RawOmegaAComparisonTailWindowPayload := by
  exact
    { cutoff := arith.cutoff
      tailEnd := arith.tailEnd
      finiteLower := arith.finiteLower
      finiteUpper := arith.finiteUpper
      tailWindowLower := arith.tailWindowLower
      tailWindowUpper := arith.tailWindowUpper
      tailRemainderRadius := arith.tailRemainderRadius
      tailRadius := arith.tailRadius
      finiteLowerF := finiteLowerF
      finiteUpperF := finiteUpperF
      tailLowerF := tailLowerF
      tailUpperF := tailUpperF
      hCutoff_nonneg := arith.hCutoff_nonneg
      hTailWindow := arith.hTailWindow
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
      hTailRemainder := hTailRemainder
      hTailLowerArith := arith.hTailLowerArith
      hTailUpperArith := arith.hTailUpperArith
      hPayloadLowerArith := arith.hPayloadLowerArith
      hPayloadUpperArith := arith.hPayloadUpperArith }

def controlK9RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_analytic
    (arith : ControlK9RawOmegaAComparisonTailWindowArithmeticPayload)
    (analytic : ControlK9RawOmegaAComparisonTailWindowAnalyticPayload arith) :
    ControlK9RawOmegaAComparisonTailWindowPayload := by
  exact
    controlK9RawOmegaAComparisonTailWindowPayload_of_arithmetic_and_comparison
      arith
      analytic.finiteLowerF analytic.finiteUpperF
      analytic.tailLowerF analytic.tailUpperF
      analytic.hProfileInt
      analytic.hFiniteLowerInt analytic.hFiniteUpperInt
      analytic.hFiniteLower analytic.hFiniteUpper
      analytic.hFiniteLowerBound analytic.hFiniteUpperBound
      analytic.hTailLowerInt analytic.hTailUpperInt
      analytic.hTailLower analytic.hTailUpper
      analytic.hTailWindowLower analytic.hTailWindowUpper
      analytic.hTailRemainder

/-- Analytic-only primary raw-Omega direct integral payload, parameterized by
the already checked arithmetic payload.

This is the generator-facing landing surface for Arb-backed chunk-integral
certificates: the generated import proves direct lower/upper bounds for the
raw-Omega finite window and tail window, rather than proving pointwise
polynomial comparison envelopes. -/
structure PrimaryK11RawOmegaADirectTailWindowAnalyticPayload
    (arith : PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload) where
  hProfileInt : ∀ n : CoeffIndex23,
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4))
      (Set.Ioi (0 : Real))
  hFiniteLower : ∀ n : CoeffIndex23,
    arith.finiteLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        11 primaryK11Ell ((n.1 : Real) / 4) arith.cutoff
  hFiniteUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        11 primaryK11Ell ((n.1 : Real) / 4) arith.cutoff <=
    arith.finiteUpper n
  hTailWindowLower : ∀ n : CoeffIndex23,
    arith.tailWindowLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        11 primaryK11Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd
  hTailWindowUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        11 primaryK11Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd <=
    arith.tailWindowUpper n
  hTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      11 primaryK11Ell ((n.1 : Real) / 4) arith.tailEnd| <=
      arith.tailRemainderRadius n

/-- Analytic-only control raw-Omega direct integral payload, parameterized by
the already checked arithmetic payload. -/
structure ControlK9RawOmegaADirectTailWindowAnalyticPayload
    (arith : ControlK9RawOmegaAComparisonTailWindowArithmeticPayload) where
  hProfileInt : ∀ n : CoeffIndex23,
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4))
      (Set.Ioi (0 : Real))
  hFiniteLower : ∀ n : CoeffIndex23,
    arith.finiteLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        9 controlK9Ell ((n.1 : Real) / 4) arith.cutoff
  hFiniteUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAFinitePart
        9 controlK9Ell ((n.1 : Real) / 4) arith.cutoff <=
    arith.finiteUpper n
  hTailWindowLower : ∀ n : CoeffIndex23,
    arith.tailWindowLower n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        9 controlK9Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd
  hTailWindowUpper : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart
        9 controlK9Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd <=
    arith.tailWindowUpper n
  hTailRemainder : ∀ n : CoeffIndex23,
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
      9 controlK9Ell ((n.1 : Real) / 4) arith.tailEnd| <=
      arith.tailRemainderRadius n

def primaryK11RawOmegaAFiniteTailBoundsCert_of_arithmetic_and_directTailWindow
    (arith : PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload)
    (analytic : PrimaryK11RawOmegaADirectTailWindowAnalyticPayload arith) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert
      arith.cutoff arith.finiteLower arith.finiteUpper arith.tailRadius := by
  refine ⟨?_⟩
  intro n
  have hTailWindowCert :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowIntervalCert
        11 primaryK11Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd
        (arith.tailWindowLower n) (arith.tailWindowUpper n)
        (arith.tailRemainderRadius n) :=
    { hWindowLower := analytic.hTailWindowLower n
      hWindowUpper := analytic.hTailWindowUpper n
      hRemainder := analytic.hTailRemainder n }
  have hTail :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) arith.cutoff| <=
        arith.tailRadius n :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATail_abs_le_of_tailWindowIntervalCert
      11 primaryK11Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd
      (arith.tailWindowLower n) (arith.tailWindowUpper n)
      (arith.tailRemainderRadius n) (arith.tailRadius n)
      arith.hTailWindow
      ((analytic.hProfileInt n).mono_set (by
        intro eta heta
        exact lt_of_le_of_lt arith.hCutoff_nonneg heta))
      hTailWindowCert
      (arith.hTailLowerArith n) (arith.hTailUpperArith n)
  exact
    { hFiniteLower := analytic.hFiniteLower n
      hFiniteUpper := analytic.hFiniteUpper n
      hTail := hTail
      hLower := arith.hPayloadLowerArith n
      hUpper := arith.hPayloadUpperArith n }

def controlK9RawOmegaAFiniteTailBoundsCert_of_arithmetic_and_directTailWindow
    (arith : ControlK9RawOmegaAComparisonTailWindowArithmeticPayload)
    (analytic : ControlK9RawOmegaADirectTailWindowAnalyticPayload arith) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert
      arith.cutoff arith.finiteLower arith.finiteUpper arith.tailRadius := by
  refine ⟨?_⟩
  intro n
  have hTailWindowCert :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowIntervalCert
        9 controlK9Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd
        (arith.tailWindowLower n) (arith.tailWindowUpper n)
        (arith.tailRemainderRadius n) :=
    { hWindowLower := analytic.hTailWindowLower n
      hWindowUpper := analytic.hTailWindowUpper n
      hRemainder := analytic.hTailRemainder n }
  have hTail :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) arith.cutoff| <=
        arith.tailRadius n :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATail_abs_le_of_tailWindowIntervalCert
      9 controlK9Ell ((n.1 : Real) / 4) arith.cutoff arith.tailEnd
      (arith.tailWindowLower n) (arith.tailWindowUpper n)
      (arith.tailRemainderRadius n) (arith.tailRadius n)
      arith.hTailWindow
      ((analytic.hProfileInt n).mono_set (by
        intro eta heta
        exact lt_of_le_of_lt arith.hCutoff_nonneg heta))
      hTailWindowCert
      (arith.hTailLowerArith n) (arith.hTailUpperArith n)
  exact
    { hFiniteLower := analytic.hFiniteLower n
      hFiniteUpper := analytic.hFiniteUpper n
      hTail := hTail
      hLower := arith.hPayloadLowerArith n
      hUpper := arith.hPayloadUpperArith n }

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
