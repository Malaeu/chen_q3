import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker

set_option linter.mathlibStandardSet false
set_option autoImplicit false

/-!
Raw-Omega Taylor/model payload adapter.

This module is the generated-import target shape for the active Step33A.1-A
raw-Omega route.  A concrete generator should fill the four payload structures
below with Taylor/model certificates and validity proofs; this file folds those
proofs into the existing chunked-range receiver.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkTaylorPayload

open CenteredCoeffPayloadImport
open scoped BigOperators

structure PrimaryFinite where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      11 primaryK11Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i : Real))
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  valid : ∀ n : CoeffIndex23, ∀ i : Nat, ∀ hi : i < 26,
    (cert n i hi).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure PrimaryTail where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      11 primaryK11Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  valid : ∀ n : CoeffIndex23, ∀ i : Nat, ∀ hi : i < 26,
    (cert n i hi).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure ControlFinite where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      9 controlK9Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i : Real))
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  valid : ∀ n : CoeffIndex23, ∀ i : Nat, ∀ hi : i < 26,
    (cert n i hi).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure ControlTail where
  chunkLower : CoeffIndex23 -> Nat -> Real
  chunkUpper : CoeffIndex23 -> Nat -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 ->
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      9 controlK9Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
      (chunkLower n i) (chunkUpper n i)
  valid : ∀ n : CoeffIndex23, ∀ i : Nat, ∀ hi : i < 26,
    (cert n i hi).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkLower n i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkUpper n i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

def chunkValueFromFin26 (f : Fin 26 -> Real) (i : Nat) : Real :=
  if h : i < 26 then f ⟨i, h⟩ else 0

theorem chunkValueFromFin26_apply (f : Fin 26 -> Real) (i : Fin 26) :
    chunkValueFromFin26 f i.1 = f i := by
  unfold chunkValueFromFin26
  simp [i.2]

structure PrimaryFiniteFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      11 primaryK11Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  valid : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure PrimaryTailFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      11 primaryK11Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  valid : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure ControlFiniteFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      9 controlK9Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  valid : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure ControlTailFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      9 controlK9Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  valid : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).Valid
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure PrimaryFiniteResidualAnchorFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      11 primaryK11Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  envelope : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ResidualAnchorEnvelopeData
      (cert n i)
  hRadiusNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).radius : Real)
  hRemainderNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).remainder : Real)
  hLeft : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    ((cert n i).center : Real) - ((cert n i).radius : Real) <=
      ((0 : Real) + (10 : Real) * (i.1 : Real))
  hRight : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real)) <=
      ((cert n i).center : Real) + ((cert n i).radius : Real)
  hIntegralLower : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    chunkValueFromFin26 (chunkLower n) i.1 <= (cert n i).lowerModelIntegral
  hIntegralUpper : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).upperModelIntegral <= chunkValueFromFin26 (chunkUpper n) i.1
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure PrimaryTailResidualAnchorFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      11 primaryK11Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  envelope : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ResidualAnchorEnvelopeData
      (cert n i)
  hRadiusNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).radius : Real)
  hRemainderNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).remainder : Real)
  hLeft : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    ((cert n i).center : Real) - ((cert n i).radius : Real) <=
      rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real)
  hRight : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real) <=
      ((cert n i).center : Real) + ((cert n i).radius : Real)
  hIntegralLower : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    chunkValueFromFin26 (chunkLower n) i.1 <= (cert n i).lowerModelIntegral
  hIntegralUpper : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).upperModelIntegral <= chunkValueFromFin26 (chunkUpper n) i.1
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure ControlFiniteResidualAnchorFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      9 controlK9Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  envelope : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ResidualAnchorEnvelopeData
      (cert n i)
  hRadiusNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).radius : Real)
  hRemainderNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).remainder : Real)
  hLeft : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    ((cert n i).center : Real) - ((cert n i).radius : Real) <=
      ((0 : Real) + (10 : Real) * (i.1 : Real))
  hRight : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real)) <=
      ((cert n i).center : Real) + ((cert n i).radius : Real)
  hIntegralLower : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    chunkValueFromFin26 (chunkLower n) i.1 <= (cert n i).lowerModelIntegral
  hIntegralUpper : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).upperModelIntegral <= chunkValueFromFin26 (chunkUpper n) i.1
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure ControlTailResidualAnchorFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  cert : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
      9 controlK9Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  envelope : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ResidualAnchorEnvelopeData
      (cert n i)
  hRadiusNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).radius : Real)
  hRemainderNonneg : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    0 <= ((cert n i).remainder : Real)
  hLeft : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    ((cert n i).center : Real) - ((cert n i).radius : Real) <=
      rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real)
  hRight : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real) <=
      ((cert n i).center : Real) + ((cert n i).radius : Real)
  hIntegralLower : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    chunkValueFromFin26 (chunkLower n) i.1 <= (cert n i).lowerModelIntegral
  hIntegralUpper : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    (cert n i).upperModelIntegral <= chunkValueFromFin26 (chunkUpper n) i.1
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

def PrimaryFiniteFin.toPrimaryFinite
    (payload : PrimaryFiniteFin) :
    PrimaryFinite :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    cert := by
      intro n i hi
      exact payload.cert n ⟨i, hi⟩
    valid := by
      intro n i hi
      exact payload.valid n ⟨i, hi⟩
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryTailFin.toPrimaryTail
    (payload : PrimaryTailFin) :
    PrimaryTail :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    cert := by
      intro n i hi
      exact payload.cert n ⟨i, hi⟩
    valid := by
      intro n i hi
      exact payload.valid n ⟨i, hi⟩
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlFiniteFin.toControlFinite
    (payload : ControlFiniteFin) :
    ControlFinite :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    cert := by
      intro n i hi
      exact payload.cert n ⟨i, hi⟩
    valid := by
      intro n i hi
      exact payload.valid n ⟨i, hi⟩
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlTailFin.toControlTail
    (payload : ControlTailFin) :
    ControlTail :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    cert := by
      intro n i hi
      exact payload.cert n ⟨i, hi⟩
    valid := by
      intro n i hi
      exact payload.valid n ⟨i, hi⟩
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryFiniteResidualAnchorFin.toPrimaryFiniteFin
    (payload : PrimaryFiniteResidualAnchorFin) :
    PrimaryFiniteFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    cert := payload.cert
    valid := by
      intro n i
      exact
        RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_residual_anchor_envelope_data_model_integral_bounds
          n i.1 (payload.cert n i) (payload.envelope n i)
          (payload.hRadiusNonneg n i) (payload.hRemainderNonneg n i)
          (payload.hLeft n i) (payload.hRight n i)
          (payload.hIntegralLower n i) (payload.hIntegralUpper n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryTailResidualAnchorFin.toPrimaryTailFin
    (payload : PrimaryTailResidualAnchorFin) :
    PrimaryTailFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    cert := payload.cert
    valid := by
      intro n i
      exact
        RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_residual_anchor_envelope_data_model_integral_bounds
          n i.1 (payload.cert n i) (payload.envelope n i)
          (payload.hRadiusNonneg n i) (payload.hRemainderNonneg n i)
          (payload.hLeft n i) (payload.hRight n i)
          (payload.hIntegralLower n i) (payload.hIntegralUpper n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlFiniteResidualAnchorFin.toControlFiniteFin
    (payload : ControlFiniteResidualAnchorFin) :
    ControlFiniteFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    cert := payload.cert
    valid := by
      intro n i
      exact
        RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_residual_anchor_envelope_data_model_integral_bounds
          n i.1 (payload.cert n i) (payload.envelope n i)
          (payload.hRadiusNonneg n i) (payload.hRemainderNonneg n i)
          (payload.hLeft n i) (payload.hRight n i)
          (payload.hIntegralLower n i) (payload.hIntegralUpper n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlTailResidualAnchorFin.toControlTailFin
    (payload : ControlTailResidualAnchorFin) :
    ControlTailFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    cert := payload.cert
    valid := by
      intro n i
      exact
        RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_residual_anchor_envelope_data_model_integral_bounds
          n i.1 (payload.cert n i) (payload.envelope n i)
          (payload.hRadiusNonneg n i) (payload.hRemainderNonneg n i)
          (payload.hLeft n i) (payload.hRight n i)
          (payload.hIntegralLower n i) (payload.hIntegralUpper n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

structure PrimaryFiniteRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert
      11 primaryK11Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure PrimaryTailRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert
      11 primaryK11Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure ControlFiniteRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert
      9 controlK9Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure ControlTailRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert
      9 controlK9Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure PrimaryFiniteResidualAnchorRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData
      11 primaryK11Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure PrimaryTailResidualAnchorRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData
      11 primaryK11Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure ControlFiniteResidualAnchorRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData
      9 controlK9Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure ControlTailResidualAnchorRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData
      9 controlK9Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure PrimaryFiniteCellSlopeDirectEnvelopeRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
      11 primaryK11Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure PrimaryTailCellSlopeDirectEnvelopeRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
      11 primaryK11Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

structure ControlFiniteCellSlopeDirectEnvelopeRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
      9 controlK9Ell ((n.1 : Real) / 4)
      ((0 : Real) + (10 : Real) * (i.1 : Real))
      ((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n

structure ControlTailCellSlopeDirectEnvelopeRefinedFin where
  chunkLower : CoeffIndex23 -> Fin 26 -> Real
  chunkUpper : CoeffIndex23 -> Fin 26 -> Real
  data : ∀ n : CoeffIndex23, ∀ i : Fin 26,
    RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
      9 controlK9Ell ((n.1 : Real) / 4)
      (rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))
      (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))
      (chunkValueFromFin26 (chunkLower n) i.1)
      (chunkValueFromFin26 (chunkUpper n) i.1)
  hLowerSum : ∀ n : CoeffIndex23,
    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
      ∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkLower n) i
  hUpperSum : ∀ n : CoeffIndex23,
    (∑ i ∈ Finset.range 26, chunkValueFromFin26 (chunkUpper n) i) <=
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n

def PrimaryFinite.toChunkedRangePayload
    (payload : PrimaryFinite) :
    PrimaryK11RawOmegaAFiniteWindowChunkedRangePayload :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
          11 primaryK11Ell ((n.1 : Real) / 4)
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.chunkLower n i) (payload.chunkUpper n i)
          (payload.cert n i hi) (payload.valid n i hi)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryTail.toChunkedRangePayload
    (payload : PrimaryTail) :
    PrimaryK11RawOmegaATailWindowChunkedRangePayload :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
          11 primaryK11Ell ((n.1 : Real) / 4)
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.chunkLower n i) (payload.chunkUpper n i)
          (payload.cert n i hi) (payload.valid n i hi)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum
    hRemainder := primaryK11RawOmegaATailRemainder_abs_le_generated }

def ControlFinite.toChunkedRangePayload
    (payload : ControlFinite) :
    ControlK9RawOmegaAFiniteWindowChunkedRangePayload :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
          9 controlK9Ell ((n.1 : Real) / 4)
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.chunkLower n i) (payload.chunkUpper n i)
          (payload.cert n i hi) (payload.valid n i hi)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlTail.toChunkedRangePayload
    (payload : ControlTail) :
    ControlK9RawOmegaATailWindowChunkedRangePayload :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
          9 controlK9Ell ((n.1 : Real) / 4)
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.chunkLower n i) (payload.chunkUpper n i)
          (payload.cert n i hi) (payload.valid n i hi)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum
    hRemainder := controlK9RawOmegaATailRemainder_abs_le_generated }

def PrimaryFiniteRefinedFin.toChunkedRangePayload
    (payload : PrimaryFiniteRefinedFin) :
    PrimaryK11RawOmegaAFiniteWindowChunkedRangePayload :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunks
          (payload.data n ⟨i, hi⟩)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryTailRefinedFin.toChunkedRangePayload
    (payload : PrimaryTailRefinedFin) :
    PrimaryK11RawOmegaATailWindowChunkedRangePayload :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunks
          (payload.data n ⟨i, hi⟩)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum
    hRemainder := primaryK11RawOmegaATailRemainder_abs_le_generated }

def ControlFiniteRefinedFin.toChunkedRangePayload
    (payload : ControlFiniteRefinedFin) :
    ControlK9RawOmegaAFiniteWindowChunkedRangePayload :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunks
          (payload.data n ⟨i, hi⟩)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlTailRefinedFin.toChunkedRangePayload
    (payload : ControlTailRefinedFin) :
    ControlK9RawOmegaATailWindowChunkedRangePayload :=
  { chunkLower := fun n i => chunkValueFromFin26 (payload.chunkLower n) i
    chunkUpper := fun n i => chunkValueFromFin26 (payload.chunkUpper n) i
    chunkCert := by
      intro n i hi
      exact
        RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunks
          (payload.data n ⟨i, hi⟩)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum
    hRemainder := controlK9RawOmegaATailRemainder_abs_le_generated }

def PrimaryFiniteResidualAnchorRefinedFin.toPrimaryFiniteRefinedFin
    (payload : PrimaryFiniteResidualAnchorRefinedFin) :
    PrimaryFiniteRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryTailResidualAnchorRefinedFin.toPrimaryTailRefinedFin
    (payload : PrimaryTailResidualAnchorRefinedFin) :
    PrimaryTailRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlFiniteResidualAnchorRefinedFin.toControlFiniteRefinedFin
    (payload : ControlFiniteResidualAnchorRefinedFin) :
    ControlFiniteRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlTailResidualAnchorRefinedFin.toControlTailRefinedFin
    (payload : ControlTailResidualAnchorRefinedFin) :
    ControlTailRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryFiniteCellSlopeDirectEnvelopeRefinedFin.toPrimaryFiniteRefinedFin
    (payload : PrimaryFiniteCellSlopeDirectEnvelopeRefinedFin) :
    PrimaryFiniteRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def PrimaryTailCellSlopeDirectEnvelopeRefinedFin.toPrimaryTailRefinedFin
    (payload : PrimaryTailCellSlopeDirectEnvelopeRefinedFin) :
    PrimaryTailRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlFiniteCellSlopeDirectEnvelopeRefinedFin.toControlFiniteRefinedFin
    (payload : ControlFiniteCellSlopeDirectEnvelopeRefinedFin) :
    ControlFiniteRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

def ControlTailCellSlopeDirectEnvelopeRefinedFin.toControlTailRefinedFin
    (payload : ControlTailCellSlopeDirectEnvelopeRefinedFin) :
    ControlTailRefinedFin :=
  { chunkLower := payload.chunkLower
    chunkUpper := payload.chunkUpper
    data := by
      intro n i
      exact
        RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
          (payload.data n i)
    hLowerSum := payload.hLowerSum
    hUpperSum := payload.hUpperSum }

structure Payload where
  primaryFinite : PrimaryFinite
  primaryTail : PrimaryTail
  controlFinite : ControlFinite
  controlTail : ControlTail

structure PayloadFin where
  primaryFinite : PrimaryFiniteFin
  primaryTail : PrimaryTailFin
  controlFinite : ControlFiniteFin
  controlTail : ControlTailFin

structure ResidualAnchorPayloadFin where
  primaryFinite : PrimaryFiniteResidualAnchorFin
  primaryTail : PrimaryTailResidualAnchorFin
  controlFinite : ControlFiniteResidualAnchorFin
  controlTail : ControlTailResidualAnchorFin

structure RefinedPayloadFin where
  primaryFinite : PrimaryFiniteRefinedFin
  primaryTail : PrimaryTailRefinedFin
  controlFinite : ControlFiniteRefinedFin
  controlTail : ControlTailRefinedFin

structure ResidualAnchorRefinedPayloadFin where
  primaryFinite : PrimaryFiniteResidualAnchorRefinedFin
  primaryTail : PrimaryTailResidualAnchorRefinedFin
  controlFinite : ControlFiniteResidualAnchorRefinedFin
  controlTail : ControlTailResidualAnchorRefinedFin

structure CellSlopeDirectEnvelopeRefinedPayloadFin where
  primaryFinite : PrimaryFiniteCellSlopeDirectEnvelopeRefinedFin
  primaryTail : PrimaryTailCellSlopeDirectEnvelopeRefinedFin
  controlFinite : ControlFiniteCellSlopeDirectEnvelopeRefinedFin
  controlTail : ControlTailCellSlopeDirectEnvelopeRefinedFin

def PayloadFin.toPayload
    (payload : PayloadFin) :
    Payload :=
  { primaryFinite := payload.primaryFinite.toPrimaryFinite
    primaryTail := payload.primaryTail.toPrimaryTail
    controlFinite := payload.controlFinite.toControlFinite
    controlTail := payload.controlTail.toControlTail }

def ResidualAnchorPayloadFin.toPayloadFin
    (payload : ResidualAnchorPayloadFin) :
    PayloadFin :=
  { primaryFinite := payload.primaryFinite.toPrimaryFiniteFin
    primaryTail := payload.primaryTail.toPrimaryTailFin
    controlFinite := payload.controlFinite.toControlFiniteFin
    controlTail := payload.controlTail.toControlTailFin }

def ResidualAnchorRefinedPayloadFin.toRefinedPayloadFin
    (payload : ResidualAnchorRefinedPayloadFin) :
    RefinedPayloadFin :=
  { primaryFinite := payload.primaryFinite.toPrimaryFiniteRefinedFin
    primaryTail := payload.primaryTail.toPrimaryTailRefinedFin
    controlFinite := payload.controlFinite.toControlFiniteRefinedFin
    controlTail := payload.controlTail.toControlTailRefinedFin }

def CellSlopeDirectEnvelopeRefinedPayloadFin.toRefinedPayloadFin
    (payload : CellSlopeDirectEnvelopeRefinedPayloadFin) :
    RefinedPayloadFin :=
  { primaryFinite := payload.primaryFinite.toPrimaryFiniteRefinedFin
    primaryTail := payload.primaryTail.toPrimaryTailRefinedFin
    controlFinite := payload.controlFinite.toControlFiniteRefinedFin
    controlTail := payload.controlTail.toControlTailRefinedFin }

def Payload.toChunkedRangePayload
    (payload : Payload) :
    RawOmegaAChunkedRangePayload :=
  { primaryFinite := payload.primaryFinite.toChunkedRangePayload
    primaryTail := payload.primaryTail.toChunkedRangePayload
    controlFinite := payload.controlFinite.toChunkedRangePayload
    controlTail := payload.controlTail.toChunkedRangePayload }

def Payload.toChunkIntegralBoundsCert
    (payload : Payload) :
    RawOmegaAChunkIntegralBoundsCert :=
  payload.toChunkedRangePayload.toChunkIntegralBoundsCert

def Payload.toDirectTailWindowInputs
    (payload : Payload) :
    RawOmegaADirectTailWindowInputs :=
  payload.toChunkIntegralBoundsCert.toDirectTailWindowInputs

def PayloadFin.toChunkedRangePayload
    (payload : PayloadFin) :
    RawOmegaAChunkedRangePayload :=
  payload.toPayload.toChunkedRangePayload

def PayloadFin.toChunkIntegralBoundsCert
    (payload : PayloadFin) :
    RawOmegaAChunkIntegralBoundsCert :=
  payload.toPayload.toChunkIntegralBoundsCert

def PayloadFin.toDirectTailWindowInputs
    (payload : PayloadFin) :
    RawOmegaADirectTailWindowInputs :=
  payload.toPayload.toDirectTailWindowInputs

def ResidualAnchorPayloadFin.toChunkedRangePayload
    (payload : ResidualAnchorPayloadFin) :
    RawOmegaAChunkedRangePayload :=
  payload.toPayloadFin.toChunkedRangePayload

def ResidualAnchorPayloadFin.toChunkIntegralBoundsCert
    (payload : ResidualAnchorPayloadFin) :
    RawOmegaAChunkIntegralBoundsCert :=
  payload.toPayloadFin.toChunkIntegralBoundsCert

def ResidualAnchorPayloadFin.toDirectTailWindowInputs
    (payload : ResidualAnchorPayloadFin) :
    RawOmegaADirectTailWindowInputs :=
  payload.toPayloadFin.toDirectTailWindowInputs

def RefinedPayloadFin.toChunkedRangePayload
    (payload : RefinedPayloadFin) :
    RawOmegaAChunkedRangePayload :=
  { primaryFinite := payload.primaryFinite.toChunkedRangePayload
    primaryTail := payload.primaryTail.toChunkedRangePayload
    controlFinite := payload.controlFinite.toChunkedRangePayload
    controlTail := payload.controlTail.toChunkedRangePayload }

def RefinedPayloadFin.toChunkIntegralBoundsCert
    (payload : RefinedPayloadFin) :
    RawOmegaAChunkIntegralBoundsCert :=
  payload.toChunkedRangePayload.toChunkIntegralBoundsCert

def RefinedPayloadFin.toDirectTailWindowInputs
    (payload : RefinedPayloadFin) :
    RawOmegaADirectTailWindowInputs :=
  payload.toChunkIntegralBoundsCert.toDirectTailWindowInputs

def ResidualAnchorRefinedPayloadFin.toChunkedRangePayload
    (payload : ResidualAnchorRefinedPayloadFin) :
    RawOmegaAChunkedRangePayload :=
  payload.toRefinedPayloadFin.toChunkedRangePayload

def ResidualAnchorRefinedPayloadFin.toChunkIntegralBoundsCert
    (payload : ResidualAnchorRefinedPayloadFin) :
    RawOmegaAChunkIntegralBoundsCert :=
  payload.toRefinedPayloadFin.toChunkIntegralBoundsCert

def ResidualAnchorRefinedPayloadFin.toDirectTailWindowInputs
    (payload : ResidualAnchorRefinedPayloadFin) :
    RawOmegaADirectTailWindowInputs :=
  payload.toRefinedPayloadFin.toDirectTailWindowInputs

def CellSlopeDirectEnvelopeRefinedPayloadFin.toChunkedRangePayload
    (payload : CellSlopeDirectEnvelopeRefinedPayloadFin) :
    RawOmegaAChunkedRangePayload :=
  payload.toRefinedPayloadFin.toChunkedRangePayload

def CellSlopeDirectEnvelopeRefinedPayloadFin.toChunkIntegralBoundsCert
    (payload : CellSlopeDirectEnvelopeRefinedPayloadFin) :
    RawOmegaAChunkIntegralBoundsCert :=
  payload.toRefinedPayloadFin.toChunkIntegralBoundsCert

def CellSlopeDirectEnvelopeRefinedPayloadFin.toDirectTailWindowInputs
    (payload : CellSlopeDirectEnvelopeRefinedPayloadFin) :
    RawOmegaADirectTailWindowInputs :=
  payload.toRefinedPayloadFin.toDirectTailWindowInputs

end RawOmegaAChunkTaylorPayload
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
