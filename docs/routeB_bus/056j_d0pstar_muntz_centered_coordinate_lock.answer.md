# GOAL 056 / Phase 4A answer — D0 Pstar to Müntz centered coordinate lock (XW.6)

```yaml
GOAL: 056
PHASE: 4A
NODE: D0PstarMuntzCenteredCoordinateLock
STATUS: CLOSED
EXACT_RESULT: G6_S2_XW6_SAME_INDEX_COORDINATE_CONTRACT_MATERIALIZED_RESIDUAL_OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Materialized production contract

```yaml
PRODUCTION_MODULE: Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
PRODUCTION_SHA256: ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
PRODUCTION_LINES: 195
PROOF_DB_DECLARATIONS: 16
PROOF_DB_STATUS: proven
```

The module defines one exact source object at every selected index:

```text
i_k = (S.canonical.parent (S.canonical.extract k)).1
P_k = S.source.pair i_k
h_k = prolateCombination P_k
```

It then places the two transform coordinates on that same object:

```text
selectedGwinTransformCoordinate S k z
  = Gwin h_k (lambda_m i_k) (-i*z)

selectedRawTransformCoordinate S k z
  = rawFplus S.canonical.kTrial i_k (-z).
```

The stored `lambda_eq`, `eStar_memLp`, and `trialNonzero` witnesses are reused
literally.  `selectedTrialNormalizer` is the exact `sTrial_m_N` factor already
inside the XW.8 coefficient row.  No second family, source pair, schedule, or
window parameter was introduced.

## Exact decomposition

The new module proves the orientation expansion

```text
selectedFamily (canonicalApproximation S.canonical) k (-z)
  = selectedCenteringFactor S k *
      selectedRawTransformCoordinate S k z
```

and the honest reconstruction

```text
selectedFamily (canonicalApproximation S.canonical) k z
  = selectedMuntzApproximation S k z
    + selectedCenteringFactor S k *
        selectedGalerkinCoordinateDefect S k (-z).
```

The defect is retained as an explicit difference between the exact normalized
Galerkin raw coordinate and the exact scaled full-window Gwin coordinate.  No
zero, limit, compactness, or tail theorem about it is asserted.

## Plant results

```yaml
P056J_1:
  result: FIRED
  evidence: rfl rejects parent k = parent (extract k)
P056J_2:
  result: FIRED
  evidence: rfl rejects rawFplus(...,z) = selectedRawTransformCoordinate(...,z)
P056J_3:
  result: FIRED
  evidence: source audit finds selectedTrialNormalizer and sTrial_m_N in the scaled coordinate
P056J_4:
  result: FIRED
  evidence: theorem inventory has no defect-zero or defect-Tendsto declaration
```

The temporary two-mutation Lean plant was removed after both expected failures
were recorded.

## Validation

```yaml
DIRECT_LEAN: PASS
TARGET_BUILD: PASS_7774_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK: PASS
HOLE_SCAN: ZERO
FORBIDDEN_IMPORTS: ZERO
PUBLIC_AXIOMS: STANDARD_TRIPLE_ONLY
ORCHESTRATOR_TESTS: PASS_67_OF_67
PROOF_DB_REIMPORT: proven, 16 declarations, 196 parser lines
```

## Boundary and next executable object

XW.6 is closed at the exact same-index type/orientation layer.  This is real
progress: the only remaining discrepancy is now a named Galerkin coordinate
defect, not an ambiguous family or sign convention.

The next executable object is
`D0PstarMuntzGalerkinResidualCrosswalk` (Phase 4B): identify the coordinate
defect with an object-first transform of
`gTrial_m - P_m_N gTrial_m`, preserve the same `parent ∘ extract` sequence,
and prove compact-open decay on every compact subset of the centered strip.
Only after that may the `Rminus` and `Rplus` locally-uniform tails be composed.

No strict `SlotS2`, route promotion, or RH claim follows.  The route remains
`CHALLENGER / NOT_RH`; Bus 010 remains `VOID`; Goal 055 remains `HOLD`.
