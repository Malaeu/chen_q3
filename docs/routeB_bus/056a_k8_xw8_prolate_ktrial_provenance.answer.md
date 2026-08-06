# GOAL 056 / Phase 1 — XW.8 prolate-to-kTrial provenance — answer

```yaml
GOAL: 056
PHASE: 1
NODE: XW.8
STATUS: CLOSED
RESULT: G6_S2_XW8_PROVENANCE_CONTRACT_MATERIALIZED_EXISTENCE_OPEN

SCOPE: PRODUCTION_TYPE_CONTRACT
VERIFIER: LEAN_PLUS_PLANTED_FALSIFIERS
ARSENAL_USED:
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

PRODUCTION_FILE:
  path: q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
  sha256: 3004f7551bcf187bb21d0de19a1e6c90f9836c749d00836ed8543389e54423b1

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## Exact result

The production family can no longer acquire a prolate label merely because an
unrelated `ProlatePair` exists.  The new contract requires, for every exact
`PairIndex (m,N)`:

1. the source `ProlatePair`;
2. the literal lock `P.pw.lambda = lambda_m i`;
3. the exact `MemLp` certificate for
   `E_star (prolateCombination P)` on `I_m i`;
4. the exact `TrialNonzero` certificate;
5. equality between the `CanonicalData.kTrial` consumed by production and the
   coefficient family constructed from the resulting `c_n` row.

Consequently
`ProlateCanonicalSourceData.canonical_kTrial` proves that the row consumed by
`centeredPstarFamily` is exactly the Fourier row of the normalized projected
starred sum of the same source packet.  The existing production `parent` and
`extract` remain untouched, and `selectedFamily_apply` exposes their literal
composition by `rfl`.

## Public surface

| Declaration | Role | Status |
|---|---|---|
| `ProlateKTrialSourceData` | same-index source packet plus lambda/carrier/nonzero suppliers | `MATERIALIZED` |
| `ProlateKTrialSourceData.coefficientFamily` | exact `c_n` row of `prolateCombination` | `MATERIALIZED` |
| `coefficientFamily_kTrial` | definitional finite-row provenance | `PROVED` |
| `ProlateCanonicalSourceData` | production canonical data plus mandatory family equality | `MATERIALIZED` |
| `canonical_kTrial` | source row equals production row | `PROVED` |
| `selectedFamily_apply` | exact production parent/extract expansion | `PROVED` |

All three public theorems have exactly the standard axiom triple
`[propext, Classical.choice, Quot.sound]`.

## Plant results

```yaml
P056A_1:
  result: FIRED
  evidence: omitted lambda lock is rejected with "Fields missing: lambda_eq"
P056A_2:
  result: FIRED
  evidence: arbitrary hTrial_m is not definitionally equal to prolateCombination of the stored pair
P056A_3:
  result: FIRED
  evidence: an independently supplied coefficient row cannot prove equality to coefficientFamily by rfl
```

The scratch plant files were deleted after the expected failures were
recorded.

## Engineering repair

The first representation duplicated the dependent type
`CentralIndex source.coefficientFamily` in a wrapper structure.  Direct Lean
was correct, but `.olean` generation became pathologically slow.  The final
representation stores the already-dependent production `CanonicalData` once
and requires the exact equality
`canonical.kTrial = source.coefficientFamily`.  This preserves the invariant,
compiles the target in 13 seconds, and avoids a new normalization hotspot.

## Still open

This contract proves no inhabitant.  The following remain explicit suppliers:

- source PSWF mode construction or an independently ratified certified-data
  replacement;
- `MemLp` and `TrialNonzero` for the exact prolate packet at every index;
- a central-nonzero cofinal production schedule;
- the centered `Gwin` / `rawFplus ... (-z)` coordinate lock;
- finite Galerkin residual and locally-uniform `Rminus` / `Rplus` decay;
- every-`ClusterData` identification required by strict `SlotS2`.

The next executable object is `MuntzV3ProductionExportClosureAudit`, followed
by `D0PstarMuntzCenteredCoordinateLock` (XW.6).  The exact request-project
receiver must first be shown portable from Lean 4.28 to the production Lean
4.26 module graph without importing `RequestProject.Main` or any raw roof.

## Validation

```yaml
DIRECT_LEAN: PASS
TARGET_BUILD: PASS_7757_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK: PASS
TAINT: ZERO
PUBLIC_AXIOMS: STANDARD_TRIPLE_ONLY
PLANTS: 3_OF_3_FIRED
ORCHESTRATOR_TESTS: PASS_67_OF_67
ROUTEB_STATUS_CHECK: PASS
PROOF_DB_REIMPORT:
  document: D0ProlateKTrialSource
  status: proven
  parser_declarations: 1
  note: current parser records the first namespace-local declaration only
```

`CHALLENGER / NOT_RH`; Bus 010 `VOID`; Goal 055 `HOLD`;
`ARISTOTLE_SUBMISSION: NONE`; `PX_RH_CLAIM: NOT_MADE`.
