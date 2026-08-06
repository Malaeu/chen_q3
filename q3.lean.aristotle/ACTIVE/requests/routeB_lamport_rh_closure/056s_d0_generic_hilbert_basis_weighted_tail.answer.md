# GOAL 056 / Phase 4J answer — generic Hilbert-basis weighted tail

```yaml
GOAL: 056
PHASE: 4J
NODE: D0HilbertBasisWeightedTail
STATUS: CLOSED
EXACT_RESULT: G6_S2_D0_GENERIC_HILBERT_BASIS_PARSEVAL_AND_WEIGHTED_TAIL_PROVED
OPERATIVE_CLASS: TRY_G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL
ARSENAL_USED: [C04, C09, C10, C12]

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 10
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated decision and honest status

The tenth batch in the same living Proshka phase chat selected the abstract
generic Hilbert-basis receiver at pin
`0dea3fc20e0b0af45ed8aad50eed578a1a485b54`. Its exact 33,274-byte verdict
is archived canonically and in the bus mirror with SHA-256
`f0609ecd4e804bd09c2aa839fe0096c2dd1ac70d06ade0f6aab18da406dfcbfe`.
`Answer now` appeared and was not clicked.

This transaction closes exactly the abstract implication

```text
complete complex Hilbert basis + summable dominating weight
  -> exact complement Parseval identity
  -> weighted finite-tail bound
```

It does not prove `V_n_m` completeness, the log-window unitary transport, a
physical-frequency estimate, source-specific uniform energy control,
selected projection-tail decay, bounded normalizers, compact-open
convergence, strict `SlotS2`, or RH.

## Materialized production surface

```yaml
PRODUCTION_MODULE: Q3.Proofs.RouteB.D0HilbertBasisWeightedTail
PRODUCTION_SHA256: 24956f668098ea0a940ba50ebdd4087d7645114c8c0919a5587f35f10135643c
PRODUCTION_LINES: 140
PRODUCTION_BYTES: 4589
NEW_PRODUCTION_FILES: 1
MODIFIED_PRODUCTION_FILES: 0
PUBLIC_DEFINITIONS: 0
PUBLIC_THEOREMS: 2
PRIVATE_THEOREMS: 1
PROJECT_IMPORTS: 0
```

The file imports only
`Mathlib.Analysis.InnerProductSpace.l2Space`. It proves:

1. the exact squared norm of a finite Hilbert-basis residual equals the
   coefficient `tsum` on the complement of the retained `Finset`;
2. a summable nonnegative weighted coefficient energy bounds that residual
   whenever `1 <= a * w n` outside the retained set.

The source-specific identifiers `V_n_m`, `H_m`, `modeSet`, `gTrial_m`,
`SelectedProjectionTailDecay`, and `selectedPairIndex` do not occur. No
`n^2` or physical-frequency corollary was smuggled into this transaction.
No existing production file imports the new module.

## Load-bearing plant results

```yaml
P056S_1_HILBERT_BASIS:
  result: FIRED
  evidence: the empty orthonormal family is not complete in Complex
P056S_2_INNER_ORIENTATION:
  result: FIRED
  evidence: Complex.I separates inner_basis_f from inner_f_basis by sign
P056S_3_COMPLEMENT_POLARITY:
  result: FIRED
  evidence: retained and omitted coefficient sums are not interchangeable
P056S_4_SUMMABILITY:
  result: FIRED
  evidence: a nonsummable nonnegative sequence has tsum zero in Lean
P056S_5_NONNEGATIVITY:
  result: FIRED
  evidence: a negative retained-band weight defeats the global comparison
P056S_6_OUTSIDE_BAND:
  result: FIRED
  evidence: an inside-only guard does not control an omitted coefficient
P056S_7_EXPONENT_TWO:
  result: FIRED
  evidence: exponent-two scaling is load-bearing
P056S_8_NO_SOURCE_SMUGGLING:
  result: FIRED
  evidence: strict scan finds zero forbidden source identifiers
TEMPORARY_PLANT_FILES: REMOVED
```

## Validation

```yaml
SOURCE_LOCKS: PASS_5_OF_5
HEAD_ORIGIN_BEFORE_EDIT: EQUAL
DIRECT_LEAN: PASS
DEDICATED_BUILD: PASS_2372_OF_2372
FULL_BUILD: PASS_7817_OF_7817
Q3_CHECK: PASS
HOLE_TAINT_FORBIDDEN_IMPORT_SCAN: ZERO
PUBLIC_SURFACE: 0_definitions_2_theorems_1_private_theorem
PLANTS: PASS_8_OF_8
TEMPORARY_PLANT_FILES: REMOVED
PUBLIC_THEOREM_AXIOMS: [propext, Classical.choice, Quot.sound]
PROOF_DB_DOC_STATUS: proven
PROOF_DB_DECLARATIONS: PASS_3_OF_3_proven
ORCHESTRATOR_TESTS: PASS_67_OF_67
STRICT_SPINE: P9_STRICT_PASS_sensor-refresh
OBSERVABILITY_SNAPSHOT: OBS_73a7c5540e938baf53ee
OBSERVABILITY: 8_sources_0_stale
OBSERVABILITY_FILES: 3340
OBSERVABILITY_IMPORT_EDGES: 5577
OBSERVABILITY_SORRY_SITES: 0
OBSERVABILITY_PROOF_ROOTS: 2
OBSERVABILITY_TAINT_SOURCES: 1
OBSERVABILITY_DEGRADED: 1_numeric_ZERO_COVERAGE_not_PASS
SQLITE_INTEGRITY:
  knowledge.db: ok
  aristotle_proofs.db: ok
  observability.db: ok
```

All authored files pass `git diff --check`. The existing user-owned
`qmd embed -f` process remained running and was neither duplicated nor
interrupted. The semantic embedding refresh was not started behind it.

## Honest boundary and sole next node

Phase 4J supplies a reusable analytic receiver, not its literal Q3 basis.
The exact remaining seam is to construct, source-faithfully and for each
log-window carrier, a complete basis whose coordinates are the existing
orthonormal modes:

```text
G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE
```

Its owned production file is
`D0LogWindowVNMCompletenessBridge.lean`; it is the sole authorized first
importer of this module. Physical weighted-energy control remains a later,
separate supplier even after completeness is proved.

Route B remains `CHALLENGER / NOT_RH`; Bus 010 remains `VOID`; Goal 055
remains `HOLD`; no Aristotle submission, route promotion, PX claim, or RH
claim occurred.
