# GOAL 056 / Phase 2 — Müntz-v3 production export closure audit

```yaml
GOAL: 056
PHASE: 2
NODE: MuntzV3ProductionExportClosureAudit
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Determine the complete local import closure of
`RequestProject.MuntzV3ProlateCombinationReceiver`, classify every module as
already represented in production or requiring export, and select dependency
batches that can be ported from the isolated Lean 4.28 request project into the
Lean 4.26 production project without importing `RequestProject.Main` or any
raw/canonical roof.

This phase is a source/dependency audit.  It proves no new mathematical
statement and changes no production Lean file.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_object: RequestProject.MuntzV3ProlateCombinationReceiver
  terminal_consumer: Q3.RouteB.CanonicalRHRoute.SlotS2
  relation_under_test: exact transitive module closure and production portability
  preserved_invariants:
    - theorem statements and proof bodies
    - Gwin / ZetaMellinPoleSub / Rminus / Rplus sign convention
    - positiveHalf transport
    - exact ProlatePair and prolateCombination source
    - standard axiom triple only
  forbidden_shortcuts:
    - import RequestProject.Main from production
    - import any raw or canonical roof
    - treat a successful request-project build as a production build
    - weaken theorem statements to avoid Lean 4.26 API drift
    - claim tail-smallness, SlotS2, route promotion, or RH
  cheapest_killers:
    - transitive import graph
    - module/path collision scan
    - Lean 4.26 smoke build of each dependency batch
```

## Audit procedure

1. Traverse only literal `import RequestProject.*` edges from the receiver.
2. Record path, line count, SHA-256, and direct imports for every reached file.
3. Compare the three prolate export modules against the existing production
   prolate modules.
4. Partition the remaining closure in topological dependency order.
5. Check toolchain pins and record that Lean does not promise compatibility
   between minor versions; production Lean compilation is the decisive test.
6. Scan the proposed production module graph for forbidden request-project and
   roof imports.
7. Close with an exact next batch; do not copy production Lean in this phase.

## Predictions

- `P056B_1`: the closure contains at least 12 but fewer than 20 local modules.
- `P056B_2`: the three prolate export modules have existing production
  representatives, leaving fewer than 15 new production modules.
- `P056B_3`: the first honest production action is a dependency-ordered core
  port, not the receiver leaf itself.

## Closure boundary

A passing audit authorizes only the named dependency batches.  Each batch must
compile under production Lean 4.26, preserve public statements, expose its
axioms, and pass taint scanning before the next batch starts.
