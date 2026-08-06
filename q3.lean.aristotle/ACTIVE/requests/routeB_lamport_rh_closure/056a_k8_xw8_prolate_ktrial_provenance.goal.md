# GOAL 056 / Phase 1 — XW.8 prolate-to-kTrial provenance contract

```yaml
GOAL: 056
PHASE: 1
NODE: XW.8
PARENT: 056_PHASE0
KIND: STANDING_ROOT_CHILD
BUS: NONE
STATUS: OPEN
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD

OPERATIVE_CLASS: TRY_G6_S2_XW8_PROVENANCE_CONTRACT
PROSHKA_CALLS_THIS_PHASE: 0
ARSENAL_USED:
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
```

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  owner_path: q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
  source_object: Q3.RouteB.D0Pstar.prolateCombination
  finite_chain:
    - Q3.RouteB.D0Pstar.E_star
    - Q3.RouteB.D0Pstar.gTrial_m
    - Q3.RouteB.D0Pstar.gTrial_m_N
    - Q3.RouteB.D0Pstar.kTrial_m_N
    - Q3.RouteB.D0Pstar.c_n
  production_carrier: Q3.RouteB.D0Pstar.CoefficientFamily.kTrial
  terminal_family: >-
    Q3.RouteB.CanonicalRHRoute.selectedFamily
      (Q3.RouteB.D0Pstar.canonicalApproximation D)
  relation_under_test: >-
    the coefficient row consumed by centeredPstarFamily is equal to the row
    constructed from c_n of the same prolateCombination, at the same PairIndex,
    with P.pw.lambda = lambda_m i and no unproved independent selector
  invariant_cargo:
    - exact PairIndex m/N
    - lambda_m lock
    - exact prolateCombination
    - exact MemLp certificate
    - exact TrialNonzero certificate
    - exact parent and nested extract
  forbidden_substitutions:
    - arbitrary hTrial_m
    - independently supplied CoefficientFamily
    - fixed PL2 window
    - independent parent or extract
```

The object is a data-only, no-existence contract.  It may require the analytic
suppliers needed by the existing constructors; it must not manufacture them.

## Exact public surface

1. `ProlateKTrialSourceData`, indexed by every production `PairIndex`.
2. `ProlateKTrialSourceData.coefficientFamily`, using exactly `c_n` of
   `prolateCombination`.
3. A definitional theorem exposing the exact coefficient row.
4. `ProlateCanonicalSourceData`, carrying the source bundle, one production
   `CanonicalData`, and the mandatory equality of its coefficient family with
   the source-derived family.
5. An exact canonical-row theorem plus a definitional theorem exposing the
   selected family at the production `parent (extract k)`.

## Plants

```yaml
P056A_1:
  mutation: omit P.pw.lambda = lambda_m i
  expected: CONTRACT_CONSTRUCTION_REJECTED
P056A_2:
  mutation: replace prolateCombination with an arbitrary hTrial_m
  expected: SOURCE_OBJECT_EQUALITY_LOST
P056A_3:
  mutation: replace the constructed coefficient row by an independent row
  expected: DEFINITIONAL_COEFFICIENT_THEOREM_REJECTED
```

## Gates

- direct Lean on the new module and direct consumers;
- no `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`;
- standard axiom triple only for public theorems;
- all three plants fire;
- `routeb_status.py --check`, `scripts/q3_check.sh`, and `git diff --check`;
- canon/mirror goal and answer byte equality.

```text
STOP: G6_S2_XW8_PROVENANCE_CONTRACT_NOT_MATERIALIZED
SUCCESS: G6_S2_XW8_PROVENANCE_CONTRACT_MATERIALIZED_EXISTENCE_OPEN
```

No exact Müntz receiver promotion, mode existence theorem, ground-family
identity, cofinal-path existence, tail-smallness result, SlotS2 proof,
Aristotle submission, physical Bus 010, Goal-055 change, route promotion, or
PX/RH claim is authorized by this phase.
