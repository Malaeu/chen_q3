# Research dependency protocol

Status: active operational realization of Control v9 `MINIMAL_LEMMA`, K4/K8 and
the existing review gates. This document does not create a call class, select a
Route B goal, or change `PX_RH_CLAIM` authority.

## The invariant

A named theorem, paper, floor, rate, inverse, bridge, representation or Lean
declaration is a candidate dependency X. It is never mandatory merely because a
request named it. Start from the exact downstream consumer Y, write the weakest
known contract that Y actually needs, and test whether a weaker or different
interface Z proves that contract.

Every new live dependency packet must bind:

```yaml
original_requested_object: X
downstream_consumer: Y
actual_consumer_requirement: exact contract consumed by Y
original_object_is: PROVED_NECESSARY | UNKNOWN | NOT_NECESSARY
necessity_evidence: []
known_weaker_interfaces: [Z]
weaker_interface_probe: exact test of Z
consumer_implication: exact obligation Z => Y
failure_type: NO_SOURCE | NO_DERIVATION | FORMALIZATION_COST |
              COUNTEREXAMPLE | INCOMPATIBILITY | FORMAL_IMPOSSIBILITY | OTHER
epistemic_status: RESEARCH_DEBT | MATHEMATICALLY_DEAD | UNRESOLVED
death_evidence: []
```

`PROVED_NECESSARY` requires pinned evidence. `UNKNOWN` requires an explicit
weaker-interface probe. `MATHEMATICALLY_DEAD` requires an exact counterexample,
proved incompatibility or formal impossibility and its scope. `NO_SOURCE`,
`NO_DERIVATION`, `FORMALIZATION_COST`, cost exhaustion, a failed tactic, or
`NO_PROGRESS` can kill the current attempt; none proves mathematical death.

## Independent axes

- Execution: `ACTIVE`, `KILLED`, `CLOSED`, `HOLD`.
- Epistemic: `RESEARCH_DEBT`, `MATHEMATICALLY_DEAD`, `UNRESOLVED`.
- Recheck: `KILLED_RECHECKABLE`, `REOPEN_CANDIDATE`, `SOURCE_VERIFIED`,
  `READY_FOR_RERANK`.

The epistemic registry never selects execution. A hit can create at most a
reopen candidate; existing route selection and state transactions remain
mandatory. Historical `KILL_*`, verdicts, requests, INSIGHTS and archives stay
immutable and are evidence, not current selectors.

## Search and review

The permitted answers are: exact X; a new derivation of X; weaker Z with a
checked implication to Y; an alternative representation; one theorem-sized
sublemma that strictly reduces the debt; a scoped counterexample/impossibility;
or unresolved with a precise failure type. Repeating the previous approach
without a named novelty axis is not a new probe.

A research-debt challenge is only a packet subtype. It may be sent solely when
the already existing Control v9 `EXPLORATION_REVIEW` gate is independently
eligible and `review-plan` is ready. Owner selection can prepare a packet but
does not grant this gate.

## Semantic and archive hygiene

Generated or semantic corpora must not treat dormant monitors, superseded
prompts, stale request packs or historical OPEN markers as active authority.
Fix source selectors/generators, not generated views. Exact-source language for
byte identity and a frozen admitted theorem contract remains valid; consumer-
preserving rerank happens before the contract is frozen.

## Gate

Run:

```bash
python3 orchestrator/research_dependency_gate.py check
python3 orchestrator/research_dependency_gate.py plants
```

The gate validates the canonical registry, the three byte-identical active
Proshka prompt mirrors, consumer-first markers, source-locked intake, stale
semantic exclusions, and death-evidence plants.
