# Route B session briefing

`specs_docs/session_start.sh` remains the single read-only session entry.  Its
compact `ROUTE B — SESSION BRIEF` section is computed from the live bus,
`ROUTE_B_EXECUTION_STATE.json`, `docs/Codex/CURRENT.md`, authoritative Route B
artifacts and the research-debt registry.  It does not select a goal, change a
verdict, run an external search or write a checkpoint.

The checkpoint is machine-local and deliberately noncanonical:

```text
q3.lean.aristotle/.qmd_cache/session_briefing_checkpoint.json
```

It is an ignored, deterministic JSON snapshot written atomically by the
existing `close-session` path.  It contains only the current Git `HEAD`, the
read execution address and four monotone artifact totals.  Deleting it loses
only the next delta; it cannot change Route B state.

The canonical registry
`docs/routeB_bus/RECHECKABLE_RESEARCH_DEBTS.json` contains search metadata and
links to exact verdict/state Git blobs.  It is not a verdict registry and does
not replace the execution state.  Its lifecycle is:

```text
KILLED_RECHECKABLE -> REOPEN_CANDIDATE -> SOURCE_VERIFIED -> READY_FOR_RERANK
```

A search hit may only create `REOPEN_CANDIDATE`. Exact primary-source and
project-interface verification are required for `SOURCE_VERIFIED`;
`READY_FOR_RERANK` remains non-executable and only the separate authorized
execution selector may reopen a route. Session start never performs web search.

Each reopenable row is `RESEARCH_DEBT` and `not_disproved: true`. A named object
may be `SUFFICIENT_ONLY` or `NOT_NECESSARY`; every row carries the complete
16-class `alternative_interface_audit`, and `NUMERICAL_HYPOTHESIS_ONLY` is never
proof. Goal 056's unsupported arbitrary-cofinal theorem shape is therefore a
recheckable debt with coupled-schedule and constructive-diagonal alternatives,
not a mathematical refutation. The same file's separate `adjudications` section
stores only atomically scoped `MATHEMATICALLY_DEAD` theorem shapes with exact
path/commit/blob evidence; those entries never enter ranking or reopen queues.
The briefing ranks debts by new signal, recheck age, unlock value and estimated
difficulty; these are ordering labels, not success probabilities.

The deterministic semantic projection is
`docs/routeB_bus/RESEARCH_DEPENDENCY_CLASSIFICATION.md`. It is generated from the
registry, contains a compact non-actionable dead block, and is part of the
curated `q3_docs` source set. It is semantic orientation only and cannot select
or reopen execution.

Debt prompt priority is based on `last_external_check`: 0–6 days is passive,
7–29 days normal, and 30+ days highlighted. `REOPEN_CANDIDATE` or
`SOURCE_VERIFIED` is high priority regardless of age.

When the owner chooses preparation of one research-debt challenge, the read-only
builder emits one deterministic packet subtype:

```bash
python3 orchestrator/research_debt_challenge.py rank
python3 orchestrator/research_debt_challenge.py manifest --debt-id ID \
  --request-id REQ-ID --boundary-id BOUNDARY-ID
```

The packet requires a materially novel theorem family, representation,
decomposition, weaker target, constructive derivation or counterexample search.
It is not a new Control call class. It may dispatch only through an independently
eligible Control v9 `EXPLORATION_REVIEW`, with an `OPEN` queue row and a ready
`workflow_runtime.py review-plan`; exact attachment, receipt and living-chat
rules still apply. Owner selection prepares a packet but does not grant that gate.
A research result can create at most
`REOPEN_CANDIDATE`; it cannot reopen a route by itself.

Commands:

```bash
python3 orchestrator/session_briefing.py validate
python3 orchestrator/session_briefing.py brief
python3 orchestrator/workflow_runtime.py close-session
```

The displayed counts are deliberately narrow: matching physical bus answers,
files with one machine-readable KILL outcome, queue requests marked ANSWERED,
and Proshka verdict artifacts whose first status is PROVED.  They are artifact
counts, not proof closure, Route promotion or an RH claim.

## Current Goal 058 state-migration boundary

The operative Satz9 verdict and the even/odd current-shelf closeouts are newer
than the execution state's `G3_PROLATE_RATE_CENTRAL_OVERLAP_DENOMINATOR_FLOOR`
address.  The latest even-sector report names
`SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE` only as the next independent
dependency root and explicitly requires the next physical Goal 058 rerank
before an executable attack is selected.  Therefore this package reports
`CONTROL_PLANE_DRIFT` but does not manufacture an intermediate state or mutate
`ROUTE_B_EXECUTION_STATE.json`.
