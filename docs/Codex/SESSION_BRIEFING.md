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
KILLED_RECHECKABLE -> REOPEN_CANDIDATE -> SOURCE_VERIFIED -> REOPENED
```

A search hit may only create `REOPEN_CANDIDATE`.  Exact primary-source and
project-interface verification are required for `SOURCE_VERIFIED`; reopening
still needs a separate authorized state/verdict transaction.  Session start
never performs web or literature search.

Debt prompt priority is based on `last_external_check`: 0–6 days is passive,
7–29 days normal, and 30+ days highlighted. `REOPEN_CANDIDATE` or
`SOURCE_VERIFIED` is high priority regardless of age.

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
