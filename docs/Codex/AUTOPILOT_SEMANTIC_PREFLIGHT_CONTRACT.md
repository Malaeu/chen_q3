# AUTOPILOT_002 — event-scoped refresh and semantic preflight

Status: implemented infrastructure contract. It does not execute Goal 058
mathematics, mint a goal, call Proshka, submit Aristotle, or make a proof claim.

## Closed refresh dispatch

| Reason | Ordered transaction |
|---|---|
| `verdict-intake` | verdict migrator, validation |
| `step-close` | verdict, `INSIGHTS.md`, and `Progress_Log.md` migrators; conditional semantic rebuild; validation |
| `goal-close` | all canonical migrators; declaration backfill and inventories; sensors; semantic rebuild; census; validation |
| `semantic-index-refresh` | semantic rebuild and validation only |

An unregistered reason with `--refresh` returns
`SPINE_REFRESH_REASON_UNKNOWN`. Read-only invocations remain read-only.

## Exact migration census

`orchestrator/migration_census.py` compares live source identities against
actual rows in `knowledge.db` for:

- parsed `INSIGHTS.md` journal entries;
- parsed eight-field `Progress_Log.md` decisions;
- structured Proshka verdict records.

Every invocation prints `source rows | database rows | unmigrated rows`.
`--strict` fails until all three surfaces have zero unmigrated identities.
The insight migrator replaces only its own canonical projection so obsolete
source-derived identities cannot survive as plausible rows.

## Machine-local semantic receipt

The tracked `orchestrator/state/SEMANTIC_INDEX_STATUS.json` is retained as a
historical cross-machine snapshot and has no startup authority. The live receipt
is ignored by git:

```text
q3.lean.aristotle/.qmd_cache/semantic_index_receipt.json
```

It binds:

- deterministic SHA-256 over framed repo-relative path and file bytes;
- source count, total bytes, and Markdown/Lean/TeX/YAML breakdown;
- qmd index identity, collection root, mask, and live file count;
- fixed lexical/vector plants;
- three to five dynamic queries for selected goal, exact target, terminal
  consumer, property combination, and the freshest insight when distinct;
- external Lean registry query receipts with the explicit candidate-only
  boundary.

Missing, foreign-machine, corpus-stale, collection-drifted, or failed receipts
make strict read-only startup fail and print the explicit rebuild command.

## Deep shelf mode

`./ask.sh --deep "<terms>"` keeps the normal exact cascade but always runs the
semantic layer afterwards. Exact hits therefore cannot suppress semantic
retrieval. It also queries every enabled base in
`docs/cartographer/lean_bases.yaml`; matches are candidates, not Lean truth.

## Executable SearchIntent and literature discovery

`orchestrator/workflow_runtime.py run --through supplier-preflight
--search-intent <json>` is the only production SearchIntent entry. The
read-only supplier accepts only the closed `q3_search_intent.v1` schema. The
runtime binds the physical goal hash, exact terminal consumer,
object/domain/normalization/quantifiers/assumptions/output surface,
canonical terms, typed alias hypotheses, known false friends, allow-listed
collections, network policy, and the `DISCOVERY` or `ADMISSION` boundary.

The executable budget is 3–5 distinct initial queries, at most eight distinct
initial plus feedback queries, at most eight alias hypotheses, one initial web
batch, at most one candidate-derived feedback batch, and exactly one external
Lean root scan. Local work has one monotonic 12-second budget and at most eight
qmd subprocesses. Failure, mutation, denominator drift, or cap overflow returns
`INCOMPLETE`, never absence.

`scripts/literature_discovery.py` queries current arXiv and Crossref metadata
with at most eight candidates per provider/query, 24 globally deduplicated
candidates, 512 KiB per response, 300 Unicode title characters, and 1200 excerpt
characters. Its output is discovery evidence only: alternate terminology,
characterizations, translations, dual representations and negative results are
candidates for source verification, never theorem identity or admission.

## Publication blueprint v2

Phase close regenerates `q3_blueprint.v2` from the exact NODE_REGISTRY_V10,
fresh EnvDump, active physical goal/execution/channel state and bibliography.
The manifest contains registered nodes/edges and both hashes, recorded plus
current source/consumer blob evidence, proof-relevant elaborated types,
theorem-to-axiom map, dependency/taint evidence, terminal route/phase state,
bibliography hashes and a compact edge appendix. Missing relevant declarations
or stale EnvDump fail closed with `--prepare-env`; unrelated helpers are omitted.

## Validation plants

```text
orchestrator/tests/test_autopilot002.py   9 passed
```

The plants cover closed dispatch, unknown-reason rejection, byte/path-exact
corpus drift, foreign receipt rejection, deep search after exact hits, actual
external-registry querying, and the three-column migration census.

The initial Linux bootstrap showed that the previous 1800-second qmd attempt
timed out after only part of the 2637-file collection. Embedding is incremental,
so completed vectors survived, but the operational limit was too small. Each
large embed attempt is now at least 2400 seconds and may continue through six
incremental attempts before failing closed.
