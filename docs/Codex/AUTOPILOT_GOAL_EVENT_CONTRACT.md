# AUTOPILOT_001 — registered attempts and reusable insights

Status: `VALIDATED`
Success condition: `ATTEMPT_AND_INSIGHT_WRITERS_IDEMPOTENT_AND_PROVENANCE_BOUND`

## Boundary

AUTOPILOT_001 adds durable event writers to the read-only GOAL_RUN selector from
AUTOPILOT_000. It does not dispatch Codex, select mathematics, mutate GOAL_RUN
runtime state, mint or close a goal, call an external agent, or refresh derived
indexes.

Registered attempts and reusable insights are different objects:

| Event | Canonical destination | Content |
| --- | --- | --- |
| `REGISTERED_CYCLE` | `knowledge.db` `journal_entry.kind = attempt` | complete closed controller payload for one cycle |
| `REUSABLE_INSIGHT` | `q3.lean.aristotle/docs/INSIGHTS.md` | compact checked synthesis with boundary and provenance |

Raw reasoning, speculative branches, repeated builds, and transcript exhaust do
not become insights. A later `step-close` projects the append-only insight into
`knowledge.db`; it does not make the database the source of that insight.

## Attempt contract

`q3_goal_attempt.v1` is a closed JSON object. Its controller-critical fields are:

```text
attempt_id · goal_run_id · goal_file · goal_sha256 · recorded_date
cycle_index · registered_prediction · cheapest_killer
blocker_fingerprint_before · blocker_fingerprint_after
delta_id | NONE · progress_class · cognitive_operator · next_action
source_provenance · extra
```

The writer binds the attempt ID to the goal ID and cycle, checks the current goal
bytes, accepts only the eight canonical cognitive operators, validates every
provenance file and SHA-256, and prevents `extra` from shadowing controller
fields. The canonical JSON bytes and their SHA-256 are stored in the existing
`journal_entry` table; no new table is introduced.

Crash recovery is exact:

```text
same attempt ID + same canonical payload → ALREADY_RECORDED, exit 0
same attempt ID + different payload      → ATTEMPT_ID_COLLISION, fail closed
```

## Insight contract

`q3_goal_insight.v1` is also closed. It requires a title, workstream, exact
target, compact summary, validation, explicit boundary, next target, and at
least one repository provenance row with path, locator, role, and live SHA-256.

The append contains a human-readable entry plus a machine JSON receipt. Exact
retries are idempotent. The same semantic payload under another insight ID is
deduplicated by `semantic_sha256`; one insight ID with different content fails
as `INSIGHT_ID_COLLISION`.

## Invocation

```bash
python3 orchestrator/goal_events.py record-attempt --payload /absolute/path/to/attempt.json
python3 orchestrator/goal_events.py record-insight --payload /absolute/path/to/insight.json
```

The payload file may be outside the repository. Every cited provenance file must
be a canonical repository-relative path whose current bytes match the supplied
SHA-256.

## Validation

```text
focused Ruff                                      PASS
goal-event tests                                  8 passed
exact attempt retry                               ALREADY_RECORDED
attempt ID with changed payload                   ATTEMPT_ID_COLLISION
controller field smuggled through extra           rejected
provenance drift                                  rejected
exact and semantic insight retry                  ALREADY_RECORDED
insight ID with changed content                   INSIGHT_ID_COLLISION
duplicate JSON key                                rejected
```

Implementation: `orchestrator/goal_events.py`.
Plants: `orchestrator/tests/test_goal_events.py`.
Routing authority: `docs/cartographer/TOOLS.yaml`.
