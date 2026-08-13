# AUTOPILOT_000 — GOAL_RUN contract and selector

Status: `VALIDATED_PENDING_CONTROL_ADMISSION`
Success condition: `GOAL_RUN_CONTRACT_VALIDATED_WITH_FOUR_PLANTS`

## Object boundary

`MATHEMATICAL_PHASE` is the closed six-field `phase_key` defined by
`docs/CODEX_CONTROL.md`. It can span multiple physical goal numbers and one
living Proshka chat. `GOAL_RUN` is one operational execution interval from one
physical `NNN_*.goal.md` to its matching answer. Goal number, commit, process,
session, runtime state, and elapsed time never enter mathematical phase identity.

AUTOPILOT_000 is a read-only decision layer. It selects or stops; it does not
dispatch Codex, execute mathematics, mint a goal, write `GOAL_RUNTIME.json`,
record attempts, touch a database, commit, push, or contact an external agent.

## Physical selector

The live bus is `docs/routeB_bus/`. A physical goal is executable only when its
first machine `STATUS` is `OPEN` and it has no matching valid closing answer.
For current/future goals, an answer must have a matching lexical identity, a
closing machine `STATUS`, and a nonempty result/verdict field. Historical
pre-056 pairs without modern headers are recognized only when both bytes match
their committed `HEAD` blobs; a new text file never closes a goal by existence.
`PAUSED_RESTORABLE` is physical, unanswered, resumable, and non-executable.

| Physical state | Decision |
| --- | --- |
| exactly one executable goal | `SELECT_EXACT_GOAL` |
| more than one executable goal | `AUTOPILOT_AMBIGUOUS_GOAL_SET` |
| none, no source-locked next spec | `AUTOPILOT_NEXT_GOAL_SPEC_MISSING` |
| none, valid same-phase next spec | `MINT_READY` (no mint in stage 000) |
| closed six-field key changes | `PHASE_TRANSITION_REQUIRED` |
| next spec requests PX/RH claim | `OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM` |

Unknown lifecycle tokens fail closed. Answers are never synthesized for pause.
The lexical goal identifier in the filename and first machine header must agree;
identifiers such as `057` are never coerced through YAML 1.1 octal semantics.
Duplicate machine-header keys are invalid.
The selected goal's phase, when embedded, must match the canonical active phase;
selection also requires the living conversation handle and returns the canonical
six-field phase hash rather than a caller-supplied baseline.

## Source-locked `NEXT_GOAL_SPEC`

Schema `q3_next_goal_spec.v1` is closed. It carries the target/task, terminal
consumer, source objects, required inputs, forbidden shortcuts, validation,
success/failure codes, exact six-field phase key, and source provenance.

Automatic readiness accepts only:

1. `PRECOMMITTED_SOURCE` whose source, structured receipt, and still-unanswered
   outcome guard coexist byte-exactly in one named git commit reachable from
   current `HEAD`; or
2. `OPERATIVE_PROSHKA_RESULT` under the canonical Proshka directory with a
   committed source/receipt, a `TRY_`/`KILL_`/`RUN_` class, the live conversation
   ID, the canonical last adjudicated response pin, and an external receipt
   authenticator.

For either origin, the pinned UTF-8 source must contain one structured
`NEXT_GOAL_SPEC_SOURCE` mapping that exactly matches every non-provenance field
of the proposed spec. Scattered words elsewhere in a document are not binding.
A precommitted guard must be a byte-exact `OPEN` physical goal. Its source
commit must not contain the matching answer, while current `HEAD` must contain
a committed modern answer passing identity, closing-status, and result checks.
Thus the source is provably pre-outcome but becomes ready only after the real
outcome exists; an uncommitted or malformed answer never unlocks readiness.
A hash of an unrelated honest file cannot launder a post-outcome invention.
Stage 000 never allocates a bus number or writes a goal even after `MINT_READY`.

The direct self-test creates an isolated temporary git repository and a
synthetic AUTOPILOT_000-only spec/receipt/guard commit. No production next stage
is named or made mint-ready by the contract or runtime module.

## Runtime schema

Schema `q3_goal_run.v1` is a future crash-recovery record with a closed field
set: run and file identities, source/hash pins, mathematical phase-key hash,
state, cycle/stall counters, last attempt, next target/action, operational grant,
and lease holder/heartbeat. Validation binds the run ID, canonical repo-relative
goal/answer pair, current goal SHA-256, source-commit copy of those goal bytes,
six-field phase hash against the goal or canonical channel runtime, physical
answer existence against terminal/non-terminal state, bounded counters,
last-attempt identity, allowed state/action pair, known Codex body, and RFC 3339
heartbeat. It is not proof
truth. Canon remains the physical goal/answer, execution state, live bus, source
files, and Lean kernel checks.

The operational grant is resolved by an external authority callback to a closed
record with active status, exact goal scope, exactly one required action, and
the mandatory paid/destructive/publication/PX-RH prohibitions. No resolver means
fail closed.
Therefore the standalone Stage 000 command does not expose runtime acceptance;
integration uses the Python validator only after supplying that authority. The
grant can authorize
repository writes, closeout, scoped commits, rebase, and push within that scope;
it never authorizes paid calls, destructive actions, publication, control-scope
expansion, or `PX_RH_CLAIM`.

Selection and runtime validation reject duplicate JSON keys in canonical channel
state, require the pinned source commit to be reachable from current `HEAD`, and
require the physical goal itself to remain `STATUS: OPEN`. An answer may appear
only during closing/retry or in a terminal closed state, and must pass the
modern identity/status/result checks.

## Implementation and error log

The implementation was developed by reproducing each defect, adding a focused
plant, applying the smallest in-scope repair, and rerunning the focused and full
validation sets. No defect below was accepted as a documentation-only caveat.

| Defect | Cause | Repair and durable evidence |
| --- | --- | --- |
| Self-attested source provenance | A path and hash could describe a locally chosen post-outcome source. | Require a structured source object, receipt, distinct OPEN outcome guard, byte-exact common commit, and current committed valid answer. Covered by provenance and current-outcome plants. |
| Existence-only answer closure | Any matching answer filename could hide an open goal. | Require lexical identity, `CLOSED`/`CLOSED_PHASE0`, and a nonempty scalar result token; grandfather only byte-exact committed pre-056 history. |
| Unverified operational grant | A grant ID could attest its own authority or carry extra actions. | Require an external resolver, closed record, exact goal, exactly one requested action, mandatory prohibitions, and fail closed on resolver failure. |
| Caller-controlled phase baseline | Caller input could replace current phase truth. | Always load unique-key `CHANNEL_RUNTIME.json`; caller and goal-embedded phase can only confirm it. Require the living conversation handle. |
| Duplicate-key ambiguity and `057` coercion | Ordinary YAML/JSON parsers silently overwrite duplicate keys; YAML 1.1 parses `057` as octal. | Use duplicate-rejecting loaders and lexical string headers at every depth. |
| Production scope creep | Plants named or prepared the next production stage. | Plants use only an isolated temporary git repository and synthetic Stage-000 objects. |
| Missing git source-pin enforcement | Runtime validation skipped commit verification outside a normal `.git` directory and accepted hash-shaped fiction. | Require a real commit reachable from `HEAD` and byte-exact committed goal bytes, including linked-worktree-compatible git commands. |
| Overbroad physical bus | A caller could select an arbitrary external directory. | Bind selector and production CLI to `<repo>/docs/routeB_bus`; temporary plants recreate that canonical relative layout. |
| Paused goal could be hidden by an answer | An answer was checked before pause semantics. | Reject any answer paired with `PAUSED_RESTORABLE`; retain the unanswered file as physical and resumable. |
| Nested or blank result accepted | Truthy mappings could satisfy answer closure. | Accept only a nonempty scalar result/verdict token. |
| Precommit readiness was initially unreachable | Requiring the guard to remain unanswered in current state prevented post-outcome advance. | Enforce the temporal relation instead: no answer in source commit, committed valid answer in current `HEAD`. The plant uses two commits. |
| Runtime trusted goal-embedded phase | A goal-local key could bypass channel truth. | Canonical channel phase is always primary; an embedded key must compare equal. |
| Lifecycle over-hardening broke closed history | Applying the unanswered lifecycle enum to committed closed Goal 056 rejected valid historical statuses. | Apply `OPEN`/pause/unknown selection rules to unanswered goals; allow byte-exact committed closed history while rejecting uncommitted unknown closing pairs. |

Validation snapshot on 2026-08-13 before delivery:

```text
focused Ruff                         PASS
relevant pytest                     60 passed, 12 subtests passed
P1 same phase / two goal numbers    PASS
P2 ambiguous executable set         PASS (fail closed)
P3 post-outcome unpinned spec       PASS (rejected)
P4 PX_RH_CLAIM                      PASS (owner stop)
live selector                       SELECT_EXACT_GOAL 058; selection only
strict Spine                        P9_STRICT_PASS
session_start.sh                    РАСХОЖДЕНИЙ НЕТ
Route B status                      CHECK: OK; 057 paused; 058 selected
tool manifest                       7 families; 34 tools; 19 writers
tool manifest SHA-256               ccf2a413e45ad4aef001c4113f2b81b603aa620e45d2a356806ca57a7fdbdd5d
```

Residual boundaries are intentional: Stage 000 does not dispatch, mint, persist
runtime, write a database, authenticate a real Proshka receipt by itself, or
execute closeout. The next smallest infrastructure goal is `AUTOPILOT_001`, but
it is not authorized or made executable by this contract.

Delivery lineage: Goal 057 pause semantics were committed and pushed as
`056a30fc9633dd13d073f0fafa9b6769f884b61c`. This contract and its runtime are
the separate candidate with subject
`[Linux][rh_clean][Control] Validate AUTOPILOT_000 goal-run contract`; the exact
delivered commit and remote state are verified after scoped commit/rebase/push.

## Bounded state machine

```text
BOOTSTRAP -> SELECTING -> RUNNING -> CLOSING -> CLOSED
                    |          |         |
                    |          |         `-> CLOSE_RETRY_PENDING
                    |          `-> BOUNDED_EXPLORATION / REQUESTING_PROSHKA
                    `-> STOPPED_FAIL_CLOSED

CLOSED -> MINT_READY | PHASE_TRANSITION_REQUIRED | STOPPED_CLEAN
PX_RH_CLAIM -> STOP_OWNER_REQUIRED
```

Three no-delta cycles mean `SOFT_STALL`; six permit one same-chat Proshka
review; twelve exhaust the episode. Those bounds do not convert runtime state
into proof and do not authorize owner deferral outside `PX_RH_CLAIM`.

## Four plants

- P1: two goal numbers with the same six fields hash to one mathematical phase.
- P2: two executable physical goals fail closed.
- P3: post-outcome next-goal selection without locked provenance is rejected.
- P4: `PX_RH_CLAIM` cannot reach automatic advance.

Validation:

```bash
uv run --frozen --extra dev python -m pytest orchestrator/tests/test_goal_runtime.py -q
python3 orchestrator/goal_runtime.py --selftest
python3 orchestrator/goal_runtime.py --json
python3 -c "from orchestrator import spine; print(spine.validate_tool_manifest())"
bash specs_docs/session_start.sh
```
