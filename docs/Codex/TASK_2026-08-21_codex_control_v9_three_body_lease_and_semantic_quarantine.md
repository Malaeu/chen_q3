# TASK 2026-08-21 — CODEX_CONTROL v9: three-body lease and semantic quarantine

```yaml
task_id: 2026-08-21-control-v9
transaction_name: CODEX_CONTROL_V9_THREE_BODY_LEASE_AND_SEMANTIC_QUARANTINE
authorized_by: PROSHKA_VERDICT_REQ_2026_08_21_O_CODEX_GRANT_THREE_BODY_LOOP_2026-08-21.md
verdict_commit: 72db50526d8023eaa3e42b7dfd6fb262adf4f615
verdict_blob: d08b244acd6818c4be90ba2b4d911c982fcd9b34
owner_command: "да го" (2026-08-21, Linux chat) — the explicit owner command the
               verdict requires before any global-control edit may begin
written_by: LINUX_CLAUDE
control_version_from: 8
control_version_to: 9
```

**Read the verdict in full before editing anything.** It is 673 lines and it is
the specification. This task pins the transaction and enumerates what must land;
it does not replace the verdict text.

## The one sentence the whole transaction exists for

```text
Право запушить source и право считать утверждение закрытым — разные права.
```

The kernel accepting a proof term, a source being pushable, and a statement being
usable downstream are three separate permissions. Control v8 does not
distinguish them. The falsifier is ours: commit `d5b28a09` repaired a receiver
whose gate was green and whose receipts were correct, while its load-bearing
hypothesis demanded a global `Continuous` that no production mode can satisfy —
they are `Icc.indicator` zero extensions with a nonzero endpoint value. The
implication was true and its antecedent was unreachable, so the kernel had
nothing to object to.

## Transaction scope — hard boundaries

```text
edit docs/CODEX_CONTROL.md exactly once, CONTROL_VERSION 8 -> 9
AGENTS.md                                  unchanged
docs/THREE_BODY_LOOP_DESIGN.md             stays rationale, never policy
no mathematical Lean node in this transaction
do not activate the lease until strict validation and all eight plants pass
```

`docs/CODEX_CONTROL.md` remains the single source of operative semantics. A
second policy kernel is forbidden: two texts would read alike under a coarse
view and differ exactly at the state transitions where the cost of being wrong
is highest.

## What v9 must contain

Each item below is specified in the verdict; the section names point at it.

### 1. Three admission statuses and the quarantine barrier

```text
SOURCE_WRITTEN -> KERNEL_GREEN -> SEMANTICALLY_ADMITTED(scope = ...)
MAX_KERNEL_GREEN_AWAITING_SEMANTIC_REVIEW = 1
```

While a kernel-green commit awaits independent semantic review: no theorem may
be built on it, no source-specific gap may be marked closed, `spine`/ledger may
not raise its status, and the next mathematical node does not start.

### 2. `HYPOTHESIS_PROVENANCE` in every source record

For each new or strengthened load-bearing hypothesis: `class` in
`SOURCE_FIELD | EXACT_FIT_SUPPLIER | NEW_OPEN_OBLIGATION`, plus
`source_or_supplier`, `exact_type`, `consumer`,
`production_inhabitant_or_plant`.

`EXACT_FIT_SUPPLIER` runs through the existing `orchestrator/supplier_preflight.py`
— reuse it, do not write a second checker. A receiver or bridge needs either an
exact production inhabitant or a plant demonstrating the antecedent is reachable
on the required class. Without one, the result is an abstract conditional
receiver and closes no source-specific node.

### 3. Repaired C4 — tactical repair defined literally

Proof body and tactics only. Statement, hypotheses, imports, definitions, public
surface, source object and consumer all unchanged. At most two attempts; the
second red gate is a stop and a wall report.

### 4. `CODEX_REQ` eligibility, fields and lifecycle

Eligible only as: `A` fatal / source-identity ambiguity / trust defect;
`B` hard stall — six registered no-delta cycles on one blocker fingerprint;
`C` the operative review gate control v8 already allows.

Mandatory fields: `CODEX_REQ`, `PHASE_KEY_HASH`, `BLOCKER_FINGERPRINT`,
`SOURCE_OBJECT`, `TERMINAL_CONSUMER`, `WALL`, `TRIED`, `ASK_SHELF_RECEIPT`,
`CHEAPEST_KILLER_RUN`, `PROGRESS_DELTAS`, `NEED`, `BLOCKS`, `REQUEST_BLOB`,
`SOURCE_COMMIT`.

Reuse the existing `phase_key`, `blocker_fingerprint`, `PROGRESS_DELTA` and stall
budget. Do not invent a parallel counter.

```text
OPEN -> IN_REVIEW -> ANSWERED
  └─────────────────> DROPPED        (only before claim)
```

After `IN_REVIEW` the executor may record `RESOLVED_LOCALLY_AFTER_CLAIM`, never
`DROPPED`.

### 5. Immutable body, mutable state, bound answer

```text
CODEX_REQ_<id>.md          immutable body      (append-only contract)
CODEX_REQ_STATE_<id>.yaml  lifecycle, CAS on previous blob
CODEX_ANSWER_<id>.md       immutable answer
```

The answer binds `ANSWERS_REQ`, `REQUEST_BLOB`, `REQUEST_SOURCE_COMMIT`,
`PHASE_KEY_HASH`, `BLOCKER_FINGERPRINT`, `VERDICT_PATH`, `VERDICT_BLOB`,
`DECISION`, `NEXT_NODE`, `FORBIDDEN`, `ANSWER_SCHEMA_VERSION`. An identifier
without the request blob permits silent substitution of the text under the same
name.

### 6. Pinned-session launcher and exclusive lock

```bash
codex exec resume "$CODEX_SESSION_ID" \
  -C "$REPO" \
  --sandbox workspace-write \
  --json \
  --output-schema "$SCHEMA" \
  -o "$FINAL_REPLY" \
  "<typed follow-up containing REQ_ID, answer blob and task pin>"
```

`--last` is rejected as production identity: it selects the most recent session
in the working directory, not the one owning the current task. `pgrep` is
rejected as mutual exclusion: it matches one spelling and races between check
and launch. Use `flock` or atomic `mkdir`, held for the whole runtime, with
stale recovery only after verifying PID and process start time.

Lock record: `worktree`, `branch`, `writer_body`, `pid`, `process_start_time`,
`codex_session_id`, `task_path`, `task_blob`, `phase_key_hash`, `base_head`,
`run_id`, `trigger_nonce`.

Every wake event carries `RUN_ID`, `TRIGGER_NONCE`, `SOURCE_EVENT_COMMIT`,
`ANSWER_BLOB`. Redelivery is a no-op. A changed `HEAD`, task blob, phase hash or
control version before launch is a stop, not a continue-from-memory.

### 7. Priority — origin gives no privilege

```text
P0  integrity/safety stop   — the loop halts; this is not a request to the judge
P1  already IN_REVIEW       — finish transport and return path, do not interrupt
P2  all earlier OPEN judge requests — origin-neutral FIFO by creation commit
P3  new eligible requests   — Linux batches 2-4 related walls into one chat,
                              each keeping its ID and getting its own answer
```

A new `CODEX_REQ` never overtakes an older open request. Direct executor-to-judge
transport stays forbidden.

### 8. `CODEX_AUTONOMY_LEASE_V1` replaces the perpetual grant

Bound to `control_version`, `branch`, `worktree`, `writer_lock_holder`,
`phase_key_hash`, `current_task_path` and `current_task_blob`, `allowed_paths`,
`activation_commit`, and an explicit expiry. Expires on phase-key change, task-pin
change, control-version change, writer-lock reassignment, explicit owner revoke,
or an explicit time or node budget.

The lease lifts per-action OK inside one bounded package only. It never lifts:
`PX_RH_CLAIM`, route promotion, merge to main, force push, global policy edits,
`docs/Codex/CURRENT.md`, paid or destructive or publication actions, direct
transport to the judge.

## The eight mandatory plants

Each must first be plantable as a genuine violation, then be cut off by v9.
A plant that cannot be made to fail before the repair proves nothing.

```text
1  UNINHABITED_ANTECEDENT_REPLAY          kernel-green theorem with a false
                                          production antecedent stays KERNEL_GREEN
                                          and never reaches SEMANTICALLY_ADMITTED
2  KERNEL_GREEN_NOT_SEMANTICALLY_ADMITTED consuming a quarantined theorem fails
3  WRONG_LAST_SESSION                     two sessions in one cwd; the launcher
                                          resumes the pinned id, not the latest
4  DUPLICATE_TRIGGER                      one event delivered twice starts one run
5  DROP_CLAIM_RACE                        simultaneous OPEN transitions; exactly
                                          one is legal
6  REQUEST_ID_BLOB_DRIFT                  right id, wrong request blob → rejected
7  WRITER_LOCK_COLLISION                  two bodies want the lock; one passes
8  OLDER_REQUEST_PRIORITY                 a new CODEX_REQ does not overtake an
                                          older OPEN request
```

Plant 1 is the cheapest decisive test and runs first. If the new control does
not catch the exact defect class the second body exists for, the whole lease is
unnecessary and the transaction should stop rather than continue.

The judge's registered guess at the first failure: `DROP_CLAIM_RACE` or
`WRITER_LOCK_COLLISION` — the mathematical roles are separated better than the
operational state machine.

Plants live beside the existing suite in `orchestrator/tests/`; the bounded
exploration budget they reuse is already covered by
`test_bounded_exploration_control.py`.

## Validation

```bash
./orchestrator/spine.py --strict --stdout --reason session-start
./specs_docs/session_start.sh
# registered targeted control tests + all eight new plants
```

```text
SUCCESS: CONTROL_V9_THREE_BODY_LOOP_ALL_PLANTS_GREEN
FAILURE: CODEX_GRANT_CONTROL_V9_OR_PLANT_MISMATCH
```

## Registered predictions — do not repair retroactively

```text
P_O_1  the uninhabited-antecedent plant blocks a kernel-green theorem before
       downstream consumption
P_O_2  pinned SESSION_ID plus an exclusive lock removes wrong-session and
       duplicate-run ambiguity
P_O_3  fingerprint and one-open gates cut judge traffic without blocking genuine
       fatal walls
P_O_4  the first implementation defect will be lifecycle or writer-lock state,
       not Codex CLI output parsing
```

Record what actually happened against each. A prediction ledger is worth keeping
only for the entries where we were wrong; the Linux body falsified one on
2026-08-21 by reading a match against a registered fallback as a hit for the main
prediction, and the repair of that entry is in commit `edfedf0d`.

## Forbidden in this transaction

```text
starting the loop first and writing the lifecycle and semantic gate afterwards
```

That is the same post-hoc repair the audit already caught, and it is a C09
defect: the object must be fixed before the outcome, not after the answer
arrives.

## If you hit a wall

`docs/routeB_bus/CODEX_REQ_2026-08-21_<slug>.md` with every mandatory field
above, pushed. Not to the judge directly — the browser lives on the Linux body.
