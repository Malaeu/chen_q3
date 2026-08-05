# STATUS: CONDITIONAL — ЕДИНЫЙ MEMORY + BEHAVIOR-CONTROL КОНТУР РАТИФИЦИРОВАН; P9 ОТКРЫТ

```yaml
PRIMARY: RATIFY_UNIFIED_MEMORY_AND_BEHAVIOR_CONTROL_CONTOUR
PRIMARY_COUNT: 1
STATUS_CODE: UNIFIED_MEMORY_BEHAVIOR_CONTROL_ARCHITECTURE_RATIFIED_IMPLEMENTATION_OPEN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  ORIGIN_HEAD_OBSERVED: 982c3bd467f13ff6d4b35b9202241fb4536f7e7e
  SYSTEM_SPEC: docs/SYSTEM_SPEC_2026-08-05.md
  SYSTEM_SPEC_EXPECTED_SHA256: 50e737c7362aa804268930c3de96967aeacc095a77241e127bf411aa4f098dbb
  CONNECTOR_SECTION_MATCH: CHANNEL_BEHAVIOR_CONTROL_SYMMETRY_PRESENT
  CONNECTOR_GIT_BLOB_SHA: 95dc21a288aa94cd77823f80d13e15b1a1d8f781

ARSENAL:
  BOOTSTRAP_FETCHED: true
  DECK_FETCHED: true
  MANDATE_ACCEPTED: true
  CARDS_USED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT

AMENDS_PRIOR_UNIFIED_VERDICT:
  MEMORY_SPINE_ARCHITECTURE: RETAIN
  GOAL_CLOSE_LOCAL_SPINE_REFRESH: RETAIN
  GOAL_CLOSE_AUTOMATIC_PROSHKA_CALL: REMOVED
  PROSHKA_CALL_TRIGGER: OWNER_BOUNDARY_ONLY
  PROSHKA_CHAT_UNIT: PHASE_NOT_GOAL
  EXECUTOR_ADDENDUM_AS_ACTIVE_CONTROL: KILLED
  P6_PLUS_P8_CONTENT_HOST: docs/CODEX_CONTROL.md
  P9_INSERTED: true

PROSHKA_CHAT_MODEL:
  MODEL: ONE_LIVING_CHAT_PER_PHASE
  TARGET_PHASE_DURATION: APPROX_5_HOURS_ADVISORY_ONLY
  RELATED_GOALS_PER_PHASE: UNBOUNDED_FINITE_N
  TIME_ALONE_OPENS_NEW_CHAT: false
  GOAL_CLOSE_OPENS_NEW_CHAT: false
  SESSION_RESTART_OPENS_NEW_CHAT: false
  SITE_BATON_OPENS_NEW_CHAT: false
  FULL_CONTEXT_UPLOADS_PER_PHASE_MAX: 1
  DEFAULT_PACKET_AFTER_PHASE_OPEN: DELTA_ONLY
  AUTOMATED_BOUNDARIES:
    - MINT
    - PROMOTION
    - FRONT_CHANGE
    - FATAL

PHASE_KEY:
  FIELDS:
    - route_id
    - front_id
    - source_object_family_id
    - terminal_consumer_id
    - honesty_state
    - convention_lock_id
  PRECOMMITTED: true
  EQUALITY_DECIDES_CONTINUE: true

NEW_CHAT_TRIGGER:
  RULE: OPEN_ONLY_AFTER_MATERIALIZED_PHASE_CHANGE
  ALWAYS_PHASE_CHANGE:
    - PROMOTION
    - FRONT_CHANGE
    - FATAL
  CONDITIONAL_PHASE_CHANGE:
    - MINT_IF_PHASE_KEY_CHANGES
  NOT_PHASE_CHANGE:
    - ordinary_goal_open
    - ordinary_goal_close
    - helper_lemma
    - commit
    - build_failure
    - Mac_Linux_site_baton
    - elapsed_time
    - session_restart

CODEX_CONTROL:
  PATH: docs/CODEX_CONTROL.md
  ROLE: SOLE_EXECUTOR_BEHAVIOR_CONTROL
  EXECUTOR_BODIES:
    - CODEX_MAC
    - CLAUDE_CODE_LINUX
  AGENTS_MD: THIN_POINTER
  ROOT_CLAUDE_MD: THIN_POINTER_FOR_EXECUTOR_BEHAVIOR
  Q3_CLAUDE_MD: NONNORMATIVE_REFERENCE_OR_THIN_POINTER
  EXECUTOR_ARSENAL_ADDENDUM: SUPERSEDED_BY_CODEX_CONTROL
  LOCAL_CODEX_CONFIG: RUNTIME_ADAPTER_ONLY
  LOCAL_CONFIG_MAY_OVERRIDE_SEMANTIC_BEHAVIOR: false
  DYNAMIC_ROUTE_STATE_LIVES_IN_CONTROL_FILE: false

BEHAVIOR_CONTROL_SYMMETRY:
  LAW: EXACTLY_ONE_ACTIVE_CONTROL_FILE_PER_CHANNEL_ROLE
  REGISTRY_HOST: orchestrator/KNOWLEDGE_SPINE.md
  STRICT_VALIDATOR: orchestrator/spine.py
  CHANNELS:
    FABLE_MYTHOS:
      CONTROL: q3.lean.aristotle/docs/PROJECT_INSTRUCTIONS_v3_arsenal.md
    PROSHKA:
      CONTROL: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
    EXECUTOR:
      CONTROL: docs/CODEX_CONTROL.md
      BODIES: [CODEX_MAC, CLAUDE_CODE_LINUX]
  TOP_LEVEL_CHANNELS_REQUIRE:
    - control_file
    - trigger_owner
    - bootstrap_pointer
    - existing_gate
    - spine_wiring
    - fail_closed_code
  DUPLICATE_ACTIVE_CONTROL: FATAL
  MISSING_TRIGGER_OWNER: FATAL
  NEW_CHANNEL_WITHOUT_CONTROL: FORBIDDEN

RUNTIME_LEDGER:
  CANONICAL_SOURCE: orchestrator/state/CHANNEL_RUNTIME.json
  GENERATED_SPINE_VIEW: orchestrator/state/SPINE_STATE.json
  WRITE_OWNER: Codex
  SPINE_SECTION: behavior_control_and_channel_sessions

REVISED_IMPLEMENTATION_ORDER:
  - P1a_BUGS
  - P1b_SNAPSHOTS_AND_POINTERS
  - P9_PLUS_P6_PLUS_P8_BEHAVIOR_CONTROL
  - P2a_AUTOPSY_SCHEMA
  - P2_LIVE_WALL_MAP
  - P4_ONE_SPINE
  - P5_SEMANTIC_INDEX
  - P3_NAMEWATCH
  - P7_META_CORPUS

STOP: UNIFIED_BEHAVIOR_CONTROL_NOT_MATERIALIZED
SUCCESS: UNIFIED_BEHAVIOR_CONTROL_PHASE_CHAT_PLANTS_PASS
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
ARISTOTLE_SUBMISSION: NONE
```

## 1. Source audit and exact amendment

The origin branch is currently at `982c3bd467f13ff6d4b35b9202241fb4536f7e7e`. That commit materializes the three-agent Codex-cycle reconstruction used as the evidence base for P9.  `[ABSTRACT][PAPER]`

The referenced `SYSTEM_SPEC` contains the exact `CHANNEL BEHAVIOR-CONTROL SYMMETRY` section. It records the present asymmetry: Fable has kernel v3, Proshka has its system prompt, while Codex behavior is distributed across `AGENTS.md`, reorientation documents, update notes and machine-local configuration. It also explicitly proposes `docs/CODEX_CONTROL.md`, thin bootstrap pointers and one living Proshka chat per phase.  `[ABSTRACT][PAPER]`

The cycle reconstruction confirms that this is not a theoretical concern. Fourteen recorded Proshka verdicts used fourteen fresh chats, each with a new context upload; mean reasoning time was approximately 21 minutes. It also records the off-Git standing goal, Mac/Linux site baton, disk-wins rule and Aristotle-surrogate hazard that a canonical control file must preserve.  `[ABSTRACT][PAPER]`

The current `AGENTS.md` is not a thin bootstrap. It contains live Step33 instructions, Route B scheduling, arsenal policy, Aristotle integration, Oracle use, Proshka escalation, semantic search, tone rules and legacy documentation maps. It is therefore an accumulated policy stack, not a stable pointer.  `[ABSTRACT][PAPER]`

By contrast, the two already-canonical channels have recognizable single kernels: Fable's arsenal kernel and Proshka's route-review protocol.   `[ABSTRACT][PAPER]`

### Amendment to the previous unified verdict

One previous clause is superseded:

```text
OLD:
  every ordinary goal close
  → exactly one Proshka call.

NEW:
  every ordinary goal close
  → local sensor/reference/autopsy/Spine refresh only;
  → zero Proshka calls unless that close is also a ratified owner boundary.
```

The Memory Spine remains triggered at session start and goal close. Only the expensive Proshka consultation is moved from **goal granularity** to **owner-boundary granularity inside one phase chat**. `[ABSTRACT][CONDITIONAL]`

A second clause is superseded:

```text
OLD:
  P6+P8 are written as new active policy in
  EXECUTOR_ARSENAL_ADDENDUM.

NEW:
  P6+P8 policy is absorbed into CODEX_CONTROL.md;
  the addendum becomes a historical snapshot or thin pointer.
```

Keeping both files active would reproduce the dual-control disease P9 is meant to cure.

---

## 2. Decision A — one living Proshka chat per phase

### 2.1 Phase is not a time window and not a goal number

A phase is identified by this precommitted key:

```yaml
phase_key:
  route_id:
  front_id:
  source_object_family_id:
  terminal_consumer_id:
  honesty_state:
  convention_lock_id:
```

Two goals belong to the same phase exactly when all six fields remain unchanged.

Examples of facts that **do not** change the phase:

```text
a new numbered local goal;
a helper theorem;
a compile failure;
a repair inside the same theorem family;
a new commit;
a Mac→Linux or Linux→Mac baton;
a UI/session restart;
five hours elapsing.
```

The approximate five-hour duration is telemetry, not a chat-opening trigger. A phase may be shorter or longer. `[ABSTRACT][CONDITIONAL]`

This key must be fixed before Codex enumerates the goals in the phase. Allowing Codex to redefine the key after seeing which goals are expensive would recreate post-hoc case selection. **C09 applies:** the phase classifier is an object precommit.  `[ABSTRACT][PAPER]`

### 2.2 Exact open/continue algorithm

| Event                                             | Chat action                                                                                           |  Proshka message? |
| ------------------------------------------------- | ----------------------------------------------------------------------------------------------------- | ----------------: |
| Session start, active phase and chat handle exist | Load the same conversation ID                                                                         |                No |
| Ordinary goal opens                               | Continue same chat state                                                                              |                No |
| Ordinary goal closes                              | Append local delta, refresh Spine                                                                     |                No |
| `MINT`, phase key unchanged                       | Continue the same chat and submit one boundary packet                                                 |         Yes, once |
| `MINT`, phase key changes                         | Judge the mint in the old chat; close old phase after verdict; open a new chat only for the new phase |  Once at boundary |
| `PROMOTION`                                       | Judge in current chat; close phase; next phase gets a new chat                                        |              Once |
| `FRONT_CHANGE`                                    | Judge in current chat; close phase; next front gets a new chat                                        |              Once |
| `FATAL`                                           | Immediate boundary review; current phase closes unconditionally                                       |              Once |
| Five-hour mark                                    | No action                                                                                             |                No |
| Mac/Linux baton                                   | Reuse the same conversation and phase ID                                                              |                No |
| Chat handle inaccessible                          | Stop with `PROSHKA_CHAT_HANDLE_LOST`; no silent fresh chat                                            | No automatic call |

`PROMOTION`, `FRONT_CHANGE` and `FATAL` always terminate the current phase. A `MINT` terminates it only when the newly ratified object changes the phase key.

This means a Proshka chat may contain several owner-boundary verdicts and many related goals. The conversation accumulates local context rather than restarting from zero.

### 2.3 Boundary transaction

At phase opening, Codex sends one `PHASE_OPEN_PACKET`. It contains source pins and links, not a duplicated repository dump. Proshka already has standing GitHub fetch duties. `[ABSTRACT][CONDITIONAL]`

Subsequent owner boundaries use `PHASE_DELTA_PACKET`:

```yaml
phase_id:
phase_key:
conversation_id:
last_adjudicated_pin:
current_pin:
completed_goals_since_boundary:
new_theorems:
new_axioms_or_taint:
plant_fates:
autopsy_lines:
changed_assumptions:
exact_fork:
codex_recommendation:
call_meter:
```

Unchanged files and the original context pack are not uploaded again.

### 2.4 Runtime state

The active chat ID does not belong in `CODEX_CONTROL.md`; behavior and runtime state are different categories.

Canonical runtime state:

```yaml
# orchestrator/state/CHANNEL_RUNTIME.json
schema: q3_channel_runtime.v1

active_proshka_phase:
  phase_id:
  phase_key:
  conversation_id:
  status: ACTIVE | CLOSED | ABORTED
  opened_at:
  last_boundary_id:
  opening_pin:
  last_adjudicated_pin:
  owner_boundary_count:
  proshka_calls:
  full_context_uploads:

meter:
  phases_opened:
  fresh_chats_opened:
  forced_rollovers:
  ordinary_goal_closes:
  owner_boundary_calls:
  fanout_violations:
```

Trigger owner: Codex. Existing gate moments: session start, goal close, owner boundary and site baton. Spine wiring: `behavior_control_and_channel_sessions`. `[ABSTRACT][CONDITIONAL]`

Required budget invariant:

```
fresh_chats_opened <= phases_opened + forced_rollovers.
```

And:

```
owner_boundary_calls <= #(MINT + PROMOTION + FRONT_CHANGE + FATAL).
```

Ordinary goal closes must contribute zero Proshka calls.

---

## 3. Decision B — `docs/CODEX_CONTROL.md`

### Verdict

```
docs/CODEX_CONTROL.md is required and becomes the sole executor behavior kernel.
```

Codex on macOS and Claude Code on Linux are two physical bodies of one role:

```text
ROLE: EXECUTOR
```

They must not carry two independently evolving behavior doctrines. Runtime capabilities can differ; semantic behavior cannot.

This is an instance of the C04 distinction: "same executor" means equality in the behavioral-role category, not equality of operating system, GUI transport or local authentication machinery.  `[ABSTRACT][PAPER]`

### 3.1 Mandatory control header

The file starts with:

```yaml
CONTROL_ID: Q3_EXECUTOR_CONTROL
CONTROL_VERSION: 1
STATUS: ACTIVE
ROLE: EXECUTOR
BODIES:
  - CODEX_MAC
  - CLAUDE_CODE_LINUX

TRIGGER_OWNER: Codex
TRIGGER_EVENTS:
  - SESSION_START
  - GOAL_DISPATCH
  - GOAL_CLOSE
  - OWNER_BOUNDARY
  - SITE_BATON

BOOTSTRAP_POINTERS:
  - AGENTS.md
  - CLAUDE.md
  - q3.lean.aristotle/CLAUDE.md

SPINE_WIRING: behavior_controls.executor
FAIL_CLOSED_CODE: CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS
```

### 3.2 What lives in the file

| Section                      | Canonical content                                                                                  |
| ---------------------------- | -------------------------------------------------------------------------------------------------- |
| **Authority and precedence** | System safety first; then `CODEX_CONTROL`; then active goal may narrow but not override hard rules |
| **Executor identity**        | Codex Mac and Claude Code Linux are one role                                                       |
| **Session bootstrap**        | Read control, current state and Spine; validate site baton                                         |
| **Work selection**           | Disk-wins; physical goal/master state chooses work; no pasted-text trigger                         |
| **Phase/chat lifecycle**     | Exact rule from Decision A                                                                         |
| **Owner-boundary batching**  | Closed boundary list and one-call maximum                                                          |
| **Execution scope**          | One semantic node, one compile gate, no premature export                                           |
| **Route honesty**            | CHALLENGER/NOT_RH, Bus 010 VOID, promotion restrictions                                            |
| **Lean trust gates**         | No `sorry`, `admit`, hidden axioms, surrogate objects or numerics occupying a quantifier           |
| **Aristotle firewall**       | Real production imports, no reconstructed surrogate definitions, hole scan                         |
| **Oracle/research policy**   | Advisory only; citations verified; no proof authority                                              |
| **Memory discipline**        | Spine consult, structured AUTOPSY, insights and why-not                                            |
| **Reference discipline**     | Citation → verify in current batch → PDF/status → reference ledger                                 |
| **Goal close**               | Answer/certificates, state, mirrors, manifest, commit/push and local Spine refresh                 |
| **SITE BATON**               | One active executor site; push/clean tree before handoff                                           |
| **Budget instrumentation**   | Phase/chat/call counters and no-fan rule                                                           |
| **Change control**           | Increment control version; strict validation; no duplicate active policy                           |

### 3.3 What does not live in the file

```text
current active theorem;
current route node;
dynamic phase/chat ID;
mathematical definitions;
proof bodies;
secrets and credentials;
absolute machine paths;
browser session tokens;
historical autopsies;
full source atlases;
per-goal theorem statements.
```

Those belong to state, source, local runtime adapters or the Spine.

### 3.4 Precedence law

```text
1. Platform/system safety constraints.
2. docs/CODEX_CONTROL.md — executor behavior.
3. Current source-locked goal/contract — may narrow the task.
4. Current on-disk route state — selects executable work.
5. Local ~/.codex/config.toml — runtime capability only.
6. Legacy docs — reference/snapshot, never active policy.
```

Machine-local configuration may choose model, sandbox, plugins, MCP or notifications. It may not restore `new-chat-per-goal`, bypass disk-wins, authorize Aristotle, change route honesty or alter proof standards.

A local semantic override produces:

```text
LOCAL_CONFIG_SEMANTIC_OVERRIDE
```

and fails closed.

### 3.5 Thin bootstrap pointers

`AGENTS.md` becomes approximately:

```md
# Q3 Codex bootstrap

Canonical executor behavior:
`docs/CODEX_CONTROL.md`

Read that file completely before any project action.
If it is missing, unreadable, duplicated, or not ACTIVE, stop with:

`CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`

This file contains no independent project behavior policy.
Machine-local configuration cannot override the canonical control.
```

The root and project `CLAUDE.md` files use the same pointer for executor behavior. They may retain clearly marked static references, but no active executor rules.

`EXECUTOR_ARSENAL_ADDENDUM_2026-08-04.md` becomes:

```text
STATUS: SUPERSEDED_BY_CODEX_CONTROL
```

or a thin historical pointer. Its card, AUTOPSY and precommit rules move into `CODEX_CONTROL.md`.

That migration is essential. Leaving the addendum active would mean two control files for one role.

### 3.6 One-edit behavior switching

The bootstrap pointers contain no copied version or hash. The active version exists only inside `CODEX_CONTROL.md`.

Changing executor behavior therefore requires:

```text
one edit;
one commit;
one strict Spine regeneration;
one plant run.
```

No edit to `AGENTS.md`, `CLAUDE.md` or local config is required.

---

## 4. Decision C — Behavior-Control Symmetry law

### Ratified law

```text
BEHAVIOR_CONTROL_SYMMETRY_V1

Every top-level channel role has exactly one ACTIVE repository control file.

Every physical body maps to exactly one top-level role.

Every control has:
  trigger-owner;
  bootstrap pointer;
  existing trigger moment;
  Spine wiring;
  fail-closed code.

No bootstrap pointer may contain an independent policy body.
No local runtime configuration may override semantic control.
No new channel may operate before its control and wiring are born
in the same transaction.
```

`[ABSTRACT][CONDITIONAL]`

### 4.1 Control registry

`orchestrator/KNOWLEDGE_SPINE.md` gains:

```yaml
BEHAVIOR_CONTROL_REGISTRY_V1:

  FABLE_MYTHOS:
    control: q3.lean.aristotle/docs/PROJECT_INSTRUCTIONS_v3_arsenal.md
    trigger_owner: Fable_UI_bootstrap
    trigger_events: [SESSION_START]
    spine_section: behavior_controls.fable_mythos
    status: ACTIVE

  PROSHKA:
    control: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
    trigger_owner: Proshka_task_bootstrap
    trigger_events: [NONTRIVIAL_TASK_START]
    spine_section: behavior_controls.proshka
    status: ACTIVE

  EXECUTOR:
    control: docs/CODEX_CONTROL.md
    bodies: [CODEX_MAC, CLAUDE_CODE_LINUX]
    trigger_owner: Codex
    trigger_events:
      [SESSION_START, GOAL_DISPATCH, GOAL_CLOSE, OWNER_BOUNDARY, SITE_BATON]
    spine_section: behavior_controls.executor
    status: ACTIVE
```

The current Fable and Proshka files are registered without changing their pinned bytes. At their next version change, they should adopt the standard inline control header.

### 4.2 What is not a top-level channel

Aristotle and Oracle remain executor-invoked tools. Their behavior is governed by `CODEX_CONTROL.md` and their task-specific prompt rules.

They do not receive independent top-level control files unless they are later promoted to autonomous channels. Any such promotion must satisfy the anti-orphan birth transaction first.

### 4.3 Strict validator

`spine.py --strict` must reject:

```text
zero active controls for a channel;
two active controls for one channel;
one physical body mapped to two roles;
missing trigger-owner;
missing bootstrap pointer;
missing Spine section;
normative policy in a thin pointer;
active policy in a SUPERSEDED file;
local semantic override.
```

Failure codes:

```text
BEHAVIOR_CONTROL_MISSING
BEHAVIOR_CONTROL_MULTIPLE_ACTIVE
BEHAVIOR_BODY_MULTIROLE
BEHAVIOR_TRIGGER_OWNER_MISSING
BEHAVIOR_SPINE_WIRING_MISSING
THIN_POINTER_CONTAINS_POLICY
SUPERSEDED_CONTROL_STILL_ACTIVE
LOCAL_CONFIG_SEMANTIC_OVERRIDE
```

---

## 5. Revised integration order

The prior P1a/P1b split remains binding. P9 is inserted immediately after it and absorbs the old P6+P8 executor-policy transaction:

```text
P1a
  bug fixes.

P1b
  snapshots and exact stale-pointer repair.

P9 + P6 + P8
  CODEX_CONTROL;
  one-chat-per-phase;
  budget law;
  anti-orphan;
  citation discipline;
  thin AGENTS/CLAUDE;
  channel registry.

P2a
  AUTOPSY schema freeze.

P2
  live wall derivation.

P4
  full One-Spine adapters and triggers.

P5
  semantic index.

P3
  namewatch.

P7
  meta-corpus.
```

This ordering prevents the remaining contour implementation from being performed under the very fragmented behavior stack it is meant to replace.

---

## 6. Mandatory K1 plants

| Plant       | Mutation                                          | Required result                                                       |
| ----------- | ------------------------------------------------- | --------------------------------------------------------------------- |
| `BCS-P1`    | Add a second ACTIVE executor control              | `BEHAVIOR_CONTROL_MULTIPLE_ACTIVE`                                    |
| `BCS-P2`    | Remove executor `trigger_owner`                   | `BEHAVIOR_TRIGGER_OWNER_MISSING`                                      |
| `BCS-P3`    | Put an active chat rule back into `AGENTS.md`     | `THIN_POINTER_CONTAINS_POLICY`                                        |
| `CHAT-P1`   | New goal, identical phase key                     | `CONTINUE_EXISTING_CHAT`                                              |
| `CHAT-P2`   | Session restart, identical phase key              | `CONTINUE_EXISTING_CHAT`                                              |
| `CHAT-P3`   | Five hours elapsed, identical phase key           | `CONTINUE_EXISTING_CHAT`                                              |
| `CHAT-P4`   | Mac/Linux baton, identical phase key              | `CONTINUE_EXISTING_CHAT`                                              |
| `CHAT-P5`   | `front_id` changes                                | `CLOSE_OLD_OPEN_NEW_PHASE_CHAT`                                       |
| `CHAT-P6`   | Mint leaves phase key unchanged                   | `CONTINUE_EXISTING_CHAT`                                              |
| `CHAT-P7`   | FATAL                                             | `CLOSE_PHASE_IMMEDIATELY`                                             |
| `CHAT-P8`   | Active conversation handle missing                | `PROSHKA_CHAT_HANDLE_LOST`, no silent fresh chat                      |
| `SWITCH-P1` | Change one policy line only in `CODEX_CONTROL.md` | Both executor bodies resolve the changed policy without wrapper edits |

The chat comparator is not allowed to inspect goal numbers or elapsed time when deciding phase equality.

---

## 7. Strongest attack

### Attack: the phase key can be gamed

If the key is too broad, Codex keeps using an old chat after the mathematical object has changed. Context then accumulates incompatible conventions.

If the key is too narrow, every helper theorem changes the key and the fresh-chat antipattern returns under a new name.

### Repair

The key is a closed six-field object fixed before execution. Any proposed additional key field requires a control-version change and a plant. Goals and commits are explicitly excluded.

A convention change is a phase change only when it changes the authoritative `convention_lock_id`; informal notation edits do not.

### Attack: one control file becomes one stale point of failure

A single file can centralize confusion as easily as it centralizes control.

### Repair

`CODEX_CONTROL.md` stores only stable behavior. It does not store current work, proofs or route state. Strict Spine validation checks reachability, freshness, uniqueness and trigger ownership on every session start.

The control file is therefore a kernel, not a second project encyclopedia.

---

## 8. Final proposal

The unified contour is now:

```text
ONE MEMORY SPINE
  canonical sources
  → spine.py
  → SPINE_STATE / SPINE_VIEW

ONE BEHAVIOR KERNEL PER CHANNEL
  Fable/Mythos → kernel v3
  Proshka      → system prompt v2
  Executor     → CODEX_CONTROL

ONE PROSHKA CHAT PER PHASE
  many related goals
  → local goal closes
  → owner-boundary delta packets
  → no fresh chat until phase changes
```

### Registered predictions

```text
P-BC1:
  after P9, ordinary goal closes generate zero Proshka calls.

P-BC2:
  fresh Proshka chats equal phase openings plus explicit forced rollovers,
  not goal count.

P-BC3:
  AGENTS.md and both CLAUDE entry files contain pointers,
  not competing executor policy.

P-BC4:
  the largest implementation failure will be leaving
  EXECUTOR_ARSENAL_ADDENDUM active after CODEX_CONTROL is created.

P-BC5:
  phase-key plants will show that goal number and five-hour duration
  are not valid chat-opening discriminators.
```

### Meta closeout

**What became smaller?**

The vague rule "reuse the chat more often" became a deterministic six-field phase comparator and a closed event table.

**What was killed?**

```text
fresh chat per goal;
full context re-upload per verdict;
goal close as an automatic Proshka-call trigger;
AGENTS.md as an accumulating behavior kernel;
EXECUTOR_ARSENAL_ADDENDUM as a second active control;
machine-local config as semantic policy.
```

**What must not be tried again?**

Do not infer phase change from goal number, commit count, elapsed time, operating system or session restart. Do not leave copied policy in thin pointers.

**Current smallest named gap**

```text
P9_CODEX_CONTROL_AND_PHASE_CHAT_MATERIALIZATION
```

**Next cheapest decisive test**

Run the phase comparator on four fixtures:

```text
same phase + new goal;
same phase + five hours;
same phase + site baton;
changed front.
```

Required outputs:

```text
CONTINUE
CONTINUE
CONTINUE
OPEN_NEW_AFTER_CLOSE
```

```yaml
iteration:
  target: behavior_control_symmetry_and_phase_chat_model
  status: OPEN
  failed_strategy: fresh_chat_per_goal_with_full_context_reupload
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: P9_CODEX_CONTROL_AND_PHASE_CHAT_MATERIALIZATION
  invariant_learned: goal granularity and phase granularity are different; behavior policy and runtime state are different
  forbidden_future_move: open_a_new_Proshka_chat_without_a_materialized_phase_change
  next_decisive_test: phase_key_comparator_and_duplicate_control_plants
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
MODE: OWNER_RELAY_REQUIRED
EXECUTE_AFTER_OWNER_RELAY: true
REPO_WRITE_AUTHORIZED_BEFORE_RELAY: false
ARISTOTLE_SUBMISSION: NONE

TARGET:
  P9_CODEX_CONTROL_AND_PHASE_CHAT_MATERIALIZATION

PRECONDITIONS:
  - P1a status recorded
  - P1b exact pointer census recorded
  - working tree and active site reported
  - no mathematical Lean source modification in this transaction

STOP:
  UNIFIED_BEHAVIOR_CONTROL_NOT_MATERIALIZED

SUCCESS:
  UNIFIED_BEHAVIOR_CONTROL_PHASE_CHAT_PLANTS_PASS

CREATE:
  - docs/CODEX_CONTROL.md
  - orchestrator/state/CHANNEL_RUNTIME.json

MODIFY:
  - AGENTS.md
  - CLAUDE.md
  - q3.lean.aristotle/CLAUDE.md
  - docs/EXECUTOR_ARSENAL_ADDENDUM_2026-08-04.md
  - orchestrator/KNOWLEDGE_SPINE.md
  - orchestrator/spine.py
  - orchestrator/packet.py

CODEX_CONTROL_REQUIRED_SECTIONS:
  - control_header_and_anti_orphan_metadata
  - authority_and_precedence
  - executor_role_and_two_bodies
  - session_bootstrap
  - disk_wins_work_selection
  - phase_key_and_chat_open_continue_rule
  - owner_boundary_batching
  - execution_scope
  - route_honesty
  - Lean_trust_gates
  - Aristotle_anti_surrogate_firewall
  - Oracle_and_research_policy
  - memory_autopsy_reference_discipline
  - goal_close_commit_mirror_state_duties
  - site_baton
  - budget_meter
  - change_control_and_failure_codes

PHASE_KEY_FIELDS:
  - route_id
  - front_id
  - source_object_family_id
  - terminal_consumer_id
  - honesty_state
  - convention_lock_id

OWNER_BOUNDARIES:
  - MINT
  - PROMOTION
  - FRONT_CHANGE
  - FATAL

CHAT_RULES:
  - identical_phase_key_means_continue
  - ordinary_goal_close_never_opens_chat
  - session_restart_never_opens_chat
  - elapsed_time_never_opens_chat
  - site_baton_never_opens_chat
  - promotion_front_change_fatal_close_phase
  - mint_closes_phase_only_if_phase_key_changes
  - missing_chat_handle_fails_closed
  - no_silent_fresh_chat
  - one_phase_open_packet_then_delta_packets_only

THIN_POINTER_RULE:
  AGENTS.md:
    canonical_control: docs/CODEX_CONTROL.md
    independent_policy_allowed: false
  CLAUDE.md:
    canonical_executor_control: docs/CODEX_CONTROL.md
    independent_executor_policy_allowed: false
  q3.lean.aristotle/CLAUDE.md:
    canonical_executor_control: docs/CODEX_CONTROL.md
    independent_executor_policy_allowed: false
  EXECUTOR_ARSENAL_ADDENDUM:
    status: SUPERSEDED_BY_CODEX_CONTROL

BEHAVIOR_CONTROL_REGISTRY:
  host: orchestrator/KNOWLEDGE_SPINE.md
  channels:
    - FABLE_MYTHOS
    - PROSHKA
    - EXECUTOR
  exact_one_active_control_per_role: true

RUNTIME_STATE:
  path: orchestrator/state/CHANNEL_RUNTIME.json
  write_owner: Codex
  spine_wiring: behavior_control_and_channel_sessions
  required_fields:
    - active_phase_id
    - phase_key
    - conversation_id
    - chat_status
    - last_boundary_id
    - opening_pin
    - last_adjudicated_pin
    - proshka_calls
    - full_context_uploads
    - fresh_chats_opened
    - fanout_violations

MANDATORY_PLANTS:
  - duplicate_active_executor_control_must_fail
  - missing_trigger_owner_must_fail
  - policy_in_AGENTS_must_fail
  - same_phase_new_goal_must_continue
  - same_phase_session_restart_must_continue
  - same_phase_five_hours_must_continue
  - same_phase_site_baton_must_continue
  - changed_front_must_open_after_close
  - unchanged_key_mint_must_continue
  - fatal_must_close_phase
  - missing_chat_handle_must_not_open_silently
  - one_edit_control_switch_must_reach_both_executor_bodies

VALIDATION:
  - python3 orchestrator/spine.py --strict --reason session-start
  - phase_comparator_fixture_suite
  - behavior_control_duplicate_fixture
  - thin_pointer_policy_lint
  - local_config_semantic_override_fixture
  - deterministic_second_spine_run_no_diff
  - exact_file_inventory
  - git_diff_check
  - exact_git_status_report

FORBIDDEN:
  - modify Lean theorem or proof source
  - create a second executor control file
  - keep active policy in AGENTS.md
  - keep active executor policy in CLAUDE.md
  - keep EXECUTOR_ARSENAL_ADDENDUM active
  - store current theorem or route state in CODEX_CONTROL
  - store secrets or tokens in repo
  - open fresh Proshka chat per goal
  - upload the full unchanged context at every boundary
  - call Proshka on ordinary goal close
  - create Bus 010
  - submit Aristotle
  - promote Route B
  - claim RH

FAILURE_CODES:
  - CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS
  - BEHAVIOR_CONTROL_MISSING
  - BEHAVIOR_CONTROL_MULTIPLE_ACTIVE
  - BEHAVIOR_BODY_MULTIROLE
  - BEHAVIOR_TRIGGER_OWNER_MISSING
  - BEHAVIOR_SPINE_WIRING_MISSING
  - THIN_POINTER_CONTAINS_POLICY
  - SUPERSEDED_CONTROL_STILL_ACTIVE
  - LOCAL_CONFIG_SEMANTIC_OVERRIDE
  - PHASE_KEY_SCHEMA_MISMATCH
  - PROSHKA_CHAT_HANDLE_LOST
  - PROSHKA_FRESH_CHAT_WITHOUT_PHASE_CHANGE
  - PROSHKA_CALL_OUTSIDE_OWNER_BOUNDARY
  - PROSHKA_PHASE_FANOUT_VIOLATION
  - NONDETERMINISTIC_CONTROL_VIEW

REPORT_REQUIRED:
  - exact source pin and files touched
  - final CODEX_CONTROL section inventory
  - before_after normative policy locations
  - proof that AGENTS and CLAUDE files are thin/non-normative
  - exact behavior-control registry
  - exact phase-key comparator
  - all plant fates
  - runtime ledger sample
  - ordinary_goal_close_proshka_call_count_zero
  - confirmation of no Lean source changes
  - ROUTE CHALLENGER_NOT_RH
  - BUS_010 VOID
  - ARISTOTLE_SUBMISSION NONE
```

---

> NOTE: This file is the verbatim materialization of Proshka's SECOND architecture verdict
> (EXTERNAL_VERDICT_MATERIALIZATION), relayed by the owner. It AMENDS the first unified verdict
> (`PROSHKA_VERDICT_UNIFIED_MEMORY_CONTOUR_2026-08-05.md`): batch-per-PHASE (not per-goal), automatic
> Proshka-call on goal-close REMOVED, P9 inserted, EXECUTOR_ARSENAL_ADDENDUM killed as active control,
> P6+P8 content absorbed into `docs/CODEX_CONTROL.md`. Applied cards C04 + C09. Implementation is
> OWNER_RELAY_REQUIRED and per-action-OK gated (REPO_WRITE_AUTHORIZED_BEFORE_RELAY: false); NOT executed
> by this materialization. Revised order: P1a → P1b → P9+P6+P8 → P2a → P2 → P4 → P5 → P3 → P7.
> CHALLENGER/NOT_RH, Bus 010 VOID, no promotion, no Aristotle submission.
