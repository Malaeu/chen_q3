# Q3 Executor Control

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
  - DELEGATED_STRATEGIC_REVIEW
  - PX_RH_CLAIM
  - SITE_BATON

BOOTSTRAP_POINTERS:
  - AGENTS.md
  - CLAUDE.md
  - q3.lean.aristotle/CLAUDE.md

SPINE_WIRING:
  - behavior_controls.executor
  - behavior_control_and_bounded_exploration
FAIL_CLOSED_CODE: CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS

ANTI_ORPHAN:
  trigger_owner: Codex
  existing_entry_gates:
    - NAMED_THEOREM_SHAPE_FORK
    - EXPLORATION_STALL
    - LOOP_TRAP
  control_host: docs/CODEX_CONTROL.md
  runtime_host: orchestrator/state/CHANNEL_RUNTIME.json
  durable_memory_host: q3.lean.aristotle/aristotle_db/knowledge.db
  fail_closed_code: EXPLORATION_CONTOUR_ORPHANED
```

> **Active kernel.** This is the single semantic behavior control for both
> executor bodies. `AGENTS.md`, both `CLAUDE.md` entry files, and the former
> executor addendum are thin pointers and contain no independent active policy.

## 1. Authority and precedence

Precedence is: platform/system safety; explicit operational instruction;
this active control; the source-locked task or goal, which may narrow
but not weaken the control; physical on-disk route state; local runtime
configuration; historical documents. Local configuration controls capability,
not mathematical policy.

At every session start, each executor body audits machine-local memory and
bootstrap instructions for semantic rules that contradict this control. An
unresolved local rule such as fresh-chat-per-goal is not a harmless historical
note; strict startup must fail closed with:

```text
NATIVE_MEMORY_SEMANTIC_OVERRIDE
```

There is exactly one mathematical owner boundary:

```text
PX_RH_CLAIM
```

Only the Owner may authorize the final claim that the project has achieved
PX/RH. Every other mathematical or proof-architecture decision is standingly
delegated to Codex and Proshka together, including theorem shape; route
selection, killing, pivoting, and mathematical promotion; canonical object or
definition design and mint; theorem/contract formulation and semantic
revision; axiom or trust proposals; front and phase-key changes; experimental
admission; and decisive-test selection and interpretation.

For a non-PX/RH decision, returning `OWNER_AUTHORITY_REQUIRED`, `OWNER_FORK`,
or “owner choose A/B” is a control failure:

```text
MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH
```

Naming firewall: historical control-plane `Rule A` / `Rule B` labels are never
proof-route names. Proof routes are written `Route A` / `Route B`; new control
rules use descriptive identifiers instead of ambiguous letters.

Operational permission is a different category. A selected mathematical route
stays selected if commit/push, publication, paid API use, or an irreversible
external action still needs an explicit operational command. The state becomes
`OPERATIONAL_ACTION_PENDING`; it does not reopen mathematical route selection.

## 2. Executor role and two bodies

`CODEX_MAC` and `CLAUDE_CODE_LINUX` are two physical bodies of one `EXECUTOR`
role. OS, authentication, GUI, notification, model, sandbox, and plugin
differences are runtime adapters only. They may not produce two semantic
policies. A body may act only after resolving the same active control.

## 3. Session bootstrap and disk-wins selection

At session start:

1. Read the active executor control completely.
2. Read `SESSION_ENTRY.md`, the task-specific physical state, and the current
   generated Spine view.
3. Run strict control/runtime validation.
4. Inspect Git branch, worktree, and site baton without treating `untracked` as
   foreign.
5. Select work from physical on-disk state. Pasted text, browser state, a stale
   monitor, or a remembered goal never creates an executable goal.

For Route B, its execution state/control and physical bus decide whether a goal
exists. Codex never manufactures the next bus number. A challenger route never
silently replaces the canonical mainline.

## 4. Phase key and one living Proshka chat

A mathematical phase is the closed six-field object:

```yaml
phase_key:
  route_id:
  front_id:
  source_object_family_id:
  terminal_consumer_id:
  honesty_state:
  convention_lock_id:
```

Equality of all six fields means continue the existing chat. Goal number,
helper lemma, commit, build failure, elapsed time, session restart, and site
baton are excluded from the comparator. A real key change closes the old phase
and permits a new chat after Codex and Proshka decide the change. No owner
mathematical approval is required.

The conversation handle lives only in
`orchestrator/state/CHANNEL_RUNTIME.json`. A missing handle fails closed with
`PROSHKA_CHAT_HANDLE_LOST`; no silent fresh chat is allowed. One phase-open
packet is followed only by delta packets. Ordinary goal close opens no chat,
uploads no full context, and causes zero Proshka calls.

## 5. Proshka call taxonomy and operative classes

Allowed call classes are:

- `DELEGATED_STRATEGIC_REVIEW` for `MINT`, `PROMOTION`, `FRONT_CHANGE`, or
  `FATAL`; Codex and Proshka decide, and a new chat is permitted only after an
  actual phase-key change.
- `EXPLORATION_REVIEW`, once per exploration ID and once per
  `(phase_id, blocker_fingerprint)` pair, in the same chat and with one
  `EXPLORATION_DELTA_PACKET`.
- `PX_RH_CLAIM_REVIEW`, whose only valid owner result is
  `OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM`.

Proshka must return exactly one machine-operative class:

```text
TRY_<route_id>
KILL_<route_or_family_id>
RUN_<test_id>
OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM
```

Every other `OWNER_AUTHORITY_REQUIRED_*`, `OWNER_FORK`, or owner-choice result
is invalid. `RUN` includes a precommitted outcome map so interpreting the test
does not require a second review.

## 6. BOUNDED_EXPLORATION_PHASE

`BOUNDED_EXPLORATION_PHASE` (human alias: “fantasy phase”) is a reversible
research substate inside an unchanged six-field mathematical phase. It is not
a channel, daemon, proof authority, phase change, or permission to wander.

Entry is allowed only through:

- `NAMED_THEOREM_SHAPE_FORK`: two to five genuinely distinct normalized
  theorem shapes, same phase and honesty state, no source-locked winner, every
  candidate reversible and carrying a cheapest killer. Three to five is a
  target, never a padding requirement. Tactics, wrappers, or file layouts for
  one theorem are not distinct routes.
- `EXPLORATION_STALL`: three consecutive registered cycles preserve one
  blocker fingerprint and contain no validated belief-changing delta.
- `LOOP_TRAP`: repairs change only names, wrappers, segmentation, packaging, or
  placement while preserving the source object, consumer, implication,
  dependencies, invariants, dropped structure, and blocker.

Codex owns entry-predicate evaluation, normalized fingerprints, the
plain-language blocker, two-to-five real candidates, cheap reversible
discriminators, progress validation, counters, runtime hygiene, and notices.

## 7. Exploration loop and normalized identity

Before acting, Codex states: exact desired conclusion; unavailable implication
or data; forbidden shortcuts; smallest uncertainty. Each candidate states:
preserved invariants; dropped structure; cheapest killer; expected viable
evidence; rollback target.

Allowed cheap discriminators are repository/knowledge search, primary-source
audit, an exact symbolic counterexample, a read-only finite diagnostic, or a
temporary Lean harness outside tracked production source.

Blocker fingerprints exclude paths, theorem names, commits, wrappers, wording,
build counts, and time. They include the phase key, source object, terminal
consumer, missing implication and dependency IDs, preserved invariants,
quantifier scope, and mathematical domain. Route fingerprints include the
normalized theorem shape, assumptions, conclusion, dependencies, invariants,
dropped structures, and decisive-test class. Equal normalized fingerprints
make a renamed restart fail with `EXPLORATION_ALIAS_RESTART`.

## 8. Two-key decision and proof-truth firewall

The Codex key is `locally_executable && source_compatible`. The Proshka key is
`mathematically_honest && non_surrogate`. Both keys complete the delegated
mathematical decision and select one implementation route. Disagreement runs
the cheapest belief-changing test; owner escalation is forbidden.

Two keys are not proof. Source identity, exact consumer match, Lean or accepted
certificate validation, taint and axiom gates, quantifier preservation, units,
normalization, and absence of hidden RH input remain independently required.
Agreement about a reconstructed object fails with
`EXPLORATION_SURROGATE_COLLUSION`.

## 9. Closed PROGRESS_DELTA schema

```yaml
delta_id:
exploration_id:
cycle_index:
kind: THEOREM_OR_LEMMA_CLOSED | SOURCE_FOUND | SOURCE_ABSENCE_CERTIFIED |
      HYPOTHESIS_REMOVED | COUNTEREXAMPLE_FOUND | BLOCKER_DECOMPOSED |
      QUANTITATIVE_INTERVAL_NARROWED | DEPENDENCY_EDGE_REMOVED
scope: ABSTRACT | FINITE_CELL | COFINAL_FAMILY
verifier: LEAN | ARB_INTERVAL | PAPER | CONDITIONAL
subject_id:
blocker_fingerprint_before:
blocker_fingerprint_after:
before:
after:
decision_effect: CANDIDATE_SELECTED | CANDIDATE_KILLED |
                 ASSUMPTION_REMOVED | SOURCE_STATUS_CHANGED |
                 BLOCKER_STRICTLY_SHRUNK | INTERVAL_STRICTLY_NARROWED |
                 DEPENDENCY_REMOVED
evidence:
  - kind:
    ref:
    sha256:
validated:
stall_counter_reset:
```

A counter resets only for validated `LEAN`, `ARB_INTERVAL`, or `PAPER`
evidence with a nonempty decision effect and evidence reference. A
`CONDITIONAL` delta may be recorded but never resets the counter. Commits,
builds, wrappers, renames, wording, elapsed time, context uploads, and renamed
restarts are non-progress.

Per-kind guards require exact before/after evidence: the intended theorem and
trust audit; a precommitted source search; a source-faithful counterexample; a
strictly smaller blocker; the same quantity/units/domain with certified smaller
width; or proof that a dependency is no longer consumed.

## 10. Cycle comparator and state machine

A registered cycle is one precommitted candidate action with an expected
belief change, cheapest killer or implementation step, result, and a delta ID
or null. Repeated builds inside it are not new cycles.

- Three no-delta cycles: `SOFT_STALL`; stop implementation, return to local
  exploration, choose the cheapest killer, no Proshka call.
- Six no-delta cycles: `HARD_STALL`; one same-chat exploration review only if
  unused for this phase/blocker.
- Eight active reasoning hours: warning and nonblocking notice only; time never
  changes state or authorizes a call.
- Twelve registered cycles: `EXPLORATION_BUDGET_EXHAUSTED`; close the episode.
- After the one review, another hard stall or a failed decisive test with no
  belief change is terminal. Exit by `KILL`, `TRY` of a pre-analysed
  alternative, or `RUN` of a registered discriminator; never `OWNER_FORK`.

An actual phase/front/key change is a delegated Codex+Proshka decision that
closes the old phase and opens a new chat only after the key changes.

## 11. Experimental isolation and normal-loop admission

Before route selection, work is read-only or ephemeral outside tracked math
source. After both keys, code lives in a dedicated experimental branch or
worktree with a stable exploration ID and, if committed, trailers:

```text
Q3-Experimental: <exploration_id>
Q3-Not-Promoted: true
```

Production imports, public theorem dependencies, source-locked claims from
experimental results, and wholesale merge before admission are forbidden.

Normal-loop admission requires: one operative Proshka result or precommitted
`RUN` outcome; both keys; unchanged phase key; named exact source and consumer;
frozen theorem/contract; validated progress delta; source/Lean gate; taint and
axiom gate; scoped diff; rollback target. Admission selects an implementation
target; it is neither proof truth nor a PX/RH claim.

## 12. Owner notice and operational separation

Notices are required at exploration entry, material route selection, hard
stall, canonical mint, trust change, mathematical promotion, and phase change.
They contain:

```yaml
blocker:
candidates:
what_died:
what_was_learned:
selected_route:
rollback:
mathematical_decision:
operational_action_pending:
owner_mathematical_action_required:
```

For every non-PX/RH event,
`owner_mathematical_action_required: false`. A notice blocks mathematics only
for `PX_RH_CLAIM`. A platform-required operational permission may block the
concrete external action, never the mathematical decision.

## 13. Route honesty and trust gates

Every route keeps its declared honesty state until an explicit delegated
phase-key change. Challenger evidence is not a canonical or PX/RH claim.
Closure, a green build, numerics, a dashboard, or two-agent agreement is not
semantic proof.

Lean admission rejects `sorry`, `admit`, `exact?`, hidden axioms, unsafe or
native computation occupying a mathematical quantifier, surrogate objects,
wrong imports, changed statements, and unverified dependencies. A downloaded
Aristotle result is a draft until hole scan, real production imports, exact
source-object/consumer comparison, axiom audit, and direct Lean compilation
pass. Aristotle and Oracle are executor-invoked tools, never proof authorities;
paid calls still require their operational budget gate.

Research begins with exact target and consumer, current knowledge search, and
primary-source verification. Citations are checked in the current batch; a
paper, advisory model, or numeric diagnostic cannot silently become proof
truth.

### 13.1 Arsenal, AUTOPSY and reference discipline

Before creating a new theorem, route object, certificate, prompt or brief, the
executor consults the generated Spine, queries `knowledge.db` on the key terms,
and scans the arsenal deck by mechanism signature. The decision record names
the rejected alternatives and why they were not selected. If a goal declares a
card, its answer carries `ARSENAL_USED: Cxx`.

Auxiliary profiles, cutoffs, weights, matrices, sampling schemes and certificate
partitions are object-precommitted before outcomes are inspected. Post-hoc
objects are relabelled as weaker exploratory results and never exported as the
precommitted claim.

Every `INCONCLUSIVE`, `WALL`, or `KILLED` result carries one or more exact lines:

```text
AUTOPSY: dropped=<AUTOPSY_TAG_V1>; note=<nonempty one-line text>
```

The closed `AUTOPSY_TAG_V1` set is:

```text
SOURCE_IDENTITY
OBJECT_IDENTITY
DOMAIN
QUANTIFIER
NORMALIZATION
ORIENTATION
LOCALIZATION
SIGN
PARITY
MULTIPLICITY
BOUNDEDNESS
COUPLING
ENDPOINT
REGULARITY
COMPACTNESS
MEASURE_VS_ALGEBRA
SPECTRAL_ORDERING
CANCELLATION
DEPENDENCY
TRUST
```

One tag per line; multiple lines are allowed. Legacy free-text AUTOPSY lines
remain `LEGACY_UNCLASSIFIED`, are never auto-retagged, and are ineligible for
namewatch. A missing or malformed required line blocks goal close.

When a goal, answer, verdict or insight cites a publication, the same batch
verifies the source and exact supported claim, records publication status and
the person-name gate when relevant, stores an open-access PDF under the existing
litreview corpus (or marks `OWNER_FETCH_REQUIRED`), updates both
`docs/routeB_bus/litreview/REFERENCES.md` and `references.bib`, then runs the
litreview validator. A citation has no proof authority merely because it is
listed.

## 14. Memory, goal close, site baton, and budget

Active exploration state lives in `CHANNEL_RUNTIME.json`: at most five
candidates, twelve cycle summaries, one compact prior close, and one validated
latest delta. On close, raw candidate prose and logs are removed. Exactly one
compact `exploration_close` journal row is durable; links connect it to existing
objects. Speculative exhaust, repeated builds, and raw chat transcripts are
not durable memory.

### Database role boundary

The project has three deliberately separate SQLite databases, while Codex has
a fourth machine-local database. They solve different problems:

```yaml
PROJECT_DATABASE_ROLES:
  semantic_project_memory:
    path: q3.lean.aristotle/aristotle_db/knowledge.db
    owns: [kills, moves, dossiers, postmortems, exclusions, reviewed_journal]
    authority: canonical_for_project_semantic_memory
  proof_artifact_registry:
    path: q3.lean.aristotle/aristotle_db/aristotle_proofs.db
    owns: [documents, lemma_status, specifications, Aristotle_provenance]
    authority: metadata_index_not_Lean_kernel_truth
  observability_projection:
    path: q3.lean.aristotle/aristotle_db/observability.db
    owns: [sensor_snapshots, holes, import_edges, taint, axiom_dependencies,
           numeric_results, Proshka_timing_projection]
    authority: derived_noncanonical_atomically_rebuildable
  native_codex_episodic_memory:
    path_class: ~/.codex/memories_1.sqlite
    owns: [memory_generation_jobs, stage_outputs, local_recall_runtime]
    authority: noncanonical_machine_local_runtime
DATABASE_SEPARATION_RULE: PROJECT_DATABASES_MUST_NOT_BE_MERGED
```

`knowledge.db` may record a compact reviewed conclusion about an episode;
`aristotle_proofs.db` may index a checked artifact; `observability.db` may
project current sensor and operational records; native Codex memory may help
recover context. None may silently import the authority of another. In
particular, native recall cannot establish a project decision, proof status, or
PX/RH claim; the artifact registry cannot establish Lean truth; raw timing or
sensor rows cannot establish a decision; and no cross-database merge or
cross-database foreign-key graph is part of the architecture. Spine reads
project databases through explicit read-only adapters and renders a view,
never a replacement source of truth.

At ordinary goal close, refresh local sensors and Spine, materialize only the
authorized answer/certificates/state/mirror/manifest duties, and make zero
Proshka calls. Commit, push, publication, or handoff occurs only when the
concrete operational action is authorized. A site baton never changes policy,
phase, or chat; handoff state must be explicit and recoverable.

Meters distinguish delegated strategic reviews, exploration reviews, PX/RH
claim requests, ordinary goal-close calls, mathematical owner-deferral
violations, and chat fanout. Required invariants include:

```text
ordinary_goal_close_calls_to_proshka = 0
exploration_review_calls_per_exploration_id <= 1
fresh_chats_opened <= phases_opened + forced_rollovers
mathematical_owner_deferral_violations = 0
```

## 15. Failure codes and change control

```text
CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS
LOCAL_CONFIG_SEMANTIC_OVERRIDE
PROSHKA_CHAT_HANDLE_LOST
PROSHKA_FRESH_CHAT_WITHOUT_PHASE_CHANGE
PROSHKA_PHASE_FANOUT_VIOLATION
EXPLORATION_CONTOUR_ORPHANED
EXPLORATION_RUNTIME_MISSING
EXPLORATION_ENTRY_REJECTED_NOT_A_FORK
PROGRESS_DELTA_SCHEMA_INVALID
PROGRESS_DELTA_INVALID_COSMETIC
STALL_COUNTER_RESET_INVALID
EXPLORATION_PHASE_KEY_SMUGGLE
EXPLORATION_SURROGATE_COLLUSION
EXPLORATION_TWO_KEY_NOT_INDEPENDENT
PROSHKA_UNSTRUCTURED_OWNER_DEFERRAL
EXPLORATION_REVIEW_OUTSIDE_GATE
EXPLORATION_REVIEW_DUPLICATE
EXPLORATION_CHAT_FANOUT
EXPERIMENTAL_CANONICAL_CONTAMINATION
EXPLORATION_ALIAS_RESTART
EXPLORATION_BUDGET_EXHAUSTED
EXPLORATION_KB_NOISE_POLICY_VIOLATION
PROJECT_DATABASE_ROLE_COLLISION
NATIVE_MEMORY_SEMANTIC_OVERRIDE
OBSERVABILITY_SNAPSHOT_INVALID
SEMANTIC_INDEX_PLANT_FAILED
ARTIFACT_IDENTITY_DRIFT
AUTOPSY_REQUIRED_MISSING
AUTOPSY_SCHEMA_INVALID
NORMAL_LOOP_ADMISSION_EVIDENCE_MISSING
NONDETERMINISTIC_EXPLORATION_VIEW
MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH
PX_RH_CLAIM_WITHOUT_OWNER_AUTHORIZATION
OPERATIONAL_GATE_MISUSED_AS_MATHEMATICAL_DEFERRAL
INVALID_OWNER_AUTHORITY_REQUIRED_CLASS
```

Changing semantic behavior requires a control-version increment, strict
validation, plants, and one edit to this active kernel. No wrapper or local
configuration may duplicate the changed policy.
