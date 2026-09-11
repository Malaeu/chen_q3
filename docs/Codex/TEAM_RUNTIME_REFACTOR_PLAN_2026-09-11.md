# Q3 team execution and workflow repair plan

Date: 2026-09-11
Status: IMPLEMENTATION AUTHORIZED 2026-09-11; cross-host extension under review; not itself executable policy or a new mathematical goal.
Authoring task: 01a08f80-f033-7a31-8f3a-3aef042a3fbc / local.
Mathematical owner remains 01a084f4-7498-7021-bac2-91d184d58dc7 until an explicit safe handoff.

## 1. Outcome and boundaries

One orchestrator owns continuation, assignment, integration and the problem queue
for the existing Q3 repository. Bounded execution agents return verified work and
evidence-backed observations of code, ordering, contract and instruction defects.
An independent checker distinguishes a real defect from stale context, an agent
mistake or a correctly enforced guard. Confirmed defects affecting the current
task are repaired before dependent work proceeds; independent mathematical work
continues where its own prerequisites remain satisfied.

This plan implements one programmatic entry and a bounded repair cycle around
the existing mathematical task. It does not promise elimination of every future
bug, execution while the computer/app is off, proof by agent consensus, or
automatic weakening of a safety/proof/authority boundary. No new service,
scheduler, database, mathematical selector or global ~/.codex policy edit.
Current owner authority, immutable requests, source normalization, review rules
and owner-only PX_RH_CLAIM remain in force. The owner authorized implementation
on 2026-09-11 and added home/work continuity. The cross-host extension and each
implementation manifest retain required review.

## 2. Facts and components to reuse

- Existing front door: orchestrator/workflow_runtime.py::live_plan_v10. It builds
  one local startup snapshot, but does not reconcile RESUME with that snapshot.
- Existing durable writer: resume_checkpoint, _execution_writer_epoch,
  _resume_cas_bytes and the framed archive. Preserve crash/replay/conflict tests
  and all original history bytes. These helpers do not prove observation truth.
- Existing startup git_dirty is scoped to startup paths plus declared owned paths.
  Keep its meaning; add an explicit whole-worktree observation and ownership view.
- Existing durable registries: docs/Codex/RESUME.md (current continuation),
  docs/Codex/AGENTS_LEDGER.md (assignments), docs/INSTRUCTION_ISSUES.md (issues).
  Existing session protocols hold longer evidence. Do not copy complete logs into
  every checkpoint or create a second source of current issue/assignment truth.
- Existing tools manifest and workflow/startup/closeout tests remain the execution
  and verification route. Use existing source-dependent refresh contracts.
- Cross-host source audit confirmed that active v10 lock binds only the local
  inode/descriptor, while CODEX_CONTROL section11 still describes richer legacy
  PID/boot/session metadata. Correct that claim in the same reviewed control edit;
  do not advertise unimplemented fencing. SITE_BATON is an event class only.
  bind_request.py currently holds a local lock through push: include this active
  path in the exact intent/pinned-commit/push/readback repair, with network waits
  outside the filesystem lock and unknown push outcomes reconciled before replay.
- Reuse goal_events.py's tested unique-key JSON loader, provenance/retry patterns
  and legacy-prefix boundary design where their contracts fit. Its record_attempt
  is q3_goal_attempt.v1, with goal-bound IDs, cycle_index1..12 and mathematical
  prediction/operator/progress fields; generic agent reports must not be forced
  through it. record_insight is for checked reusable synthesis, not every report
  or adjudication. record_delegated_review remains tied to real Proshka phases.
  INSTRUCTION_ISSUES remains the one issue registry; technical complaints do not
  become mathematical RESEARCH_DEBT or MATHEMATICALLY_DEAD by being recorded.
- Read-only observations on 2026-09-11: plan HOLD with no fatal errors at9005b347.
  Earlier SLACK was prepared/bound but undelivered after a transport failure.
  RESUME revision17, observed13:49:46+02:00, records the owner's manual message in
  chat6aa3e75b and live processing; canonical chat/attachment reconciliation remains
  pending. This plan did not independently repeat that browser observation. These
  successive snapshots are acceptance examples, never fixed current dispatch
  authority. A ready request, observed manual delivery and an accepted verdict
  remain different subjects/states; do not replay or interrupt this live work.
- docs/AGENT_OS_MAP_AND_REFACTORING_2026-08-23.md and its concurrency receipt
  preserve prior design/provenance. They concern a broader discovery program;
  do not activate their historical commands or restart those tasks.

## 3. Roles, capacity and ownership

Proposed execution profile: gpt-6-astra/max orchestrator; gpt-5.6-luna/max bounded
workers. Record the actual resolved model/effort for each assignment; do not claim
that a requested profile changes a running parent automatically. A model change
or a capability failure is visible. Do not silently substitute another model.
Luna is the default for clear implementation, reproduction and source-inspection
tasks, not an automatic final authority for difficult mathematics. Hard analytical
questions remain with the orchestrator/Proshka and the applicable proof reviews.

Use native subagents. Initial operating target: two independent workers and one
reserved reviewer slot, at most three active children of the sole orchestrator.
Unused slots stay unused. This changes the current GOAL two-live-agent ceiling
only after the project rule change is reviewed and activated. Until then keep
the current limit. No recursive delegation. A reviewer may be reused for followup
on the same exact subject, but may not have authored the reviewed change.
The resident mandatory review route remains native gpt-5.6-terra/medium unless
the owner explicitly changes that separate reviewer policy.

Every assignment names the owning task/host, assignment ID, mathematical or
repair objective, exact input commits and hashes, permitted paths, prerequisites,
expected result path, stopping condition, estimated duration and next check.
An assignment is not open-ended authority to fix neighboring modules or rules.
Observing a neighboring defect creates a report without expanding write scope.

One repository may contain isolated git worktrees. Parallel workers that write
code use separate owned worktrees pinned to an immutable base. Read-only workers
can share an immutable snapshot. If isolation is unavailable, serialize writes;
disjoint filenames alone are insufficient for shared index/HEAD/control safety.
The orchestrator alone integrates into the canonical checkout, changes shared
control/queue/checkpoint/registry files, stages, commits, pushes and delivers to
Proshka. Workers supply a named patch and complete new-file manifest; they do not
perform those canonical actions. Do not share writable databases or generated
build outputs between worker worktrees. Keep the existing databases distinct.
Prefer retaining the existing mathematical task as the orchestrator. The proposed
profile does not require a new task, a new mathematical goal or an owner transfer.
Use section3.1 only when the actual execution owner must change.

After the reviewed project candidate-write exception is activated, a worker may
edit only ordinary, explicitly assigned files in its isolated worktree WITHOUT
the common writer lock. Two such edits may proceed concurrently. It may not
stage, commit, rebase, fetch, update refs/config, create/remove worktrees, modify
Git metadata or write shared controls, registries, databases or generated outputs.
Check path ownership including symlink targets and actual output destinations.
Until activation, this paragraph grants no exception to current writer rules.

The orchestrator holds the existing common-dir writer lock for shared Git,
control and registry mutations and canonical integration. Worktree creation and
any Git rebase needed for a candidate belong to the orchestrator under that lock.
At integration, compare base, changed paths, read dependencies, tests and payload
hashes again. Drift invalidates affected evidence: preserve and reconcile the
candidate, then repeat only affected checks. Never overwrite foreign bytes.

### 3.1 Execution-owner transfer and stale-owner rejection

The existing lock epoch protects one filesystem transaction, not ownership of an
app task. Add a distinct monotonically increasing ownership_epoch in the current
checkpoint's versioned ownership observation, together with owner task/host,
handoff ID/state and evidence locators. This records an independently established
assignment; it grants no authority beyond the user/control. A checked transfer
changes the epoch once. Retries of the same transfer do not increment it again.

Every registered shared writer and dispatch preflight checks task/host, epoch,
handoff state, expected source hashes and any exact delegated-path grant under
the canonical writer lock. Stale-owner requests fail before mutation. Delegation
names the same epoch, assignee, command and paths; it does not create a second
owner. An external-effect preflight durably reserves its operation ID and intent.
That reservation remains an outstanding operation until its outcome is observed;
handoff cannot clear it merely by timing out. Native browser/app effects are not
atomic with local files. Do not hold a filesystem lock during a network wait or
pretend the native tool enforces a repository token. Its caller must respect the
preflight; a reserved or unknown action must be reconciled before transfer.

Before entering a transfer, establish the exact native watch capability contract:
the available update route must explicitly support changing the target task while
preserving the automation ID, expose inspectable target/settings readback and
accept the intended existing task/host. Check the actual tool schema/current
watch, supported-operation evidence and any platform rejection; do not infer
capability from a generic update method name. Save this scoped preflight evidence
and recheck it before step3. If unsupported, unavailable or unverified, do not
advance ownership: retain the existing owner task and watch. This does not block
the same-owner execution profile. Tests cover this result, not a fabricated
successful retarget. A later transport failure after a supported preflight still
uses the explicit pending-state recovery below.

Transfer sequence, recorded through the existing checkpoint/history writer:

1. The current owner saves HANDOFF_INTENT, exact old/new task+host, epoch N,
   transfer ID and authorized scope. It stops new dispatch/assignments. Only
   draining already-recorded operations, read-only checks and the named handoff
   transitions remain allowed; the new task has no execution ownership yet.
2. Collect a quiescence receipt from the current owner: base HEAD, hashes of
   shared/owned dirty paths, complete assignment/job/watch inventory, outstanding
   external operations and durable outputs. Quiesce all processes that can still
   write canonical state; preserve isolated candidates. Unresolved external
   intents or unknown canonical writers block transfer. Save HANDOFF_QUIESCED.
3. After the supported watch-target preflight, under the common writer lock,
   compare the checkpoint and all boundary hashes again. Atomically record
   owner=new, epoch=N+1, WATCH_RECONCILE_PENDING and the
   immutable transfer evidence. Epoch N is retired. Ordinary execution is still
   held for both tasks; only the named transfer reconciliation may mutate state.
4. Using the native automation tool, retarget the EXISTING watch to the new task,
   preserving its fields/cadence. Read it back and persist exact watch ID, target,
   settings and observation evidence in the existing protocol/checkpoint. Then,
   under lock and expected hashes, record ACTIVE at N+1 with the handoff receipt.
   The new owner may act only after reading that verified durable receipt and
   rechecking the operation prerequisites. The old task stays observation-only.

A crash before step3 leaves ownership at N with an explicit pending transfer;
the recorded participants reconcile/finish it before ordinary execution. A
transfer still at N can instead be cancelled with a durable receipt only after
confirming the old watch target/settings remain intact and no transfer effect is
outstanding; this retains N rather than rolling back an advanced epoch. A crash
after step3 leaves N retired and the new owner waiting for watch reconciliation.
If the watch update outcome is unknown, inspect that same watch, never create a
replacement or blindly update again. Old/new watch wakes during either pending
state can only reconcile the transfer; they cannot start mathematics or dispatch.
After step4 a lost caller receipt is resolved from the same durable transfer ID.
Do not roll an epoch back, steal ownership on elapsed time or infer death from
another task's empty agent list. A later reverse handoff uses a new epoch.

This is cooperative runtime fencing, not operating-system isolation: agents run
as the same user. Registered routes and instructions can reject stale ownership;
arbitrary raw shell writes outside those routes are not physically impossible.
Migration must inventory every allowed shared mutation path before activation;
no legacy write/dispatch entry may remain an unguarded permitted exception.

### 3.2 Home/work continuity across independent clones

An OS label (CODEX_MAC/CODEX_LINUX) and the app-relative host alias local are not
installation identities. The closed q3_team_installation.v1 local record contains
a cryptographically random 32-byte installation_secret and installation_ref =
SHA-256 of UTF-8 "q3-team-installation-v1", one NUL byte and the secret bytes.
The secret is stored as 64 lowercase hex characters only in a regular private
mode0600 file in the Git common directory; it is never committed, printed in a
receipt, copied as a template or recovered from a remote checkpoint. The public
64-hex installation_ref MAY appear in tracked owner/release/claim records. It is
a stable namespace, not an OS authentication or mathematical authority claim.
Always recompute the reference locally and reject a mismatch. Independent clones
generate independent secrets/references; a reference collision during init is
an error, never automatic adoption of the other installation. Linked worktrees
share the same local installation record. Task/watch/process bindings remain
separate local data. Derive the checkout root from git, not a path saved by the
other computer. Store project locators relative to the repository; absolute local
paths/handles remain local or explicitly historical evidence.

The tracked checkpoint preserves the frontier, immutable request/chat identities,
source hashes, complete stage subjects, owner installation/task and ownership
epoch. It does not make foreign agent handles, boot/process identities, tool
availability, browser tabs, index receipts or local databases valid here. A new
computer reads the same plan and obtains a local reconciliation list. Local
initialization is a registered explicit writer, including safe initial creation
of the existing writer-lock file when absent; plan itself creates nothing.
Uninitialized state must not be mistaken for an already matching owner.

flock protects transactions sharing one Git common directory only. Cross-clone
transfer requires observable coordination through the existing canonical remote
branch, using ordinary named commits/non-force pushes, with no new service or
ownership branch. Git pull alone grants no execution ownership. The runtime
prepares/verifies records; existing Git delivery remains separate from plan.

1. The old owner stops new effects, reconciles outstanding effect outcomes and
   canonical writers, preserves essential outputs and pauses its execution watch.
   An external request whose delivery is known may continue remotely: preserve
   its identity for successor intake. An UNKNOWN send/launch outcome cannot be
   erased to make handoff possible. Save a release manifest with exact scope,
   checkpoint/source pins, owned dirty paths and watch/quiescence evidence.
2. Publish RELEASED at epoch N to the existing branch and verify the remote
   commit/record. A local release or an unobserved push result is not transferable.
   The old owner remains non-dispatching, including after restart.
3. At home, inspect whole-tree changes before synchronization; preserve foreign
   bytes and merge conflicts. Read the exact remote release and initialize local
   identity/capabilities. Prepare CLAIM_PENDING at N+1, bound to that release,
   receiving installation/task and already preserved operation IDs. Publish it
   by ordinary fast-forward push and independently verify the remote record.
   Concurrent claims from the same release cannot both fast-forward; the loser
   reconciles the remote owner and never rebases/retries its claim as a new grant.
4. Persist a local watch intent bound to the remotely verified claim ID before
   using native tools. Reuse at most one native watch on the receiving installation,
   creating one
   only after confirming local absence. Verify its local target, settings and
   a real scheduled wake. Record local reconciliation and the exact successful
   claim receipt before ACTIVE. The old installation's watch stays paused or
   observation-only and can never acquire execution on its own.

CLAIM_PENDING recovery is an explicit branch of the same transfer. The same
installation, after restart, reads its private binding and the exact remote claim
and resumes the unfinished watch-intent/readback/activation step. Lost create or
update confirmation requires inspecting the existing local automation; it never
repeats the effect merely because a receipt is absent. While watch state is
UNKNOWN, keep the remote claim pending with WATCH_RECONCILIATION_REQUIRED and the
exact installation/tool/user unblock condition; all contenders stay non-dispatching.
If the claiming installation proves that its watch is absent or paused and no
effect could have been issued, it may publish CLAIM_ABORTED at the same N+1 with
that evidence, exact claim predecessor and ordinary non-force push/readback.
That is a release for a fresh N+2 claim, never rollback to N. A failed/unknown
abort push is reconciled against the same remote operation. An installation
whose local identity or watch observation is unavailable cannot be impersonated
by another clone: report INSTALLATION_RECOVERY_REQUIRED and the specific recovery
condition, continue permitted observation, and require identity restoration or
an explicit owner-directed recovery with verified quiescence. No timeout takeover.

All ordinary shared writers/dispatch preflights check the installed identity,
task, epoch and transfer state. A separate registered remote-observation operation
checks the current canonical remote branch before effects; a cached origin ref
or receipt age never establishes remote ownership. Offline/failed observations
hold cross-host acquisition, canonical publication and new external effects,
while permitting scoped read-only work and isolated candidates. An observation
is consumed for its exact operation and inputs, not reused as an evergreen grant.
Transfers require the old owner's quiescence; elapsed time alone cannot break an
ownership lease. The user may resume from home without inventing agent results,
copying the work computer's local runtime state or restarting the mathematics.

Native automation IDs and targets need not be portable across computers. The
invariant is one globally active execution owner with one execution watch on its
installation, not one hard-coded automation ID valid everywhere. Same-installation
handoff still uses section3.1 and its verified target-update capability. A missing
cross-host native retarget feature is handled by releasing the old site's work
and reconciling the receiving site's native watch, never a fallback daemon or
raw app-database editing. Cross-host compatibility tests use two independent
clones and a local bare remote; actual home-device execution is reported separately
from those tests. Portable Python/git/filesystem behavior is tested on Linux and
Darwin contracts without assuming local Linux paths exist at home.

## 4. One entry: extend the existing plan

The user-facing entry remains python3 orchestrator/workflow_runtime.py plan.
No wrapper chain or new resume selector. GOAL states objective/delegation,
CODEX_CONTROL owns executor policy, RESUME stores observations. Section5 remains
a compatibility anchor, not a required extra program stage.
At activation, update GOAL section2/5 and SESSION_ENTRY together: the old app goal
sentence remains valid, but its pointer leads to this command. The model is no
longer required to reconstruct a manual GOAL -> RESUME -> plan read sequence.
Triggered policy/source reading still applies when a decision needs its content.

Inside the existing read epoch, add a bounded continuation observation that:

1. Validates current checkpoint schema, size, revision, checksum/archival binding,
   source identities and selected physical goal against existing canonical facts.
2. Reads the exact current assignment/issue records needed for this continuation,
   reports whole-worktree dirty paths with declared ownership, and exposes unknown
   ownership rather than treating an empty local agent list as global absence.
3. Separates mathematical admission, local technical readiness, pending external
   observations and environment availability. A proof HOLD is not silently lifted;
   a missing browser surface does not make offline source reading impossible.
4. Returns a short operating card: owner, frontier, current operation/subject,
   completed evidence, proposed next step, required checks, blockers by scope,
   running/unknown assignments, open blocking issues and precise evidence locators.
   Stored mathematical prose is displayed as a proposal; it never selects a goal,
   proves a result or grants execution merely by containing READY or DONE.

plan stays read-only, local, bounded and network-free. It never launches agents,
Lean, refreshes, worktrees, browser actions or automatic fixes. Keep the current
output contract compatible during shadow validation; version any incompatible
change explicitly. Do not emit all GOAL history or entire issue/agent logs.

Current application/agent/browser state cannot be proved by a local file alone.
For such prerequisites, emit NEEDS_LIVE_OBSERVATION with an exact subject, native
tool/read obligation and expected evidence. The orchestrator performs the named
read, binds the receipt to that operation/source/owner, and reconciles again before
the dependent action. Provider state can change: a saved timestamp alone never
establishes current delivery or ownership. Missing handles remain UNKNOWN.
This consolidates the technical procedure while leaving semantic judgments and
native tool execution with the orchestrator; do not market it as an all-knowing
single offline command.

Every stage must name its subject. Request preparation/review, delivery, verdict
receipt, independent mathematical review, parent check, acceptance and publication
are distinct. A prior FLOW proof's receipt=DONE cannot mean that a new SLACK
request has been delivered. Define and test legal transitions and the evidence
each transition requires. Before an external effect persist its intent; after
the effect persist observed confirmation. An unknown outcome triggers inspection
of the original operation and blocks blind replay.

Keep current GOAL/RESUME size bounds. If current schema changes, migrate under
expected hashes; retain validation of historical v1 envelopes as historical bytes,
without allowing old records to become current authority. A newly strict parser
must not make the byte-exact archive unrecoverable.

## 5. Reports: capture evidence, then decide

All agents, including the orchestrator, report problems noticed in their assigned
work. There is no obligation to audit the whole repository on every file read.
No finding is a defect merely because it was asserted confidently or repeated by
several agents. A report contains:

- ID, reporter/owning task, observation time, immutable base and relevant file hashes;
- suspected class: code defect, rule conflict, missing prerequisite/order,
  artifact/interface mismatch, repeated cost, environment failure or agent context;
- expected behavior with the exact rule/contract source; actual behavior and
  minimal reproduction or trace, including A-before-B dependencies;
- effect on the current objective and exact operations that must pause;
- evidence paths/hashes, uncertainty and a proposed minimal repair if justified.

The agent saves essential evidence in its owned durable work area and sends the
report to the orchestrator. A temporary chat message alone is not the record.
Before accepting intake, the owner copies any essential worktree-only artifacts
to the existing canonical report/protocol area and verifies their exact hashes;
an immutable repository source locator needs no duplicate copy. Intake never
depends on a worktree that may later become unavailable. Artifact copying has
its own named-path intent/readback receipt; a crash resumes that exact copy.

### 5.1 Deterministic report and receipt contract

Use q3_issue_report.v1. Canonical payload bytes are UTF-8 JSON with sorted object
keys, compact separators, no duplicate keys, no floats/non-finite numbers, no
implicit text/path normalization, and exactly one final LF. Strings retain their
exact Unicode code points. Canonical arrays whose order is non-semantic (input
paths, evidence locators, affected operations) use the schema's lexicographic
order and reject duplicates. Specify the encoder and cross-platform fixtures in
Phase A0 rather than relying on equivalent-looking text.

Required immutable fields: schema, reporter_task/host, assignment_id, attempt_id,
observed_at, subject_id/type, base_commit, sorted input path/hash pairs,
suspected_class, expected_behavior plus rule source, actual_behavior,
reproduction, affected_operations, evidence locator/hash pairs and uncertainty.
The reporter fixes attempt_id BEFORE sending, saves these bytes, and reuses the
same attempt and bytes after interruption. The payload does not contain its own
derived ID. report_id is report- followed by the full SHA-256 of these canonical
bytes; initial issue_id is issue- followed by the same digest. Neither ID claims
the suspected defect is real. A changed report uses a new attempt with a
supersedes_report_id link; it never edits an accepted immutable report.

The sole registrar applies owner/epoch and writer-lock checks, then:

- Existing report ID and identical canonical bytes: return the prior verified
  receipt/NOOP even if later events have changed the whole registry hash.
- Same reporter+assignment+attempt with different bytes: CONFLICT, no rewrite.
- New report with a stale expected registry hash: stop, reread and reconcile;
  do not overwrite intervening events or invent a different attempt on retry.
- New valid report: durably append a length-framed event through atomic file
  replacement and verify readback before confirming REGISTRY_RECORDED.

Each event binds issue_id, report_id, typed event payload, previous event hash and
payload hash. event_id derives from the canonical envelope excluding event_id
itself. Its durable receipt binds event/report/issue IDs, pre/post registry hashes
and evidence hashes. Receipt hashes exclude their own hash field; receipts live
in the existing protocol area, outside the bytes whose post-hash they describe.
If interrupted after the registry replacement but before receipt persistence,
reconstruct the same receipt from the verified event chain and complete durability
before replying. Later events do not turn an exact replay into a new report.
Archive segments retain a verified chain and attempt-to-report lookup so moving
old events into the existing protocol area does not defeat deduplication.

Preserve the original INSTRUCTION_ISSUES text as a byte-exact legacy prefix.
The first structured segment has one validated marker carrying that prefix's
length/hash; later records are length-framed, never parsed by incidental Markdown
headings. Explicitly map open legacy items to IDs with their source ranges/hash;
unmapped historical items are not automatically closed. Existing assignment
history receives an equally explicit versioned envelope/migration contract.
No second current-issues registry is introduced. Summary views are derived and
cannot override source events. Corrupt or ambiguous history blocks its dependent
transition, preserves all bytes and requires verified recovery, never truncation.

A source/symptom/reproduction fingerprint only proposes duplicate candidates.
An evidenced classification event explicitly links a duplicate to its surviving
issue; all reports/source versions remain addressable. Similar descriptions at
different source versions are not silently collapsed. Register narrowly scoped
record/transition commands in workflow_runtime.py only where current writers do
not cover them. No worker directly patches shared registries. Report intake has
no authority to change proof/control/dispatch states.

### 5.2 Classification and repair delivery

Lifecycle: OBSERVED -> REPRODUCING -> disposition. Dispositions are CONFIRMED_BUG,
CONFIRMED_RULE_CONFLICT, AGENT_CONTEXT_ERROR, EXPECTED_GUARD, UNREPRODUCED,
DUPLICATE or DEFERRED with evidence and reason. Report severity and reviewer
severity retain their issuer and cannot be silently downgraded by the owner.

A confirmed repository repair has a typed issue/repair subject and separate
states: ASSIGNED -> FIX_CANDIDATE -> FIX_VERIFIED -> FIX_COMMITTED ->
FIX_PUSH_VERIFIED. FIX_VERIFIED binds exact candidate/dependency/test hashes;
FIX_COMMITTED requires the verified named payload and commit identity;
FIX_PUSH_VERIFIED requires its push receipt and a fresh remote-ref/ancestry check.
REGISTRY_RECORDED means only that the report was saved. None of these states
means delivery to Proshka, mathematical acceptance, or the owner-only PX_RH_CLAIM.
Non-file dispositions close against their own checked evidence/recheck and do
not fabricate a commit or push. Ambiguous publication is never a generic DONE.

Use one independent reproducer/checker for an ordinary substantive report. For
disputed root cause or a cross-component rule change, use two independent bounded
analyses (reproduction and contract impact), then orchestrator adjudication. Keep
their evidence separate until collection; agreement is not a substitute for a
reproduction or a proof. The original reporting/implementing agent never accepts
its own result. Required native methodology review retains its exact scope,
baseline/diff, prior findings and ModeA/ModeB rules; no policy change by majority.
Schedule the two analyses within the same child limit, sequentially if needed;
do not recursively spawn a separate team or displace an in-flight canonical write.

Agent mistakes receive a corrected assignment/context and one targeted recheck.
An expected guard stays in place; improve the prerequisite path or explanation if
that is the actual problem. An unreproduced claim stays explicit and unaccepted.
The orchestrator's own error is sent to a checker under the same rule.

## 6. Repair priority and rule effectiveness

Record a newly observed problem promptly. For a confirmed defect on the current
task's dependency path, fix it before continuing affected work. Stop all writes
only when the evidence establishes a shared integrity/ownership hazard; otherwise
pause the exact dependent operation and continue independent authorized work.
Platform restrictions require an allowed transport/environment repair or an exact
external unblock condition, never an invented repository exception.

For nonblocking inefficiency or unrelated scope, keep a reasoned queue and batch
compatible repairs at a safe boundary. Initial discipline: one active workflow
repair at a time; a 15-minute reproduction budget triggers explicit orchestrator
reassessment, not automatic dismissal or permission to publish an unresolved
required finding. Extend only with a concrete evidence-producing next action.
Do not let harmless bookkeeping become a permanent gate on mathematics.
A worker may include a minimal repair candidate with its report when that change
already lies within its assigned write scope. It need not await a second assignment
just to propose that fix. Durable intake and independent acceptance still apply;
the candidate alone cannot close the issue or relax its dependent-operation hold.

Each operative rule needs one canonical owner, a clear trigger, required evidence,
affected operation, recovery path and a regression scenario. Test both a valid
case that must proceed and an invalid case that must stop: a rule that blocks
everything is not correct. Rules protecting
different scopes must not be merged into a generic red light. Repair a mistaken
ordering or duplicate requirement at its source; do not create another compensating
instruction. Preserve invariant proof/authority checks while removing demonstrated
redundancy. Time/call-count observations diagnose cost; they do not waive checks.

Refresh only when indexed inputs changed, after batching compatible changes.
Reuse validation evidence only if its full dependency identity remains valid;
do not confuse content synchronization with backend/query/probe validation.
The already recorded index-cost issue is a candidate repair, not an automatic
license to skip current tests. Measure owner interruptions, entry latency,
duplicate actions, repeat checks, queue age, false positives and repair recurrence
from existing receipts. Do not add a telemetry service or optimize for issue count.

## 7. Implementation order and exact areas

Phase A0: freeze the exact versioned checkpoint/ownership, assignment and report
schemas, event/receipt identities, owner-preflight coverage and legal transitions.
Review the complete migration fixtures and command/path authority manifest before
changing a live parser. Preserve old history validators/bytes. Record the legacy
open-issue mapping and required archive lookup contract. Readers in Phase A use
these defined contracts, not fields invented by later phases. This is a design
and fixture step within the existing files/tests, not a new runtime service.
Include the precise native watch-target capability/readback preflight and the
unsupported/unverified same-owner fallback before enabling any owner transfer.
Define the closed installation and remote release/claim receipts before adding
host readers. A generic git pull/rebase must never be used to retry a failed
ownership claim. The existing Proshka binding writer is included in the guarded
shared-write inventory; no permitted legacy route may bypass the owner preflight.

Phase A: implement the continuation observation in workflow_runtime.py and
startup_runtime.py, extend their existing tests and TOOLS manifest. Shadow-check
against current manual recovery on immutable fixtures before activating. Keep
production selector and proof gates unchanged. Correct contract wording in the
same reviewed change, not in a later undocumented exception.

Phase B: structured assignments and scoped ownership in AGENTS_LEDGER plus
registered writers in the existing runtime. Implement owner-epoch/handoff checks
AND the minimum section5.1 durable report intake in INSTRUCTION_ISSUES before
enabling any live concurrent candidate writes. Verify report replay/conflict,
receipt recovery and exact dependent-operation pause first. Worktree demos before
those checks are fixture-only. Then demonstrate isolated candidate delivery and
one canonical integration; activate the reviewed project role/capacity exception.
During this bounded pilot, the owner applies the existing independent review
procedure to received issues; unadjudicated current-path defects keep their
affected action pending. Global configuration remains unchanged.

Phase C: extend that already functioning intake with structured adjudication and
repair-delivery transitions, using existing runtime tests. Exercise one real
issue end-to-end before enabling routine automatic repair. Do not create a second
registrar or defer Phase B's report durability to this later phase.

Phase D: wire the existing local native bridge heartbeat to the new entry and
assignment checks. Keep continuation10min/agent necessity20min and quiet unchanged
behavior. Verify a real wake, owner recovery, report intake and continuation.
Cross-host migration follows section3.2: one execution watch on the active owner
installation, no duplicate local watch and no falsified native goal state.

Phase E: measure the pilot, remove superseded instruction paths by the reviewed
manifest, and deliver named commits and ordinary pushes from the canonical owner.
Preserve original histories and existing symlinks. Expand concurrency only after
the pilot demonstrates independent work and lower total completion cost.
Include the current-entry claims in orchestrator/README.md and
orchestrator/CONDUCTOR.md in
that reference audit: they still describe the older Claude/Mythos distribution.
Classify historical/manual paths explicitly and retain necessary compatibility;
do not disable relay.py merely because its description is old. Only proven live
conflicting instructions enter the exact correction manifest.

Likely implementation files: orchestrator/workflow_runtime.py,
orchestrator/startup_runtime.py, their existing tests, docs/cartographer/TOOLS.yaml,
docs/CODEX_CONTROL.md, docs/Codex/GOAL.md, docs/Codex/RESUME.md and its history,
docs/Codex/AGENTS_LEDGER.md, docs/INSTRUCTION_ISSUES.md,
q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md, docs/CODEX_AS_SECOND_BODY.md and the
existing session protocol. Each phase must narrow this to its exact named paths.
No file is changed just because it appears in this list.
The cross-host source audit additionally scopes orchestrator/bind_request.py and
its existing tests for the active lock/network-wait and ownership-preflight path.

Implementation module boundary: one new orchestrator/team_records.py is justified
for the shared strict issue/assignment framing, parsing and transitions used by
the existing planner and registered writers. It is an imported helper with no
launcher, selector, scheduler or database. Extend existing workflow runtime tests;
do not introduce a second test framework. Ownership/local-host reconciliation and
command registration remain in workflow_runtime.py, reusing its durable writer.
Local installation files belong only in the resolved Git common directory.

## 8. Acceptance and migration

Before implementation, get a safe boundary from the current mathematical owner:
record ready/unknown external operations, collect completed outputs, pin the
current worktree and preserve every foreign byte. The planning task must not
become a second live orchestrator by editing RESUME ahead of the handoff.
Keeping that same task as owner needs scoped implementation delegation, not a
ceremonial owner transfer. A real change of owner requires all of section3.1,
including the durable handoff receipt and verified existing-watch target.
During migration, exactly one canonical writer; candidate agents use only their
isolated scopes. Do not interrupt or duplicate the prepared/live SLACK operation.

Required acceptance cases:

1. Cold agent, no conversation history: one plan identifies the same physical
   frontier, owner, operation subject, next proposal and exact required live checks.
2. A prerequisite A missing before B blocks B with the right reason; unrelated C
   remains available. Reordering without evidence cannot suppress a valid guard.
3. Two workers modify overlapping dependencies: no lost bytes, no mixed index/HEAD,
   no acceptance based on a stale baseline. An abandoned worker remains UNKNOWN
   until durable outputs/owner evidence establish the outcome. Two permitted
   isolated candidate edits actually run concurrently without the common lock;
   a worker's forbidden registered shared mutation is rejected.
4. Concurrent/duplicate issue ingestion and crashes before/after durable steps:
   exact replay after later events returns the same report/issue/receipt;
   conflicting bytes for one attempt fail; stale-hash new intake preserves all
   foreign bytes. Recovery after event save but before receipt save, archived
   replay lookup and lost worktree evidence are tested explicitly.
5. Seeded agent-context error is rejected as a code fix; a genuine ordering bug is
   reproduced independently, minimally fixed, regression-tested and published.
6. Ready but undelivered request does not enter verdict waiting; ready verdict
   arriving during idle resumes intake; lost send receipt never automatically
   resends; changed checked source invalidates the relevant acceptance stage.
7. Reporting/closing an issue cannot select a mathematical goal, change a phase,
   bypass a platform rejection, admit a proof or authorize PX_RH_CLAIM.
8. Exact original archive remains readable/recoverable after schema migration;
   GOAL/RESUME stay bounded; plan output stays bounded as histories grow.
9. Actual native wake after migration, including owner recovery after interruption.
   Unavailable runtime or a postponed wake is reported honestly, not marked passed.
10. Independent plan/artifact review converges; scoped tests and required derived
    refresh pass; final named commit/ordinary push and remote hashes are verified.
11. Handoff interruptions before/after every durable phase and the non-atomic
    watch update: exactly one active epoch; old-owner writers/dispatch are rejected;
    both pending-state wakes remain non-dispatching. An unknown reserved external
    effect blocks transfer until reconciled. No timeout-based ownership theft,
    double watcher, automatic resend or activation without a checked receipt.
    Unsupported/unverified target-update capability prevents advancing the epoch
    and leaves the same-owner route available; it cannot strand a new owner by
    assuming the target update is possible.
12. Report storage, local repair commit, verified push and mathematical acceptance
    cannot be substituted for one another; typed subjects and required receipts
    reject those transitions while accepting the corresponding valid transitions.
13. Two independent clones with different absolute roots and installation IDs:
    pull preserves project continuation but never imports live local handles;
    simultaneous claims yield one verified owner, offline/stale remote checks do
    not permit execution, release/claim push receipt loss is reconciled, and
    resuming the old computer cannot replay work. Linux and Darwin host contracts
    preserve the same logical frontier. Local init handles a missing lock file
    without truncating/replacing an existing lock or creating files during plan.
    Test private/public identity mismatch, collision rejection and absence of
    installation_secret in every shared artifact/CLI receipt. Crash after remote
    CLAIM_PENDING and before/after native watch action must resume that same claim
    or establish a verified CLAIM_ABORTED before a new epoch can be claimed.

Do not promise constant-time history validation without a measured, integrity-safe
implementation. Bound normal startup reads/output and test growth explicitly;
recovery may perform a separate full historical verification when needed.

## 9. Review record

Pass1: native gpt-5.6-terra/medium, exact initial candidate SHA-256
15ff0df2028c264d12173c3c9c21cacaed868a471d87150a9b751d5e84244f7b.
Three HIGH findings (owner handoff, report identity/replay, worktree-lock scope)
and one MEDIUM finding (ambiguous repair publication). Revised sections3.1,
5.1/5.2, worktree rules, phased contracts and acceptance cases address each item;
the original severities are retained and were independently confirmed closed in
Pass2.

Pass2: native gpt-5.6-terra/medium, exact candidate SHA-256
2f55e29b65e92591608a4d10d5c2f912e267a062b2b12476c105b699429b9c77.
All four Pass1 findings independently confirmed resolved. Two new MEDIUM findings:
report intake must precede live concurrency, and native watch retarget capability
must be checked before ownership transfer. Revised Phase B/C and section3.1/A0
address them; Pass3 independently confirmed both closed. No severity downgraded
and no unresolved item user-accepted.

Pass3 and Pass4: the same native gpt-5.6-terra/medium reviewer checked identical
35823-byte candidate SHA-256
5b80cc35018a165015af3a7d282bcdb31c325c82949da1b001be94240215c145.
Both were on-target CLEAN with no CRITICAL/HIGH/MEDIUM/LOW/WORDING findings.
All six prior substantive findings were independently confirmed resolved.
Mode A original-plan convergence reached: two consecutive clean passes. The
initial review/status annotation preserved sections1-8 exactly. The later user
instruction authorizing implementation added cross-host requirements; those new
changes receive separate review and are not covered by the old clean receipts.
Implementation, runtime activation, worker policy, ownership transfer and
external actions had not been performed at the original plan handoff.

Discovery audit: native gpt-5.6-luna/max, read-only, completed. Confirmed existing
plan/RESUME gap, writer primitives, scoped dirty observation, narrow goal-event
contracts and legacy entry documentation. The suggestion to use record_attempt
for arbitrary agent reports was rejected after source inspection of its closed
goal/cycle schema; reuse its sound primitives without inventing mathematical
attempts. No runtime or mathematical state changed. Discovery was an input to the
plan; the separate Pass3/Pass4 receipts above establish review convergence.
This file is a proposal only. Its publication as a document never activates its
future execution rules or supersedes the current mathematical owner's state.

## 10. Implementation continuation (observations only)

User authorized implementation and home/work integration. Cross-host plan X1 HIGH
private/public identity and MEDIUM CLAIM_PENDING recovery findings were fixed;
X2 and X3 independently CLEAN on exact47,476bytes SHA256
f307a9b132ec9e4487cbee27de4859887f54e7c236ac4ec82209d091f22ce6a4.
This section updates progress only; reviewed architecture above is unchanged.
Authoring task remains01a08f80; mathematical owner remains01a084f4.

Implementation is underway ONLY in isolated local clones:
- Root: /home/chirurgie/.cache/q3-team-2026-09-11-01a08f80, base9005b347.
  workflow_runtime/startup_runtime candidate adds installation namespace, typed v2
  checkpoint, owner transitions, explicit remote/native observation and plan card.
  Still incomplete and not yet independently reviewed or activated.
- Luna/max records helper: /home/chirurgie/.cache/q3-team-records-2026-09-11-01a08f80,
  basee8a95fac. helper/tests prepared; parent found interleaved-event predecessor
  bug and returned it for repair before integration.
- Luna/max bind_request: /home/chirurgie/.cache/q3-team-bind-2026-09-11-01a08f80,
  basee8a95fac. Repairing locked network push, mutable HEAD publication and recovery.
No descendants; current two-live-child ceiling retained.

Mathematical owner is publishing independent SLACK/OD1/OC1 paper results separately.
Shared runtime/control/checkpoint/ledger/issues integration still requires exact
diff/manifest and fresh preimage hashes plus the owner's maintenance boundary.
All foreign files are preserved. Only this plan is delegated in the shared tree.
The observed manual chat mismatch is an independently identified spine/runtime
reconciliation defect; it is NOT fixed by the current root candidate or authority
to replay dispatch. Owner was told exact current coverage and disjoint repair scope.

Next: finish root implementation and tests, collect/fix worker candidates, review
exact implementation and docs, obtain coordinated shared-write boundary, migrate
CURRENT mathematical state, batch required refresh, verify native wake, named
commit and ordinary push. No native watch change or mathematical takeover yet.

Latest implementation observation 2026-09-11T15:20+02:00:
Root isolated runtime/startup/team_records/TOOLS and existing tests changed.
203 workflow/startup tests passed before the latest typed source/watch additions;
37 targeted resume/team-record/team-runtime tests pass after those additions.
Records helper integrated sha d44929b0d87069ec84185888f4606374498c41eda12145895ae622acd0dad585.
Native docs and binding workers stopped with expired Codex refresh-token errors;
all their partial files survive in their recorded clones. Doccandidate has7files,
GOAL12042bytes, not integrated. Binding candidate passes7own tests but parent
found unguarded intent writes, speculative adapters and other unresolved defects;
not integrated. A1 independent CORE-only review dispatched to existing native
team_plan_review using immutable /home/chirurgie/.cache/q3-team-review-a1-2026-09-11-01a08f80
with manifest.json after30seconds; its outcome and authentication remain pending.
A1 is not final artifact convergence; native wake, canonical integration, commit
and push remain UNPERFORMED. Mathematical owner published8a463c09 and independently
reviews its disjoint actual-chat reconciliation; no shared boundary yet.

Latest implementation observation 2026-09-11T14:56:32.884319+00:00 (supersedes older progress above):
- Canonical math remains owned by01a084f4; BPY/DENSITY intake/publication is
  independent. No shared integration boundary yet. Do not repeat that mathematics.
- Alias-only candidate at /home/chirurgie/.cache/q3-alias-integration-2026-09-11-01a08f80
  has isolated verification commit4c8cf9c2; never push its local-clone origin.
  Exact A4 artifact /home/chirurgie/.cache/q3-alias-review-a4-2026-09-11-01a08f80
  manifest78e43c3247442d2635c1cd72066298df2750b8b263c756c3e2bebe63b5180fa4.
  Native A4/A5 CLEAN/CLEAN on identical bytes. Prior HIGH shared intake and
  MEDIUM uncommitted wrapper source/stale census are fixed. Repo skill127cfec8,
  local wrapper072a2ade; original7832bytes/5a55efd4 preserved exactly in archive.
  Four scoped registration tests and14wrapper scenarios PASS. Full41module:
  clean08bb baseline10failures/errors, candidate7, introduced0; remaining baseline
  cases are not waived or claimed green. Source docs/TOOLS is regenerated.
  Wrapper is NOT installed and canonical skill is NOT yet present. Await math
  owner's explicit nine-path boundary, fresh hashes, infrastructure commit,
  one semantic refresh (TOOLS/SESSION_ENTRY are indexed DIRECT_FILES), named
  commit/push and external wrapper preimage validation. No broad staging.
- Core isolated tests reached231PASS before latest changes. Binding B3/B4
  CLEAN/CLEAN remains separate. CORE A2 found HIGH: unrelated old git locator
  could stand for a verified repair commit. Luna/max team_records_worker now owns
  minimum source/commit provenance repair and corresponding issue tests in ROOT
  clone; do not replace them from older worker copies.
- Root independently reproduced CLAIM_PENDING watch CREATE then PAUSE collision
  blocking safe abort. Action-specific durable watch intents are being checked
  against real local Git release/claim/abort/reclaim fixtures; they are not native
  app wake evidence. Root owns watch transition functions and transfer tests.
- Outstanding full-refactor acceptance: complete core/whole artifact convergence,
  exhaustive allowed-writer inventory, actual migrated current v2 RESUME/short
  GOAL, live issue lifecycle, foreign-source/epoch intake, fresh cold entry,
  concurrent isolated-worker pilot and actual scheduled wake after activation.
  No full runtime deployment or completion is claimed.

Alias-only publication INTENT 2026-09-11T15:17:29.471575+00:00:
START_ALIAS confirmed by mathematical owner01a084f4 at HEAD79c48a02; owner retains mathematics and pauses shared writes until explicit HANDBACK.
Exact A4/A5 manifest 78e43c3247442d2635c1cd72066298df2750b8b263c756c3e2bebe63b5180fa4; nine reviewed repository paths only, original skill archive first.
Required next stages: named infrastructure commit, one registered semantic refresh, scoped registration/startup checks, ordinary push, committed-skill local wrapper validation, observed receipt and HANDBACK.
Core runtime, mathematics, RESUME/history/ledger/bridge and foreign files excluded. Missing confirmation requires checking this original action before any retry.
Exact alias manifest (external-wrapper is a separate local installation after the repository commit):
```json
{
  "base": "08bb6739bad1394e7267365fa58707457e8e974e",
  "verification_commit": "4c8cf9c268eb091a22ec2fc051e35a81c0f5bdc6",
  "files": {
    ".agents/skills/alias-hunt/SKILL.md": {
      "sha256": "127cfec8e331b6c200774c19d9c738dab6eef32eb8efdd0d8400c5178b35e21b",
      "bytes": 8235,
      "before_sha256": "ABSENT"
    },
    "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md": {
      "sha256": "9268663ea83c35b0f22edf87fb4a6cc3c5b8c6d99da2993d6c5fab829df10737",
      "bytes": 5926,
      "before_sha256": "27c947adce3ea2668f969750927d5296e2c91150bff9c2d929d0e8eae57cc4f0"
    },
    "docs/cartographer/TOOLS.yaml": {
      "sha256": "b14af9d775c2ea7287936a0ca228b8b409fb3e78696758790ca9278930e25256",
      "bytes": 148529,
      "before_sha256": "ad552a0e89e1e502262fb1067a6f11777d7f9b5037f8586f463a05185b9de062"
    },
    "docs/CODEX_AS_SECOND_BODY.md": {
      "sha256": "64feb08d823918648958d4959d0465c05bce091c466966e63a19de61df324079",
      "bytes": 34619,
      "before_sha256": "d32b5f845a8c7561ba2262237909152fc324a01961ced381df56fc5af995aa47"
    },
    "docs/Codex/CARD_CROSS_HOST_Q3_WORKFLOW_AND_TOOL_INVENTORY.md": {
      "sha256": "3289f6e412d5c94a744619c60e15fd30fd759fa5321672db82f1efd1237a8696",
      "bytes": 19004,
      "before_sha256": "4f133a34ea0d261798b00465636bff8f5dc7c7f244110bc5169fd3056a76ee32"
    },
    "docs/INSTRUCTION_ISSUES.md": {
      "sha256": "4deefbfaad6b75e127ff94115adb8d21fbfd6dc92fa588e2cdcb4dcf102a518c",
      "bytes": 18415,
      "before_sha256": "a2eea0f4c2120f24c193b8ac780242454b2d80f428c5d4743577ff65600e87d2"
    },
    "docs/TOOLS.md": {
      "sha256": "8db635f9078324ff0c6047267045166ea0c59ee9caca6f6625d3e9335cea5082",
      "bytes": 114861,
      "before_sha256": "5d9f2be8026b0286a519f29e17c4f6d91f997130a7025122d144f49a9d68b348"
    },
    "orchestrator/tests/test_tool_manifest_memory_wiring.py": {
      "sha256": "205680aefa90d6c368805edd78121dd2264bdbd99d371477acb4e54a86960907",
      "bytes": 32155,
      "before_sha256": "4bde515dcf77bb539963d3d3ffc50cc1ac24807b28d254a6f08cadcfa7f8a988"
    },
    "docs/session_protocols/alias-hunt-original-5a55efd4f856ee6d457fac335e270293a8623da1a13903082da0a7668d124a69.md": {
      "sha256": "5a55efd4f856ee6d457fac335e270293a8623da1a13903082da0a7668d124a69",
      "bytes": 7832,
      "before_sha256": "ABSENT"
    },
    "external-wrapper/SKILL.md": {
      "sha256": "072a2aded3c597bc7083044a412d73d330e394aa74969f901982fe10d59fc47c",
      "bytes": 3668,
      "before_sha256": "5a55efd4f856ee6d457fac335e270293a8623da1a13903082da0a7668d124a69"
    }
  }
}
```
Foreign preimages preserved/excluded:
```json
{
  "docs/CHAT_DIGESTS.md": "41dd67bf44e0984e029a034ecf02bacb4c66ecdbe8411dcc454fcae42b0e4a0d",
  "docs/routeB_bus/litreview/CSORDAS_PLANAT_LOGCONCAVITY_USAGE_CARDS.md": "8fa808cffa9e6e1a71e85c12808e103acf9cace85eec4c499475af377e6ffa09",
  "docs/routeB_bus/litreview/REFERENCES.md": "b8434212c2d2661a53a4efff7b77bff98b55ecd82785e3bc5aca1384646f0766",
  "docs/routeB_bus/litreview/SL20_ALIAS_HUNT_USAGE_CARDS.md": "a54a650104d4c7033b945c0f0f0ee467a60045348046161ca8b6c88cd42fa406",
  "docs/routeB_bus/litreview/pdfs/2007.12889.pdf": "e610f7a0de324a610fd24ee9fafa4356e5005a9af811245f016d6c0d791ed3a2",
  "docs/routeB_bus/litreview/pdfs/2301.00421.pdf": "e4100e529d74cdc4dfa855aa24bcf34a88562d9facebefd70de6e529f9a1ce2e",
  "docs/routeB_bus/litreview/pdfs/2602.20313.pdf": "9c781e387c7f93372fa0436977b5d1e6336c12470d00dc538025acc7497cda9c",
  "docs/routeB_bus/litreview/references.bib": "42764351aa4b2b5a085cbc41baaf959946e8d49c2acd231861f543924bea4344"
}
```

Alias-only activation CONFIRMED 2026-09-11T15:22:11.900636+00:00:
Nine exact A4/A5 paths committed as 521935c05f7a16341c22dc7a0ce51d3de7a079d7 and ordinary push verified by live ls-remote. Original skill bytes remain exactly archived at docs/session_protocols/alias-hunt-original-5a55efd4f856ee6d457fac335e270293a8623da1a13903082da0a7668d124a69.md.
Canonical four registration tests PASS (0.694s); repo/wrapper metadata PASS; installed local wrapper emits exact committed skill127cfec8, wrapper072a2ade, original5a55efd4. No mathematical search or repeated Proshka send was launched by this integration.
One registered refresh111.837s, strict session_start13.686s/exit0, ask alias-hunt3.167s/exit0/ASK_STATUS HITS. Total129.384s including four tests. Corpus b9ef9a891368f1d082cf20a9ba5eed9d00dec67b2704ed3c1e9d6e17b0112d34 freshly recomputed and matches machine-local receipt. Full commands/output: docs/session_protocols/alias-hunt-activation-2026-09-11.log, 98618 bytes, SHA256 b8b33a683820d405071504b5ecec6048b35b58924ba146be9b6e76223c488bb5.
All8foreign preimage hashes recorded above remain unchanged and unstaged. Receipt plan/log are outside the resolved indexed corpus; these evidence writes require no second refresh. The core runtime is NOT activated: integration route/inventory review and final artifact/native-wake acceptance remain outstanding.
Original alias baseline comparison remains 41 tests: baseline10failures/errors, candidate7, introduced0; seven preexisting failures are NOT a full-suite PASS.
Fourteen wrapper fixtures on the exact deployed bytes:
```json
{
  "wrapper_sha256": "072a2aded3c597bc7083044a412d73d330e394aa74969f901982fe10d59fc47c",
  "skill_sha256": "127cfec8e331b6c200774c19d9c738dab6eef32eb8efdd0d8400c5178b35e21b",
  "results": [
    {
      "case": "home",
      "expected_success": true,
      "exit": 0,
      "status": "PASS"
    },
    {
      "case": "work space",
      "expected_success": true,
      "exit": 0,
      "status": "PASS"
    },
    {
      "case": "subdirectory",
      "expected_success": true,
      "exit": 0,
      "status": "PASS"
    },
    {
      "case": "foreign",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "missing",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "symlink",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "duplicate",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "inactive",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "conflicting_id",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "untracked_skill",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "uncommitted_skill",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "modified_skill",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "staged_skill",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    },
    {
      "case": "nonrepo",
      "expected_success": false,
      "exit": 1,
      "status": "PASS"
    }
  ],
  "fixtures": "/home/chirurgie/.cache/q3-alias-fixtures-yrn_p4m1"
}

```
Receipt publication INTENT: commit only this plan and the full activation log, then ordinary push to the same branch; missing confirmation means inspect local/remote commits. Native HANDBACK will carry exact final commit and remote observation.


## 11. Reviewed integration contract and implementation continuation

The following exact supplemental I5 proposal is preserved as review history,
not executable authority. I4 WORDING / I5 CLEAN completed Mode A.

```text
# Narrow completion of the reviewed Team Runtime writer contract

Status: isolated implementation proposal; no live policy is changed by this file.
Parent scope: owner-authorized TEAM_RUNTIME_REFACTOR_PLAN_2026-09-11, especially
sections 3.1, 5 and 7. Native coverage audit confirmed two HIGH findings:
reviewed worker files have no legal canonical integration route, and callable
AVAILABLE/DEGRADED writers are absent from the exhaustive writer inventory.

## Outcome and limits

Complete the existing sole-owner integration step and writer inventory. Add no
service, database, task selector, shell dispatcher, scheduler or proof admission.
Retain current release/claim/epoch, independent review and named publication.
Arbitrary same-user shell writes remain outside cooperative enforcement.

## One registered source integration command

Add `team-integrate-candidate --candidate <manifest.json>` to workflow_runtime.py.
It copies exact declared bytes under the mode-specific gates below; it never commits, pushes, dispatches,
changes ownership or accepts a theorem. REVIEWED_SOURCE candidate Git objects
must already have been obtained through an existing authorized read/fetch operation; this command
does not fetch or wait for a network operation while holding the writer lock.

The closed q3_team_integration.v1 manifest has exactly: schema, mode,
operation_id, owner_task, installation_ref, epoch, expected_head,
implementer_assignment, assignment_sha256, checker_assignment, candidate_commit,
and files. assignment_sha256 hashes the existing canonical immutable assignment
view; mutable status observations do not silently change the producer identity.
Mode is EVIDENCE_INTAKE or REVIEWED_SOURCE. Hashes are full SHA256; before_sha256
may instead be ABSENT. Source-copy Git objects must be present locally before
that mode runs. No deletions, renames of existing files, symlink components or
executable evidence files are accepted.

The manifest uses the existing canonical JSON encoder and limits. Its exact
bytes are pinned by RESUME operation.subject={kind: REPAIR, id: operation_id,
sha256: manifest_sha256}; operation.command names this registered command.
The detached candidate may live in the owner's durable local output area.
It need not first be copied into a shared report. Operation.inputs binds only
existing source dependencies. The manifest has NO RESUME digest: the private
reservation, saved after RESUME, binds its exact checkpoint hash. This removes
the manifest/RESUME hash cycle. Before destination changes the private operation
record durably stores the complete exact manifest, so recovery does not depend
on an unsaved command argument or worker directory.

EVIDENCE_INTAKE is the missing intake prerequisite, not an acceptance shortcut.
It accepts only new immutable content-addressed files at
docs/session_protocols/team-evidence-<full-sha256>.bin, containing the exact
observed bytes. candidate_commit and checker_assignment must be null. Each sorted
unique file record has exactly path, before_sha256, sha256 and content_base64;
strict canonical base64 decodes to the exact hash-named bytes within the existing
payload limits. There is no arbitrary source-path read. The producing assignment
and immutable view hash must be present; an orchestrator assignment can preserve
the raw output of its already observed native tool call. The detached manifest is
the bounded input container; preparing it in the owner's assigned local output
area needs no prior canonical write or Git commit. An exact already-present file is a
verified NOOP; another hash/path or a shared registry, runtime, policy, shelf,
index or mathematical source destination is rejected. Evidence is labelled
unadjudicated observation. The route cannot mark FIX_VERIFIED or any mathematical
stage DONE. A later native-result record may reference the saved bytes; it cannot
pretend the bytes themselves authenticated a native execution. In particular,
intake does not require a pre-existing native RESULT record: the current native
record writer itself needs durable output/provider bytes. Authenticating that
later observation and binding its actual provider/source/assignment identity is a
separate prerequisite before the data can support classification or acceptance.
Untrusted bytes can be retained as evidence without becoming trusted instructions.

For BOTH modes, resolve the exact immutable producing assignment and verify its
immutable-view hash, base_commit and owner/epoch against the registry and
reservation. Only REVIEWED_SOURCE requires a Git source: each sorted unique file
record has exactly path, source_path, before_sha256 and sha256;
candidate_commit must resolve to a Git commit object, and
git merge-base --is-ancestor assignment.base_commit candidate_commit must pass.
Read each source as git show candidate_commit:source_path and verify the complete
blob bytes, path mode and expected hash. A local object/hash is not ancestry.

REVIEWED_SOURCE requires source_path == path, expected_head equal to the exact
implementer assignment.base_commit, and a non-null independent checker. The
checker's immutable base must equal that same commit. A changed canonical base
requires a new assignment and corresponding review, not a silent transplant.
It uses a closed completed-output artifact q3_team_integration_review.v1 with
exactly schema, manifest_sha256, base_commit, candidate_commit, files (sorted
path/sha256 pairs), implementer_assignment, checker_assignment, verdict. The
base_commit must equal the immutable assignment bases and expected_head.
verdict must be
SOURCE_INTEGRATION_APPROVED, explicitly scoped to these bytes, not mathematical
admission. Read this artifact from the genuine completed checker RESULT output,
verify its output hash and native owner/model/source/assignment provenance, and
compare every field with the manifest and assignments. A negative/missing verdict,
an unrelated output or a textual occurrence of a hash cannot satisfy this gate.
Reuse team_records' strict canonical parsing and native-observation validation;
this is a typed review artifact, not another registry or issue lifecycle.

The owner first records an exact integration INTENT, observes the current remote
owner and reserves that operation using the existing registered commands. Each
REVIEWED_SOURCE source file must be covered by the implementer's permitted paths. Intake and
reviewed integration are separate operation IDs and reservations. The checker
must be distinct from the implementer and owner; required review convergence
remains a prerequisite. A reported completion or arbitrary output file is not enough.
For REVIEWED_SOURCE, independently checked Git source bytes, rather than a
mutable worker directory, are the copy source. This uses an isolated candidate Git commit before canonical
integration; that local object is neither an accepted result nor publication.

Under the existing writer lock, validate actor/epoch, the exact saved intent and
local reservation, unchanged canonical HEAD, complete named candidate sources,
review and assignment pins, and ALL destination preimages before the first write.
Existing destination bytes must be clean against the recorded HEAD; an existing
untracked destination is not ABSENT. Foreign dirty paths outside this manifest
are preserved and excluded. Only source files authorized by these assignments
may be copied; checkpoints, ownership registries and local runtime records keep
their own writers and cannot be destinations. The integration manifest/output
evidence cannot overwrite itself. Refuse duplicate/escaping paths and symlinks.

Before any destination changes, durably retain the exact intent, all preimages
and candidate hashes through the existing private operation record. Preimages
are recoverable from recorded HEAD, or ABSENT; no foreign uncommitted bytes are
overwritten. Reuse existing atomic per-file CAS, fsync and readback helpers.
This is a recoverable sequence, not a claim of an atomic multi-file filesystem
transaction. A partial write remains RESERVED/INCOMPLETE; there is no completed
receipt until every named file has the candidate bytes and durable readback.
Before any write, set an integration-pending marker in that existing private
operation record. All canonical and external-effect writers check this marker
BEFORE mutable control/source validation and refuse other operations. Checkpoint,
record, watch, publication and other writers cannot run on the mixed tree.
Read-only inspection and exact recovery of that SAME operation remain allowed.
Only its full durable confirmation clears the hold. Generic effect confirmation
cannot clear an integration marker, nor can another intake or owner transfer.

Use the already available immutable verification checkout as the executing code
root and the existing --root option for the canonical destination. Pin that
engine's committed runtime/dependency identity in the private reservation and
retain it through completion/recovery. The copy therefore does not overwrite its
own executing recovery code. Recovery validates the persisted authority and
original/candidate destination states; it does not require a half-updated canonical
runtime or control to import successfully. No new daemon or generic shell launcher.

Exact replay is local reconciliation of this SAME intent. Require unchanged
actor/epoch, RESUME intent, HEAD and persisted candidate/review manifest. Each
destination must have its original bytes or the recorded candidate bytes; any
third state stops. Verify candidate bytes already present; replace only remaining
original bytes. A changed mathematical source manifest may block ordinary work
after a partial integration, but the original integration recovery must compare
the persisted preimages/candidate bytes rather than demand the old destination
bytes globally. No new remote grant is inferred, renewed or used for another
action. The global pending hold is checked independently of the possibly updated
control flag and is enforced at every registered writer entry, including commands
that currently call _team_actor directly instead of team_guard. Final durable
receipt records exact file hashes and completes only this
local integration operation; the owner separately updates current source pins
and repeats invalidated checks before acceptance/publication.

## Complete advertised writer coverage

Inventory all writes:true tools with callable status ENABLED, AVAILABLE or
DEGRADED. Require exactly one fenced/inherited_only/isolated_only placement for
each. Check native effects separately against their closed allow-list. Every
non-fenced tool entry explicitly states that canonical direct invocation is
disabled under Team Runtime; inherited tools require the existing transaction,
and local isolated file producers return candidates for the integration command.
Network/external entries retain an explicit named effect protocol; they are not
silently relabelled file producers. These rules
specialize existing manifest invokes rather than implying that AVAILABLE bypasses
ownership. Restore the independently added canonical Slack reconciliation entry
when merging the latest owner's manifest; do not lose it or broaden its scope.

Concrete missing routes, based on the current registered implementations:

| Tool | Inventory group and preserved execution |
|---|---|
| slack-manual-chat-reconciliation | fenced: retain the existing fixed-receipt spine writer, add the owner/epoch/pending-integration check inside its existing writer transaction; no generic CHANNEL_RUNTIME copy or new chat authority |
| tool-census | isolated_only: run tools_census.py --markdown in a pinned isolated checkout; return docs/TOOLS.md as a reviewed source candidate with its actual manifest/source identity |
| task-specific-generators | isolated_only: select the exact existing script and output paths from the current task; inspect real destinations first, run ordinary local file producers in isolation, integrate only named reviewed outputs; this family never authorizes an unclassified network/database writer |
| packet-ingest | isolated_only: run the existing packet.py ingest in an isolated checkout; preserve exact reply and bus/mirror/queue/metadata candidate bytes; integrate reviewed transport artifacts only, and recompute SPINE_VIEW through its existing registered owner route rather than copy a generated control view |
| aristotle | isolated_only for files, named native effect aristotle-submit for submission: exact authorized input/model/project boundary -> saved INTENT -> remote observation/reservation -> one existing registered skill submission from isolated input -> observed provider project ID plus input hash; on unknown outcome query existing projects/input before any submission; collect the existing project's result into isolated output, then evidence intake and independent Lean validation/source integration. No fee or new submission authority is granted |
| paper-ingest | isolated_only for files, named native effect paper-ingest for the existing full source-acquisition command: pin source identifier, explicit bibliography key, script hash, isolated output paths and Zotero destination; saved INTENT -> remote observation/reservation -> one paper.sh invocation in the isolated checkout -> observed PDF/metadata/registry hashes and Zotero item/attachment IDs. Lost receipt requires checking that exact isolated run and remote DOI/archiveID/items/attachments; lookup error is UNKNOWN, not absence. Do not rerun the whole command after a partial/unknown result; reconcile the unfinished stage under a new exact scoped intent only after the original outcome is resolved. The existing Zotero behavior is disclosed, not silently discarded or attributed to local isolation |
| cartographer-loaders | isolated_only classification retains HUMAN-only external execution. Codex does not run machine-local loader scripts. A human-supplied reviewed import packet can enter evidence intake; any canonical knowledge.db import still requires its existing exact database-write route and checks, never generic source-file integration |

The two named native effects extend the existing closed effect allow-list; they
are not a shell executor or new service. Their effect guards use the existing
operation reservation and confirmation. Actual provider outputs stay separate
from intent/reservation, including for the local-file portion of network tools.
Add the minimal owner/pending guard to the existing spine Slack writer and its
existing channel-writer tests; this preserves a currently callable canonical route.
Do not treat AVAILABLE or DEGRADED as permission to bypass these conditions.

Correction of an agent report: comparing inventory only with ENABLED faithfully
describes the current implementation bug; it does not justify excluding the six
other callable writers that this repair explicitly covers. The invariant is all
three callable statuses. Alias-hunt is correctly excluded because writes=false.

The issue-specific q3_repair_review.v1 artifact also needs an explicit positive
verdict for its exact issue/repair/source manifest. A completed negative review
cannot be recorded as FIX_VERIFIED. Extend its closed validator and existing
negative-review regression case before final artifact convergence; do not infer
approval from the mere existence of a completed output.

## Files and acceptance

Use existing workflow_runtime.py, team_records.py, existing test_workflow_runtime.py, TOOLS.yaml,
spine.py and its existing test_channel_runtime_writer.py,
and narrow control/GOAL/routing references. Reuse team_records.py validation where
it already owns the exact checked candidate identity. No second journal/schema
for issues or reports. Keep GOAL <=12KiB and RESUME <=8KiB.

Required checks: independent candidate copied exactly; evidence intake without a
pre-existing canonical output (followed by real independent review); no manifest/
checkpoint hash cycle; a negative completed review cannot approve integration;
first raw native output intake without prior Git/canonical/native RESULT record;
candidate object type and producing-base ancestry enforced for REVIEWED_SOURCE;
unrelated/older-branch candidate and changed assignment/base review rejected;
preserved foreign dirty
file; changed preimage/review/source/owner/epoch rejected before writes; existing
untracked destination and symlink rejected; crash before and between file writes,
exact partial/completed replay and third-state drift; every other registered
writer is held during partial integration; fresh-process recovery from the pinned
immutable engine after partial runtime-source update; no commit/push or network
call; all callable writers represented; isolated/inherited direct canonical
routes refused by cooperative routing. Complete the already required concurrent
isolated-worker pilot with this real integration command. Independent plan and
exact artifact review precede activation; actual native wake remains separate.
```

Implementation refinement after I6 HIGH: the same command now supports
--recover-operation <id>, mutually exclusive with --candidate. It restores
the exact persisted manifest only for the named PENDING copy. I7 HIGH
also closed the completed-replay rewrite: COMPLETE accepts only candidate
bytes and never reapplies an original preimage. No new operation authority.

Current isolated candidate: a0af6fab plus these reviewed-response fixes and
route documentation. Writers snapshot1ae63411 was integrated as d534b8f5.
Workflow/channel suite196 PASS before the final replay/card additions;
nine integration regressions PASS after completed-replay correction.
Actual fresh-process recovery test is assigned to team_records_worker.
Next: final exact artifact convergence, current mathematical v2 migration
at a new owner boundary, cold entry/concurrent pilot/real issue lifecycle,
actual native scheduled wake, scoped publication. No canonical Team Runtime
activation or new maintenance window has occurred. Alias delivery is DONE.

I8 HIGH bridge writer guard fixed in4753f668 and independently confirmed closed
in I9. I9 MEDIUM required the actual fresh-process recovery test; worker
a1ebdc6c is integrated asdf053bc2, with the parent correction that the pending
plan is top-level HOLD/exit2 and continuation RECOVERY_ONLY. The subprocess
kill/recovery case PASS in2.028s; four additional integration boundary cases
PASS. It preserves a committed immutable engine, loses/tampers the detached
manifest, checks the fresh pending plan, recovers by saved operation, and refuses
completed recovery. Provider observations in fixtures are simulated, not native
wake evidence. Parent routing checks7PASS; request-binding checks9PASS.
Exact artifact convergence and live activation criteria above remain pending.

## 12. Initial-publication repair (review candidate)

Deployment preparation after I10/I11 CLEAN found a separate HIGH: _team_remote
requires a v2 remote before the first v2 push, while INTENT confirmation requires
a prior private reservation. Existing v2-only two-clone fixtures did not cover
initial publication. No canonical activation has occurred. The owner has granted
preparation only until a fresh maintenance boundary after its current result.

Keep the existing writers and add one narrowly registered command in
workflow_runtime.py, with its tests in test_workflow_runtime.py:

```text
team-bootstrap-publish --operation-id <id> --expected-head <commit> --expected-remote-commit <commit> --expected-remote-resume-sha256 <sha256>
team-bootstrap-publish --operation-id <id> --reconcile-only
```

This is only initial owner-preserving v1-to-v2 publication on the existing
origin/rh_clean, never a second ownership acquisition or a mathematical selector.
Initial use requires local v2/ACTIVE/epoch1/no transfer, the actual task and
private installation identity, an exact publication INTENT with the same ID,
unchanged source/input hashes, and local HEAD equal to the explicit candidate.
The committed candidate RESUME must equal the current checkpoint. The verified
history must contain the owner-preserving v1 local-install INTENT and its real
local-commit confirmation, as well as the exact pinned remote v1 checkpoint.
The local-install operation ID is `<publication-id>:local-install`; its confirmed
evidence names `bootstrap_local_commit:<commit>`, an ancestor of the candidate.
This confirms local installation only, never the later remote publication.
Before any reservation, the live remote
must match both expected commit and RESUME hash, retain the same owner/host,
physical goal, source/request/phase pins, and be an ancestor of the candidate.
An already-v2 remote cannot start this route. The scoped legacy migration grant
and safe boundary remain required; flags or model output do not supply authority.
Before the local-install intent, the current v1 operation must be NONE or
CONFIRMED. Resolve any existing INTENT/UNKNOWN from its own evidence first;
never replace it with the maintenance operation. The bootstrap validator checks
that immediate archived predecessor and the actual owner boundary, rather than
treating the isolated clone's stale mathematical checkpoint as current.

The publication scope is closed before the candidate commit: `operation.inputs`
contains every changed non-checkpoint path and its exact reviewed after-SHA256;
`operation.subject` is REPAIR / operation ID / SHA256(canonical JSON inputs).
Create this new v2 PUBLISH/INTENT only after final non-checkpoint bytes and the
required refresh are known. The migrated operation was already CONFIRMED from
an actual local commit, so this creates no unresolved-operation replacement and
needs no prediction of later derived hashes. It is the saved reviewed migration
scope; runtime flags never authorize additional paths.
The only two metadata exceptions are RESUME.md and GOAL_HISTORY.md: their
committed bytes must equal the verified current checkpoint/history. The history
must extend the exact remote history by complete verified entries, retaining its
bytes as a prefix and the pinned v1 checkpoint. No reset or rebuilt history.

Under the existing writer lock, verify that `remote..candidate` is a linear
non-merge descendant chain, and the full tree diff is exactly the sorted union
of operation.inputs and those two metadata paths. Each input hash must match
the candidate blob and unchanged working bytes. Require regular Git blobs with
mode100644 or100755; reject deletions, symlinks, duplicate/noncanonical paths,
extra or omitted changes and foreign unmentioned paths. Unchanged foreign dirty
files outside the committed diff are preserved and never staged by this command.
Build a closed `q3_team_bootstrap_publish.v1` manifest with operation ID, branch,
remote predecessor commit/checkpoint/history hashes, candidate commit and parent
chain, input-scope digest, and sorted file rows containing path, before/after
SHA256 and before/after mode (ABSENT/null only for newly added preimages).
Store this whole manifest and its canonical JSON hash in the private RESERVED
operation, alongside exact actor/installation/epoch and candidate checkpoint.
The full manifest is private to avoid a self-referential committed-checkpoint
hash. Reconciliation validates this same saved manifest; arguments cannot select
a different candidate or scope after reservation.

Recheck checkpoint, history, HEAD, inputs and private preimage under the existing
writer lock, then durably save the reservation before the first push. Release
the lock for exactly one ordinary non-force fast-forward update. Recheck the mandatory
`git merge-base --is-ancestor <expected-remote> <candidate>` invariant; only then
invoke `git push --no-follow-tags --recurse-submodules=no origin
<candidate>:refs/heads/rh_clean`. The server rejects an update that would remove
commits from its current tip. There is no force option (including any lease),
plus-prefixed refspec or moving HEAD. Check the fetch/push endpoint is the same
single origin; mirror mode is forbidden. Existing hooks and config stay intact.
Do not retry the push automatically. No config, hook or other branch changes.
The expected remote commit is an observation checked before reservation, not an
atomic lock on a remote branch. If another actor moves the branch to an already
reviewed ancestor of the exact candidate, ordinary fast-forward publication may
succeed and preserves its entire history. If the new tip is not an ancestor,
the server refuses and reconciliation reports UNKNOWN. We do not promise exact
expected-tip compare-and-swap or protection against arbitrary remote resets by
uncooperative actors. Those were supplemental overclaims, not owner-authorized
requirements. Validate each intermediate candidate commit as well as the final
tree: changed paths stay within the closed migration scope; every RESUME retains
the same owner/host and mathematical pins. No foreign changes can be published
temporarily and hidden by a later revert.

After the push, re-observe the remote branch and candidate checkpoint, then
durably confirm only the identical expected candidate commit and v2 bytes.
On old/different/unavailable remote evidence return UNKNOWN without replaying
the push. A repeated invocation, including one after a lost receipt, performs
reconciliation only from the persisted operation; argument drift is rejected.
Reconcile-only without an existing operation does not reserve or push anything.
Do not manufacture a pre-action reservation after observing an already executed
push. A crash after reservation but before push can therefore remain UNKNOWN:
the command reports the exact unresolved operation and never guesses absence.
The ordinary checkpoint writer then consumes the real confirmed private receipt
for INTENT-to-CONFIRMED. A technical publication never advances proof acceptance.

Register exact effects in TOOLS: private q3_team_local.v1, fetched Git objects,
origin/rh_clean tracking reference and the existing remote rh_clean reference.
Add it to fenced inventory and the cross-host card; regenerate docs/TOOLS once
after the final registration changes. Reuse the existing remote-read, actor,
source, operation and durable-write helpers; no new service, database or module.
The old remote read may be factored into a version-neutral private read helper;
normal team-observe-remote remains v2-only.

Bootstrap order at the actual boundary:
1. Reconcile and finish any existing v1 INTENT/UNKNOWN independently. Only from
   NONE/CONFIRMED save exact preimages and a v1 PUBLISH/INTENT for the reviewed named local
   runtime/registry installation only, ID `<publication-id>:local-install`,
   retaining the actual mathematical state and the exact known subset hashes.
2. Install the reviewed runtime/registry/TOOLS subset; make its named local
   commit (TOOL_MANIFEST must match HEAD before resume-checkpoint).
3. While the control is still the old version without TEAM_RUNTIME_VERSION,
   use the registered checkpoint writer to confirm that v1 local-install
   operation from the actual subset commit and readback, recording
   `bootstrap_local_commit:<commit>`. The new runtime accepts v1-to-v1 under this
   old control. Then run registered local-init and save the first actual-owner
   v2 checkpoint, preserving that CONFIRMED operation kind/ID/state and pins,
   original history and readback. Add its typed fields without claiming a push.
4. Install final reviewed GOAL/control/entry and generated docs/TOOLS.md. Make
   a named local source/control commit BEFORE the single batched refresh or
   any further checkpoint: actual startup rejects an uncommitted control or
   declared startup surface. docs/TOOLS.md belongs only to this final source
   batch, not the earlier runtime/TOOLS.yaml installation. Run the required
   refresh and independently verify all final non-checkpoint bytes. If refresh
   changes a startup-relevant tracked derived path, commit its final bytes before
   step5; an intermediate commit must never carry a different version of a path
   already bound to the final input manifest. If it would, stop and revise the
   installation sequence before publication. Do not bypass the startup gate.
5. Save a second v2 checkpoint starting the distinct final PUBLISH/INTENT
   operation `<publication-id>`, command workflow-team-bootstrap-publish, with
   the exact final inputs and bound REPAIR subject. Verify its history/readback.
   This explicit final checkpoint precedes publication and never confirms it
   by prediction; the earlier local-install confirmation cannot substitute.
6. Make the named exact checkpoint/history candidate commit. Run team-bootstrap-publish, which
   constructs, verifies and reserves its full closed manifest before any push.
7. Only after its actual confirmed receipt may a normal checkpoint record
   INTENT-to-CONFIRMED; it does not recursively require another publication.
No skip-fatal and no caller-identity substitution. Indexed inputs finish before
one required batched refresh. Native assignment pilot, issue lifecycle and
scheduled wake are separate acceptance steps after remote ownership exists.

Parent full-tree subprocess acceptance found the missing step4 commit barrier
after Bp8's static CLEAN. With the actual registered local-init, clean plan was
HOLD with zero fatal errors; dirty control was FATAL with
STARTUP_CONTROL_BLOB_DRIFT and STARTUP_RELEVANT_DIRTY_PATHS. Supplemental Bp8
classified this HIGH. The explicit local commit ordering above fixes the plan;
the bootstrap fixture's mocked plan had not tested this startup condition.

Required tests use a local bare remote initially at a real v1 checkpoint: exact
first publication; forbidden v2 start, foreign owner/epoch/changed pins or local
candidate drift; refusal without saved intent or matching original history;
interruption before reservation, after reservation/before push, after server-side
push/before local confirmation; same-operation reconciliation with zero repeat
pushes; changed/unknown remote, argument conflicts and unrelated foreign bytes;
extra/omitted/deleted/symlinked candidate paths, incorrect hashes/modes, unbound
scope digest, history replacement and non-linear candidate ancestry.
Change the remote between its final observation and push: a nonancestor tip is
refused without loss; a reviewed intermediate ancestor may fast-forward without
losing any commit and is confirmed only by exact candidate readback. Test a
rollback without claiming atomic expected-tip equality. Reject a non-descendant
candidate before any push. Assert no force/lease or hook/config override occurs.
Independent plan and exact artifact review must converge before this repair is
used. I10/I11 do not cover this newly discovered HIGH or its implementation.


## 13. Final preparation after the published observer advice

Preparation base8477fd769721eacab272356acaf48cf4fcc6c61d includes the accepted
density resultb7bf286e and parallel observer advice. Preserve all their ancestry
and bytes; GOAL section6 is retained verbatim. The mathematical owner confirmed
the direct user instruction and same-owner/same-watch interpretation recorded
in INSTRUCTION_ISSUES. Do not install this clone's stale RESUME or history.

Current evidence:225 workflow/channel/bind tests PASS89.680s, including real
subprocess termination after server ref update and fresh-process reconciliation
without a second push. A full-tree, actual CLI/actor/lock/registration rehearsal
passed all21 source paths and the correct intermediate commit order with a
local bare remote. This is fixture evidence only: canonical migration, semantic
refresh, actual concurrent assignments, issue lifecycle and native scheduled
wake are still separate acceptance criteria.

The exact rehearsal script, complete suite output and successful rehearsal log
are preserved in docs/session_protocols/team-runtime-preparation-2026-09-11.log.
This additional receipt path must be bound in final operation.inputs, alongside
all21 source paths and any ACTUAL owner-authored protocol/ledger/derived changes.
Only RESUME and GOAL_HISTORY are bootstrap metadata exceptions. The prepared
merge history is NEVER the canonical publication history: the actual owner
installs the reviewed bytes as named linear commits on its fresh canonical base.

Final native read-only review dispatch intent: existing /root/team_core_review,
gpt-5.6-terra/medium, no descendants, owning task01a08f80, two sequential passes
on one immutable manifest/diff. Exact base/candidate/file hashes and raw native
review receipts remain external to those frozen inputs. Expected bound15minutes
per pass. No source edits by the reviewer, no acceptance of its own work.
The prepared source remains NON_EXECUTABLE until those checks converge and the
mathematical owner grants the safe boundary and executes section12.


Final source B5/B6 CLEAN/CLEAN was followed by one actual-entry LOW finding:
legacy v1 continuation leaked a raw ownership KeyError alongside its valid
migration blocker. One v2-only local-observation guard and a failing-before,
passing-after regression repair this diagnostic. Five targeted tests PASS6.175s;
actual CLI now reports only applicable migration/replay holds, no fatal errors
or writes. The earlier225-test suite remains evidence for unchanged behavior;
it does not claim to have run the new test. Exact replacement manifest and two
new on-target source passes are required before activation. SIBLING and the
canonical owner/watch/checkpoint remain untouched. No further tool census is
needed: registration, tool inventory and startup front door did not change.


## 14. Addressed technical watch after CADENCE correction

Earlier Wp2/Wp3 plan037f5e6c and unexecuted5minute CREATE intent are WITHDRAWN by published CADENCE430b9317. They were isolated preparation only, never canonical. Historical5/10 test evidence remains in the preparation log; it does not describe current behavior. Wp4/Wp5 are CLEAN/CLEAN on the following exact v3 plan (3650bytes, SHA256f5a59eb7bc14b41d12ab096023795a26eba6ae617e0b773120709b10944e02fc).

# Scoped CADENCE reconciliation, successor of Wp2/Wp3

Authority: the direct user confirms GOAL section6 and ADVICE_* as owner instructions and requires section6 verbatim; SIBLING remains exclusively with the mathematical owner. Published CADENCE430b9317f0ab154b02ff93a188a92723bd4179dc corrects the observer's WATCH09f11c6a: continuation stays10, agent checks20. No dual5/10 acceptance or new schema. No mathematical/shared-write ownership is transferred. The technical watch remains task-local to01a08f80-f033-7a31-8f3a-3aef042a3fbc.

Exact predecessor: isolated c7f806fe merges09f11c6a over67d4bc9f. Source67d4bc9f had B7/B8 CLEAN. The5/10 code, tests and GOAL section3 transition were only uncommitted preparation and were NEVER canonical. Wp1 MEDIUM required exact integer checks (membership accepts floats); Wp2/Wp3 CLEAN applied to the now-superseded5/10 plan, not to this correction.

Minimum outcome: preserve the existing10/20 schema values and original reviewed GOAL section3 byte-for-byte; preserve all eight section6 lines from8477fd76. Restore PhaseD's10minute instruction. Keep exact type(x) is int for BOTH cadence fields to enforce the existing integer contract; continuation_minutes ==10, agent_check_minutes ==20. Reject5, floats, bools, strings, arrays, null and other values before any private receipt write. This is schema validation repair, not a new accepted schema/cadence. One existing-test-file regression checks valid10, no inferred scheduled wake, every rejected input and unchanged receipt. Existing owner/watch/legacy checks remain.

Update only the isolated workflow_runtime.py and existing test, GOAL, the existing plan/issues/preparation log and generated TOOLS documentation. Preserve prior evidence as historical; explicitly mark the5minute preparation and unexecuted CREATE intent superseded. No services, database, second selector, fake identity, canonical write, old RESUME/history install or external Codex process. The current mathematical owner must independently reconcile its actual bridge (last provider observation5; CADENCE's unchanged10 assertion is stale). This task does not touch it.

Native technical watch: inspect saved inventory again, reuse a matching existing task watch; create only on confirmed absence, native heartbeat named Q3 — стройка и советы, existing technical target01a08f80, ACTIVE,10minutes. Prompt reads canonical plan and technical handback, observes published TO:STROJKA/BOTH advice by commit/content hash versus own reports (shared HEAD is not a cursor), and resumes only already authorized technical work in isolation until actual owner boundary. It preserves math owner/SIBLING and does not mutate the shared checkout or auto-fast-forward it. Record intent before native mutation, provider readback after, reconcile unknown effect without replay. Unchanged quiet, meaningful result/failure/user-action reports; agent necessity20minutes. Existing10minute mathematical bridge is separate and remains under its owner. Scheduled wake evidence must be an actual provider event, distinct from settings.

Validation and completion: narrow regression including no-write failures, unchanged section6/full original section3 and GOAL<=12KiB; preserve complete225-test/rehearsal evidence without rerunning the nonrepeatable fixture. Two exact artifact passes after this plan converges; native create/readback and real wake are still pending. Deliver exact source manifest to actual owner for section12 linear installation on its current base and real migration/refresh/publication. Shared boundary is closed; do not mark canonical refactor accepted from isolated tests.

Current observation: mathematical owner independently restored bridge ACTIVE10 via the native tool; technical task read the saved inventory and confirmed it. No further change to bridge or GOAL section3 is needed. The current technical CREATE intent replaces the withdrawn5minute intent and is not executed until exact artifact review and a fresh inventory establish that this task still lacks a watch.

Name: Q3 — стройка и советы
Target: 01a08f80-f033-7a31-8f3a-3aef042a3fbc
Kind: native heartbeat; interval10minutes; ACTIVE; notification preference unchanged/default.
Prompt SHA256: 2588756170013c9958717db90776d8514beba4c61d3eb4955188cfa929fb7fac

```text
Продолжай ту же техническую задачу рефакторинга Q3 в задаче 01a08f80-f033-7a31-8f3a-3aef042a3fbc. Выполни канонический python3 orchestrator/workflow_runtime.py plan и прочитай сохранённую точку продолжения этой технической задачи в docs/Codex/TEAM_RUNTIME_REFACTOR_PLAN_2026-09-11.md и docs/session_protocols/team-runtime-preparation-2026-09-11.log отдельной копии /home/chirurgie/.cache/q3-team-2026-09-11-01a08f80. При недоступности копии восстанови её местоположение из последних результатов этой задачи, без новой математической цели или повторной установки.

Проверяй опубликованные на origin/rh_clean docs/Codex/ADVICE_*.md, адресованные TO: STROJKA или TO: BOTH, и состояние передачи технического пакета. Читай адресованный совет целиком. Сравнивай его коммит и хеш содержимого с собственными сохранёнными результатами и REPORT_<date>_<NAME>_STROJKA.md: общий HEAD не является отметкой обработки. В отдельной технической копии origin указывает на локальную папку, поэтому для наблюдения опубликованных советов прочитай адрес origin канонического репозитория и выполни git fetch --no-tags с этим явным адресом и refs/heads/rh_clean. Зафиксируй полученный коммит из FETCH_HEAD и читай советы из него. Сейчас подтверждённый адрес — https://github.com/Malaeu/chen_q3.git. Не меняй git config и не обновляй общее рабочее дерево автоматически.

Математический владелец 01a084f4-7498-7021-bac2-91d184d58dc7 и SIBLING остаются за основной задачей. При закрытой общей границе записи выполняй только ранее авторизованную техническую работу изолированно и передавай точный проверенный пакет действующему владельцу. Не меняй его исходники, расчёты, фазу, владение и вахту. После подтверждённой установки доведи обязательные проверки входа, параллельной работы, обработки проблем и реального пробуждения до наблюдаемого результата. Не повторяй действие с неизвестным исходом: сначала проверь первоначальное намерение и подтверждения.

Ответы по советам сохраняй по ADVICE_PROTOCOL с исходным коммитом и хешем и честным статусом VICTORY, DEFEAT или PARTIAL. Проверяй необходимость своих агентов каждые 20 минут; пустой список не завершает задачу. Вахта возвращается каждые 10 минут и не создаёт новую цель, задачу или математического владельца. При неизменном состоянии молчи; сообщай только о содержательном результате, сбое или необходимом действии пользователя. Настройка не подтверждает пробуждение: сохрани фактическое событие планового запуска и его время. Не выставляй complete или blocked ради проверки. После простоя сначала сверь факты и сохранённые результаты.
```

Concrete origin-route reconciliation: the preparation clone's origin is the canonical local filesystem clone, not GitHub. Its native prompt therefore reads the canonical origin URL and fetches that explicit URL into its own FETCH_HEAD, without changing git config or the shared tree. Actual command git fetch --no-tags https://github.com/Malaeu/chen_q3.git refs/heads/rh_clean returned published e6b5128d68357f1f8a48b63d24c0e2d46b43a554. Addressed CADENCE hash663b5e70554d64defb14da9e3396fa5b792a7da646e693e8b0346e803a7316d0 and corrected WATCH hasha509ba1d87a6905c3e57d78781649eb29874ee4fb7842c8fffd2620fb5381b8f both bind to430b9317. This enforces the reviewed origin-observation requirement; no new task or storage protocol is introduced.
