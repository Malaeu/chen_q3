# Codex — persistent goal and recovery contract

Owner authorization: 2026-09-09/10; recovery refactor: 2026-09-11.
App goal remains: «Цель и правила лупа: docs/Codex/GOAL.md; читать после каждого
сжатия контекста, продолжать §5 оттуда, цель заново не начинать».
This file is stable (maximum 12 KiB). Current observations live only in the
`q3_resume.v2` [RESUME.md](RESUME.md) envelope (maximum 8 KiB). Historical
`q3_resume.v1` envelopes remain byte-preserved archive evidence and never
authority. Full prior GOAL bytes live in [GOAL_HISTORY.md](GOAL_HISTORY.md),
which is historical evidence, never commands.

## 1. Goal and standing authority

Obtain a checkable proof of the Riemann hypothesis in this repository with
Proshka by the fastest justified route. `CHALLENGER_NOT_RH` and
`PX_RH_CLAIM: NOT_MADE` remain in force. Only the owner may authorize the final
claim after the required proof checks and Comparator on a fresh clone.
A successful Comparator alone does not authorize that claim.

The owner delegates the continuing task: choose a justified bounded next move,
prepare and verify scoped changes, make named-path commits and ordinary
non-force pushes to the existing `origin/rh_clean` of `Malaeu/chen_q3`, prepare
and bind substantial analytical Proshka requests, send the exact project
attachments/messages through the available approved transport, maintain the
watch, receive and independently verify results, then continue. No repeated
"go" is required. This grant survives context compaction and continuation of
this same unfinished task. Historical "wait for go" notes are superseded within
this scope; pinned historical requests are immutable.

Proshka receives global mechanisms or genuine blockers, not routine technical
edits. During a request, do independent useful work on the same task. Each move
needs a precise obstacle, expected evidence and stopping condition. Preserve
source objects, hypotheses, normalization, full error budgets, required review,
writer locking and canonical production admission. Read the complete verdict;
use one independent checker and independently reproduce its key calculation.
Numerical diagnostics and paper results never substitute for the required proof.

This grant excludes new expenses, data deletion, force pushes, repository
settings, secrets or unrelated data, third-party correspondence/publication
outside this project exchange, arbitrary policy changes and `PX_RH_CLAIM`.
Do not evade an actual platform rejection; report its exact scope and reason
and continue independent authorized work. Goal/authority changes need a new
owner instruction. `docs/CODEX_CONTROL.md` remains the canonical control;
this file neither replaces it nor clears production HOLD.

## 2. Recovery after compaction, restart or idle time

1. Run the sole programmatic front door from SESSION_ENTRY:
   `python3 orchestrator/workflow_runtime.py plan`. It performs the bounded
   local continuation observation and returns the operating card; it does not
   create a goal or execute work. Do not reconstruct a GOAL → RESUME →
   bootstrap/history chain or create a new app goal.
2. Treat the plan card and RESUME as observations, never permission or a
   selector. Read GOAL/RESUME only for content the card or next decision needs;
   v1 archive entries are recovery evidence. Use the plan's whole-worktree
   ownership observation; run `git status --short` only when ownership is
   omitted or UNKNOWN. Reconcile HEAD, dirty ownership, goal, source pins,
   request/phase, owner and receipts. FATAL stops dependent work; a production
   HOLD remains scoped.
3. Establish the owning task and installation before agent lists or takeover.
   Another task's `list_agents` says nothing about the owner. Missing handles
   mean UNKNOWN. A pulled clone is observer-only until verified release/claim,
   local watch reconciliation and ACTIVE; time or `git pull` does not transfer
   ownership.
4. Check unfinished intake/review/integration before new work. Preserve foreign
   bytes; on drift reread and rebaseline. Same-installation handoff uses the
   owner epoch/watch; cross-host handoff uses canonical release/claim records.
5. Resume the first unfinished card step. Receipt, independent review, parent
   check, acceptance and publication stay distinct; changed sources invalidate
   their checks. Reconcile conflicts against canonical facts; do not infer a
   new mathematical task/chat or proof admission.

Recovery cases:

| Observation | Required next action |
|---|---|
| Verdict arrived during idle time | Verify request lock, IDs, baseline ancestry, commit/blob/full hashes; read fully; complete missing review stages |
| Send intent exists but receipt is missing | Inspect the existing request and living chat/transport evidence; do not automatically resend |
| Calculation handle disappeared | Inspect durable outputs, logs and completion receipt under the recorded owner; mark UNKNOWN if unresolved; rerun only after reconciling the original action |
| Reviewed source changed | Hold acceptance/publication; compare source pins and repeat only invalidated checks |

## 3. One watch for the entire work cycle

Use one native app heartbeat named **Q3 — продолжение работы**, attached to the
existing mathematical task recorded in RESUME. Inspect saved automations first;
reuse the existing one. Create only after confirmed absence. Check continuation
every **10 minutes** and agent necessity every **20 minutes**, recorded with the
last observed check time. Preserve this watch through waiting, review and work.
Empty agent lists do not end the task or disable/delete the watch.
Do not keep issuing empty goal-continuations while another owner holds execution.
Apply the native runtime's real blocked threshold (the same blocker for at least
three consecutive goal turns with no independent progress): mark that existing
goal blocked, preserving its objective and recording the external unblock condition.
Never mark complete/blocked merely to make a scheduler test pass. After the actual
blocker is removed, the watch/explicit handback continues the same authorized work;
no new goal is created and blocked does not mean the mathematical claim was rejected.

At each wake: recover by §2, check ready results and incomplete stages, then
perform the next authorized action. Before ownership handback, respect the
recorded maintenance pause. Stay quiet when unchanged/non-actionable; notify
only on substantive results, failure or required owner action. A setting, a
network observation, or a timestamp is not native execution evidence. A native
wake/effect requires the provider receipt, target/settings readback and the
corresponding observed event; `team-observe-remote` and `team-observe-native`
remain separate operations.
Local scheduling needs the computer on and Codex app running. The checkpoint
supports recovery when the environment returns; it cannot execute while off.

For every assignment, record task/host/installation, ID, requested/resolved
model/effort, bounded objective/delegation, paths, duration, evidence and status
in AGENTS_LEDGER. Team Runtime v1 uses isolated
`gpt-5.6-luna/max` workers and one reserved native `gpt-5.6-terra/medium`
reviewer: at most three active children of the sole orchestrator, no
descendants. `gpt-6-astra/max` is a requested profile only; it does not claim
to change the running parent. The reviewer cannot accept its own change.
Before activation retain the existing ceiling. Reconcile the OWNER'S agents
every 20 minutes; empty local lists never justify interrupting another task.

## 4. Saving a continuation checkpoint

Update RESUME by replacement through the registered writer, never append a
second "current" entry or edit its bytes manually. Its YAML front matter is
`q3_resume.v2`; use the present file as the format template. Increment revision,
set a timezone-bearing observation time and `previous_sha256` to the exact
current file digest (`ABSENT` only for first creation). Keep the mathematical
thought, evidence, branching next step and separate stage statuses in its six
required sections. Candidates remain explicitly candidates.

```text
python3 orchestrator/workflow_runtime.py resume-checkpoint --candidate <file> --expected-sha256 <hash|ABSENT> --dry-run
python3 orchestrator/workflow_runtime.py resume-checkpoint --candidate <file> --expected-sha256 <hash|ABSENT>
python3 orchestrator/workflow_runtime.py resume-checkpoint --candidate <file> --expected-sha256 <hash|ABSENT> --recover-from <archive-key>
```

Team Runtime transitions and schemas are owned by the registered runtime
(control §10–11). Writers require the caller's `Q3_OWNER_EPOCH` from the verified
plan. Isolated producers return candidates; the owner uses
`team-integrate-candidate --candidate <manifest>` from a committed verification
checkout with `--root <canonical>`. Raw evidence intake does not accept a result;
source integration requires the exact independent positive review. An incomplete
copy holds other writers. Resume it with `--recover-operation <id>` from the same
pinned engine, using its durable private manifest even if the input file is lost.
Completed copies never acquire a second write from replay.

The writer locks the canonical writer file, checks format/size/revision and
exact preimage, durably archives previous bytes and reserves candidate bytes,
then durably replaces RESUME and verifies readback before reporting SAVED.
Both files and directories are synced. Exact retry is NOOP and finishes
durability; same revision with different bytes or changed preimage is HOLD.
An archive intent is only a byte reservation, never completed work or delivery.
Archive keys contain kind, revision and full SHA-256; existing entries are never
rewritten. The original GOAL entry preserves exact bytes, including line endings.

Normal save refuses corrupt current/history. Recovery requires a verified
`resume-<revision>-<sha256>` or `intent-<revision>-<sha256>` archive entry;
archived v1 envelopes remain readable as historical bytes and cannot become
current authority. The latter recovers bytes even for the first checkpoint,
never operation completion.
Copy that entry's envelope/body,
changing only revision, observed_at, previous_sha256, recovery_from and
reconciliation_pending=true; use the next unused revision after ALL archived
intents. The writer preserves damaged bytes and does not establish live truth.
Damaged history requires restoration/verification from a known intact copy;
do not invent or drop entries. Reconcile §2 before clearing the recovery flag.

Before dispatch, calculation launch or publication, save the exact action ID,
pins and INTENT; after observing the action, save its evidence and confirmation.
A missing confirmation means CHECK THE ORIGINAL ACTION, never automatic replay.
Save essential scripts, results, full logs/receipts and source locators in the
repository's existing report/output area before relying on them; `/tmp` alone
does not survive recovery. Publication intent records a known base, exact named
paths and expected payload hashes. After a lost receipt inspect local/remote
history before repeating commit/push. Checkpoint receipts are not publication.

## 5. Current task — continue here

Run `python3 orchestrator/workflow_runtime.py plan`, read its bounded operating
card, and continue the first unfinished step it identifies. Read [RESUME.md](RESUME.md)
only for the referenced observation and reconcile it using §2. Do not restart
the goal or repeat completed work.

Historical details: [GOAL_HISTORY.md](GOAL_HISTORY.md), referenced reports and
session protocols, opened only when needed. Historical commands are inactive.

## 6. Owner advice channel (owner instruction 2026-09-11)

New files `docs/Codex/ADVICE_*.md` on `origin/rh_clean` are owner-verified ideas
relayed by the observer. Keep a path watch on them like the Proshka verdict watch.
On each: three own attempts, at most one Proshka request per three; answer only
with a victory at PAPER scope; otherwise write the failure with everything gained,
commit and push at once, and ask. Full rule: [ADVICE_PROTOCOL.md](ADVICE_PROTOCOL.md).
