# Instruction issues

## 2026-09-11 — durable continuation and one watch (owner-approved refactor)

- Resolved: GOAL mixed stable rules with a 92,155-byte evolving §5. The complete
  pre-migration bytes/hash are preserved in GOAL_HISTORY; short GOAL §2/§3/§5
  stay addressable, and RESUME is the single replaceable observation checkpoint.
- Resolved: CODEX_AS_SECOND_BODY §0/§8 required full external history and the old
  session_start bootstrap. SESSION_ENTRY now retains one canonical plan; GOAL
  and RESUME plus referenced source evidence suffice for recovery. The mathematical
  method remains; historical commands/snapshots are explicitly inactive.
- Resolved: old GOAL §3, companion §3b/§7b and the earlier app-constraint note below
  prescribed deleting/recreating watches at empty agent lists or verdict intake.
  They are superseded by one native heartbeat for the entire unfinished cycle,
  every10min / agent-necessity review every20min. Empty task-local agent lists
  do not prove another task's workers absent. Existing PAUSED bridge is reused;
  deleted agents-watch is not recreated. First real scheduled wake needs evidence.
- Resolved: companion §4 new-chat-per-batch conflicts with CODEX_CONTROL §8.
  Use the same living phase chat; missing identity requires reconciliation,
  never fallback fanout or duplicate dispatch after a missing receipt.
- Resolved: companion §3b blanket checkout and §5 push-all could discard or publish
  foreign work. Require safe ownership boundary, exact preimages under the existing
  writer lock and named reviewed paths. Owner at9772e457 explicitly paused after
  publishing all edits before this migration; every replacement rechecks its bytes.
- Implementation: workflow-resume-checkpoint is an observation-only registered
  writer, with canonical fatal startup gate, exact preimage, byte/revision archive,
  durable intent reservation and file/directory fsync. It never selects a task,
  sends a request, proves a theorem or publishes. Recovery preserves corrupt bytes
  and requires live reconciliation. The original history is never replayed as policy.
- Review adjudication: initial revision1 and q3_resume.v1 are implementation
  choices allowed by the final owner plan; reviewer withdrew findings based on
  older draft literals. The startup and owner-host findings were fixed. First-save
  recovery and orphan-intent findings are covered by regression tests.
- Delivery ordering: register/test/review the writer in a local infrastructure
  commit before using it, because canonical startup rejects an uncommitted tool
  declaration. Publish only after document migration, final review and one batched
  derived refresh. No weakened startup gate or new selector/service is introduced.
- Remaining platform limit: local app scheduling requires computer/app running;
  configuration is not proof of execution. See the session protocol for observed
  wake evidence and final verification rather than treating this rule as a receipt.

Historical issue entries below are preserved; superseded commands are not current
instructions. Global memory writes remain outside this refactor's scope.

## 2026-09-09 — autonomous Proshka dispatch versus exact push approval

- Sources: current owner's explicit delegation (Codex decides when/what to send to Proshka); AGENTS.md, `ADVISORY v1 ship rule`; `docs/CODEX_AS_SECOND_BODY.md` sections 1, 4, 5.
- Concrete effect: `bind_request.py --no-push --commit-prefix '[Codex][rh_clean][SCHUR]'` created request e11338a3a9132c88895b565d74ce189503d1c642 and binding 22a3b598d31d0b0cc7af0ad16ee80465de65aa09. Automatic approval review rejected `git push origin rh_clean`, interpreting the delegation as insufficient exact-payload push approval.
- Status: exact two-commit approval requested; no alternate transport used to bypass the rejection. Other authorized work continues.
- Proposed resolution: obtain explicit approval for this exact push; separately reconcile the owner-delegated dispatch rule and exact-payload push rule when the owner reviews instruction issues. No policy file changed by this task.

- Resolution 2026-09-09: after the owner explicitly requested repair of the publication problem and continuation, the exact three-commit push to `993ae9cdbbae6576692a9f71eb71a969ff67036a` passed automatic approval review and completed. SCHUR attachment and locator were delivered in canonical chat `6a8c3e2a-df50-83eb-b53d-dd4cc46f646f`; natural reasoning start observed. No approval policy was changed or bypassed.

## 2026-09-10 — standing authorization for the Proshka work loop

- Sources: owner's direct request to rewrite GOAL so work with Proshka proceeds automatically without repeated go; docs/Codex/GOAL.md section 5 and queue previously required a separate go for BRIDGE.
- Resolution: explicit task-scoped standing authorization is recorded in GOAL section 1.1 and the current queue entry. It covers preparation, verified commits/non-force pushes, project request attachments/messages to Proshka, watch and intake. Historical pinned requests remain unchanged. The existing phase transport, proof verification and owner-only final claim remain in force.
- Platform boundary: previous push attempts were rejected by automatic approval review even after a standing grant. The later exact owner approval allowed the ordinary push check; remote c7271cae was verified. A goal edit cannot guarantee platform approval or authorize evasion of a future rejection.

## 2026-09-10 — SATURATION transport and missing observed phase-transition writer

- Status: RESOLVED by a3220fad/d89888ff; SATURATION delivered at11:24+02 after two final byte/runtime confirmations. Historical context: its mathematical payload passed at SHA25670acf14...; the final unique-boundary payload SHA256211cf7...85c79 was then independently rechecked before binding and delivery.
- Observed evidence: the existing owner-requested BRIDGE chat is6aa24f25-0934-83eb-9151-3565fc4b3379. Browser DOM on10.09 showed request message42601c8e-ad3b-47de-b2aa-706c74cd9184 and response messageb9b96355-7515-4611-ab05-4fe88c76d963, with verdict4ae462655affe4e3511a765a54a04a6510338f72. Queue and GOAL record delivery at2026-09-10T08:33+02:00.
- Observed defect before repair: CHANNEL_RUNTIME pointed to6a8c3e2a... and the earlier tuple (front GOAL058_G1_G3_COFINAL_GROUND_TRACKING, source PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY, consumer Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots). BRIDGE/SATURATION both use the same newer tuple (front GOAL058_SECOND_EXPRESSION, source CANONICAL_TEST_SIGNED_DIRICHLET_FORM, consumer published_Weil_criterion_on_all_complex_compact_smooth_tests). Three remaining fields agree.
- Rejected with HIGH, not applied: change only conversation_id, or silently replace all four values and call it a non-transition. Those variants misattribute old phase-local calls and contradict CODEX_CONTROL section8. Runtime was left unchanged until the independently reviewed repair below.
- Source check: standalone workflow_runtime close-phase calls specs_docs/phase_close.py; it does not record a phase transition or write CHANNEL_RUNTIME. Its diagnostic spawned the default Lean gate and was terminated as an unnecessary diagnostic (own process group136097, exit143); no passed phase closure is claimed. The production close-node transaction would require a proved exact edge, currently absent. Never fake that closure for a paper chat.
- Implemented repair contract: a bounded observed owner-requested phase-transition record through existing spine.py/atomic runtime writer and existing test_channel_runtime_writer.py, registered in TOOLS. Exact runtime preimage compare-and-swap; pinned opening request commit/blob/hash/six-key; separately pinned observed delivery including chat/message ID and owner-authorization locator; immutable full predecessor archive; late_recording=true with separate observed_at and recorded_at. This records that the explicitly requested BRIDGE chat already opened before bookkeeping; never claim prior closure. Preserve production CURRENT, NODE_REGISTRY and HOLD. Preserve historical global review events/call count, give the new phase its own zero-based initial counter, then use existing record_delegated_review to backfill only verified BRIDGE as phase1/global46. Keep PHASE_ID literal from BRIDGE. Require independent review and failure-closed tests before applying. This does not grant general policy overrides or permission to invent a phase transition.

- Resolution 2026-09-10: a3220fad adds a one-off BRIDGE-only writer with fixed receipt/preimage hashes and exact successor replay; d89888ff records the observed transition as late, preserving the predecessor phase/meter and all historical events. No production closure. Found and fixed the preventive defect: review-plan had omitted all six phase headers and literal PHASE_ID; it now rejects missing, duplicate and mismatched values. 118 scoped tests pass; native plan and artifact review converged. BRIDGE phase call1/global46; SATURATION bound and delivered in the restored same chat. No HIGH finding remains open for this repair.
- App constraint observed: only one ACTIVE heartbeat is allowed per task. Once the reviewer finished, agents-watch was PAUSED before saturation was created; no workaround scheduler. During verdict intake, delete saturation first, then start the one reviewer and agents-watch. This implements the existing watch lifecycle without changing project policy.

## 2026-09-10 — Valid paper phase aborted the read-only session briefing

- Status: RESOLVED in orchestrator/session_briefing.py and its existing tests. The fixed production roof and valid BRIDGE/SATURATION paper consumer are different; the raw ledger correctly reports ACTIVE_PHASE_TERMINAL_CONSUMER_MISMATCH/INVALID, but the briefing previously treated this sole binding mismatch like corrupted proof-source evidence and aborted the whole diagnostic.
- Minimal resolution: validate the complete runtime with the existing strict duplicate-key loader and spine validator; only a valid ACTIVE phase matching the ledger's alternate terminal consumer renders NOT_BOUND_TO_THIS_ROOF, the terminal consumer and briefing BLOCKED. Raw roof stays INVALID. Missing/malformed/duplicate/inactive/changed runtime and mixed source/signature/axiom failures remain fatal. No roof, production compiler, proof-admission or policy modification.
- Verification: 120 session-briefing/workflow tests pass; native plan P2/P3 and artifact A1/A2 converged. Existing rank test drift reproduced against baseline e9899917 (both live rows HIGH); fixed its test inputs to exercise UNKNOWN-before-HIGH deterministically. Actual session_start exit0 while production plan remains HOLD NODE_REGISTRY_EXACT_EDGE_REQUIRED. No new lint findings (10 implementation +1 test finding already at baseline). This fix and its checkpoint records are outside the indexed corpus; no repeat refresh.

## 2026-09-11 — scoped startup dirtiness is not whole-worktree status

Cold resume correctly observed plan.git_dirty=false beside modified docs. Source
inspection of orchestrator/startup_runtime.py::_git_observation confirms git status
is deliberately restricted to GIT_STATUS_PATHS plus owned_paths. This is not a
full-worktree cleanliness receipt. GOAL §2 and SESSION_ENTRY now explicitly require
separate git status --short and ownership reconciliation. No selector/runtime
semantics were changed; the refactor changes are owned by the maintenance task.

## 2026-09-11 — real ownership block versus endless goal continuation

The mathematical executor's write/math ownership was transferred to the refactor
owner, yet its native goal kept producing empty continuations while the watch was
deferred. The instruction not to falsify blocked for a test did not override the
runtime's mandatory genuine-block audit. After independently confirming >=3
consecutive blocked turns, the executor used native update_goal(blocked) at11:43:48,
preserving the exact objective. GOAL §3 now explicitly points to this existing
runtime rule and the actual external unblock condition. No status is changed just
for a test; no new goal/selector or runtime-database manipulation is authorized.
