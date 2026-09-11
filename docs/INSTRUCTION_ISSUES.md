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

## 2026-09-11 — repeated search validation costs versus incremental indexing

- Confirmed implementation: scripts/q3_docs_corpus.py hashes exact curated paths
  and bytes. Any queue status/binding edit changes that corpus. It does not expire
  by elapsed time or checkpoint edits. Existing repair72c59971 preserves the
  collection and removes the generated manifest timestamp.
- Cost evidence: session protocol2026-09-11 log269, total138.877s; actual collection
  update0.935s, embedding23.209s, dynamic preflight60.084s, fixed plants30.801s.
  orchestrator/spine.py::_refresh_semantic_index unconditionally calls all three
  stages for semantic-index-refresh. This is still required by TOOLS.yaml
  q3-docs-refresh and AUTOPILOT_SEMANTIC_PREFLIGHT_CONTRACT.
- Immediate operational correction: combine binding/delivery/journal edits before
  one refresh where possible; never relabel the interim index fresh or claim
  complete absence from it. Known stale state remains explicit in RESUME.
- Open design debt, NOT implemented: separate content synchronization from
  reusable retrieval-validation evidence. Any reuse needs exact dependencies
  covering corpus/goal/query/backend/model/config/index identities and failure
  tests; current receipt alone does not justify skipping probes after a source
  change. No timing-based trust, disabled plants, new daemon or new cache added.

## 2026-09-11 — observed manual chat versus canonical review event

The owner manually sent SLACK in new chat6aa3e75b-cfac-83ed-a4e2-f7d3d81f5d59, message57e6f47f-d70f-4281-97fb-3f2b7641563d. Exact committed verdict e8a95fac and its request lock are verified. Mathematical six-field phase is unchanged, while active_proshka_phase still names6aa24f25. `orchestrator/spine.py::record_delegated_review` requires conversation equality and rejects the actual new ID with EXPLORATION_CHAT_FANOUT; substituting the old ID would falsify the event. The fixed `bridge-observed-phase-repair` tool applies only to historical BRIDGE, not SLACK.

Current disposition: actual request is ANSWERED with binding verified; independent mathematical review/report acceptance is separate. Runtime review event remains pending, not silently manufactured. Proposed repair is a minimal registered reconciliation of the owner-created replacement handle with exact predecessor/evidence pins, preserving the unchanged phase and archived old state. Refactor delegate01a08f80 has been given this concrete case for scope assessment, not blanket authority to bypass it. Independent immutable-source mathematical work continues.

Resolution 2026-09-11T14:12:20.103893+00:00: reviewed registered slack-manual-chat-reconciliation implemented in f342494e (141tests, sole checker revised CLEAN/CLEAN after HIGH fixed). Applied once; exact successor committed5ea31624, runtime SHA2562170b46949ccd5b4ed5ad5dd0b128a7b7417b93e42f75ae8f477d36ea63db1f2; actual manual conversation and phase7/global52 recorded. All6phase keys, old events and unrelated state preserved; attachment_tile_observed=false. After registration, exact CLI replay returned0 and unchanged bytes; plan fatal_errors=[], production HOLD unchanged. Issue RESOLVED at this fixed observed transport scope; no general chat-fanout bypass or proof admission.

## 2026-09-11 — alias discovery (candidate repair)

- Scope authorized by the owner in task 01a08f80-f033-7a31-8f3a-3aef042a3fbc.
  Original machine-local `~/.claude/skills/alias-hunt/SKILL.md` SHA256
  5a55efd4f856ee6d457fac335e270293a8623da1a13903082da0a7668d124a69
  requires three simultaneous workers while GOAL section3 currently caps two.
  The candidate repository skill uses three dictionaries within actual capacity.
- Its section3 permits a three-point test as identity verification and resolving
  conflicting preprints by a number. These diagnostics cannot establish a
  universal identity: exact hypotheses, source quotations, variable mappings and
  the negative control's scope must be checked independently.
- Its section4 prescribes direct shared paper writes and unconditional refresh.
  Candidate discovery is read-only; the owner performs named, locked intake and
  refresh only when the indexed source bytes actually changed.
- Independent plan S1 issued two MEDIUM findings: missing supplier-preflight
  receipt and ambiguous global-wrapper root. Both were fixed; S2/S3 CLEAN on the
  identical amended plan. Exact artifact review/activation remain separate.
- The repository skill is the single portable implementation. The local Claude
  entry is only a validated current-Q3-root pointer; it cannot choose another
  checkout or import its installation identity. This repairs home/work discovery
  without expanding mathematical authority or replacing the canonical plan.
- SESSION_ENTRY's statement that no project skills exist becomes false when
  alias-hunt is added. Its footer now names only this registered skill and keeps
  the older catalogues historical. Exploratory source-pinned discovery remains
  possible with an explicit unbound-consumer status; it cannot close that edge.
- The retired Step32/Step33 entry also claimed no project skills remain; scope
  it to those archived skills. The cross-host card had 59 IDs against 89 existing
  registrations. Synchronize that already-required exact inventory, including
  alias-hunt as tool 90, and the generated tool census; do not weaken its plant.
- Agent-context correction: an empty dependency_registry affected-by result is
  not evidence that semantic refresh is unnecessary. scripts/q3_docs_corpus.py
  selects TOOLS.yaml and SESSION_ENTRY directly. Their changed bytes require
  one batched registered refresh after shared integration. The initial read-only
  audit's contrary conclusion was rejected by this direct source check.
- The existing routing plant hard-coded 59 tools and the old entry wording.
  Preserve its actual checks (nonempty unique inventory, every classification,
  one plan, diagnostic-only secondary script), removing the obsolete literals.
  Other whole-module failures must be compared with the unchanged baseline;
  they are not reported as passing alias checks or silently waived.


## 2026-09-11 — proposed bootstrap lease versus the existing non-force grant

OPEN_REVIEW in isolated task01a08f80-f033-7a31-8f3a-3aef042a3fbc; no shared activation.
Source: current docs/Codex/GOAL.md section1 grants ordinary non-force pushes and
excludes force pushes. The isolated TEAM_RUNTIME_REFACTOR_PLAN_2026-09-11.md
section12 now prescribes git push --force-with-lease with an exact expected ref
plus a proven ancestor relation. That combination is intended to guarantee only
fast-forward effects, but the command uses a force option outside the explicit
current grant. The executor must not silently widen the grant or mislabel this
as a platform rejection. Root sent the exact conflict to the implementing owner.
Proposed resolution: first reassess whether rejection of an intervening reviewed
intermediate ancestor is necessary; prefer the existing ordinary non-force push
with honest exact-source/owner/history reconciliation. If the strict race
criterion really needs another mechanism, keep that criterion open and show its
bounded alternative without hidden hook/config changes. Final plan/artifact
review and a safe shared boundary remain required. No user approval is requested
for continuing the already authorized isolated investigation.

Resolution observed 2026-09-11T17:25:02.850055+00:00: isolated owner accepted ordinary non-force push, removed the unnecessary atomic expected-tip requirement and force-with-lease; native revised-plan Bp6/Bp7 reported CLEAN/CLEAN. This resolves the proposed grant conflict at plan level only. New artifact review/crash tests remain pending in isolation; no shared core write boundary or owner transfer.


## 2026-09-11T18:52:04.157493+00:00 — owner WATCH five-minute cadence supersedes older ten-minute text

Concrete conflict: docs/Codex/GOAL.md section3 says10min, published ADVICE_2026-09-11_WATCH.md at09f11c6a and ADVICE_PROTOCOL7 require<=5min per addressed thread. The newer specific owner instruction is applied: existing MAT bridge updated through native automation API to ACTIVE/FREQ=MINUTELY;INTERVAL=5, agentcheck20 unchanged. Actual five-minute scheduled wake not yet observed. No second MATwatch. Isolated STROJKA owner01a08f80 notified and agreed to review minimal5|10 transition schema plus final5readback; no shared core installation/owner transfer. Leave GOAL/control rewrite to that reviewed package; do not report saved10 as observed5.

Resolution 2026-09-11T19:04:13.476829+00:00: published CADENCE430b9317 explicitly withdraws observer5min; actual bridge was already5, so its claim unchanged10 was stale. Root read CADENCE fully and used native automation_update to RESTORE actual10/ACTIVE, then TOML readback INTERVAL=10. No dual5/10schema or GOAL/control rewrite needed. Isolated technical owner notified. Original5 transition remains historical fact, not a current rule.


## 2026-09-11 — imported reviewed technical preparation records

Canonical prefix is preserved byte-for-byte at SHA2568425d88d39677eabee3940de755eb2480e9b449139e2a56b47d2ecb1c3f8ace4. The following exact additive records come from reviewed source46ab04b5. They are dated preparation history, not new authority or canonical activation. Provisional force/5minute statements are superseded by their recorded corrections below and CADENCE430b9317.

## 2026-09-11 - Team Runtime binding review (isolated candidate)

Runtime review B1 HIGH found an unconfirmed publication reservation; fixed in
the isolated candidate and independently confirmed closed B2. B2 HIGH found
publication of pre-existing unrelated local ancestors; candidate now requires
HEAD at the freshly observed remote base before binding. B3/B4 were CLEAN on
identical binding bytes. This does not claim whole-runtime deployment or final
artifact convergence. Canonical alias and Slack repairs above are preserved.

## 2026-09-11 - Team Runtime integration review (isolated candidate)

Sources: workflow_runtime.py, team_records.py, spine.py, TOOLS.yaml; exact
supplemental plan I5 eeeb1ee8ada05361912d3e8ed03fd579c099380e49a9f8ada12b0020cc75ea7c.
Missing reviewed-source intake and incomplete callable writer coverage were HIGH
contract defects. The isolated implementation adds the single guarded source/
evidence route and covers ENABLED/AVAILABLE/DEGRADED writers, preserving Slack,
Zotero, Aristotle and human-only loader semantics. A completed negative repair
review no longer implies FIX_VERIFIED: its exact verdict must be REPAIR_APPROVED.

I6 HIGH: recovery incorrectly required the detached manifest despite retaining
its exact bytes. Fixed by explicit --recover-operation using the persisted
manifest; unchanged owner/checkpoint/base/review/engine still required.
I7 HIGH: completed replay could reapply original preimages. Fixed by limiting
recovery to PENDING and making completed replay reject every changed destination.
Both fixes have regression cases. Required final independent convergence, real
fresh-process recovery and canonical activation remain separate acceptance steps.

I8 HIGH: bridge-observed-phase-repair was incorrectly classified isolated_only
despite its direct canonical CHANNEL_RUNTIME writer. It is now fenced and calls
team_guard inside the writer epoch before control validation or reading the event.
The existing channel-writer tests check guarded preimage drift and rejection of
pending integration, foreign owner, changed epoch and unreconciled ownership
before any bridge mutation. This preserves the fixed historical receipt scope.

Parent routing check found a wording-only mismatch with the existing diagnostic
entry assertion. SESSION_ENTRY retains the established "manual diagnostic" wording
and identifies the previous contour explicitly; its one-command startup and the
test's semantic requirements remain unchanged.

I9 MEDIUM: missing real fresh-process recovery acceptance is covered by the
test-only worker candidate a1ebdc6c, integrated as df053bc2. Parent execution
found an agent-context error in the new assertion: the recovery-only card is
inside a top-level HOLD (exit2), not a READY/exit0 plan. Corrected the assertion;
the production gate was retained. The actual subprocess was killed after the
first runtime write; a new process recovered the persisted manifest despite
detached candidate loss/tampering. It also checked the immutable engine identity,
unchanged Git heads, candidate modes, pending-only plan and completed-replay
refusal. Native provider receipts in this fixture are explicitly simulated;
the test does not establish actual app wake or live assignment acceptance.

Bootstrap-publish audit HIGH (open): _team_remote rejects an initial v1 remote,
so the first v2 publication cannot obtain the required pre-action reservation;
_team_owner_transition then cannot confirm that operation without a real private
receipt. I10/I11 code convergence did not test this initial deployment sequence.
The scoped one-time repair and crash/replay criteria are proposed in the existing
Team Runtime plan section12. No canonical source/identity/watch change occurred.

Bootstrap plan pass Bp1: HIGH Unbound publication candidate; MEDIUM Intent
ordering ambiguity. Section12 now fixes a precommitted reviewed input-scope
digest and validates an exact closed candidate tree manifest, durably reserved
outside the committed checkpoint to avoid self-reference. It explicitly orders
the first owner-preserving migration and the second final PUBLISH/INTENT
checkpoint. Independent supplemental convergence remains pending.

Bp2 TOOL-FAILURE: the reviewer hashed section12 WITH its header, while the prompt
specified the body AFTER the header; actual source bytes did not drift. Its
preliminary HIGH correctly exposed unavailable final refresh hashes at the early
v1 intent. The revised order confirms local installation in v1 from a real local
commit under old control, migrates that CONFIRMED operation unchanged, and starts
a distinct exact v2 publication INTENT only after final bytes/refresh. Future
review inputs use an entire extracted immutable section file to avoid boundary
ambiguity. This finding is not a clean review or an artifact acceptance.

Bp3 HIGH Unresolved v1 operation replacement: explicit NONE/CONFIRMED entry
prerequisite added; validator must inspect the archived immediate predecessor.
Bp3 HIGH Remote predecessor race: a fixed expected-ref lease is paired with a
mandatory ancestor check, allowing only a conditional fast-forward update.
It cannot remove remote history; generic force/config/hook changes stay forbidden.
Tests must cover remote rollback/intermediate-ancestor races after observation.

Owner preflight corrected Bp4/Bp5 authority on2026-09-11: GOAL grants ordinary
non-force pushes and does not authorize even ancestry-restricted force-with-lease.
The isolated provisional option was removed before any execution; shared files
and remote were untouched. Section12 now states the actual non-force guarantee:
no remote commit loss, exact closed reviewed candidate and final readback;
the pre-reservation expected-tip observation is not an atomic remote CAS.
The earlier strict-CAS requirement was an unrequested strengthening. Intermediate
commits are scope/owner checked so reverted foreign changes cannot hide in the
published history. Bp4/Bp5 do not establish acceptance of these changed bytes.

Bp6/Bp7 CLEAN on the identical owner-corrected section12,10877bytes,
SHA256d61d48c2dc41aac4c29bb76681b9100248827f2175dd056bd7605fd17e16c0d7.
This closes supplemental plan review, not implementation or migration acceptance.

B1 HIGH Pending publication not fenced: a later registered checkpoint writer
could mutate the current RESUME/history between reservation and network push.
The existing pending-writer guard now recognizes RESERVED/UNKNOWN bootstrap
receipts before mutable control validation, and only the original bootstrap
reconciliation may enter. Plan displays its recovery-only command. No new lock
file or service; exact race/crash tests and artifact reconvergence are pending.

Parent found one direct entry contradiction during the required tool census:
tools_census.py:274 hardcoded codex-session-start as automatic startup while
TOOLS.yaml classifies it MANUAL and names workflow-runtime as the front door.
The catalogue now reads startup_and_control.front_door from that existing
manifest. This adds one existing source file to the exact migration scope;
it changes generated documentation only, not runtime selection or authority.



Parent full-tree startup rehearsal found the omitted final local commit barrier.
Bp8 static CLEAN covered schema transitions but missed actual dirty-control
startup; supplemental Bp8 HIGH confirmed that installing final control and
then saving a checkpoint before committing causes STARTUP_CONTROL_BLOB_DRIFT.
Section12 now requires a named final source/control commit before refresh and
checkpoint, and a clean declared startup surface after refresh. The real
registered local-init followed by plan returned HOLD with zero fatal errors;
the same full fixture with a dirty control returned FATAL as required.
The startup gate remains unchanged; no canonical files or identity were touched.


## 2026-09-11 — advice intake versus one owner and one native watch

Parallel Claude commit8477fd769721eacab272356acaf48cf4fcc6c61d added GOAL
section6 and ADVICE_PROTOCOL while the Team Runtime package was isolated.
The mathematical owner task01a084f4-7498-7021-bac2-91d184d58dc7 confirmed a
direct user instruction to read section6 and ADVICE_2026-09-11_SIBLING.md.
Its native handback to01a08f80-f033-7a31-8f3a-3aef042a3fbc confirms the scope:
keep section6 verbatim; intake committed advice using the SAME bridge and
owner, without changing the physical selector, phase or production admission.
The request for a victory-only mathematical answer does not suppress mandatory
runtime progress/failure reporting. The observer's separate review channel is
not permission for the executor to create another same-phase Proshka chat.
Advice is a bounded candidate to examine, not an accepted theorem.

Resolution: preserve the complete foreign commit/ancestry and section6 bytes;
rebaseline the exact GOAL preimage; record this interpretation here and in the
existing native watch prompt at activation. No new watcher, mathematical task,
owner change or unreviewed proof acceptance is introduced by the integration.


Post-review actual-entry finding, original native severity LOW:
`_team_continuation` at orchestrator/workflow_runtime.py attempted v2 ownership
observation on a valid legacy v1 checkpoint. Its correct migration HOLD was
accompanied by raw code "'ownership'". The parent reproduced this with an actual
CLI call; the independent reviewer confirmed a diagnostic defect, without any
change to authority or migration order. Local/actor observation is now limited
to v2. A regression failed on the original extra blocker and passed after the
single schema guard. Five targeted legacy/v2/foreign-owner/source-drift tests
PASS6.175s; actual CLI retains migration and replay holds, no fatal errors or
writes, and no raw KeyError. No schema/selector/guard authority was weakened.


Owner09f11c6a ADVICE_WATCH supersedes the earlier single-global-watch/10minute
wording with one watch per addressed task at5minutes; mathematical ownership
and single shared writer remain unchanged. The actual mathematical owner
confirmed this interpretation and updated the existing bridge natively.
Initial native inventory still needs to accept the previous10minute setting,
while final acceptance records actual5. The existing observation schema now
requires exact int cadence in{5,10} and exact int agent check20; floats/bools
are refused. Wp1 MEDIUM exposed the type ambiguity; Wp2/Wp3 CLEAN/CLEAN.
One new regression failed before the repair and the five targeted
watch/owner/legacy cases passed in5.703s after it. GOAL section6 remains verbatim.
Technical advice uses its own task/report evidence and cannot execute mathematics.
A shared HEAD is not an advice-processing cursor: another executor may advance
it first. Match addressed ADVICE content/commit against this task's own REPORT
or continuation evidence. No new cursor database or duplicate mathematical
watch is added; actual native creation/wake acceptance remains pending.


CADENCE430b9317f0ab154b02ff93a188a92723bd4179dc withdraws the observer's5minute figure; the preceding WATCH transition is historical and superseded, not canonical policy. The isolated uncommitted dual5/10 guard and GOAL section3 rewrite were never installed. The final candidate retains exact integer10/20 and the previous GOAL section3. Wp1's type finding still warrants rejecting floats/bools before private observation writes. Wp4/Wp5 CLEAN/CLEAN cover this narrowed correction. The mathematical owner already reconciled its actual temporary5minute bridge back to10 through the native tool, independently matched by read-only inventory. The technical task retains its separate10minute addressed-advice continuation under WATCH/CADENCE, no mathematical selector or shared write ownership. GOAL section6 is unchanged. Earlier unexecuted5minute CREATE intent is withdrawn; current intent and exact prompt are in plan section14.

Technical advice-watch origin mismatch: the isolated preparation clone's origin is the local canonical path. Polling that alias alone would wait for somebody else to update the shared clone, although advice was already published on GitHub. The technical prompt now resolves canonical origin and fetches its explicit URL into the isolated FETCH_HEAD, records the resulting commit, and compares advice hashes with its own report evidence. Actual direct read matched e6b5128d on https://github.com/Malaeu/chen_q3.git. No git config/shared HEAD change or mathematical-owner action is needed.


## 2026-09-11 — technical advice-report verdict scope

Source conflict: docs/Codex/ADVICE_PROTOCOL.md section4 and docs/Codex/ADVICE_2026-09-11_WATCH.md step2 reserve VICTORY for an asked statement proved or refuted with a witness at PAPER scope. The technical task initially labelled REPORT_2026-09-11_CADENCE_STROJKA.md VICTORY for a verified configuration/source correction. This was an agent reporting error, not mathematical proof or grounds to rewrite owner rules. Native reviewer R1 assigned HIGH. The header is now PARTIAL, the opening describes technical checks only, and the report explicitly retains pending canonical migration and scheduled-wake acceptance. REPORT_2026-09-11_WATCH_STROJKA.md was already PARTIAL and never claimed an actual wake. R2/R3 CLEAN/CLEAN verified the exact repaired reports; R1's original severity remains unchanged. No global rule, GOAL section6 or protocol was modified to silence the finding.
