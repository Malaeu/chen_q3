# STATUS: RUN_SOURCE_LOCK_BINDING_PREFLIGHT
```yaml
OPERATIVE_CLASS: RUN_SOURCE_LOCK_BINDING_PREFLIGHT
PRIMARY: BIND_THREE_STAGE_FASTEST_KILL_PLAN_BEFORE_ADJUDICATION
PRIMARY_COUNT: 1
DATE: 2026-09-03

CONTROL_PLANE:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: f1adecb9e22672b47913bbf2df10475bf6796cfe
  PROTOCOL_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  PROTOCOL_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4

REQUEST_INTAKE:
  RECEIVED_AS: CHAT_PASTE
  BYTE_EXACT_UTF8_TXT_ATTACHMENT: false
  CANONICAL_SHORT_INSTRUCTION: MISSING
  REQ_ID: MISSING
  REVIEW_PLAN_BINDING: MISSING
  REQUEST_REPO_PIN: MISSING
  REQUEST_BLOB_OR_SHA256: MISSING
  REVIEW_BOUNDARY: MISSING
  EXPECTED_DELIVERABLE_PATH: MISSING
  SOURCE_LOCK_CONSISTENT: false

ADJUDICATION:
  MATHEMATICAL_AUDIT_PERFORMED: false
  STEP_1_CHARACTERIZATION_CLAIM_JUDGED: false
  STEP_2_RELLICH_COFINAL_CLAIM_JUDGED: false
  STEP_3_GAP_TRACKING_CLAIM_JUDGED: false
  USER_PREDICTION_P_0_75_SCORED: false
  REASON: SOURCE_LOCKED_REQUEST_INTAKE_NOT_SATISFIED

ROUTE_EFFECT:
  ROUTE_FAMILY_KILLED: false
  THEOREM_SHAPE_KILLED: false
  ATTEMPT_KILLED: false
  ROUTE_MUTATION: false
  COUNT_MUTATION: false
  CLAIM_MUTATION: false

CLOSES:
  - UNBOUND_ADJUDICATION_ATTEMPT
OPENS: []

REQUIRED_BINDING_PACKET:
  FORMAT: BYTE_EXACT_UTF8_TXT
  REQUIRED_FIELDS:
    - REQ_ID
    - CANONICAL_SHORT_INSTRUCTION
    - REPO
    - BRANCH
    - PIN
    - REQUEST_PATH_OR_ATTACHMENT_NAME
    - REQUEST_SHA256_OR_GIT_BLOB
    - REVIEW_BOUNDARY
    - AUTHORIZED_WRITE_SCOPE
    - EXPECTED_VERDICT_PATH
    - REGISTERED_PREDICTIONS
  CONTENT_RULE: PRESERVE_THE_THREE_STAGE_PLAN_BYTE_FOR_BYTE
  PREDICTION_RULE: PRESERVE_P_STEP1_0_75_WITHOUT_RETROACTIVE_EDIT

DOWNSTREAM_CONSUMER: PROSHKA_FAIL_CLOSED_ROUTE_ADJUDICATION
ACTUAL_CONSUMER_REQUIREMENT: ONE_BOUND_BYTE_EXACT_REQUEST_WITH_PIN_AND_BOUNDARY
ORIGINAL_REQUESTED_OBJECT: THREE_STAGE_FASTEST_KILL_PATH_TO_RH
ORIGINAL_OBJECT_IS: UNKNOWN
KNOWN_WEAKER_INTERFACES: []
FAILURE_TYPE: NO_SOURCE
EPISTEMIC_STATUS: UNRESOLVED
NOVELTY_AXIS: TRANSPORT_AND_PREDICTION_INTEGRITY
REOPEN_TRIGGER: BOUND_REQUEST_PACKET_WITH_MATCHING_HASH_AND_REVIEW_PLAN_BINDING

REGISTERED_PREDICTION:
  P_BIND_1:
    statement: the exact bound request will permit a decisive paper-first audit without Lean source edits
    probability: 0.98
    fate: PENDING

CHEAPEST_DECISIVE_TEST:
  name: REQUEST_HASH_AND_BINDING_CHECK
  pass: attachment_bytes_sha256_equals_registered_request_sha256_and_pin_exists
  fail: any_missing_or_mismatched_binding_field

LIKELIEST_FAILURE:
  code: REQUEST_BOUNDARY_OR_PREDICTION_DRIFT
  response: reject_adjudication_and_require_new_append_only_request

NEXT_LOAD_BEARING_GAP: SOURCE_LOCKED_THREE_STAGE_PLAN_REQUEST

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 4

DELIVERY:
  DOC_ONLY: true
  LEAN_FILES_WRITTEN: []
  LEAN_GATE_REQUIRED: false
  EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE
```

## ROUTE MAP

The supplied three-stage plan remains an unjudged candidate. The current protocol accepts only one byte-exact UTF-8 `.txt` request selected and bound by the registered review plan. The chat paste has no request ID, repository pin, blob or SHA-256, review boundary, or canonical short instruction. A deep verdict would therefore create an unauditable opportunity for post-hoc text and prediction drift.

No mathematical route, theorem shape, or claim is killed by this finding. Only the unbound adjudication attempt is closed.

## FINAL PROPOSAL

Materialize the exact chat payload as one bound request without rewriting it. Preserve the stated K6 prediction `p = 0.75`. Register the request path, SHA-256 or Git blob, repository pin, review boundary, and expected verdict path. Then resubmit the canonical short instruction. The first authorized audit should be paper-only and should test Step 1 before any Lean source is written.

## STRONGEST ATTACK

The strongest objection is not mathematical yet: without a byte-exact request lock, the three steps and the prediction can change between proposal, audit, and scoring. That would make any later `CONFIRMED` or `REFUTED` classification non-reproducible. The repair is exact request binding, not interpretation of the chat paste.

## CODEX DIRECTIVE

```text
TASK: Bind the three-stage fastest-kill RH plan as one byte-exact UTF-8 request.

DO:
1. Copy the user payload byte-for-byte into the registered request location.
2. Assign one REQ-ID and one canonical short instruction.
3. Record repo, branch, immutable commit pin, file Git blob and SHA-256.
4. Record review boundary: paper adjudication only; no Lean source and no route promotion.
5. Preserve the registered prediction P_STEP1_NO_UNIQUENESS with p=0.75 exactly.
6. Register the request in the review plan before delivery.

DO NOT:
- paraphrase the plan;
- alter the probability;
- add results after the prediction;
- select another request from repository OPEN markers;
- authorize Lean or numerical execution.

SUCCESS:
SOURCE_LOCKED_THREE_STAGE_PLAN_REQUEST_READY

FAILURE:
SOURCE_LOCK_BINDING_OR_HASH_MISMATCH
```

## META CLOSEOUT

- **What became smaller?** The blocker is reduced to one transport object: a bound request packet.
- **What was killed?** Only the unbound-adjudication attempt.
- **What must not be tried again?** Do not issue a deep mathematical verdict from mutable chat prose under the current intake protocol.
- **Current smallest named gap:** `SOURCE_LOCKED_THREE_STAGE_PLAN_REQUEST`.
- **Next cheapest decisive test:** compare the attached request bytes with the registered SHA-256 and verify the commit pin.
- **Prior predictions:** none scored. The user's `p=0.75` remains unscored and must be preserved in the bound request.

```yaml
iteration:
  target: three-stage fastest-kill RH plan intake
  status: OPEN
  failed_strategy: unbound_chat_adjudication
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: SOURCE_LOCKED_THREE_STAGE_PLAN_REQUEST
  invariant_learned: prediction_and_request_bytes_must_be_fixed_before_testing
  forbidden_future_move: deep_verdict_from_unbound_chat_payload
  next_decisive_test: request_hash_and_binding_check
```

## DEPENDENCY EPISTEMICS

```yaml
DOWNSTREAM_CONSUMER: PROSHKA_FAIL_CLOSED_ROUTE_ADJUDICATION
ACTUAL_CONSUMER_REQUIREMENT: ONE_BOUND_BYTE_EXACT_REQUEST_WITH_PIN_AND_BOUNDARY
ORIGINAL_REQUESTED_OBJECT: THREE_STAGE_FASTEST_KILL_PATH_TO_RH
ORIGINAL_OBJECT_IS: UNKNOWN
KNOWN_WEAKER_INTERFACES: []
FAILURE_TYPE: NO_SOURCE
EPISTEMIC_STATUS: UNRESOLVED
NOVELTY_AXIS: TRANSPORT_AND_PREDICTION_INTEGRITY
KILL_SCOPE: NONE
KILL_EVIDENCE_KIND: NONE
REOPEN_TRIGGER: BOUND_REQUEST_PACKET_WITH_MATCHING_HASH_AND_REVIEW_PLAN_BINDING
```

## VERIFICATION HANDOFF

This commit writes documentation only. No Lean source changed, so no `lake`, module build, `q3_check`, or axiom-profile gate applies. The Linux body only needs to verify that the path exists in `rh_clean`, the commit is a direct branch update, and the file begins with the declared operative class.