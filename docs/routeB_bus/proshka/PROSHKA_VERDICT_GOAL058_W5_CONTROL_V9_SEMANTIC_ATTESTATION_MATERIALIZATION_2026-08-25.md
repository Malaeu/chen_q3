# STATUS: OPEN — REPAIR_W5_CONTROL_V9_SEMANTIC_ATTESTATION_MATERIALIZATION
```yaml
PRIMARY: REPAIR_W5_CONTROL_V9_SEMANTIC_ATTESTATION_MATERIALIZATION
OPERATIVE_CLASS: REPAIR_W5_CONTROL_V9_SEMANTIC_ATTESTATION_MATERIALIZATION
PRIMARY_COUNT: 1
DOCUMENT_ROLE: CONTROL_PLANE_ADJUDICATION

REQUEST:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  REQUEST_COMMIT: 38dd9f131aec0efb8a470ff4fa7ff7cbdbe9131a
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_CODEX_GOAL058_W5_CONTROL_V9_SEMANTIC_ATTESTATION_MATERIALIZATION_2026-08-25.md
  REQUEST_GIT_BLOB: 550d2c5f46ef0f5a360706bc193cc98ba56bb051
  ENTRY_ID: GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825

OPERATIVE_SEMANTIC_JUDGMENT:
  COMMIT: dd469b72ee3118a0257dd19296f3db7a02a05518
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CODEX_REQ_GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_SEMANTIC_ADMISSION_2026-08-25.md
  GIT_BLOB: b635ba98b2c465ffe271b0775afd174f74953c19
  OPERATIVE_CLASS: TRY_W5_QUANTITATIVE_SHIFTED_ENERGY_SEMANTIC_ADMISSION
  STATUS: AUTHORITATIVE_CURRENT_BRANCH_JUDGMENT

DUPLICATE_JUDGMENT:
  COMMIT: adcce6a6adab355884e76d2436693e7c43512cbe
  CURRENT_BRANCH_FILE_PRESENT: false
  REMOVAL_COMMIT: 21c1c9e97c7118eb7b86b5c2dc6c6c33444f006e
  CLASSIFICATION: HISTORICAL_REDUNDANT_DUPLICATE
  SEMANTIC_DISAGREEMENT_WITH_OPERATIVE_JUDGMENT: false
  MAY_SERVE_AS_ATTESTATION: false

CURRENT_QUARANTINE:
  PATH: orchestrator/state/SEMANTIC_QUARANTINE.json
  GIT_BLOB: dc819d8413954bb3330773a8c874388400d85762
  STATUS: KERNEL_GREEN
  ADMITTED_SCOPE: []
  SEMANTIC_ATTESTATION_ID: null
  DISPATCH_BARRIER: SEMANTIC_QUARANTINE_ACTIVE

CONTROL_PATH_AUDIT:
  POLICY_REQUIRES_EXTERNAL_RECEIPT: true
  CLOSED_RECEIPT_SCHEMA_IMPLEMENTED: true
  BYTE_FOR_FIELD_VALIDATOR_IMPLEMENTED: true
  INJECTED_RESOLVER_LIBRARY_SEAM_IMPLEMENTED: true
  TEST_ONLY_LAMBDA_RESOLUTION_IMPLEMENTED: true
  DURABLE_EXTERNAL_RESOLVER_IMPLEMENTED: false
  EXTERNAL_RECEIPT_REGISTRY_IMPLEMENTED: false
  ATOMIC_KERNEL_GREEN_TO_ADMITTED_MUTATOR_IMPLEMENTED: false
  CLI_ADMIT_COMMAND_IMPLEMENTED: false
  DEFAULT_VALIDATE_THREADS_RESOLVER: false
  DEFAULT_LAUNCH_THREADS_RESOLVER: false
  DEFAULT_GOAL_RUNTIME_THREADS_RESOLVER: false
  EXISTING_OPERATIVE_MATERIALIZATION_PATH: false

CLASS_DECISION:
  TRY: REJECTED_NO_EXISTING_OPERATIVE_RESOLVER_PATH
  KILL: REJECTED_RECEIPT_SCHEMA_CAN_REPRESENT_THE_ADMITTED_JUDGMENT_EXACTLY
  REPAIR: SELECTED

SELECTED_REPAIR:
  CODE: CONTROL_V9_LINUX_ATTESTATION_BROKER_AND_ATOMIC_ADMIT
  CONTROL_VERSION_AFTER_REPAIR: 9
  POLICY_SEMANTICS_CHANGED: false
  STATE_SCHEMA_CHANGED: false
  RECEIPT_SCHEMA_CHANGED: false
  REASON_NO_VERSION_BUMP: >-
    The repair materializes the already specified external-resolver seam and
    KERNEL_GREEN-to-SEMANTICALLY_ADMITTED transition without changing any
    closed field, issuer, status meaning, admission rule, or authority boundary.

  EXTERNAL_BROKER:
    SOCKET_PATH: /run/q3-control-v9/semantic-attestation.sock
    OWNER_ROLE: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
    QUERY_SCHEMA: q3_semantic_attestation_query.v1
    QUERY_FIELD: attestation_id
    RESPONSE_SCHEMA: q3_semantic_attestation.v1
    ISSUE_OPERATION_EXPOSED_TO_CODEX: false
    INLINE_RECEIPT_PAYLOAD_ACCEPTED_FROM_CODEX: false
    CALLER_SELECTED_RECEIPT_PATH_ACCEPTED: false
    FAILURE_IF_UNAVAILABLE: SEMANTIC_ATTESTATION_INVALID

  REPOSITORY_ADAPTER:
    RESOLVER_FUNCTION: resolve_linux_semantic_attestation
    INPUT: attestation_id
    OUTPUT: closed q3_semantic_attestation.v1 object or null
    TRANSPORT: fixed Unix-domain socket only
    SHELL_INVOCATION: false
    ENVIRONMENT_PATH_OVERRIDE: false

  ATOMIC_TRANSITION:
    FUNCTION: materialize_semantic_admission
    CLI: semantic-admit
    CLI_ARGUMENTS:
      - entry-id
      - attestation-id
    FORBIDDEN_CLI_ARGUMENTS:
      - receipt-path
      - receipt-json
      - issuer
      - admitted-scope
      - source-commit
      - source-blob
    LOCK: existing stable Control-v9 flock
    IDEMPOTENCY: same entry and same attestation ID returns no-op
    CONFLICT: different attestation ID or non-KERNEL_GREEN source state fails closed
    MUTABLE_FIELDS_ONLY:
      - status
      - admitted_scope
      - semantic_attestation_id
    ADMITTED_SCOPE_SOURCE: externally resolved receipt
    WRITE_ORDER:
      - resolve receipt
      - construct candidate state in memory
      - validate complete candidate with the same resolver
      - atomically replace tracked state

  RESOLVER_THREADING:
    - three_body_loop validate
    - three_body_loop launch internal preflight
    - goal_runtime selection
    - goal_runtime runtime-state validation
    - any dispatch-clear check

W5_MATERIALIZATION_LOCK:
  ATTESTATION_ID: ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
  ADMITTED_SCOPE:
    - W5_FIXED_K_QUANTITATIVE_FOURIER_DECAY_EXACT_W4_BUDGET
    - W5_FIXED_K_LITERAL_SHIFTED_FORM_ENERGY_MAJORANT

  EXACT_STATE_DELTA:
    status:
      FROM: KERNEL_GREEN
      TO: SEMANTICALLY_ADMITTED
    admitted_scope:
      FROM: []
      TO:
        - W5_FIXED_K_QUANTITATIVE_FOURIER_DECAY_EXACT_W4_BUDGET
        - W5_FIXED_K_LITERAL_SHIFTED_FORM_ENERGY_MAJORANT
    semantic_attestation_id:
      FROM: null
      TO: ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
    ALL_OTHER_ENTRY_FIELDS: BYTE_IDENTICAL

  EXACT_RECEIPT:
    schema: q3_semantic_attestation.v1
    attestation_id: ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
    issuer: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
    status: ADMITTED
    control_version: 9
    task_path: docs/Codex/TASK_2026-08-25_goal058_w5_quantitative_shifted_energy.md
    task_blob: 5e9d7835cb4a31947000006cdbaecd85b40dbff3
    source_commit: d50e1899261c7b318e5d9a3c1977fcba18a7e79c
    source_git_blob: 5205b76c962a01411dffbe6ded97bf2eaa6fd313
    theorem_ids:
      - Q3.RouteB.D0Pstar.selectedFerrersAbelLogZeroExtension_fourier_decay_quantitative
      - Q3.RouteB.D0Pstar.selectedFerrersAbelLimit_shiftedEnergy_le_majorant
    admitted_scope:
      - W5_FIXED_K_QUANTITATIVE_FOURIER_DECAY_EXACT_W4_BUDGET
      - W5_FIXED_K_LITERAL_SHIFTED_FORM_ENERGY_MAJORANT
    terminal_consumer: W5 cofinal selected-Ferrers shifted-energy rate
    closes:
      - W5_QUANTITATIVE_SHIFTED_ENERGY_EXTRACTION
    opens:
      - W5_COFINAL_PACKET_BUDGET_RATE
    normalization: production selectedFerrersLemma73SourcePacket with the repaired full-endpoint W4 jump ledger and literal shifted Archimedean symbol
    domain: literal selected-Ferrers additive-log packet on the production source window and the whole Fourier line
    quantifiers: for every k : Nat; the universal envelope is independent of k and all remaining k-dependence is explicit in the W4 packet budget
    hypothesis_provenance_sha256: 4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945

VALIDATION_GATE_AFTER_IMPLEMENTATION:
  TARGETED_TESTS:
    - python3 -m unittest orchestrator.tests.test_three_body_loop
    - python3 -m unittest orchestrator.tests.test_goal_runtime
  MATERIALIZATION_COMMAND: >-
    python3 orchestrator/three_body_loop.py semantic-admit
    --entry-id GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825
    --attestation-id ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
  STATE_VALIDATION_COMMAND: python3 orchestrator/three_body_loop.py validate
  REQUIRED_RESULT:
    - current entry is SEMANTICALLY_ADMITTED
    - admitted scope is the exact two-item list above
    - semantic attestation ID is exact
    - dispatch-clear validation no longer raises SEMANTIC_QUARANTINE_ACTIVE
    - no other quarantine field changes

MANDATORY_PLANTS:
  - broker unavailable rejects admission
  - unknown attestation ID rejects admission
  - wrong issuer rejects admission
  - any receipt field drift rejects admission
  - arbitrary receipt path is not an accepted interface
  - inline JSON receipt is not an accepted interface
  - SOURCE_WRITTEN entry cannot be admitted
  - second different attestation ID cannot replace an admitted receipt
  - pre-admission KERNEL_GREEN still blocks dispatch
  - post-admission valid external receipt clears only the quarantine barrier

SELECTED_REPRESENTATION:
  CODE: FIXED_EXTERNAL_BROKER_PLUS_ATOMIC_STATE_TRANSITION
  KILL_POWER: 10
  COST: 4

RUNNER_UP_NOT_SELECTED:
  CODE: TRACKED_RECEIPT_PLUS_DETACHED_PUBLIC_KEY_SIGNATURE
  KILL_POWER: 10
  COST: 7
  REASON: >-
    It is durable across machines but adds key management and signature tooling
    not required to materialize the existing resolver abstraction.

FORBIDDEN_REPAIRS:
  - treat the Proshka markdown verdict as q3_semantic_attestation.v1
  - accept an unsigned tracked receipt through a built-in repo resolver
  - let Codex pass receipt JSON, receipt path, issuer or admitted scope
  - set status to SEMANTICALLY_ADMITTED without resolving the receipt
  - delete or retire the quarantine entry to evade admission
  - mutate theorem statements, Lean source, W4 artifacts, Route state or RH-facing artifacts

CLOSES:
  - W5_CONTROL_V9_ATTESTATION_PATH_ADJUDICATION
OPENS:
  - CONTROL_V9_LINUX_ATTESTATION_BROKER_AND_ATOMIC_ADMIT

ARSENAL_MANDATE:
  ACCEPTED: true
  SIDECAR_EXECUTION_TRIGGERED: false
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

QUEUE_AUDIT:
  OLDER_OPEN_REQUEST_BLOCKING_THIS_ADJUDICATION: false
  CURRENT_DIRECT_REQUEST_IN_QUEUE: false

PREDICTION_LEDGER:
  PRIOR_REGISTERED_PREDICTIONS_FOR_THIS_REQUEST: NONE
  RETROACTIVE_PREDICTION_MINTED: false

REGISTERED_PREDICTIONS_FOR_REPAIR:
  P_CTRL_W5_1:
    probability: 0.92
    prediction: the existing closed receipt validator accepts the exact W5 receipt without a state-schema or control-version change
  P_CTRL_W5_2:
    probability: 0.86
    prediction: the first implementation defect will be incomplete resolver threading through launch or goal_runtime rather than a receipt field mismatch
  P_CTRL_W5_3:
    probability: 0.99
    prediction: no Lean source or mathematical theorem change is required
  LIKELIEST_FAILURE: RESOLVER_NOT_THREADED_THROUGH_ALL_DISPATCH_ENTRY_POINTS

AUTOPSY:
  - dropped=DEPENDENCY; note=Control v9 defines a resolver callback and closed receipt validator but wires no durable resolver or state transition into production entry points.
  - dropped=TRUST; note=An unsigned tracked receipt or caller-selected path would allow Codex to self-resolve the authority it is forbidden to possess.

SCOPE: ABSTRACT
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
QUARANTINE_STATE_MUTATED_BY_THIS_VERDICT: false
LEAN_EDIT: false
CONTROL_EDIT_AUTHORIZED_BY_THIS_VERDICT: false
DOWNSTREAM_W5_DISPATCH_AUTHORIZED: false
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Item | Verdict | Exact boundary | Tags |
|---|---|---|---|
| W5 mathematical semantic judgment | **OPERATIVE** | Commit `dd469b72...` and current blob `b635ba98...` admit exactly fixed-`k` quantitative Fourier decay and the literal shifted-form energy majorant. This request does not reopen that judgment. | `[COFINAL_FAMILY][LEAN]` |
| Raced duplicate | **REDUNDANT** | Commit `adcce6a6...` agreed semantically, but its duplicate file was removed by `21c1c9e...`; it is history, not a second operative judgment or receipt. | `[ABSTRACT][PAPER]` |
| Closed receipt schema and validator | **PRESENT** | `three_body_loop.py` has the exact closed fields and byte-for-field comparison required by Control v9. | `[ABSTRACT][PAPER]` |
| Durable external resolver | **ABSENT** | Repository search finds no receipt registry, authority broker, default resolver, or production resolver adapter. | `[ABSTRACT][PAPER]` |
| State-transition writer | **ABSENT** | The CLI exposes `validate`, request validation, launch, and read-only watch, but no semantic-admission transition. | `[ABSTRACT][PAPER]` |
| Existing TRY path | **REJECTED** | A callback type used by tests is not an operative materialization path. Default validation and dispatch call the state loader without a resolver. | `[ABSTRACT][PAPER]` |
| KILL of W5 admission | **REJECTED** | The exact prior judgment fits every closed receipt field; the failure is control plumbing, not semantic incompatibility. | `[COFINAL_FAMILY][PAPER]` |
| Selected repair | **OPEN** | Add one fixed Linux authority broker, one resolver adapter, one atomic transition, and thread the resolver through every dispatch gate. | `[ABSTRACT][CONDITIONAL]` |

## FINAL PROPOSAL

Freeze the mathematical judgment at `dd469b72...`. Do not ask for another W5 semantic review.

Implement one bounded **control-only** transaction named:

```text
CONTROL_V9_LINUX_ATTESTATION_BROKER_AND_ATOMIC_ADMIT
```

The transaction must preserve Control version 9, the quarantine schema and the receipt schema. It must not accept an inline receipt, caller-selected path, issuer or scope. The external Linux broker is the sole authority source; repository code only resolves an already issued ID and performs the validated three-field state transition.

After the repair is green, the independent Linux auditor issues the exact receipt frozen above. The control plane then performs the exact state delta. Only after `validate` and dispatch-clear tests are green may the next mathematical target be `W5_COFINAL_PACKET_BUDGET_RATE`.

This verdict itself changes no quarantine state and authorizes no downstream mathematical dispatch.

## STRONGEST ATTACK

### Attack 1 — use the Proshka verdict itself as the receipt

Rejected. The verdict is the semantic judgment. Control v9 requires a different closed object, a different issuer and an externally resolved authority path. Treating Markdown as the receipt collapses judge and admission transport into one object. **[C04][C10]**

### Attack 2 — add a tracked JSON file and let the default resolver read it

Rejected unless independently authenticated. Codex already has repository write authority inside its goal scope. An unsigned tracked file would allow Codex to mint the receipt and then resolve its own work, violating the central three-body separation. **[C09]**

### Attack 3 — the missing resolver means the semantic admission must be killed

Rejected. The exact W5 theorem IDs, source bytes, task bytes, normalization, domain, quantifiers, `CLOSES`, `OPENS` and empty canonical provenance digest fit the existing receipt schema without weakening or reinterpretation. The gap is executable control plumbing.

### Attack 4 — delete the quarantine entry and continue

Rejected. Deletion erases the required tracked transition and converts a control defect into silent history loss. No retirement mechanism was authorized by the request.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION AUTHORIZED BY THIS VERDICT.

Do not edit Lean.
Do not mutate SEMANTIC_QUARANTINE.json.
Do not create or self-resolve a semantic receipt.
Do not start W5_COFINAL_PACKET_BUDGET_RATE.
Do not edit docs/CODEX_CONTROL.md or orchestrator code without a separate explicit owner grant for the named control-only repair.

Next admissible implementation target under such a grant:
  CONTROL_V9_LINUX_ATTESTATION_BROKER_AND_ATOMIC_ADMIT
```

## META CLOSEOUT

**What became smaller?**

The blocker is no longer “semantic admission cannot be materialized.” It is one exact missing control component: a fixed external Linux resolver plus an atomic three-field transition.

**What was killed?**

- interpreting the test-only callback seam as a production path;
- treating the Proshka verdict as the Linux receipt;
- unsigned tracked-receipt self-resolution;
- deleting quarantine to bypass the transition;
- killing a mathematically compatible admission because of missing plumbing.

**What must not be tried again?**

Do not mint another W5 semantic verdict. Do not pass receipt bytes or scope from Codex. Do not change theorem semantics to fit the control implementation.

**Current smallest named gap:**

```text
CONTROL_V9_LINUX_ATTESTATION_BROKER_AND_ATOMIC_ADMIT
```

**Next cheapest decisive test:**

Run the existing closed receipt validator against the exact frozen receipt via the future broker, then verify that only `status`, `admitted_scope` and `semantic_attestation_id` change and that dispatch-clear succeeds.

**Fate of prior registered predictions:**

No prior prediction existed for this control request; none was created retroactively.

**Memory entry:**

```yaml
iteration:
  target: W5 Control-v9 external semantic-attestation materialization
  status: OPEN
  failed_strategy: treat injected test callback as an operative external path
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: CONTROL_V9_LINUX_ATTESTATION_BROKER_AND_ATOMIC_ADMIT
  invariant_learned: semantic judgment, receipt issuance, receipt resolution and state mutation are four distinct powers
  forbidden_future_move: unsigned tracked receipt or caller-supplied receipt path
  next_decisive_test: exact frozen W5 receipt through a fixed external broker and atomic three-field state transition
```
