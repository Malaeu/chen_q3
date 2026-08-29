# STATUS: CONDITIONAL — TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT
```yaml
PRIMARY: TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT
OPERATIVE_CLASS: TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT
PRIMARY_COUNT: 1
DOCUMENT_ROLE: CONTROL_V9_CROSS_HOST_TRANSPORT_ADJUDICATION

REQUEST_LOCK:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  REQUEST_COMMIT: ea553fb4c818c10162f578258cc4d30671dce5cf
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_CONTROL_V9_CROSS_HOST_SEMANTIC_ATTESTATION_TRANSPORT_2026-08-29.md
  REQUEST_GIT_BLOB: 4a697a6755890c6d42dd1d15f173068a2545a258
  REQUEST_SOURCE_HEAD: 9ac216dcdd47f6a0b3c56ca17bd4255bcebee3b9
  REVIEW_BASE_HEAD: 9a44db6139634e3464bf5d9393c02ddde7e798aa

CURRENT_OBJECT:
  CONTROL_VERSION: 9
  QUARANTINE_ENTRY: GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825
  ATTESTATION_ID: ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
  STATUS: SEMANTICALLY_ADMITTED
  ADMITTED_SCOPE:
    - W5_FIXED_K_QUANTITATIVE_FOURIER_DECAY_EXACT_W4_BUDGET
    - W5_FIXED_K_LITERAL_SHIFTED_FORM_ENERGY_MAJORANT
  OPEN_MATHEMATICAL_GAP:
    - W5_COFINAL_PACKET_BUDGET_RATE
  MATHEMATICAL_JUDGMENT_REOPENED: false

DEFECT:
  CODE: CONTROL_V9_MAC_STARTUP_FIXED_LINUX_SOCKET_UNAVAILABLE
  MAC_PLATFORM: Darwin
  FIXED_SOCKET: /run/q3-control-v9/semantic-attestation.sock
  SOCKET_PRESENT_ON_MAC: false
  REMOTE_SSH_ENDPOINT_LIVE: false
  STRICT_STARTUP_RESULT: SEMANTIC_ATTESTATION_INVALID
  ROOT_CAUSE: >-
    The production resolver binds every startup to a Unix-domain socket and a
    receipt registry that exist only on the independent Linux auditor host.
    The authority boundary is correct, but the selected transport is not
    cross-host available.

CLASS_DECISION:
  TRY_CONTROL_V9_AUTHENTICATED_REMOTE_ATTESTATION_RESOLUTION:
    status: VALID_BUT_NOT_SELECTED
    reason: >-
      A mutually authenticated live lookup can preserve independence, but it
      makes the complete Mac executor unavailable whenever the Linux auditor,
      network path, endpoint discovery, or tunnel is unavailable. That is an
      explicit online service design, not an offline-safe cross-host design.
    whole_mac_executor_offline_when_linux_unavailable: true

  TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT:
    status: SELECTED
    reason: >-
      A detached signature by the independent Linux auditor preserves receipt
      authenticity and byte binding while allowing strict Mac startup with the
      Linux host and its socket fully offline. Codex may transport or alter
      tracked bytes but cannot manufacture a valid signature.

  REPAIR_CONTROL_V9_CROSS_HOST_ATTESTATION_ARCHITECTURE:
    status: NOT_REQUIRED
    reason: >-
      The existing resolver seam and exact receipt validator remain valid. The
      signed-offline resolver returns the unchanged q3_semantic_attestation.v1
      object, so no admission meaning, state schema, receipt schema, or authority
      boundary changes.

CONTROL_VERSION_DECISION:
  VERSION_AFTER_IMPLEMENTATION: 9
  VERSION_BUMP_REQUIRED: false
  RECEIPT_SCHEMA_CHANGED: false
  QUARANTINE_SCHEMA_CHANGED: false
  ADMISSION_RULE_CHANGED: false
  AUTHORITY_ROLE_CHANGED: false

SIGNED_OFFLINE_TRANSPORT:
  SCHEME: OPENSSH_SSHSIG
  KEY_TYPE: ssh-ed25519
  HASH_ALGORITHM: sha512
  SIGNATURE_NAMESPACE: q3-control-v9-semantic-attestation
  SIGNER_PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR

  PRIVATE_KEY:
    LOCATION_LINUX: /var/lib/q3-control-v9/private/semantic-attestation-ed25519
    OWNER: independent Linux semantic auditor account
    MODE: "0600"
    AVAILABLE_TO_CODEX: false
    AVAILABLE_TO_MAC_COMMITTING_BODY: false
    TRACKED_IN_REPOSITORY: false

  MAC_TRUST_ROOT:
    ALLOWED_SIGNERS_PATH: /etc/q3-control-v9/semantic_attestation_allowed_signers
    REVOCATION_PATH: /etc/q3-control-v9/semantic_attestation_revoked_ids.v1.json
    OWNER_UID: 0
    REQUIRED_FILE_TYPE: regular_file_not_symlink
    REQUIRED_DIRECTORY_OWNER_UID: 0
    REQUIRED_DIRECTORY_GROUP_OR_WORLD_WRITABLE: false
    REQUIRED_FILE_GROUP_OR_WORLD_WRITABLE: false
    MISSING_OR_UNSAFE_TRUST_RESULT: CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID

  ALLOWED_SIGNERS_FORMAT: >-
    Exactly one active line: principal
    LINUX_INDEPENDENT_SEMANTIC_AUDITOR, option
    namespaces="q3-control-v9-semantic-attestation", and one ssh-ed25519
    public key. No wildcard principal and no second active key are accepted.

  TRACKED_BUNDLE:
    DIRECTORY: orchestrator/attestations/control-v9
    RECEIPT_PATH_TEMPLATE: orchestrator/attestations/control-v9/{attestation_id}.receipt.json
    SIGNATURE_PATH_TEMPLATE: orchestrator/attestations/control-v9/{attestation_id}.receipt.sshsig
    PATH_SOURCE: strict attestation_id token only
    CALLER_SELECTED_PATH: forbidden
    ENVIRONMENT_PATH_OVERRIDE: forbidden
    INLINE_RECEIPT: forbidden

EXACT_SIGNED_BYTES:
  INNER_SCHEMA: q3_semantic_attestation.v1
  JSON_ENCODING: UTF-8
  DUPLICATE_KEYS: rejected
  CANONICAL_FORM: >-
    json.dumps(receipt, ensure_ascii=False, sort_keys=True,
    separators=(",", ":")).encode("utf-8") followed by exactly one LF byte.
  SIGNED_PAYLOAD: exact complete receipt file bytes including the final LF
  VERIFY_ORDER:
    - read raw receipt bytes and detached signature
    - verify SSHSIG over the raw bytes before JSON parsing
    - parse as unique-key UTF-8 JSON
    - require raw bytes equal the canonical form plus one LF
    - require exact attestation_id
    - pass the unchanged parsed receipt to the existing Control-v9 validator
  PARSED_OR_RESERIALIZED_BYTES_MAY_BE_SIGNED_INSTEAD: false

REPLAY_AND_REVOCATION:
  SAME_ID_SAME_BYTES_REPLAY: idempotently accepted
  SAME_ID_DIFFERENT_BYTES: signature or exact-field validation fails closed
  DIFFERENT_ID: separate independently signed bundle required
  REVOCATION_SCHEMA: q3_semantic_attestation_revocations.v1
  REVOCATION_FIELDS:
    - schema
    - revoked_attestation_ids
  REVOKED_ID_RESULT: CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED
  LIVE_NETWORK_REVOCATION_REQUIRED: false
  REVOCATION_FRESHNESS: >-
    Snapshot-based. The Mac trusts only the currently installed root-owned
    revocation file. This design makes no claim of live revocation freshness.
  KEY_COMPROMISE_RESPONSE:
    - remove the old public key from the Mac trust root
    - generate a new auditor-controlled Ed25519 key
    - re-sign every still-live receipt byte-for-byte
    - install the new bundles
    - atomically install an allowed-signers file containing only the new key
  DUAL_KEY_GRACE_WINDOW: forbidden
  OLD_KEY_AFTER_ROTATION: rejected

STARTUP_SEMANTICS:
  MAC_RESOLVER: resolve_signed_offline_semantic_attestation
  LINUX_AUDITOR_RESOLVER: existing resolve_linux_semantic_attestation may remain
  PLATFORM_SELECTION: fixed by trusted program logic, not environment input
  REMOTE_FALLBACK_ON_MAC: forbidden
  CACHE_OF_PREVIOUSLY_PARSED_RECEIPT: forbidden
  STATE_MUTATION_DURING_VALIDATE: forbidden
  ALL_ENTRY_POLICY: >-
    Before any Mac dispatch, enumerate every quarantine entry. Every
    SEMANTICALLY_ADMITTED entry must have one valid, non-revoked, signed bundle
    whose parsed receipt passes the existing exact validator. One missing or
    invalid bundle fails the complete startup; partial validation and status
    downgrade are forbidden.
  KERNEL_GREEN_ENTRY: remains quarantined and does not become admitted from a bundle alone
  LINUX_HOST_REQUIRED_DURING_MAC_STARTUP: false
  NETWORK_REQUIRED_DURING_MAC_STARTUP: false

FAILURE_CODES:
  - CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING
  - CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID
  - CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID
  - CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED
  - CONTROL_V9_OFFLINE_ATTESTATION_RECEIPT_INVALID
  - CONTROL_V9_OFFLINE_ATTESTATION_ALL_ENTRY_VALIDATION_FAILED
  - SEMANTIC_ATTESTATION_INVALID

MANDATORY_PLANTS:
  - Linux socket absent and network unavailable, valid signed bundle passes Mac startup
  - missing receipt fails closed
  - missing detached signature fails closed
  - one-byte receipt mutation fails signature verification
  - signature by an unpinned key fails
  - wrong signer principal fails
  - wrong SSHSIG namespace fails
  - group-or-world-writable trust file fails
  - symlinked trust or revocation file fails
  - revoked attestation ID fails despite a valid signature
  - valid signature over a receipt with one quarantine field drift fails exact validation
  - unsigned tracked JSON never resolves
  - caller-selected receipt path and environment override are rejected
  - one valid bundle plus one missing bundle among two admitted entries fails whole startup
  - validation never edits SEMANTIC_QUARANTINE.json

VALIDATION_GATE_AFTER_IMPLEMENTATION:
  WORKDIR: repository root
  TESTS: >-
    python3 -m unittest
    orchestrator.tests.test_signed_offline_semantic_attestation
    orchestrator.tests.test_three_body_loop
    orchestrator.tests.test_goal_runtime
  MANUAL_SIGNATURE_CHECK: >-
    /usr/bin/ssh-keygen -Y verify
    -f /etc/q3-control-v9/semantic_attestation_allowed_signers
    -I LINUX_INDEPENDENT_SEMANTIC_AUDITOR
    -n q3-control-v9-semantic-attestation
    -s orchestrator/attestations/control-v9/{attestation_id}.receipt.sshsig
    < orchestrator/attestations/control-v9/{attestation_id}.receipt.json
  MAC_STATE_CHECK: python3 orchestrator/three_body_loop.py validate
  MAC_GOAL_CHECK: python3 orchestrator/goal_runtime.py --json
  STATE_IMMUTABILITY_CHECK: git diff --exit-code -- orchestrator/state/SEMANTIC_QUARANTINE.json
  REQUIRED_RESULTS:
    - signature verification exit code is zero
    - THREE_BODY_STATE_VALID
    - goal_runtime returns valid JSON without SEMANTIC_ATTESTATION_INVALID
    - test -S /run/q3-control-v9/semantic-attestation.sock remains false on Mac
    - Linux auditor host may be unreachable throughout the Mac gate
    - every SEMANTICALLY_ADMITTED entry is validated
    - tracked quarantine bytes remain unchanged

CLOSES:
  - CONTROL_V9_CROSS_HOST_ATTESTATION_TRANSPORT_ARCHITECTURE
  - CONTROL_V9_MAC_STARTUP_LIVE_LINUX_DEPENDENCY
OPENS:
  - CONTROL_V9_SIGNED_OFFLINE_RESOLVER_IMPLEMENTATION
  - CONTROL_V9_SIGNED_RECEIPT_EXPORT_AND_MAC_TRUST_INSTALL
  - CONTROL_V9_ALL_ENTRY_OFFLINE_STARTUP_GATE
NEXT_LOAD_BEARING_GAP: CONTROL_V9_SIGNED_OFFLINE_RESOLVER_IMPLEMENTATION

MATHEMATICAL_BOUNDARY:
  W5_THEOREMS_CHANGED: false
  W5_ADMITTED_SCOPE_CHANGED: false
  W5_MATHEMATICAL_VERDICT_CHANGED: false
  W5_COFINAL_RATE_CLOSED: false
  DOWNSTREAM_ROUTE_STATUS_CHANGED: false
  ROUTE_PROMOTION: false
  RH_CLAIM: false

ARSENAL_MANDATE:
  ACCEPTED: true
  SIDECAR_EXECUTION_TRIGGERED: false
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

PREDICTION_FATE:
  PRIOR_ONLINE_BROKER_EQUAL_KILL_POWER: CONFIRMED
  PRIOR_ONLINE_BROKER_LOWER_TOTAL_COST: REFUTED_BY_CANONICAL_MAC_STARTUP_DEFECT
  PRIOR_SIGNED_OFFLINE_EQUAL_KILL_POWER: CONFIRMED
  PRIOR_NO_LEAN_CHANGE_REQUIRED: CONFIRMED
  RETROACTIVE_REPAIR: false

REGISTERED_PREDICTIONS:
  P_CTRL_XHOST_1:
    probability: 0.98
    prediction: the existing exact receipt validator accepts the unchanged inner receipt after detached-signature verification
  P_CTRL_XHOST_2:
    probability: 0.94
    prediction: a one-byte mutation of the canonical receipt fails SSHSIG verification before JSON parsing
  P_CTRL_XHOST_3:
    probability: 0.90
    prediction: Mac strict startup passes with the Linux host fully offline after trust and bundles are installed
  P_CTRL_XHOST_4:
    probability: 0.82
    prediction: the first implementation failure is OpenSSH allowed-signers namespace or filesystem-permission integration, not receipt semantics
  LIKELIEST_FAILURE: OPENSSH_ALLOWED_SIGNERS_OR_TRUST_PERMISSION_NORMAL_FORM

SCOPE: ABSTRACT
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

IMPLEMENTATION_AUTHORIZED_BY_THIS_VERDICT: false
LEAN_EDIT: false
QUARANTINE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
```

## ROUTE MAP

| Candidate | Verdict | Exact boundary | Tags |
|---|---|---|---|
| Authenticated remote lookup | **VALID, NOT SELECTED** | It preserves independent authority but explicitly makes Mac strict startup depend on the live Linux host and network. With the current dead endpoint it does not repair the reproducer. | `[ABSTRACT][PAPER]` |
| Signed offline receipt | **TRY — SELECTED** | The independent auditor signs the exact closed receipt bytes. The Mac checks a root-pinned key, revocation snapshot, signature, canonical bytes, then the existing exact field validator. No live Linux dependency remains. | `[ABSTRACT][CONDITIONAL]` |
| Replacement Control architecture | **NOT REQUIRED** | The resolver abstraction and receipt validator are sound. Only the transport representation changes; the inner receipt and admission semantics do not. | `[ABSTRACT][PAPER]` |
| Current W5 admission | **UNCHANGED** | The tracked entry is already `SEMANTICALLY_ADMITTED` with exactly two admitted scopes; `W5_COFINAL_PACKET_BUDGET_RATE` remains open. | `[COFINAL_FAMILY][LEAN]` |

## FINAL PROPOSAL

Freeze **signed offline transport** as the only selected Mac path.

The trusted operation is not “copy a receipt into the repository.” The trusted operation is:

```text
independent Linux auditor
  signs exact canonical q3_semantic_attestation.v1 bytes
    ↓
tracked receipt + detached SSHSIG may travel through Git
    ↓
Mac verifies against a root-owned, single-key allowed-signers file
    ↓
Mac rejects revoked IDs
    ↓
existing Control-v9 byte-for-field validator checks the quarantine entry
    ↓
strict startup continues without any live Linux connection.
```

This preserves the separation of powers. A committing body may alter the tracked receipt or signature, but such a change cannot produce a valid auditor signature. The private key never reaches the repository, Codex, or the Mac writer account.

The old Unix-socket broker remains legal on the independent Linux auditor host. It is no longer the Mac startup dependency.

## STRONGEST ATTACK

### Attack 1 — a tracked receipt lets Codex self-resolve

An **unsigned** tracked receipt would do exactly that and remains forbidden. A signed bundle does not. Codex can write arbitrary bytes but cannot create an SSHSIG accepted by the root-pinned auditor key. The exact field validator still binds the authenticated bytes to the quarantine entry. **[C09][C10]**

### Attack 2 — offline revocation is stale

Correct. This architecture does not pretend otherwise. Revocation is a root-owned snapshot installed on the Mac. It trades live revocation freshness for startup availability. Every startup rechecks the installed snapshot; a revoked ID fails closed. A policy requiring globally fresh revocation on every startup would necessarily select the online remote design and accept total Mac unavailability when Linux or the network is down.

### Attack 3 — signature verification of parsed JSON permits representation drift

Rejected by construction. SSHSIG covers the exact raw canonical file bytes, including the final LF. Verification occurs before parsing. After parsing, the runtime requires the bytes to equal the unique canonical encoding and then invokes the existing exact receipt validator.

### Attack 4 — key rotation creates a permissive overlap

Forbidden. Exactly one active key is accepted. Rotation requires re-signing every live receipt and atomically replacing the trust root. Any inconsistent intermediate state fails startup rather than accepting two authority generations.

### Attack 5 — one valid W5 bundle hides another broken admitted entry

Rejected by the all-entry gate. Strict startup validates every `SEMANTICALLY_ADMITTED` entry. One missing, revoked, malformed, wrongly signed, or field-drifting bundle blocks the entire executor.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION AUTHORIZED BY THIS VERDICT.

NEXT EXACT CONTROL-ONLY TRANSACTION AFTER OWNER GRANT:
  CONTROL_V9_SIGNED_OFFLINE_RESOLVER_IMPLEMENTATION

Required scope:
  - add a signed-offline resolver with the frozen SSHSIG contract;
  - select it by trusted platform logic on Darwin;
  - validate all admitted entries before dispatch;
  - add every mandatory plant listed above;
  - do not edit Lean, W5 mathematics, quarantine mathematical fields,
    Route state, or RH-facing artifacts.

Success:
  Mac validate and goal_runtime pass with the Linux socket absent and the Linux
  host unreachable, while every admitted receipt is authenticated and exact.

Failure code:
  CONTROL_V9_SIGNED_OFFLINE_RESOLVER_NOT_GREEN
```

## META CLOSEOUT

- **What became smaller?** The defect is no longer “cross-host attestation.” It is one bounded implementation: verify a detached auditor signature and feed the unchanged receipt into the existing validator.
- **What was killed?** The assumption that a fixed Linux Unix socket is a cross-host-safe Mac startup path.
- **What must not be tried again?** Unsigned tracked receipts, caller-selected paths, inline receipt JSON, environment-selected trust, or silent remote fallback.
- **Current smallest named gap:** `CONTROL_V9_SIGNED_OFFLINE_RESOLVER_IMPLEMENTATION`.
- **Next cheapest decisive test:** one-byte receipt mutation under the pinned SSHSIG verifier, followed by a full Mac startup with the Linux host offline.
- **Prediction fate:** online broker kill-power confirmed; its cost/availability advantage refuted; signed-offline runner-up promoted without retroactive probability repair.
- **Memory entry:** cross-host authority must be represented by portable authenticated evidence, not by an unspoken live-host dependency.
