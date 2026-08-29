# STATUS: FATAL — KILL_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE
```yaml
PRIMARY: KILL_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE
OPERATIVE_CLASS: KILL_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE
PRIMARY_COUNT: 1
DOCUMENT_ROLE: CONTROL_V9_OWNER_ROOT_BRIDGE_ADJUDICATION

REQUEST_LOCK:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  REQUEST_COMMIT: d1c42021fc285b9870db15d44e2cde39cbe4e1cb
  REQUEST_PARENT: 261e79a65759024e6746fa8a7855b378aa326862
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE_2026-08-29.txt
  REQUEST_GIT_BLOB: c72f93fdcd84a45fe18c93d68991b7c97c74bea1

OPERATIVE_W5_JUDGMENT:
  COMMIT: dd469b72ee3118a0257dd19296f3db7a02a05518
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CODEX_REQ_GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_SEMANTIC_ADMISSION_2026-08-25.md
  GIT_BLOB: b635ba98b2c465ffe271b0775afd174f74953c19
  STATUS: PROVED
  ADMITTED_SCOPE:
    - W5_FIXED_K_QUANTITATIVE_FOURIER_DECAY_EXACT_W4_BUDGET
    - W5_FIXED_K_LITERAL_SHIFTED_FORM_ENERGY_MAJORANT
  OPEN_MATHEMATICAL_GAP:
    - W5_COFINAL_PACKET_BUDGET_RATE
  MATHEMATICAL_JUDGMENT_REOPENED: false

OPERATIVE_TRANSPORT_JUDGMENT:
  COMMIT: 66533ae2a009c7d495aeee2b842c85e21b2d2da0
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CONTROL_V9_CROSS_HOST_SEMANTIC_ATTESTATION_TRANSPORT_2026-08-29.md
  GIT_BLOB: 8ff0d94b4d6a66cfd6d02e262e36ad8d6b28fdc5
  OPERATIVE_CLASS: TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT
  CONTROL_VERSION: 9
  SIGNER_PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
  SIGNATURE_NAMESPACE: q3-control-v9-semantic-attestation

CONCURRENT_DECISIVE_FACT:
  COMMIT: 6ca3214575f9d7f8583e1ee93f270df97cb00fa6
  PARENT: d1c42021fc285b9870db15d44e2cde39cbe4e1cb
  DIRECT_CHILD_OF_REQUEST: true
  COMMIT_MESSAGE: "[Linux-Claude][rh_clean][Control-v9] Return signed offline attestation receipt for W5"
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_CONTROL_V9_SIGNED_OFFLINE_RECEIPT_2026-08-29.md
  SOURCE_RECORD_GIT_BLOB: 364eb14e959316ed94a65a9a8641721a061649c3
  SIGNATURE_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.sshsig
  SIGNATURE_GIT_BLOB: 22e60ad16c41c32842868a499df69c26df48a30a
  SIGNATURE_BYTES: 334
  SOURCE_REPORTED_VERIFY_EXIT_CODE: 0
  JUDGE_RERAN_SIGNATURE_VERIFY: false

AUTHENTICATED_OBJECT:
  ATTESTATION_ID: ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
  RECEIPT_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.json
  RECEIPT_BYTES: 1435
  RECEIPT_SHA256: e02d953cc4e894da1a18ce6a3ab546f83346c5a6e568c4ceeb32480c741eee38
  RECEIPT_GIT_BLOB: 3fb888192ff4f1e43d3dbe27bca3c2c3e6b32547
  FINAL_BYTE: "0x0a"
  INNER_SCHEMA: q3_semantic_attestation.v1
  INNER_ISSUER: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
  SIGNATURE_SCHEME: OPENSSH_SSHSIG
  KEY_TYPE: ssh-ed25519
  HASH_ALGORITHM: sha512
  SIGNATURE_NAMESPACE: q3-control-v9-semantic-attestation
  SIGNER_PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
  PUBLIC_KEY_FINGERPRINT: SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y

REQUEST_PREMISE_FATE:
  LINUX_SIGNATURE_UNAVAILABLE_UNTIL_MONDAY: REFUTED_BY_CONCURRENT_COMMIT
  PRODUCTION_BLOCKED_ONLY_BY_MISSING_DETACHED_SIGNATURE: NO_LONGER_TRUE
  REMAINING_LOCAL_BLOCKER: MAC_ROOT_TRUST_INSTALL_AND_STRICT_GATE

CLASS_DECISION:
  TRY_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE:
    status: KILLED
    reason: >-
      Control v9 freezes the authenticated signer and the inner receipt issuer
      as LINUX_INDEPENDENT_SEMANTIC_AUDITOR. An owner-root signature is a
      different authority law, not another representation of the same v9
      authority. The current validator must reject it through the existing
      principal, namespace, pinned-key, or issuer checks.

  REPAIR_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE:
    status: NOT_SELECTED_SUPERSEDED
    reason: >-
      If the independent signature were genuinely unavailable, an honestly
      named owner-root emergency authority would require a separately versioned
      control policy and separate trust semantics. The direct child of the
      request now contains the selected Linux-auditor detached signature, so
      that repair has no remaining operational benefit and would create a
      competing authority path.

  KILL_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE:
    status: SELECTED
    reason: >-
      The canonical Control-v9 path is now supplied exactly. Adding the proposed
      bridge would increase the trusted computing and authority surface without
      closing any live defect.

KILL_GROUNDS:
  - code: OWNER_ROOT_IS_NOT_LINUX_INDEPENDENT_AUDITOR
    detail: >-
      The owner may install the Mac trust root, but may not authenticate bytes
      under the independent Linux semantic-auditor principal.
  - code: CONCURRENT_PRIMARY_TRANSPORT_NOW_PRESENT
    detail: >-
      The exact receipt already has the required detached Linux-auditor SSHSIG.
  - code: DUAL_AUTHORITY_PATH_INCREASES_ATTACK_SURFACE
    detail: >-
      A temporary fallback resolver, key, manifest, ceremony receipt, expiry
      parser, and cleanup path would add ambiguity after the primary path exists.
  - code: OWNER_MANIFEST_IS_NOT_A_SURROGATE_FOR_AUDITOR_SIGNATURE
    detail: >-
      Binding the Proshka verdict blob and receipt hash does not turn an owner
      signature into independent semantic-auditor authentication.

CONTROL_VERSION_DECISION:
  VERSION_AFTER_VERDICT: 9
  VERSION_BUMP_REQUIRED: false
  REASON: >-
    No owner-root bridge is introduced. The already selected Control-v9
    Linux-signed offline transport remains the sole Darwin authority path.
  RECEIPT_SCHEMA_CHANGED: false
  QUARANTINE_SCHEMA_CHANGED: false
  ADMISSION_RULE_CHANGED: false
  AUTHORITY_ROLE_CHANGED: false

OWNER_ROOT_BRIDGE_FREEZE:
  STATUS: KILLED_NOT_MINTED
  BRIDGE_MANIFEST_SCHEMA: NONE
  BRIDGE_MANIFEST_PATH: NONE
  BRIDGE_SIGNATURE_PATH: NONE
  BRIDGE_SIGNER_PRINCIPAL: NONE
  BRIDGE_SSHSIG_NAMESPACE: NONE
  OWNER_PRIVATE_KEY_PATH: NONE
  OWNER_ALLOWED_SIGNERS_PATH: NONE
  OWNER_REVOCATION_PATH: NONE
  LIVE_CHAT_COMPARISON_CEREMONY_RECEIPT: FORBIDDEN_AS_AUTHORITY_INPUT
  MAXIMUM_EXPIRY: NOT_APPLICABLE
  CLEANUP_SEMANTICS: >-
    Do not create or install any owner-root bridge artifact. If provisional
    untracked owner-bridge keys, manifests, signatures, or trust files were
    created locally before this verdict, remove them before the strict startup
    gate. They have no canonical path and no authority status.
  MAY_ADMIT_OTHER_QUARANTINE_ENTRY: false
  MAY_ADMIT_CURRENT_W5_ENTRY: false

CANONICAL_DARWIN_TRANSPORT:
  RESOLVER: resolve_signed_offline_semantic_attestation
  PLATFORM_SELECTION: trusted sys.platform branch
  RECEIPT_PATH_SOURCE: exact attestation_id token
  CALLER_SELECTED_PATH: forbidden
  ENVIRONMENT_OVERRIDE: forbidden
  INLINE_RECEIPT: forbidden
  REMOTE_FALLBACK: forbidden
  AUTHORITY_FALLBACK: forbidden
  CACHE_OF_PARSED_RECEIPT: forbidden
  STATE_MUTATION_DURING_VALIDATION: forbidden

  ALLOWED_SIGNERS_PATH: /etc/q3-control-v9/semantic_attestation_allowed_signers
  REVOCATION_PATH: /etc/q3-control-v9/semantic_attestation_revoked_ids.v1.json
  REQUIRED_PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
  REQUIRED_NAMESPACE: q3-control-v9-semantic-attestation
  REQUIRED_KEY_TYPE: ssh-ed25519
  REQUIRED_ACTIVE_KEY_COUNT: 1
  REQUIRED_PUBLIC_KEY_FINGERPRINT: SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y

  EXACT_ALLOWED_SIGNERS_LINE: >-
    LINUX_INDEPENDENT_SEMANTIC_AUDITOR
    namespaces="q3-control-v9-semantic-attestation" ssh-ed25519
    AAAAC3NzaC1lZDI1NTE5AAAAIHuGHK0iP7MQKiXrUNMB7DBRw3Qj2P1UdooD3IycYhaA

  EMPTY_REVOCATION_BYTES: >-
    {"revoked_attestation_ids":[],"schema":"q3_semantic_attestation_revocations.v1"}\n
LINUX_PRIVATE_KEY_LOCATION_DEVIATION:
  FROZEN_PATH: /var/lib/q3-control-v9/private/semantic-attestation-ed25519
  SOURCE_REPORTED_ACTUAL_PATH: ~/.local/share/q3-control-v9/private/semantic-attestation-ed25519
  SOURCE_REPORTED_DIRECTORY_MODE: "0700"
  SOURCE_REPORTED_KEY_MODE: "0600"
  PRIVATE_KEY_ENTERED_REPOSITORY: false
  EXISTING_SIGNATURE_VALIDITY_EFFECT: NONE
  MAC_TRUST_EFFECT: NONE
  CLASSIFICATION: NONBLOCKING_HYGIENE_DEVIATION_FOR_ALREADY_EMITTED_SIGNATURE
  FUTURE_SIGNING_RULE: >-
    Before another production attestation is signed with this key, move the
    unchanged private key to the frozen path or obtain a new judged repair.
    This verdict does not authorize future signing from the interim path.

EXISTING_FAILURE_CODES_RETAINED:
  - CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING
  - CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID
  - CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID
  - CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED
  - CONTROL_V9_OFFLINE_ATTESTATION_RECEIPT_INVALID
  - CONTROL_V9_OFFLINE_ATTESTATION_ALL_ENTRY_VALIDATION_FAILED
  - SEMANTIC_ATTESTATION_INVALID

OWNER_BRIDGE_REJECTION_BY_EXISTING_RUNTIME:
  OWNER_PRINCIPAL_IN_ALLOWED_SIGNERS: CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID
  OWNER_KEY_WITH_LINUX_PRINCIPAL_UNPINNED: CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID
  TWO_ACTIVE_KEYS: CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID
  RECEIPT_ISSUER_CHANGED_TO_OWNER: SEMANTIC_ATTESTATION_INVALID
  NEW_OWNER_BRIDGE_FAILURE_CODE_REQUIRED: false

ALL_ENTRY_POLICY:
  CURRENT_ADMITTED_ENTRY_COUNT: 1
  CURRENT_ENTRY: GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825
  CURRENT_STATUS: SEMANTICALLY_ADMITTED
  CURRENT_ATTESTATION_ID: ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
  CURRENT_QUARANTINE_GIT_BLOB: c17c34cb54a65356dd61075181f53a91a941022b
  PARTIAL_VALIDATION: forbidden
  STATUS_DOWNGRADE_ON_FAILURE: forbidden
  COMPLETE_STARTUP_FAILS_ON_ANY_INVALID_ADMITTED_ENTRY: true

MANDATORY_ADVERSARIAL_PLANTS:
  SOURCE_PRESENT_AT_REVIEW_HEAD:
    - valid Linux-signed bundle passes with socket and network absent
    - missing receipt fails closed
    - missing signature fails closed
    - one-byte receipt mutation fails signature verification
    - signature by unpinned key fails
    - wrong principal fails
    - wrong namespace fails
    - writable or symlinked trust material fails
    - revoked ID fails despite valid signature
    - signed receipt field drift fails exact validator
    - unsigned tracked JSON never resolves
    - caller path and environment override are rejected
    - validation does not edit quarantine state
    - one valid plus one missing admitted bundle fails whole-state validation

  OWNER_BRIDGE_KILL_PLANTS:
    - owner principal in the one-line allowed-signers file fails trust validation
    - owner signature under the Linux principal fails pinned-key verification
    - Linux and owner keys together fail the exactly-one-active-key rule
    - changing inner issuer to OWNER_ROOT_PROSHKA_VERDICT_TRANSPORT fails exact validation

MAC_ROOT_INSTALL_AND_STRICT_GATE:
  OWNER_ROLE: privileged installer only, not semantic signer
  REQUIRED_FILES:
    - /etc/q3-control-v9/semantic_attestation_allowed_signers
    - /etc/q3-control-v9/semantic_attestation_revoked_ids.v1.json
  REQUIRED_OWNER_UID: 0
  REQUIRED_FILE_TYPE: regular_file_not_symlink
  REQUIRED_DIRECTORY_GROUP_OR_WORLD_WRITABLE: false
  REQUIRED_FILE_GROUP_OR_WORLD_WRITABLE: false

  MANUAL_SIGNATURE_CHECK: >-
    /usr/bin/ssh-keygen -Y verify
    -f /etc/q3-control-v9/semantic_attestation_allowed_signers
    -I LINUX_INDEPENDENT_SEMANTIC_AUDITOR
    -n q3-control-v9-semantic-attestation
    -s orchestrator/attestations/control-v9/ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.sshsig
    < orchestrator/attestations/control-v9/ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.json

  TARGETED_TESTS:
    - python3 -m unittest orchestrator.tests.test_signed_offline_semantic_attestation
    - python3 -m unittest orchestrator.tests.test_three_body_loop
    - python3 -m unittest orchestrator.tests.test_goal_runtime

  STATE_CHECK: python3 orchestrator/three_body_loop.py validate
  GOAL_CHECK: python3 orchestrator/goal_runtime.py --json
  STATE_IMMUTABILITY_CHECK: git diff --exit-code -- orchestrator/state/SEMANTIC_QUARANTINE.json

  REQUIRED_RESULTS:
    - manual SSHSIG verification exits zero
    - targeted tests pass
    - THREE_BODY_STATE_VALID
    - goal_runtime emits valid JSON without SEMANTIC_ATTESTATION_INVALID
    - quarantine state bytes remain unchanged
    - Linux socket and network may remain unavailable throughout the Mac gate

STARTUP_AND_EXECUTION_AUTHORITY:
  SUCCESSFUL_LINUX_BUNDLE_VALIDATION_AUTHORIZES_STRICT_STARTUP: true
  OWNER_ROOT_BRIDGE_AUTHORIZES_STRICT_STARTUP: false
  SUCCESSFUL_STARTUP_MINTS_EXECUTION_GRANT: false
  NEXT_ALREADY_AUTHORIZED_NON_RH_NODE_MAY_RUN: >-
    Only if its separate action-time grant, lease, path scope, node budget, and
    control preconditions remain valid after the strict startup gate. This
    verdict creates no mathematical or execution authorization.

STRONGEST_CONTROL_ONLY_WORK_BEFORE_NEXT_NODE:
  - install the exact one-key Linux-auditor trust root on Mac
  - install the canonical empty revocation snapshot
  - verify the exact detached signature over the exact receipt bytes
  - run the existing mandatory plants and strict all-entry startup gate
  - remove any provisional owner-bridge artifacts

CLOSES:
  - CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE_ADJUDICATION
  - CONTROL_V9_TEMPORARY_FALLBACK_AUTHORITY_AMBIGUITY
OPENS: []
NEXT_LOAD_BEARING_GAP: CONTROL_V9_MAC_TRUST_INSTALL_AND_STRICT_STARTUP_GATE

MATHEMATICAL_BOUNDARY:
  W5_THEOREMS_CHANGED: false
  W5_ADMITTED_SCOPE_CHANGED: false
  W5_MATHEMATICAL_VERDICT_CHANGED: false
  W5_COFINAL_PACKET_BUDGET_RATE_CLOSED: false
  LEAN_EDIT: false
  QUARANTINE_EDIT: false
  ROUTE_PROMOTION: false
  RH_CLAIM: false

ARSENAL_MANDATE:
  ACCEPTED: true
  SIDECAR_EXECUTION_TRIGGERED: false
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE
  CARD_KILL_SIGNATURES:
    C04: same receipt bytes do not make Linux-auditor and owner-root authority identical
    C09: a fallback authority chosen after the incident may not be relabeled as the precommitted v9 authority
    C10: a signed bridge manifest is not the independent-auditor signature consumed by the validator

QUEUE_AUDIT:
  CURRENT_REQUEST_IN_PROSHKA_QUEUE: false
  REQUEST_ID: DIRECT_REQUEST_D1C42021
  REQ_2026_08_21_P: ALREADY_ANSWERED_LATER_IN_QUEUE_STALE_OPEN_DUPLICATE
  OLDER_LIVE_QUEUE_REQUEST_BLOCKING_THIS_VERDICT: false

PREDICTION_FATE:
  TRY_OWNER_ROOT_UNDER_CONTROL_V9_IS_AUTHORITY_EQUIVALENT: REFUTED
  REPAIR_OWNER_ROOT_WOULD_BE_REQUIRED_IF_LINUX_SIGNATURE_REMAINED_UNAVAILABLE: CONDITION_FALSIFIED_BEFORE_VERDICT
  SIGNED_OFFLINE_LINUX_TRANSPORT_HAS_EQUAL_KILL_POWER: CONFIRMED
  SIGNED_OFFLINE_LINUX_TRANSPORT_CAN_ARRIVE_WITHOUT_LEAN_CHANGE: CONFIRMED
  OWNER_ROOT_BRIDGE_LIKELY_FAILURE_IS_DUAL_AUTHORITY_AMBIGUITY: CONFIRMED_BY_STRUCTURE
  RETROACTIVE_REPAIR: false

REGISTERED_PREDICTIONS:
  P_OWNER_KILL_1:
    probability: 0.99
    prediction: the current Control-v9 runtime rejects an owner principal or owner key without any new owner-bridge-specific code
  P_OWNER_KILL_2:
    probability: 0.94
    prediction: the remaining first Mac integration failure, if any, is root-owned allowed-signers or revocation-file installation rather than receipt semantics
  P_OWNER_KILL_3:
    probability: 0.97
    prediction: the exact Linux-signed bundle passes the unchanged byte-for-field W5 validator after Mac trust installation
  LIKELIEST_FAILURE: MAC_ROOT_TRUST_PERMISSION_OR_ALLOWED_SIGNERS_NORMAL_FORM

SCOPE: ABSTRACT
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
IMPLEMENTATION_AUTHORIZED_BY_THIS_VERDICT: false
OWNER_BRIDGE_IMPLEMENTATION_AUTHORIZED: false
LEAN_SOURCE_EDITED: false
RH_CLAIMED: false
```

## ROUTE MAP

| Candidate | Verdict | Decisive fact | Tags |
|---|---|---|---|
| `TRY_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE` | **KILLED** | Control v9 authenticates one exact law: a receipt whose inner issuer and detached signer are the independent Linux semantic auditor. An owner-root key is a different authority, even when it signs a manifest containing the same hashes. | `[ABSTRACT][PAPER]` |
| `REPAIR_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE` | **SUPERSEDED** | A separate, honestly named emergency authority could only exist under a new control policy. Before this verdict landed, the direct child of the request delivered the precommitted Linux-auditor signature. The repair now closes nothing. | `[ABSTRACT][PAPER]` |
| `KILL_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE` | **SELECTED** | The canonical signature bundle exists. A second temporary authority path would only increase trusted surface, resolver complexity, cleanup burden, and ambiguity. | `[ABSTRACT][PAPER]` |
| Linux-signed offline receipt | **SOURCE RETURN PRESENT; MAC GATE PENDING** | Exact receipt bytes, signature blob, principal, namespace, public-key fingerprint, and a reported successful local verification are source-locked. This judge did not rerun `ssh-keygen` or the Mac tests. | `[FINITE_CELL][PAPER]` |
| W5 semantic admission | **UNCHANGED** | The one admitted entry retains exactly the two fixed-`k` scopes. `W5_COFINAL_PACKET_BUDGET_RATE` remains open. | `[COFINAL_FAMILY][LEAN]` |

The source change that kills the emergency premise is causally clean: commit
`6ca32145...` is the direct child of request commit `d1c42021...`. The verdict
therefore does not use unrelated later route work to evade the request. It uses
the exact authority artifact the request said was missing.

## FINAL PROPOSAL

Do not build the owner-root bridge.

Keep Control version 9 and finish the already selected transport:

```text
exact W5 receipt bytes
  + detached Linux-auditor SSHSIG
  + one root-owned Mac allowed-signers line
  + root-owned empty revocation snapshot
  + unchanged exact receipt validator
  + all-entry startup validation
  → strict Mac startup without a live Linux connection.
```

The owner has one legitimate privileged role here: install and protect the
Mac trust files. That role does not include signing semantic authority or
creating a second resolver path.

The strongest remaining control-only transaction is:

```text
CONTROL_V9_MAC_TRUST_INSTALL_AND_STRICT_STARTUP_GATE
```

A green result clears the startup barrier. It does not mint a lease, select a
mathematical theorem, close the W5 cofinal rate, promote Route B, or claim RH.

## STRONGEST ATTACK

### Attack 1 — “The Linux return commit is unsigned, so the problem remains.”

The Git commit is transport, not authority. The authority artifact is the
detached SSHSIG over the exact 1435 receipt bytes. The source record reports a
successful `ssh-keygen -Y verify` under the frozen principal, namespace, and
public-key fingerprint. The Mac must rerun that verification before startup.
An unsigned Git commit cannot forge the detached signature. `[C04][C10]`

### Attack 2 — “The owner bridge is only a harmless temporary fallback.”

It is not harmless. It adds a second private key, second principal, second
namespace or issuer interpretation, a new manifest schema, expiry semantics,
cleanup semantics, and resolver precedence. After the primary Linux signature
exists, every one of those is pure attack surface. The existing runtime already
rejects owner keys and multiple active keys fail closed. `[C09]`

### Attack 3 — “The owner visibly compared the hashes with Proshka, so the owner is merely authenticating Proshka.”

A visible comparison is a useful human ceremony, but it is not the independent
semantic-auditor signature required by Control v9. The Proshka verdict and the
receipt are different objects with different issuers and consumers. A manifest
that names both does not merge their authority classes. `[C04][C10]`

### Attack 4 — “The Linux private key is not yet at the frozen `/var/lib` path.”

That is a real hygiene deviation and is recorded, not erased. It does not alter
the public key, signed bytes, principal, namespace, or validity of the already
emitted signature. The same key must move to the frozen location before any
future production signing, or that future signing needs a new adjudication.
The Mac trust gate consumes only the public key and detached signature.

### Repaired weakest statement

The owner may perform **root installation of the exact Linux public trust
material** and run the strict gate. The owner may not act as a substitute
semantic signer.

## CODEX DIRECTIVE

```text
NO OWNER-ROOT BRIDGE IMPLEMENTATION.

NEXT CONTROL-ONLY TASK:
  CONTROL_V9_MAC_TRUST_INSTALL_AND_STRICT_STARTUP_GATE

INPUTS:
  branch containing 6ca3214575f9d7f8583e1ee93f270df97cb00fa6;
  exact receipt blob 3fb888192ff4f1e43d3dbe27bca3c2c3e6b32547;
  exact signature blob 22e60ad16c41c32842868a499df69c26df48a30a;
  exact one-line Linux-auditor allowed-signers entry from the source record;
  canonical empty revocation snapshot.

FORBIDDEN:
  generate an owner key;
  sign an owner manifest;
  add an owner principal, namespace, issuer, or fallback resolver;
  accept two active keys;
  edit the receipt;
  edit SEMANTIC_QUARANTINE.json;
  edit Lean;
  infer execution authority from startup success.

VALIDATION:
  run the exact manual SSHSIG check;
  run the three targeted unittest modules;
  run three_body_loop.py validate;
  run goal_runtime.py --json;
  confirm quarantine-state byte immutability;
  confirm Linux socket and network are not required.

SUCCESS:
  CONTROL_V9_MAC_STRICT_STARTUP_GREEN_WITH_LINUX_OFFLINE

FAILURE:
  report the first exact existing Control-v9 failure code;
  do not switch to owner-root fallback.
```

## META CLOSEOUT

**What became smaller?**

The three-way authority fork collapsed to one path: the already selected
Linux-auditor signed-offline resolver.

**What was killed?**

```text
TRY_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE
REPAIR_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE
```

The TRY dies by authority mismatch. The REPAIR is superseded because its only
operational premise was falsified by the direct child of the request.

**What must not be tried again?**

Do not convert an owner hash-comparison ceremony into cryptographic semantic
authority. Do not add a second key or fallback resolver after the primary
signature exists.

**Current smallest named gap:**

```text
CONTROL_V9_MAC_TRUST_INSTALL_AND_STRICT_STARTUP_GATE
```

**Next cheapest decisive test:**

Install the exact Linux public trust material on Mac and rerun the existing
strict signature plus all-entry validation gate.

**Fate of registered predictions:**

- `TRY` under unchanged Control v9: **refuted as authority-equivalent; kill confirmed**.
- `REPAIR` conditional on continued Linux unavailability: **condition falsified by new source**.
- signed-offline Linux path: **source return confirmed; Mac runtime gate pending**.
- no Lean change required: **confirmed**.

No prediction was retroactively repaired.

**Memory entry:**

```yaml
iteration:
  target: temporary owner-root Proshka-verdict bridge
  status: FATAL
  failed_strategy: second authority path after primary signature return
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: CONTROL_V9_MAC_TRUST_INSTALL_AND_STRICT_STARTUP_GATE
  invariant_learned: same bytes do not make two signer roles the same authority
  forbidden_future_move: do not add fallback authority after the precommitted authority artifact exists
  next_decisive_test: Mac root trust install plus strict offline startup gate
```

## VERIFICATION HANDOFF

This transaction writes documentation only.

```yaml
BRANCH: rh_clean
PATH_WRITTEN:
  docs/routeB_bus/proshka/PROSHKA_VERDICT_CONTROL_V9_OWNER_ROOT_PROSHKA_VERDICT_BRIDGE_2026-08-29.md
LEAN_FILES_WRITTEN: []
LEAN_GATE_REQUIRED: false
EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE
POST_WRITE_CHECKS:
  - fetch the verdict path from rh_clean
  - confirm the verdict commit is the branch head or an ancestor of the harvested head
  - confirm no Lean or quarantine-state path changed in the verdict commit
```
