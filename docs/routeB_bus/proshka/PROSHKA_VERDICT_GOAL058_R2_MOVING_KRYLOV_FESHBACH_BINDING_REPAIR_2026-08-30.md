# STATUS: PROVED — REPAIR_R2_VERDICT_REQUEST_BYTE_BINDING
```yaml
PRIMARY: REPAIR_R2_VERDICT_REQUEST_BYTE_BINDING
OPERATIVE_CLASS: KILL_R2_MOVING_KRYLOV_FESHBACH
PRIMARY_COUNT: 1
DOCUMENT_ROLE: APPEND_ONLY_REQUEST_VERDICT_BYTE_BINDING_REPAIR

BINDING_REPAIR_REQUEST:
  REQUEST_ID: REQ-2026-08-29-R2K-BINDING-REPAIR
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  REQUEST_COMMIT: "79e0742fa0d501eb452ec108f97def135d55a391"
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_R2_VERDICT_BINDING_REPAIR_2026-08-30.txt
  REQUEST_GIT_BLOB: "3438ad495a4c889000994ed87878118c5bac7c02"
  AUTHORITATIVE_ATTACHMENT:
    NAME: PROSHKA_REQUEST_GOAL058_R2_VERDICT_BINDING_REPAIR_2026-08-30.txt
    BYTES: 2200
    LINES: 55
    SHA256: "93b486bec1a667736c9cd7896a969e095d2d031745c35cee9f0d319b53dddae9"
    FINAL_LF: true

ORIGINAL_REQUEST_BINDING:
  ORIGINAL_REQUEST_ID: REQ-2026-08-29-R2K
  ORIGINAL_REQUEST_INTRODUCING_COMMIT: "02e60cc4177e9ec45b3571dfd082253d20f12f92"
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_R2_MOVING_KRYLOV_FESHBACH_DISCRIMINATOR_2026-08-29.txt
  BYTES: 4682
  LINES: 108
  SHA256: "a746da60b5a6052a0e32d6341681d4848bb9c36b4a20b88c50a0f41271031e3f"
  GIT_BLOB: "067dd5f70bca53b948003702de49aca13bde0102"
  FINAL_LF: true

DIRECT_VERIFICATION_AT_ORIGINAL_REQUEST_COMMIT:
  PATH_FETCHED_AT_EXACT_COMMIT: true
  GITHUB_REPORTED_GIT_BLOB_MATCH: true
  BYTE_COUNT_RECOMPUTED: 4682
  LINE_COUNT_RECOMPUTED: 108
  SHA256_RECOMPUTED: "a746da60b5a6052a0e32d6341681d4848bb9c36b4a20b88c50a0f41271031e3f"
  GIT_BLOB_RECOMPUTED: "067dd5f70bca53b948003702de49aca13bde0102"
  FINAL_BYTE_HEX: "0a"
  ALL_CORRECTED_VALUES_MATCH: true

ORIGINAL_VERDICT_BINDING:
  ORIGINAL_VERDICT_COMMIT: "81da25d6ed2675800bb72d6feaf1a42a1f292a03"
  ORIGINAL_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_R2_MOVING_KRYLOV_FESHBACH_DISCRIMINATOR_2026-08-29.md
  ORIGINAL_VERDICT_GIT_BLOB: "beeffcd1ca7dd8f038f99a8e151d22e3fec021a5"
  ORIGINAL_STATUS: FATAL
  ORIGINAL_OPERATIVE_CLASS: KILL_R2_MOVING_KRYLOV_FESHBACH
  ORIGINAL_ARTIFACT_MUTATED: false

INCORRECT_MANIFEST_SUPERSEDED_ONLY:
  BYTES: 5398
  LINES: 111
  SHA256: "04d0b471f6f8c59b3176d12e257df7cf3e5d90e45afc199b290379467ef30dd3"
  GIT_BLOB: "067dd092faf722d7db193c160c2f1324285217b2"
  CLASSIFICATION: WRONG_ATTACHMENT_BYTE_BINDING
  MAY_BE_USED_AS_REQUEST_LOCK: false

REPAIR_EFFECT:
  CORRECTED_FIELD_CLASS: REQUEST_BYTE_BINDING_ONLY
  MATHEMATICAL_CONTENT_CHANGED: false
  OPERATIVE_CLASS_CHANGED: false
  KILL_DECISION_PRESERVED: true
  SOURCE_AUDIT_REOPENED: false
  LEAN_AUTHORIZED: false
  CODEX_AUTHORIZED: false
  NEXT_CONTROL_ACTION: OWNER_RERANK_AFTER_R2_KILL

IMMUTABILITY_GUARD:
  ORIGINAL_REQUEST_EDITED: false
  ORIGINAL_VERDICT_EDITED: false
  LEAN_EDITED: false
  SIX_FIELD_PHASE_KEY_CHANGED: false
  ROUTE_STATUS_CHANGED: false
  RH_STATUS_CHANGED: false

CLOSES:
  - R2_VERDICT_REQUEST_BYTE_BINDING_MISMATCH
OPENS: []

QUEUE:
  ORIGINAL_REQUEST_ID: REQ-2026-08-29-R2K
  QUEUE_STATUS_MUTATED_BY_PROSHKA: false

SCOPE: ABSTRACT
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Item | Result | Tags |
|---|---|---|
| Exact original request bytes | **VERIFIED** at commit `02e60cc4…`: 4682 bytes, 108 LF-terminated lines, SHA-256 `a746da60…31e3f`, Git blob `067dd5f7…e0102`. | `[ABSTRACT][PAPER]` |
| Original verdict identity | **VERIFIED** at commit `81da25d6…`: path and blob `beeffcd1…021a5` match the binding-repair request. | `[ABSTRACT][PAPER]` |
| Mathematical verdict | **UNCHANGED**: `KILL_R2_MOVING_KRYLOV_FESHBACH`. | `[ABSTRACT][PAPER]` |
| Lean or phase state | **UNCHANGED**. No Lean execution or edit is authorized. | `[ABSTRACT][PAPER]` |

## FINAL PROPOSAL

Treat this file as the append-only source-lock correction for the original R2 verdict. The original verdict remains immutable and operative, except that its four incorrect attachment-manifest values are superseded by the exact values recorded above.

The next control action remains:

```text
OWNER_RERANK_AFTER_R2_KILL
```

Registered prediction: a direct fetch of the original request at `02e60cc4…` reproduces all five corrected byte-lock fields. Fate: **CONFIRMED**.

## STRONGEST ATTACK

A byte-binding repair could accidentally reopen or soften the mathematical decision. This repair prevents that failure explicitly: it changes no theorem, premise, source audit, route classification, or control action. It repairs only the identity of the authoritative request bytes.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION AUTHORIZED.
Do not edit the original request, original verdict, Lean source, phase key,
Route status, or RH status.
```

## META CLOSEOUT

- **What became smaller?** The original R2 verdict now has one exact, reproducible request-byte binding.
- **What was killed?** Use of the incorrect `5398 / 111 / 04d0… / 067dd092…` manifest as the request lock.
- **What must not be tried again?** Do not mutate the pushed verdict to repair source-lock metadata; append a new correction artifact.
- **Current smallest named gap?** `OWNER_RERANK_AFTER_R2_KILL`.
- **Next cheapest decisive test?** Owner representation rerank; no additional R2 Krylov formalization.
- **Prior prediction fate?** Exact corrected byte lock: confirmed.
- **Memory entry?** R2 remains killed; only its request-byte binding changed.

## VERIFICATION HANDOFF

```text
WRITE KIND:
  docs-only append-only control artifact

LEAN FILES WRITTEN:
  none

LEAN GATE:
  not applicable

AXIOM PROFILE:
  not applicable

STATUS CHANGE:
  request-byte binding mismatch -> closed
  mathematical KILL verdict -> unchanged
```
