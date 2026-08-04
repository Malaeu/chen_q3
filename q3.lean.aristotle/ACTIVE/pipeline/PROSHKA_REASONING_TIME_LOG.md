# Proshka Reasoning-Time Log

Purpose: measure which Q3 proof nodes consume the most external-review
reasoning time.  This is an operational performance ledger, not proof
authority and not evidence that a theorem is proved.

## Recording contract

For each substantive request, append one entry with:

```yaml
proof_address:
front:
transaction:
request_message_id:
sent_at:
completed_at:
wall_seconds:
wall_human:
answer_now_shown:
answer_now_clicked: false
primary:
status:
result_pointer:
notes:
```

Use timezone-qualified ISO timestamps.  Measure from immediately before send
until generation actually completes.  Never click `Answer now`.  A timing row
does not change Lean, route, or roof status.

## Runs

### 2026-08-04 — G5 cofinal third-even root bracket source audit

```yaml
proof_address: G5_MODE4_R1A
front: G5/S1
transaction: G5_MODE4_R1A_COFINAL_THIRD_EVEN_ROOT_BRACKET_SOURCE_LOCK
request_message_id: 7e4fe1b8-815b-4142-a2be-95d19b9d7b17
sent_at: backfill_unavailable
completed_at: 2026-08-04T22:44:47+02:00
wall_seconds: ">=1282"
wall_human: ">=21m22s"
answer_now_shown: true
answer_now_clicked: false
primary: G5_MODE4_R1A_COFINAL_ROOT_BRACKET_SOURCE_GAP
status: OPEN
result_pointer: "Proshka assistant message ddb6364a-2d9b-4162-84b3-fa6ea6f0176a"
notes: >-
  First run registered after it had already started. Preserve only a
  conservative lower bound at completion; do not invent an exact send time.
  Timing instrumentation began at 2026-08-04T22:30:25+02:00
  (Unix 1785875425), after more than seven observed minutes of generation.
  The exact post-instrumentation interval was 862 seconds; adding only the
  documented seven-minute pre-instrumentation lower bound yields >=1282
  seconds. The verdict recovered a cofinal spectral localization sublemma but
  stopped at the missing exact residual-orientation bridge. Proshka selected
  owner fork B (parameterized symbolic Jacobi/Schur/Sturm), pending explicit
  owner authorization. No Lean or route-state write was authorized.
```

### 2026-08-05 — G5 direct endpoint determinant-sign adjudication

```yaml
proof_address: G5_MODE4_R1A
front: G5/S1
transaction: G5_MODE4_R1A_DIRECT_ENDPOINT_DETERMINANT_SIGNS
request_message_id: 5c6c157b-51c7-442c-b794-cfa1708b00e1
sent_at: 2026-08-05T00:41:58.824+02:00
completed_at: 2026-08-05T01:20:44.683+02:00
wall_seconds: 2326
wall_human: "38m46s observed wall; 37m29s exact UI reasoning duration"
answer_now_shown: true
answer_now_clicked: false
primary: G5_MODE4_R1A_DIRECT_DETERMINANT_SIGNS_REDUCED_TO_EXPLICIT_FINITE_LEFT_ENVELOPES
status: FIRST_VERDICT_COMPLETE_SUPERSEDED_PENDING_FOLLOWUP
result_pointer: "Proshka assistant message 0edd239b-90e9-4990-8f7e-5968f1ba2ffd"
notes: >-
  Fresh project chat. The 276937-byte context pack at SHA-256
  8861088583d68b3aedb54a13c3bd9b6d1befda501500c0d279bbb2ace3064bbd
  pins HEAD 7f4ef457 and the determinant-sign interface. The prompt also records
  Dunster arXiv:1601.00699v3 equations (106)-(107): the mode-four coefficient
  9 is source-supported asymptotically, but no explicit finite remainder
  constant or threshold was found. The observed send-to-completion wall time
  includes polling lag; the chat UI reports the exact model reasoning duration
  as 37m29s. Proshka reduced the two determinant signs to exact finite-left
  envelopes, proposed K=5m, and retained the source stop. While it reasoned,
  Codex proved the stronger canonical K=4m split and found the Bonami--Karoui
  strict differential-spectrum separator, so one follow-up adjudication is
  required before this verdict can select the next node. Never click Answer
  now; it was shown and was not clicked.
```

### 2026-08-05 — G5 K=4m and Bonami--Karoui follow-up adjudication

```yaml
proof_address: G5_MODE4_R1A
front: G5/S1
transaction: G5_MODE4_R1A_K4M_BONAMI_KAROUI_FOLLOWUP
request_message_id: 14dbb40e-e9de-44fb-bac7-300cef9d2bdc
sent_at: 2026-08-05T01:24:41.545+02:00
completed_at: pending
wall_seconds: pending
wall_human: pending
answer_now_shown: false
answer_now_clicked: false
primary: pending
status: IN_PROGRESS
result_pointer: "same fresh RH Marz 2026 project chat"
notes: >-
  Follow-up pins HEAD/origin 6710ecdc, the Lean-checked K=4m tail split and
  direct determinant-sign receiver, and Bonami--Karoui arXiv:1405.3676v2
  theorem chi-between2/boundschi2 with source/e-print hashes. It explicitly
  guards the ordered Sturm--Liouville chi_n symbols from the unrelated project
  ProlatePair.chi2 scalar and asks for exactly one next executable theorem
  package. No diagnostic 8/10 endpoint, Bus 010, route promotion, or RH claim
  is authorized. Never click Answer now.
```
