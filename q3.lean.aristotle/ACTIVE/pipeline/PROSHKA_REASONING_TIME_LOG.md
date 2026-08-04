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
completed_at: pending
wall_seconds: pending
wall_human: pending
answer_now_shown: false
answer_now_clicked: false
primary: pending
status: IN_PROGRESS
result_pointer: pending_new_RH_Maerz_2026_project_chat
notes: >-
  Fresh project chat. The 276937-byte context pack at SHA-256
  8861088583d68b3aedb54a13c3bd9b6d1befda501500c0d279bbb2ace3064bbd
  pins HEAD 7f4ef457 and the determinant-sign interface. The prompt also records
  Dunster arXiv:1601.00699v3 equations (106)-(107): the mode-four coefficient
  9 is source-supported asymptotically, but no explicit finite remainder
  constant or threshold was found. Proshka was observed in Pro reasoning
  immediately after send. Never click Answer now.
```
