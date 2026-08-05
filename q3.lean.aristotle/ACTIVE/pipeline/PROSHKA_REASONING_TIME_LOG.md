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
completed_at: 2026-08-05T01:36:22.679+02:00
wall_seconds: 701
wall_human: "11m41s observed wall; 11m24s exact UI reasoning duration"
answer_now_shown: true
answer_now_clicked: false
primary: BONAMI_KAROUI_ENDPOINTS_SOURCE_LOCKED_SCHUR_SIGN_CROSSWALK_OPEN
status: COMPLETE_ACCEPTED_WITH_SUBSEQUENT_NODE_MATERIALIZED
result_pointer: "Proshka assistant message 92f35a12-3947-4453-95c5-f48d7f52b514"
notes: >-
  Follow-up pins HEAD/origin 6710ecdc, the Lean-checked K=4m tail split and
  direct determinant-sign receiver, and Bonami--Karoui arXiv:1405.3676v2
  theorem chi-between2/boundschi2 with source/e-print hashes. It explicitly
  guards the ordered Sturm--Liouville chi_n symbols from the unrelated project
  ProlatePair.chi2 scalar and asks for exactly one next executable theorem
  package. The observed send-to-completion wall includes polling lag; the UI
  reports exact model reasoning of 11m24s. Proshka ratified the source endpoint
  formulas but kept the exact differential-spectrum-to-infinite-tail-Schur
  sign crosswalk open. Its immediate envelope package had already been proved
  more strongly at HEAD 16af794f, so Codex executed the named subsequent
  shifted-diagonal/three-coefficient Legendre recurrence crosswalk instead.
  No diagnostic 8/10 endpoint, Bus 010, route promotion, or RH claim is
  authorized. Answer now appeared while generation was active and was never
  clicked.
```

### 2026-08-05 — G5 post-recurrence B0/B1 theorem-shape adjudication

```yaml
proof_address: G5_MODE4_R1A_B0_B1
front: G5/S1
transaction: G5_MODE4_POST_RECURRENCE_OPERATOR_WEYL_SCHUR_NEXT_NODE
request_message_id: f090f129-4f44-447e-9968-ce35b5904206
sent_at: 2026-08-05T01:51:44.268+02:00
completed_at: 2026-08-05T02:07:11+02:00
wall_seconds: 927
wall_human: 15m27s observed
answer_now_shown: true
answer_now_clicked: false
primary: AUTHORIZE_G5_MODE4_RICCATI_ORBIT_UNIQUENESS
status: COMPLETE_ACCEPTED
result_pointer: "Proshka assistant message 3a5ae850-e6a4-4178-b665-4870fda8f69a"
notes: >-
  The pasted-document context pack has SHA-256
  855e0db1cca5b35b3f04c3eb5dcb239888a29478b8014d86ca7e3d7a0705f058
  and pins the already-proved finite-left envelope package and exact three-
  coefficient DLMF even-Legendre recurrence crosswalk. The request asks for
  exactly one smallest executable node downstream of the coefficient identity,
  choosing among a finite-support operator action, the Hilbert-space/domain
  crosswalk, the Weyl/recessive-tail characterization, or a source-neutral
  abstract Schur-inertia theorem. It forbids reassigning closed work, minting
  a spectral theorem as a structure field, tildePhi unless selected, Bus 010,
  route promotion, and an RH claim. Answer now appeared during generation and
  was not clicked. The UI reports exact model reasoning of 14m59s; the
  observed wall includes polling lag. Proshka selected the all-index invariant-
  cone Riccati-orbit uniqueness theorem and the source-shaped nonvanishing
  coefficient-ratio consumer. It explicitly withheld the Weyl label and left
  PSWF regular-row eventual cone membership or L2 uniqueness as the next
  source-side obligation.
```

### 2026-08-05 — G5 post-square-summable-row next-node adjudication

```yaml
proof_address: G5_MODE4_R1A_POST_L2
front: G5/S1
transaction: G5_MODE4_POST_SQUARE_SUMMABLE_ROW_NEXT_NODE
request_message_id: 58d40b6f-eab6-42b9-a261-2d72cd7a2adb
sent_at: 2026-08-05T02:26:05.694+02:00
completed_at: 2026-08-05T02:49:56.200+02:00
wall_seconds: 1430
wall_human: "23m50s observed wall; 23m07s exact UI reasoning duration"
answer_now_shown: true
answer_now_clicked: false
primary: G5_MODE4_CANONICAL_HERMITIAN_TAIL_ROW_AND_SCHUR_BOUNDARY_FLUX
status: COMPLETE_ACCEPTED
result_pointer: "Proshka assistant message 41a82262-f418-42c8-bade-a1b1f9fef1b9"
notes: >-
  The pasted-document context pack has SHA-256
  cf8df355de22195f2473226a04a377d2d32de72e94cb77aa9af77509bb86db46
  and pins the proved recurrence crosswalk, invariant-cone Riccati uniqueness,
  source-shaped ratio receiver, and canonical positive square-summable tail
  row with exact project and DLMF recurrences. The request asks for exactly one
  next theorem-sized node among diagonal Hermitian scaling, L2 Wronskian
  uniqueness, finite Green/self-energy, or the honest source regular-row
  identification gate. It forbids reassigning closed work, minting the missing
  source theorem as a field, Weyl terminology without the boundary identity,
  Bus 010, route promotion, and an RH claim. Answer now appeared during
  generation and was not clicked. Proshka selected the exact row-level
  diagonal similarity: an explicit positive telescoping scale, the resulting
  symmetric Jacobi recurrence, preservation of square summability, and the
  boundary-flux identity matching the already committed Schur correction. It
  kept the discrete-Wronskian uniqueness theorem as the next source-neutral
  node and explicitly forbade source, Weyl, resolvent, operator, Bus 010,
  promotion, and RH claims. The UI reports exact model reasoning of 23m07s;
  the observed wall includes polling lag.
```

### 2026-08-05 — G5 regular PSWF coefficient-row source-gate adjudication

```yaml
proof_address: RouteB.G5.Mode4.RegularRow
front: G5/S1
transaction: G5_MODE4_REGULAR_PSWF_COEFFICIENT_ROW_NEXT_NODE
conversation_id: 6a7291c1-3ba4-83eb-bbcb-2396b4979290
request_message_id: d1756a06-cf60-45e1-b4f3-161ba90b395a
sent_at: 2026-08-05T03:28:33.025+02:00
completed_at: 2026-08-05T03:57:01.589+02:00
wall_seconds: 1708
wall_human: 28m28s observed including polling lag
answer_now_shown: true
answer_now_clicked: false
primary: G5_MODE4_SELECT_DLMF3085_WEIGHT_MATCH_RECEIVER
status: COMPLETE_ACCEPTED_FOR_IMPLEMENTATION
result_pointer: Proshka message 4dc98809-eb18-4cb6-abb7-5283956b1d05
notes: >-
  Fresh chat in project RH_März_2026. The exact context pack has SHA-256
  3468c3b26097b6795bf86112aa0a566eafeefbf4aced3adf96e8fd9b6169e74f;
  the complete sent prompt has SHA-256
  d222c8e566586c142c98b2bb7fd3f25577caeca2ccae9f443db619f4b8207e8e.
  It pins HEAD/origin 9e462d94, the completed canonical Hermitian tail row
  and L2 Wronskian uniqueness, four empty q3_docs queries, the failed 90-second
  qmd refresh, and DLMF 30.8.1--30.8.7 plus 30.16(ii). Proshka must select
  exactly one smallest executable node between the DLMF asymptotic-to-L2
  receiver, the source-row-to-canonical-tail consumer, or a strictly smaller
  legal theorem. The prompt explicitly attacks weighted-vs-unweighted L2,
  zero denominators, phase/index drift, zero proportionality, conditional-as-
  source wrappers, and full-operator overreach. Generation is running; the UI
  showed Pro-Denkvorgang and Stop response. At 03:31:21+02:00 the early
  Answer-now action appeared; it was deliberately not clicked. Proshka then
  completed with exact UI reasoning time 27m23s and selected a strictly
  smaller Candidate C: DLMF 30.8.5 weighted normalization matches the
  committed shifted Hermitian scale pointwise, so the immediate receiver can
  prove precisely the Hermitian-row square summability required by the
  Wronskian theorem without 30.8.7, coefficient quotients, eventual
  nonvanishing, or raw unweighted L2. The selected node remains conditional:
  it does not construct or identify a regular PSWF coefficient sequence.
```
