# Proshka request: Control-v9 cross-host semantic-attestation transport

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Source head: `9ac216dcdd47f6a0b3c56ca17bd4255bcebee3b9`
- Control version: `9`
- Quarantine entry: `GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825`
- Attestation ID: `ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1`
- Existing broker verdict:
  `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_CONTROL_V9_SEMANTIC_ATTESTATION_MATERIALIZATION_2026-08-25.md`

This request does not reopen the W5 mathematical admission and does not ask
for a new receipt.  It reports a reproducible cross-host defect in the
materialization transport selected by the existing verdict.

## Exact reproducer

The admitted quarantine entry is tracked and the Linux broker implementation
is present.  On the canonical Mac checkout:

```text
$ uname -s
Darwin

$ test -S /run/q3-control-v9/semantic-attestation.sock
false

$ python3 orchestrator/goal_runtime.py --json
SEMANTIC_ATTESTATION_INVALID: semantic attestation closed fields differ: NoneType

$ python3 orchestrator/three_body_loop.py validate
SEMANTIC_ATTESTATION_INVALID: semantic attestation closed fields differ: NoneType
```

The reason is exact.  `resolve_linux_semantic_attestation` has one fixed
transport: the Unix socket
`/run/q3-control-v9/semantic-attestation.sock`.  macOS has no `/run` directory,
and the receipt registry exists only on the independent Linux auditor host.
The only configured SSH endpoint on this Mac currently refuses connections,
so an ad-hoc tunnel is not a live materialization path.

The receipt cannot be reconstructed from the tracked quarantine fields or
copied into a Mac-writable registry: every receipt field is deterministic from
tracked state, so such a copy would let the committing body self-resolve the
attestation and would destroy the independence invariant.

## What is blocked

Control section 16.8 says `BUG_FOUND_FIX_FIRST`: a reproducible gate defect
blocks return to mathematics until its reproducer is green.  Consequently the
Mac body cannot pass strict startup even though the W5 entry is already
`SEMANTICALLY_ADMITTED` on Linux.

## Required operative adjudication

Return exactly one class:

- `TRY_CONTROL_V9_AUTHENTICATED_REMOTE_ATTESTATION_RESOLUTION` if the intended
  invariant is live lookup from the independent Linux host on every startup.
  Freeze the authenticated transport, stable endpoint discovery, fail-closed
  behavior, and Mac validation commands.  State explicitly whether the whole
  Mac executor must remain unavailable whenever the Linux host is offline.
- `TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT` if an immutable receipt
  may travel to the Mac provided it carries an independently controlled
  cryptographic signature.  Freeze the signature scheme, pinned public-key
  location and rotation rule, receipt location, exact signed bytes, replay and
  revocation semantics, and validation commands.  The private signing key must
  remain unavailable to the committing body.
- `REPAIR_CONTROL_V9_CROSS_HOST_ATTESTATION_ARCHITECTURE` if neither candidate
  preserves the actual Control-v9 invariant.  Freeze the smallest replacement
  architecture and identify whether it requires a Control-version change.

The response must preserve all of these invariants:

1. Codex cannot mint, edit, or self-resolve a semantic attestation.
2. Failure to authenticate the independent auditor fails closed.
3. The receipt remains byte-for-field bound to the quarantine entry.
4. No W5 theorem, admitted scope, mathematical verdict, or downstream Route
   status changes.
5. No availability-dependent design is called cross-host-safe unless the
   required online dependency is stated explicitly.

Write and commit the append-only verdict under `docs/routeB_bus/proshka/` on
`rh_clean`, then push it.  Do not edit Lean source, historical verdicts,
quarantine mathematical fields, Route promotion, or any RH-facing artifact.
