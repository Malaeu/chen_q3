# Linux independent semantic-audit source record: Goal 058 selected fixed-cutoff obstruction

Answers
`docs/routeB_bus/LINUX_REQUEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_ATTESTATION_2026-09-01.md`.
This is an append-only signed-return record. It does not materialize semantic
admission, edit quarantine state, close adaptive or direct finite-carrier
routes, promote Route B, or make an RH claim.

## Decision

```text
AUDIT_DECISION: ADMIT
```

Independent semantic review findings:

```text
HIGH: 0
MEDIUM: 0
LOW: 1
WORDING: 0
```

The LOW observation is operational only: one independent target build replayed
`7893/7893` jobs while the executor's two-target build replayed `7894/7894`.
Both completed successfully. Job counts depend on the exact target closure and
are not receipt fields or mathematical evidence.

## Identity and pins

```yaml
ATTESTATION_ID: ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1
QUARANTINE_ENTRY: GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901
BODY: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
DATE: 2026-09-01
AUDITED_HEAD: 870200ade90198ab41cbfa32f72315df6e7f3496
AUDITED_ORIGIN_RH_CLEAN: 870200ade90198ab41cbfa32f72315df6e7f3496
REQUEST_INTRODUCING_COMMIT: 870200ade90198ab41cbfa32f72315df6e7f3496
JOINT_SOURCE_TASK_PIN: 32cccfcd7717c1734044ac16ed97724d4a480a1b
SOURCE_INTRODUCING_COMMIT: bed49f3a0646d2e7d7636ef1d1d7e0978b65d060
AUDIT_RESULT: ADMIT
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
```

The audit ran against a clean writer checkout aligned exactly with
`origin/rh_clean`. The task, source, toolchain, and manifest pins were resolved
from committed Git objects. `32cccfcd` is the first common commit containing
both exact task and source blobs; the source blob is unchanged from its
introducing commit through the audited head.

```text
TASK_BLOB:           7839d0d8fe4610bcb0909572697a9dd9e9cd85fc
SOURCE_BLOB:         8b9b1d38a91b549819b7193ccfd9d7075e65575e
LEAN_TOOLCHAIN_BLOB: e59446d59f6a2bf7f43d60788e2088a603ae6bd4
LAKE_MANIFEST_BLOB:  6d78584bac37944cbe5d7bba46f5e3b53efb74d3
LEAN_TOOLCHAIN:      leanprover/lean4:v4.26.0
```

## Receipt reconstruction and exact bytes

The canonical receipt was independently reconstructed from the quarantine
entry, pinned task and source objects, definitions, and elaborated theorems.
Canonical JSON used sorted keys, compact separators, UTF-8 encoding, no
volatile fields, and exactly one final LF. Reconstruction was byte-for-byte
equal to the tracked receipt.

The structured hypothesis provenance is exactly the empty list. Its canonical
digest is
`4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`.

```text
RECEIPT_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.json
RECEIPT_BYTES: 2032
RECEIPT_SHA256: 592885ae724cfa7712b5ef43bdfed8535253c72ea548f65d5457cf8c0a14b237
RECEIPT_GIT_BLOB: 154c15e0c6e6ee918cc39f7af8638855312522fc
RECEIPT_FINAL_BYTE: exactly one trailing LF; no CR bytes
```

## Detached signature

```text
SIGNATURE_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.sshsig
SCHEME: OPENSSH_SSHSIG
KEY_TYPE: ssh-ed25519
HASH: sha512
NAMESPACE: q3-control-v9-semantic-attestation
PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
SIGNATURE_BYTES: 334
SIGNATURE_SHA256: e78bc8f31257c7bad2bc26c18dae5222f550ac567480dbdcfc983ce9d959cfd3
SIGNATURE_GIT_BLOB: 1b4795efc437a310f300baf1d804c0163b10483f
PUBLIC_KEY_FINGERPRINT: SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
```

The exact successful local verification command was:

```bash
ssh-keygen -Y verify \
  -f /tmp/q3-attest-verify-ovtSCn/semantic_attestation_allowed_signers \
  -I LINUX_INDEPENDENT_SEMANTIC_AUDITOR \
  -n q3-control-v9-semantic-attestation \
  -s orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.sshsig \
  < orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.json
```

It returned:

```text
Good "q3-control-v9-semantic-attestation" signature for LINUX_INDEPENDENT_SEMANTIC_AUDITOR with ED25519 key SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
VERIFY_EXIT: 0
```

The exact external broker receipt bytes were compared with the tracked receipt
and matched. Lookup through the fixed Unix-domain socket returned the exact
attestation ID and issuer.

## Eight required checks

1. **Pinned objects — PASS.** Task, source, toolchain, and lake manifest blobs
   match the joint pin. The source blob is unchanged at the audited head.
2. **Elaborated declarations — PASS.** All three theorem IDs carry exactly the
   public types bound by the receipt.
3. **Schedule and normalization — PASS.** The selected schedule is literally
   `m = N = k + 2`; the even cutoff is definitionally the common source-Weil
   cutoff; cutoff `R` starts the normalized physical pair `±(R+1)`.
4. **Strict universal obstruction — PASS.** The central W02 mode gives
   `2L <= ||W02||`; this forces the band radius above `m^2`, the cutoff scale
   strictly above `m`, and hence `N < cutoff` for every natural `k`. This is
   universal, not eventual, and the inequality direction is not reversed.
5. **Negative consequence — PASS.** `Nat.not_le_of_lt` yields exactly
   `not cutoff <= N` on every selected cell. No odd/even substitution changes
   the cutoff or carrier convention.
6. **Scope firewall — PASS.** No adaptive cutoff, direct selected-`N`
   coercivity, selected Rayleigh upper envelope, finite-head correction, or
   Schur margin is proved. Those obligations remain exactly in `OPENS`.
7. **Receipt field fidelity — PASS.** `admitted_scope`, `CLOSES`, `OPENS`,
   normalization, domain, quantifiers, terminal consumer, theorem IDs,
   hypothesis provenance, and all Git pins match the quarantine entry and
   audited Lean semantics.
8. **Kernel and trust checks — PASS.** The direct Lean check and target build
   completed successfully under `leanprover/lean4:v4.26.0`. Source scan found
   no `sorry`, `admit`, `exact?`, `native_decide`, unsafe/native proof shortcut,
   new axiom, or foreign implementation hook. All three theorems depend only
   on `[propext, Classical.choice, Quot.sound]`; `git diff --check` passed.

## Admitted scope and exclusions

The signature authenticates only the fact that the existing fixed explicit
source-Weil even-tail cutoff lies strictly outside the literal selected finite
carrier on every selected Ferrers cell, and therefore the transfer premise
`cutoff <= N` is false everywhere on that schedule.

It does not obstruct an adaptive cutoff chosen inside the finite carrier, a
direct selected-`N` coercivity proof, a different finite-tail decomposition,
or any finite-head Schur/Feshbach argument. It neither closes Route B nor proves
RH.

The private key remained outside the repository at mode `0600`. Its bytes were
never printed, copied into Git, committed, transmitted, or attached. Only the
detached signature and this source record are repository outputs.

Materialization remains a separate `semantic-admit` transaction.
Route B remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
