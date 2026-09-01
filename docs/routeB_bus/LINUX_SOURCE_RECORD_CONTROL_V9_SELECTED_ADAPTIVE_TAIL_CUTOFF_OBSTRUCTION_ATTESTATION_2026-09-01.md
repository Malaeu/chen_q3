# Linux independent semantic-audit source record: Goal 058 selected adaptive cutoff obstruction

Answers
`docs/routeB_bus/LINUX_REQUEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_ATTESTATION_2026-09-01.md`.
This is an append-only signed-return record. It does not materialize semantic
admission, edit quarantine state, close the unqualified adaptive crosswalk,
promote Route B, or make an RH claim.

## Decision

```text
AUDIT_DECISION: ADMIT
```

Independent semantic review findings:

```text
CRITICAL: 0
HIGH: 0
MEDIUM: 0
LOW: 0
WORDING: 0
```

## Identity and pins

```yaml
ATTESTATION_ID: ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1
QUARANTINE_ENTRY: GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901
BODY: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
DATE: 2026-09-01
AUDITED_HEAD: ba14af22a42abe2756f87464399eca9f44cb1e59
AUDITED_ORIGIN_RH_CLEAN: ba14af22a42abe2756f87464399eca9f44cb1e59
REQUEST_INTRODUCING_COMMIT: ba14af22a42abe2756f87464399eca9f44cb1e59
KERNEL_GREEN_STATE_COMMIT: fc946cea7dead9b604dbbc4320b03e1b5b2e2ceb
JOINT_SOURCE_TASK_PIN: f88cbe75b22172f81ac8d6e190b0930b5c9f6b72
SOURCE_INTRODUCING_COMMIT: aca1823b564d6caa0407c92f4459e99e18b75175
AUDIT_RESULT: ADMIT
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
```

The audit ran against a clean writer checkout aligned exactly with
`origin/rh_clean`. The task, source, toolchain, manifest, quarantine, and
request pins were resolved from committed Git objects. The source blob is
unchanged from its introducing commit through the audited head.

```text
TASK_BLOB:           596341e66bd9e28695e72337dd12672d3135f44c
SOURCE_BLOB:         fff37ed51262174b1d1cb93e144d3cbafde30218
LEAN_TOOLCHAIN_BLOB: e59446d59f6a2bf7f43d60788e2088a603ae6bd4
LAKE_MANIFEST_BLOB:  6d78584bac37944cbe5d7bba46f5e3b53efb74d3
LEAN_TOOLCHAIN:      leanprover/lean4:v4.26.0
```

## Receipt reconstruction and exact bytes

The canonical receipt was independently reconstructed from the quarantine
entry, pinned task and source objects, imported admitted premise, and
elaborated theorem. Canonical JSON used sorted keys, compact separators,
UTF-8 encoding, no volatile fields, and exactly one final LF. Reconstruction
was byte-for-byte equal to the tracked receipt.

The structured hypothesis provenance is exactly the empty list. Its canonical
digest is
`4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`.

```text
RECEIPT_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.json
RECEIPT_BYTES: 2097
RECEIPT_SHA256: a219b393ea570c2ba25fdb61d2280b8adeedf8fc3c79229bfb7d2b7c957eb502
RECEIPT_GIT_BLOB: 393c7e541adff9b387f07589e1a1c80cfc4de2b8
RECEIPT_FINAL_BYTE: exactly one trailing LF; no CR bytes
```

## Detached signature

```text
SIGNATURE_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.sshsig
SCHEME: OPENSSH_SSHSIG
KEY_TYPE: ssh-ed25519
HASH: sha512
NAMESPACE: q3-control-v9-semantic-attestation
PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
SIGNATURE_BYTES: 334
SIGNATURE_SHA256: 03dbab020d19f0139c9f260b5e6a8c7197b49fc02291a3f1a1cb63642d8f0500
SIGNATURE_GIT_BLOB: 08eab846c79759ff5357207346e979b314c7d497
PUBLIC_KEY_FINGERPRINT: SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
```

The exact successful local verification command was:

```bash
ssh-keygen -Y verify \
  -f <(awk '{print "LINUX_INDEPENDENT_SEMANTIC_AUDITOR namespaces=\"q3-control-v9-semantic-attestation\" "$1" "$2}' \
    /home/chirurgie/.local/share/q3-control-v9/private/semantic-attestation-ed25519.pub) \
  -I LINUX_INDEPENDENT_SEMANTIC_AUDITOR \
  -n q3-control-v9-semantic-attestation \
  -s orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.sshsig \
  < orchestrator/attestations/control-v9/ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.json
```

It returned:

```text
Good "q3-control-v9-semantic-attestation" signature for LINUX_INDEPENDENT_SEMANTIC_AUDITOR with ED25519 key SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
VERIFY_EXIT: 0
```

## Eight required checks

1. **Pinned objects — PASS.** Task, source, toolchain, manifest, joint source
   pin, kernel-green state, request commit, and audited head all match. The
   source blob is unchanged at the audited head.
2. **Elaborated declaration — PASS.** The public type is exactly
   `forall k, not exists R, C_k <= R and R <= N_k`. The proof body applies the
   imported obstruction to transitivity of the two inequalities.
3. **Imported premise — PASS.** The consumed universal inequality `N_k < C_k`
   is already `SEMANTICALLY_ADMITTED`; its receipt and detached signature were
   verified against the local trusted key fingerprint.
4. **Schedule and normalization — PASS.** The selected schedule is literally
   `m = N = k + 2`; `C_k` is the common existing source-Weil even-tail cutoff;
   cutoff `R` starts the normalized physical pair `±(R+1)`.
5. **Direction and quantifiers — PASS.** `C_k <= R` is the correct direction
   for restriction from `Tail(C_k)` to the later `Tail(R)`. Together with
   `R <= N_k` it contradicts `N_k < C_k` for every natural `k`, not merely
   eventually.
6. **Scope firewall — PASS.** The theorem closes only
   `ADAPTIVE_REUSE_OF_EXISTING_EXPLICIT_EVEN_TAIL_VIA_C_LE_R_LE_N`. It does
   not rule out `R_k < C_k` with a new estimate, direct selected-`N`
   coercivity, the pure block identity, a Rayleigh envelope, or finite-head
   Schur positivity. All six obligations remain exactly in `OPENS`.
7. **Receipt field fidelity — PASS.** `admitted_scope`, `CLOSES`, `OPENS`,
   normalization, domain, quantifiers, terminal consumer, theorem ID,
   hypothesis provenance, and all Git pins match the quarantine entry and
   audited Lean semantics.
8. **Kernel and trust checks — PASS.** Direct Lean completed with exit 0 on
   the exact source bytes. Source scan found no `sorry`, `admit`, `exact?`,
   `native_decide`, unsafe/native proof shortcut, new axiom, or foreign
   implementation hook. The theorem depends only on `propext`,
   `Classical.choice`, and `Quot.sound`. The pinned source package records a
   successful target build of `7894/7894`; the redundant audit replay was
   stopped after direct kernel and source checks had independently passed.

## Admitted scope and exclusions

The signature authenticates only the impossibility of choosing a cutoff at or
after the existing explicit cutoff while also placing it no later than the
literal selected endpoint. This kills reuse of the current explicit theorem by
that adaptive restriction pattern.

It does not obstruct a new source-specific estimate before the current cutoff,
a direct selected-`N` coercivity proof, a pure finite block identity, or a
finite-head Schur/Feshbach argument. It neither closes Route B nor proves RH.

The private key remained outside the repository at mode `0600`. Its bytes were
never printed, copied into Git, committed, transmitted, or attached. Only the
detached signature and this source record are repository outputs.

Materialization remains a separate `semantic-admit` transaction.
Route B remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
