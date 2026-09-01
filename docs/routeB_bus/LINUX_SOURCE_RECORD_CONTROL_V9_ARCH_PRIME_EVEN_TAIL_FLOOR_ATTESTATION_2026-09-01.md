# Linux independent semantic-audit source record: Goal 058 Arch-Prime even-tail floor

Answers
`docs/routeB_bus/LINUX_REQUEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_ATTESTATION_2026-09-01.md`.
This is an append-only signed-return record. It does not materialize semantic
admission, edit quarantine state, promote Route B, or make an RH claim.

## Decision

```text
AUDIT_DECISION: ADMIT
```

## Identity and pins

```yaml
ATTESTATION_ID: ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1
QUARANTINE_ENTRY: GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901
BODY: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
DATE: 2026-09-01
AUDITED_HEAD: 39a09900b57df6b3483aa17ffdea6e6f044ab216
AUDITED_ORIGIN_RH_CLEAN: 39a09900b57df6b3483aa17ffdea6e6f044ab216
REQUEST_INTRODUCING_COMMIT: 39a09900b57df6b3483aa17ffdea6e6f044ab216
SOURCE_COMMIT: a5856221e1dddf7b8586f881b5e2c2a0c60d2123
AUDIT_RESULT: ADMIT
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
```

The audit ran in a clean detached checkout. The task, source, toolchain, and
manifest pins were resolved from committed Git objects, and the source blob was
unchanged at the audited head.

```text
TASK_BLOB:           4b5e85dc2ab0fc74ff8b0b3efd5b0caa5b5589f5
SOURCE_BLOB:         f9dc5ce21e00802fcb2488a61c504e957c372691
LEAN_TOOLCHAIN_BLOB: e59446d59f6a2bf7f43d60788e2088a603ae6bd4
LAKE_MANIFEST_BLOB:  6d78584bac37944cbe5d7bba46f5e3b53efb74d3
LEAN_TOOLCHAIN:      leanprover/lean4:v4.26.0
```

## Receipt reconstruction and exact bytes

The canonical receipt was independently reconstructed from the quarantine
entry, pinned task and source objects, and elaborated theorem. Canonical JSON
used sorted keys, compact separators, UTF-8 encoding, no volatile fields, and
exactly one final LF. The reconstruction was byte-for-byte equal to the
tracked receipt.

The complete structured hypothesis provenance is the empty list. Its
independently recomputed digest is
`4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`.

```text
RECEIPT_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1.receipt.json
RECEIPT_BYTES: 1843
RECEIPT_SHA256: f785ec197581afa0af7c9e3adc2109a0a4bcff8b845aeeee346e7b82dcbbb257
RECEIPT_GIT_BLOB: fbcfaa4b9dd82478f610ecbb6bb2487edaf68435
RECEIPT_FINAL_BYTE: exactly one trailing LF; no CR bytes
```

## Detached signature

```text
SIGNATURE_PATH: orchestrator/attestations/control-v9/ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1.receipt.sshsig
SCHEME: OPENSSH_SSHSIG
KEY_TYPE: ssh-ed25519
HASH: sha512
NAMESPACE: q3-control-v9-semantic-attestation
PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
SIGNATURE_BYTES: 334
SIGNATURE_SHA256: 68f0789f77d34e063d48b9f53b8e5a2ab3544fe569c64b7920565a22c4184e04
SIGNATURE_GIT_BLOB: ecc33c83dbee4195b31b4fb791113185e778fcc2
PUBLIC_KEY_FINGERPRINT: SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
```

The exact local verification command was:

```bash
ssh-keygen -Y verify \
  -f /mnt/hdd01/Soft/GitHub/.q3-attest-tmp-tXmvTu/semantic_attestation_allowed_signers \
  -I LINUX_INDEPENDENT_SEMANTIC_AUDITOR \
  -n q3-control-v9-semantic-attestation \
  -s orchestrator/attestations/control-v9/ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1.receipt.sshsig \
  < orchestrator/attestations/control-v9/ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1.receipt.json
```

It returned:

```text
Good "q3-control-v9-semantic-attestation" signature for LINUX_INDEPENDENT_SEMANTIC_AUDITOR with ED25519 key SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
VERIFY_EXIT: 0
```

## Eight required checks

1. **Pinned objects — PASS.** The task and source blobs match the pinned source
   commit. The source blob is unchanged at the audited head. The pinned
   `lean-toolchain` and `lake-manifest.json` blobs also match.
2. **Elaborated declaration — PASS.** The elaborated type and body of
   `Q3.RouteB.D0Pstar.sourceArchPrimeSesquilinearForm_re_self_lower_evenGraphFinsuppShift`
   were printed from the pinned object. The declaration has exactly the public
   theorem surface bound by the receipt.
3. **Exact vector and form — PASS.** For every `PairIndex i` and finitely
   supported complex family `c`, the vector is literally
   `sourceWeilEvenAmbientFinsuppShift i (sourceWeilEvenTailCutoff i) c` and the
   form is literally `sourceArchPrimeSesquilinearForm i` on the matching graph
   synthesis.
4. **Production lower bound and exact margin — PASS.** The proof combines the
   production Archimedean lower bound with the global Prime form-norm bound to
   obtain exactly `norm (sourceW02AmbientContinuousSesquilinearForm i) + 1 / 2`.
   It contains no retained-Prime decay premise, selected-family surrogate,
   approximate identity, closed-tail strengthening, hidden selected-Rayleigh
   estimate, or new hypothesis.
5. **Negative semantic boundary — PASS.** The theorem proves no carrier/cutoff
   crosswalk, `R_k <= N_k`, selected Rayleigh upper envelope, positive shifted
   margin, head coupling, or Schur margin. These remain exactly in `OPENS`.
6. **Hypothesis provenance — PASS.** The structured provenance is exactly the
   empty list, with canonical digest
   `4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`.
7. **Receipt fields — PASS.** `CLOSES`, `OPENS`, normalization, domain,
   quantifiers, terminal consumer, theorem ID, source/task pins, and admitted
   scope match the canonical quarantine entry and the audited Lean semantics.
8. **Kernel checks — PASS.** Under the pinned toolchain, after the standard
   dependency bootstrap in the clean checkout:

   ```text
   env -u LD_LIBRARY_PATH TMPDIR=/mnt/hdd01/Soft/GitHub/.q3-attest-tmp-tXmvTu LAKE_NO_CACHE=1 lake build Q3.Proofs.RouteB.D0PstarSourceWeilEvenTailExplicitCoercivity
   EXIT_CODE: 0
   Build completed successfully (7817 jobs)

   env -u LD_LIBRARY_PATH TMPDIR=/mnt/hdd01/Soft/GitHub/.q3-attest-tmp-tXmvTu lake env lean Q3/Proofs/RouteB/D0PstarSourceWeilEvenTailExplicitCoercivity.lean
   EXIT_CODE: 0
   ```

   The source contains no `sorry`, `admit`, `exact?`, `native_decide`,
   `unsafe`, `implemented_by`, `extern`, `partial def`, `sorryAx`, or new
   `axiom`. `git diff --check` passed. The separate elaboration harness returned
   exactly the public axiom profile `[propext, Classical.choice, Quot.sound]`.

## Admitted scope and exclusions

The signature authenticates only the coarse algebraic even-tail floor

```text
(norm W02_i + 1/2) * norm(v)^2 <= Re(ArchPrime_i(v,v))
```

for the literal finite nonzero-even synthesis at
`sourceWeilEvenTailCutoff i`. It removes the need for a separate retained-Prime
decay input only on that exact algebraic tail.

It does not prove a closed-tail theorem, `R_k <= N_k`, an adaptive cutoff
comparison, a selected Rayleigh upper envelope, a positive shifted tail gap, a
finite-head or full-sector floor, a selected complement floor, Route promotion,
publication, or RH.

The private key remained outside the repository at mode `0600`. Its bytes were
never printed, copied into Git, committed, transmitted, or attached. Only the
detached signature and this source record are repository outputs.

Materialization remains a separate authorized `semantic-admit` transaction.
Route B remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
