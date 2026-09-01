# Linux auditor request: Goal 058 Arch-Prime floor on the explicit even tail

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Quarantine entry:
  `GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901`
- Attestation ID:
  `ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1`
- Requested exact scope:
  `D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_EXPLICIT_ALGEBRAIC_FLOOR`

This is an authority action for the independent Linux semantic auditor. It
does not admit the entry by itself and does not authorize the adaptive cutoff
crosswalk, selected Rayleigh gap, corrected finite-head Schur margin, later
mathematics, Route promotion, publication, or an RH claim.

## Audit boundary

Start from a clean checkout of the canonical branch containing this request.
Independently reconstruct the receipt from the pinned task, source, quarantine
entry, and elaborated Lean declaration. Do not trust a Codex prose conclusion
or the provided receipt bytes. Compare the independently reconstructed
canonical JSON byte-for-byte with the tracked receipt and reject without
signing on any difference.

The exact admitted theorem is limited to:

```text
for every PairIndex i and finitely supported coefficient family c,
  (norm W02_i + 1/2) * norm(v)^2 <= Re(Arch-Prime_i(v,v))
```

where `v` is the literal finite nonzero-even synthesis beginning at the fixed
`sourceWeilEvenTailCutoff i`. The package removes the need for a separate
retained-Prime decay input on this coarse algebraic tail only.

The signed `OPENS`, terminal consumer, normalization, domain, and quantifiers
are load-bearing negative boundaries. This receipt does not prove a closed-
tail theorem, `R_k <= N_k`, an adaptive cutoff comparison, an upper envelope
for the selected Rayleigh scalar, a positive shifted tail gap, a finite-head
or full-sector floor, a selected complement floor, Route promotion, or RH.

## Exact bytes to authenticate

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1.receipt.json

BYTES:
  1843

SHA256:
  f785ec197581afa0af7c9e3adc2109a0a4bcff8b845aeeee346e7b82dcbbb257

GIT_BLOB_BEFORE_INTRODUCING_COMMIT:
  fbcfaa4b9dd82478f610ecbb6bb2487edaf68435

ENCODING:
  canonical UTF-8 JSON, keys sorted lexicographically, compact separators,
  no volatile fields, plus exactly one final LF
```

Recompute all three values from the canonical branch after pulling. Refuse to
sign if they differ.

## Pinned source objects

```text
TASK_PATH:
  docs/Codex/TASK_2026-09-01_goal058_arch_prime_even_tail_floor.md
TASK_BLOB:
  4b5e85dc2ab0fc74ff8b0b3efd5b0caa5b5589f5

SOURCE_COMMIT:
  a5856221e1dddf7b8586f881b5e2c2a0c60d2123
SOURCE_PATH:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilEvenTailExplicitCoercivity.lean
SOURCE_BLOB:
  f9dc5ce21e00802fcb2488a61c504e957c372691

HYPOTHESIS_PROVENANCE_SHA256:
  4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945

LEAN_TOOLCHAIN:
  leanprover/lean4:v4.26.0
LEAN_TOOLCHAIN_BLOB:
  e59446d59f6a2bf7f43d60788e2088a603ae6bd4
LAKE_MANIFEST_BLOB:
  6d78584bac37944cbe5d7bba46f5e3b53efb74d3
```

## Required semantic checks

1. Verify the pinned task and source blobs at `SOURCE_COMMIT`, verify that the
   source blob is unchanged at the audited branch head, and verify the pinned
   `lean-toolchain` and `lake-manifest.json` blobs.
2. Inspect the elaborated type and body of
   `Q3.RouteB.D0Pstar.sourceArchPrimeSesquilinearForm_re_self_lower_evenGraphFinsuppShift`.
3. Verify that the vector is exactly
   `sourceWeilEvenAmbientFinsuppShift i (sourceWeilEvenTailCutoff i) c`, and
   that the form is exactly `sourceArchPrimeSesquilinearForm i` on the matching
   graph-domain synthesis.
4. Verify the proof uses the production Archimedean lower bound and the global
   Prime form-norm bound to obtain the exact margin `norm W02_i + 1/2`. Reject
   any retained-Prime decay premise, selected-family surrogate, approximate
   identity, closed-tail strengthening, or hidden selected-Rayleigh estimate.
5. Verify that no carrier/cutoff crosswalk, `R_k <= N_k`, selected Rayleigh
   upper envelope, positive shifted margin, head coupling, or Schur margin is
   proved by this theorem. Confirm that these remain exactly in `OPENS`.
6. Recompute the complete structured hypothesis-provenance digest. It is the
   canonical digest of the empty list; no source field, supplier, inhabitant,
   or reachability plant is claimed.
7. Verify that `CLOSES`, `OPENS`, normalization, domain, quantifiers, terminal
   consumer, theorem ID, source/task pins, and admitted scope in the receipt
   match the canonical quarantine entry and audited Lean semantics.
8. Run the direct Lean check, target build, source scan, and axiom audit under
   the pinned toolchain. Reject any `sorry`, `admit`, `exact?`, `native_decide`,
   unsafe/native proof shortcut, new axiom, source/blob drift, or axiom profile
   outside `propext`, `Classical.choice`, and `Quot.sound`.

## Machine verdict

The audit output must contain exactly one unqualified machine token:

```text
AUDIT_DECISION: ADMIT
```

or

```text
AUDIT_DECISION: REJECT
```

Any timeout, partial result, qualification of `ADMIT`, failed check, byte
drift, or missing evidence is `REJECT` and must not produce a signature.

## Frozen signing contract

```text
SCHEME: OPENSSH_SSHSIG
KEY_TYPE: ssh-ed25519
HASH: sha512
NAMESPACE: q3-control-v9-semantic-attestation
PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
PRIVATE_KEY:
  /home/chirurgie/.local/share/q3-control-v9/private/semantic-attestation-ed25519
PRIVATE_KEY_MODE: 0600
PRIVATE_KEY_TRACKED: false
```

If and only if the independent audit returns the exact `ADMIT` token, sign the
exact tracked receipt bytes with `ssh-keygen -Y sign`, verify locally against
the pre-existing trusted public key, and return exactly two repository files:

1. the detached signature at the matching `.receipt.sshsig` path;
2. an append-only Linux source record containing the request-introducing
   commit, receipt byte count/SHA-256/Git blob, signature byte count/SHA-256/
   Git blob, public-key fingerprint, exact verification command and exit code,
   the eight check results, and confirmation that private key material never
   entered Git.

Do not edit the receipt bytes, Lean source, quarantine state, control policy,
Route state, or any RH-facing artifact.

## Codex materialization after signed return

After the signed return is committed and verified, Codex will run:

```bash
python3 orchestrator/three_body_loop.py semantic-admit \
  --entry-id GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901 \
  --attestation-id ATTEST_GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901_V1
```

Codex will compare the pre/post canonical state and require that exactly
`status`, `admitted_scope`, and `semantic_attestation_id` changed for this one
entry. It will then run three-body validation, close-session repair, strict
session start, and Route B status before any downstream use.

`PX_RH_CLAIM: NOT_MADE`.
