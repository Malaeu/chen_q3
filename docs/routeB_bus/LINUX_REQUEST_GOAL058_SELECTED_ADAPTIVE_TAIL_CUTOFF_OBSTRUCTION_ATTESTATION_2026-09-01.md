# Linux auditor request: Goal 058 selected adaptive explicit-tail reuse obstruction

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Quarantine entry:
  `GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901`
- Attestation ID:
  `ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1`
- Requested exact scope:
  `ADAPTIVE_REUSE_OF_EXISTING_EXPLICIT_EVEN_TAIL_VIA_C_LE_R_LE_N`

This authority action asks the independent Linux semantic auditor to verify a
negative, source-level obstruction. It does not admit the quarantine entry by
itself and does not close the unqualified adaptive crosswalk, a new earlier
source estimate, direct selected-`N` coercivity, the retained-prime shifted
floor, a selected Rayleigh upper envelope, the corrected finite-head Schur
margin, Route B, or RH.

## Audit boundary

Start from a clean checkout of the canonical branch containing this request.
Independently reconstruct the canonical receipt from the pinned task, source,
quarantine entry, imported admitted theorem, and elaborated Lean declaration.
Do not trust a Codex prose conclusion or the provided receipt bytes. Compare
the reconstructed canonical JSON byte-for-byte with the tracked receipt and
reject without signing on any difference.

The exact input is the already semantically admitted universal inequality

```text
N_k < C_k,

C_k := sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k),
N_k := (selectedFerrersPreAnchorIndex k).N.
```

The new theorem derives exactly

```text
not exists R, C_k <= R and R <= N_k.
```

The signed `OPENS`, terminal consumer, normalization, domain, and quantifiers
are load-bearing negative boundaries. The result kills only reuse of the
existing explicit tail theorem by restricting it from `Tail(C_k)` to a later
`Tail(R)` which must still begin no later than the selected endpoint.

## Exact bytes to authenticate

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.json

BYTES:
  2097

SHA256:
  a219b393ea570c2ba25fdb61d2280b8adeedf8fc3c79229bfb7d2b7c957eb502

GIT_BLOB_BEFORE_INTRODUCING_COMMIT:
  393c7e541adff9b387f07589e1a1c80cfc4de2b8

ENCODING:
  canonical UTF-8 JSON, keys sorted lexicographically, compact separators,
  no volatile fields, plus exactly one final LF
```

Recompute all three values from the canonical branch after pulling. Refuse to
sign if they differ.

## Pinned source objects

```text
TASK_PATH:
  docs/Codex/TASK_2026-09-01_goal058_selected_adaptive_tail_cutoff_obstruction.md
TASK_BLOB:
  596341e66bd9e28695e72337dd12672d3135f44c

SOURCE_COMMIT:
  f88cbe75b22172f81ac8d6e190b0930b5c9f6b72
SOURCE_PATH:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSelectedFerrersAdaptiveTailCutoffObstruction.lean
SOURCE_BLOB:
  fff37ed51262174b1d1cb93e144d3cbafde30218

KERNEL_GREEN_STATE_COMMIT:
  fc946cea7dead9b604dbbc4320b03e1b5b2e2ceb

HYPOTHESIS_PROVENANCE_SHA256:
  4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945

LEAN_TOOLCHAIN:
  leanprover/lean4:v4.26.0
LEAN_TOOLCHAIN_BLOB:
  e59446d59f6a2bf7f43d60788e2088a603ae6bd4
LAKE_MANIFEST_BLOB:
  6d78584bac37944cbe5d7bba46f5e3b53efb74d3
```

`SOURCE_COMMIT` is the first pinned commit containing both exact task and
source blobs. The Lean source itself was introduced at
`aca1823b564d6caa0407c92f4459e99e18b75175` and is byte-identical at the joint
pin and audited branch head.

## Required semantic checks

1. Verify all pinned blobs, the source-introducing and joint-pin commits, and
   that the source blob is unchanged at the audited branch head.
2. Inspect the elaborated type and body of
   `Q3.RouteB.D0Pstar.selectedFerrersPreAnchorIndex_no_tailCutoff_between_fixed_and_N`
   and the imported admitted theorem it consumes.
3. Verify that the selected schedule literally has `m = N = k + 2`, that
   `C_k` is the existing common source-Weil even-tail cutoff, and that cutoff
   `R` begins at the normalized physical pair `±(R+1)`.
4. Verify the direction: `C_k <= R` is precisely what permits restriction of
   an existing estimate on `Tail(C_k)` to the later subspace `Tail(R)`, while
   `R <= N_k` is the deliberately weaker inside-endpoint condition.
5. Verify that universal `N_k < C_k` plus `C_k <= R <= N_k` yields the exact
   contradiction for every natural `k`, with no eventuality, strictness, or
   order reversal hidden in prose.
6. Verify that the theorem does not rule out `R_k < C_k` with a new
   source-specific estimate, direct selected-`N` coercivity, the pure
   `toBlocks22` identity, a Rayleigh envelope, or finite-head Schur positivity.
   Confirm all six obligations remain exactly in `OPENS`.
7. Verify all receipt fields, including the empty hypothesis-provenance digest,
   against the quarantine entry and audited Lean semantics.
8. Run direct Lean, target build, source scan, and axiom audit under the pinned
   toolchain. Reject any hole, unsafe/native shortcut, new axiom, pin drift, or
   axiom profile outside `propext`, `Classical.choice`, and `Quot.sound`.

## Prior review evidence

The prior internal reviewer returned `ADMIT, scoped kill only` with zero
critical, high, medium, or low findings. It independently confirmed the
universal quantifier, order direction, subspace restriction, and narrow scope.
That review is evidence only. The Linux auditor must still reproduce every
required check and receipt byte independently before signing.

## Machine verdict

The audit output must contain exactly one unqualified machine token:

```text
AUDIT_DECISION: ADMIT
```

or

```text
AUDIT_DECISION: REJECT
```

Any timeout, partial result, qualified admission, failed check, byte drift, or
missing evidence is `REJECT` and must not produce a signature.

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
2. an append-only Linux source record containing all pins, exact audit checks,
   receipt and signature identities, verification command and exit code, and
   confirmation that private key material never entered Git.

Do not edit the receipt bytes, Lean source, quarantine state, control policy,
Route state, or RH-facing artifacts during the auditor return.

## Codex materialization after signed return

After the signed return is committed and verified, Codex will run:

```bash
python3 orchestrator/three_body_loop.py semantic-admit \
  --entry-id GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901 \
  --attestation-id ATTEST_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_20260901_V1
```

Exactly `status`, `admitted_scope`, and `semantic_attestation_id` may change.
Only after that transaction may the narrow explicit-reuse shortcut be closed
downstream.

`PX_RH_CLAIM: NOT_MADE`.
