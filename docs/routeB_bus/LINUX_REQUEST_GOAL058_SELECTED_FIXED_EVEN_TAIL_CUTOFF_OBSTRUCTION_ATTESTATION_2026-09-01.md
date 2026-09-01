# Linux auditor request: Goal 058 selected fixed even-tail cutoff obstruction

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Quarantine entry:
  `GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901`
- Attestation ID:
  `ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1`
- Requested exact scope:
  `FIXED_SOURCE_WEIL_EVEN_TAIL_CUTOFF_LE_SELECTED_FERRERS_N`
  and
  `FIXED_SOURCE_WEIL_EVEN_TAIL_DIRECT_TRANSFER_VIA_CUTOFF_LE_N`

This authority action asks the independent Linux semantic auditor to verify a
negative, source-level obstruction. It does not admit the quarantine entry by
itself and does not close adaptive cutoff domination, direct selected-`N`
coercivity, a selected Rayleigh upper envelope, the corrected finite-head
Schur margin, Route B, or RH.

## Audit boundary

Start from a clean checkout of the canonical branch containing this request.
Independently reconstruct the canonical receipt from the pinned task, source,
quarantine entry, and elaborated Lean declarations. Do not trust a Codex prose
conclusion or the provided receipt bytes. Compare the reconstructed canonical
JSON byte-for-byte with the tracked receipt and reject without signing on any
difference.

The exact result is limited to:

```text
for every natural k,
  (selectedFerrersPreAnchorIndex k).N
    < sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k)
```

and therefore the fixed premise

```text
sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k)
  <= (selectedFerrersPreAnchorIndex k).N
```

is false on every selected Ferrers cell. The signed `OPENS`, terminal
consumer, normalization, domain, and quantifiers are load-bearing negative
boundaries. The result kills only a transfer requiring that fixed premise.

## Exact bytes to authenticate

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1.receipt.json

BYTES:
  2032

SHA256:
  592885ae724cfa7712b5ef43bdfed8535253c72ea548f65d5457cf8c0a14b237

GIT_BLOB_BEFORE_INTRODUCING_COMMIT:
  154c15e0c6e6ee918cc39f7af8638855312522fc

ENCODING:
  canonical UTF-8 JSON, keys sorted lexicographically, compact separators,
  no volatile fields, plus exactly one final LF
```

Recompute all three values from the canonical branch after pulling. Refuse to
sign if they differ.

## Pinned source objects

```text
TASK_PATH:
  docs/Codex/TASK_2026-09-01_goal058_selected_fixed_even_tail_cutoff_obstruction.md
TASK_BLOB:
  7839d0d8fe4610bcb0909572697a9dd9e9cd85fc

SOURCE_COMMIT:
  32cccfcd7717c1734044ac16ed97724d4a480a1b
SOURCE_PATH:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSelectedFerrersEvenTailCutoffObstruction.lean
SOURCE_BLOB:
  8b9b1d38a91b549819b7193ccfd9d7075e65575e

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
source blobs. The Lean source itself was introduced at `bed49f3a0646d2e7d7636ef1d1d7e0978b65d060`
and is byte-identical at the joint pin.

## Required semantic checks

1. Verify all pinned blobs, the source-introducing commit, and that the source
   blob is unchanged at the audited branch head.
2. Inspect the elaborated types and bodies of all three theorem IDs carried by
   the receipt.
3. Verify the selected schedule literally has `m = N = k + 2` and that the
   cutoff convention starts the normalized physical pair at `R + 1`.
4. Verify the quantitative chain from the central `W02` form norm through the
   band radius and cutoff scale proves strict `N < cutoff` for every `k`, not
   merely eventually and not in the opposite direction.
5. Verify that the even cutoff is definitionally the existing common source-
   Weil cutoff and that no odd/even substitution changes the statement.
6. Verify the result proves no adaptive cutoff, direct selected-`N` coercivity,
   Rayleigh upper envelope, finite-head correction, or Schur margin. Confirm
   these remain exactly in `OPENS`.
7. Verify all receipt fields, including the empty hypothesis-provenance digest,
   against the quarantine entry and audited Lean semantics.
8. Run direct Lean, target build, source scan, and axiom audit under the pinned
   toolchain. Reject any hole, unsafe/native shortcut, new axiom, pin drift, or
   axiom profile outside `propext`, `Classical.choice`, and `Quot.sound`.

## Independent review evidence

The prior internal semantic reviewer returned `ADMIT` with zero high, medium,
or low findings and explicitly confirmed the universal quantifier, strict
direction, cutoff normalization, and negative scope. That review is evidence
only. The Linux auditor must still reproduce every required check and receipt
byte independently before signing.

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
  --entry-id GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901 \
  --attestation-id ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1
```

Exactly `status`, `admitted_scope`, and `semantic_attestation_id` may change.
Only after that transaction may the fixed transfer be closed downstream.

`PX_RH_CLAIM: NOT_MADE`.
