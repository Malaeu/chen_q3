# Linux auditor request: Goal 058 finite CCM reflection-even head/tail crosswalk

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Quarantine entry:
  `GOAL058_D0PSTAR_FINITE_CCM_REFLECTION_EVEN_HEAD_TAIL_CROSSWALK_20260901`
- Attestation ID:
  `ATTEST_GOAL058_D0PSTAR_FINITE_CCM_REFLECTION_EVEN_HEAD_TAIL_CROSSWALK_20260901_V1`
- Requested exact scope:
  `D0PSTAR_FINITE_CCM_REFLECTION_EVEN_TO_SOURCE_WEIL_HEAD_TAIL_CROSSWALK`

This is an authority action for the independent Linux semantic auditor. It
does not admit the entry by itself and does not authorize later mathematics,
Route promotion, publication, or an RH claim.

## Independent semantic verdict to reproduce

An isolated Q3 semantic-agent pass returned `ADMIT` after checking all six Lean
declarations, the literal production objects, normalization, quantifiers,
consumer condition, `CLOSES`, `OPENS`, inhabitance/reachability, empty
hypothesis provenance, axioms, and Git bindings. The Linux auditor must repeat
the audit from the canonical branch and refuse to sign on any mismatch.

The exact semantic claim is limited to this implication:

```text
literal finite CCM vector fixed by the literal reflection matrix
  -> reconstruction as the source-Weil zero-plus-symmetric-even finite head
  -> ambient orthogonality to the exact closed nonzero-even tail
```

It does not prove selected-Ferrers coercivity, a positive Schur margin,
complement-floor transport, G1/G3, Route promotion, or RH.

## Exact bytes to authenticate

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_D0PSTAR_FINITE_CCM_REFLECTION_EVEN_HEAD_TAIL_CROSSWALK_20260901_V1.receipt.json

BYTES:
  2173

SHA256:
  dd061da327967ad8e76587fdcd1f57448f4b407a1817daf34479642c3d5873c9

GIT_BLOB_BEFORE_INTRODUCING_COMMIT:
  dd2e2ced4bd967dae73ee4eb126bb24250af9ad6

ENCODING:
  canonical UTF-8 JSON plus exactly one final LF
```

Recompute all three values from the canonical branch after pulling. Refuse to
sign if they differ.

## Required semantic checks

1. Verify the task and source blobs at source commit
   `7f5cbc0589b796750312b378ec38229e9ecfb14f`.
2. Verify every `theorem_ids` declaration against its elaborated Lean type.
3. Verify that the final theorem consumes the literal condition
   `ccmComplexReflectionMatrix i.N *ᵥ x = x` and returns the stated ambient
   orthogonality for every exact closed-tail vector.
4. Verify that center mode `0`, the physical pairs `±(r+1)`, and the
   `sqrt 2` coefficient normalization are literal, not surrogate.
5. Verify that the downstream reflection-even condition in
   `selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual`
   is the same condition, while the positive coercivity/Schur margin remains
   open.
6. Verify the canonical empty provenance digest
   `4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`.
7. Run the direct Lean build and axiom audit; reject any `sorry`, `admit`,
   `exact?`, unsafe/native proof shortcut, new axiom, or source/blob drift.

## Frozen signing contract

```text
SCHEME: OPENSSH_SSHSIG
KEY_TYPE: ssh-ed25519
HASH: sha512
NAMESPACE: q3-control-v9-semantic-attestation
PRINCIPAL: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
PRIVATE_KEY:
  /var/lib/q3-control-v9/private/semantic-attestation-ed25519
PRIVATE_KEY_MODE: 0600
PRIVATE_KEY_TRACKED: false
```

If and only if the independent audit returns `ADMIT`, sign the exact receipt
bytes with `ssh-keygen -Y sign`, verify locally, and commit/push exactly:

1. the detached signature at the matching `.receipt.sshsig` path;
2. an append-only Linux source record containing the receipt SHA-256/Git blob,
   signature Git blob, public-key fingerprint, exact verification command and
   exit code, and confirmation that private key material never entered Git.

Do not edit the receipt bytes, Lean source, quarantine state, control policy,
Route state, or any RH-facing artifact.

## Mac materialization after signed return

After the signed return commit is fetched and verified, the Mac body will run:

```bash
python3 orchestrator/three_body_loop.py semantic-admit \
  --entry-id GOAL058_D0PSTAR_FINITE_CCM_REFLECTION_EVEN_HEAD_TAIL_CROSSWALK_20260901 \
  --attestation-id ATTEST_GOAL058_D0PSTAR_FINITE_CCM_REFLECTION_EVEN_HEAD_TAIL_CROSSWALK_20260901_V1
```

Then it will run the three-body validator and strict session-start gate before
any downstream theorem consumes the admitted scope.
