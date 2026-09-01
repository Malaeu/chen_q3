# Linux auditor request: Goal 058 selected even-sector Arch-Prime reduction

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Quarantine entry:
  `GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901`
- Attestation ID:
  `ATTEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901_V1`
- Requested exact scope:
  `ARCH_PRIME_SHIFTED_FLOOR_EVEN_TO_EXACT_HEVEN`

This is an authority action for the independent Linux semantic auditor. It
does not admit the entry by itself and does not authorize the open retained-
Prime floor, later mathematics, Route promotion, publication, or an RH claim.

## Audit boundary

Start from the canonical branch containing this request. Independently
reconstruct the receipt from the pinned task, source, quarantine entry, and
elaborated Lean declarations. Do not trust a Codex prose conclusion or the
provided receipt bytes. Compare the independently reconstructed canonical JSON
byte-for-byte with the tracked receipt and reject without signing on any
difference.

The exact admitted implication is limited to:

```text
eventual selected reflection-even Arch-Prime floor
  -> exact downstream selected reflection-even heven floor
```

The package also proves literal `W02` nonnegativity on the reflection-even
sector. It does not prove the Arch-Prime floor hypothesis, a nonzero production
inhabitant, positive beta, a positive margin, eventual uniform retained-Prime
control, Route promotion, or RH.

## Exact bytes to authenticate

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901_V1.receipt.json

BYTES:
  1977

SHA256:
  ab78da6f5056cd42002f44109078bb515ebcad54fbf121a865fbc8255979aa00

GIT_BLOB_BEFORE_INTRODUCING_COMMIT:
  233847d4b8623be9dea2c7f41476a32290803321

ENCODING:
  canonical UTF-8 JSON plus exactly one final LF
```

Recompute all three values from the canonical branch after pulling. Refuse to
sign if they differ.

## Pinned source objects

```text
TASK_PATH:
  docs/Codex/TASK_2026-09-01_goal058_selected_even_arch_prime_reduction.md
TASK_BLOB:
  f17f76aa08d2cfbf4b7dbed5b23dceb73bca9ce2

SOURCE_COMMIT:
  57b642ebd480728b8b30f5219dbcb1946b6422d5
SOURCE_PATH:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEvenSectorArchPrimeReduction.lean
SOURCE_BLOB:
  255131af8f3202b45b909c67fe548facaa4a4956

HYPOTHESIS_PROVENANCE_SHA256:
  00eeb8a9adaea9aa686e6d831678992e23d310743dc65c9f6ffcaf15cc95ff5a
```

## Required semantic checks

1. Verify the pinned task and source blobs at `SOURCE_COMMIT`, and verify that
   the source blob is unchanged at the audited branch head.
2. Inspect the elaborated types and bodies of all three public declarations:
   - `Q3.RouteB.D0Pstar.ccmW02Quadratic_re_nonneg_of_reflection_even`;
   - `Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix_shifted_floor_of_archPrimeShifted_floor_even`;
   - `Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMEvenSectorFloor_eventually_of_archPrimeShifted`.
3. Verify the literal factorization
   `W02 = 32 * L * sinh(L / 4)^2 * (a a^T - b b^T)`, the exact annihilation
   of the odd coordinate for every literal reflection-even complex vector,
   and the resulting nonnegative quadratic form. Reject a surrogate matrix,
   approximate identity, or real-only weakening.
4. Verify that the source shifted ledger is exactly `W02 + Arch - Prime` and
   that the selected Ferrers Rayleigh scalar is subtracted exactly once.
5. Verify that the final transfer preserves the literal finite carrier,
   reflection equation, exact selected-row-complement orthogonality, beta,
   eventual quantifier, selected Ferrers Rayleigh scalar, and source finite
   matrix without strengthening or weakening the downstream condition.
6. Recompute the complete structured hypothesis-provenance digest. Verify that
   the reachability plant is the zero-vector pointwise antecedent-shape plant
   only. It must not be accepted as a nonzero inhabitant or supplier for
   `SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR`.
7. Verify that `CLOSES`, `OPENS`, normalization, domain, quantifiers, terminal
   consumer, theorem IDs, source/task pins, and admitted scope in the receipt
   match the canonical quarantine entry and the audited Lean semantics.
8. Run the direct Lean check, target build, source scan, and axiom audit. Reject
   any `sorry`, `admit`, `exact?`, unsafe/native proof shortcut, new axiom,
   source/blob drift, or axiom profile outside `propext`, `Classical.choice`,
   and `Quot.sound`.

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
the pre-existing trusted public key, and return outside the repository:

1. the detached signature;
2. an append-only Linux source record containing the request-introducing
   commit, receipt byte count/SHA-256/Git blob, signature byte count/Git blob,
   public-key fingerprint, exact verification command and exit code, the eight
   check results, and confirmation that private key material never entered Git.

Do not edit the receipt bytes, Lean source, quarantine state, control policy,
Route state, or any RH-facing artifact.

## Codex materialization after signed return

After the signed return is committed and verified, Codex will run:

```bash
python3 orchestrator/three_body_loop.py semantic-admit \
  --entry-id GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901 \
  --attestation-id ATTEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901_V1
```

Then it will run the three-body validator, registered closeout repair, and the
strict session-start gate before any downstream theorem consumes the admitted
scope.

`PX_RH_CLAIM: NOT_MADE`.
