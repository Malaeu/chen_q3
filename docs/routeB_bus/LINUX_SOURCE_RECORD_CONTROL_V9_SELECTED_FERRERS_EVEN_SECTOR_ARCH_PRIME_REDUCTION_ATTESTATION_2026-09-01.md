# Linux independent semantic-audit source record: Goal 058 selected even-sector Arch-Prime reduction

Answers `docs/routeB_bus/LINUX_REQUEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_ATTESTATION_2026-09-01.md`.

## Decision

```text
AUDIT_DECISION: ADMIT
```

## Identity and pins

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Audited HEAD and request-introducing commit:
  `993018eb54f07e04287cfbb212386920a64e53dc`
- Audited `origin/rh_clean`:
  `993018eb54f07e04287cfbb212386920a64e53dc`
- Quarantine entry:
  `GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901`
- Attestation ID:
  `ATTEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901_V1`
- Admitted scope:
  `ARCH_PRIME_SHIFTED_FLOOR_EVEN_TO_EXACT_HEVEN`
- Lean toolchain: `leanprover/lean4:v4.26.0`, lake
  `5.0.0-src+d8204c9`, Lean commit
  `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`.

The audited worktree was clean and `HEAD = origin/rh_clean` before the audit.
The request-introducing commit was recomputed with:

```text
git log -1 --format=%H -- docs/routeB_bus/LINUX_REQUEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_ATTESTATION_2026-09-01.md
```

## Receipt bytes

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901_V1.receipt.json
BYTES:      1977
SHA256:     ab78da6f5056cd42002f44109078bb515ebcad54fbf121a865fbc8255979aa00
GIT_BLOB:   233847d4b8623be9dea2c7f41476a32290803321
FINAL_BYTE: exactly one trailing LF; final bytes 0x7d 0x0a
```

The auditor independently reconstructed canonical UTF-8 JSON from the
quarantine entry and the closed attestation fields with sorted keys, compact
separators, and one final LF. The reconstruction was byte-for-byte equal to
the tracked receipt: same 1977 bytes, SHA-256, and Git blob.

## Detached signature

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION_20260901_V1.receipt.sshsig
SCHEME:      OPENSSH_SSHSIG
KEY_TYPE:    ssh-ed25519
HASH:        sha512
NAMESPACE:   q3-control-v9-semantic-attestation
PRINCIPAL:   LINUX_INDEPENDENT_SEMANTIC_AUDITOR
SIG_BYTES:   334
SIG_SHA256:  d70975514a514b2c51c67f9170a9f055b58480b860d74c7d1a941a96106e7daf
SIG_GITBLOB: e2c025e250d4c1fcf7b5cf13c25da70f6a1cdaa6
FINGERPRINT: SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
```

The signed scratch object was an exact byte-copy of the tracked receipt
(`cmp` exit `0`, identical SHA-256 and Git blob). The dedicated private key
remained outside Git, mode `0600`; its bytes were never printed, copied,
committed, or transmitted.

## Local verification

The allowed-signers line was built from the pre-existing public key:

```text
LINUX_INDEPENDENT_SEMANTIC_AUDITOR ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIHuGHK0iP7MQKiXrUNMB7DBRw3Qj2P1UdooD3IycYhaA
```

The exact verification command used the tracked receipt as stdin:

```text
ssh-keygen -Y verify -f <allowed_signers> \
  -I LINUX_INDEPENDENT_SEMANTIC_AUDITOR \
  -n q3-control-v9-semantic-attestation \
  -s <receipt.sshsig> < <tracked-receipt.json>
```

Result:

```text
Good "q3-control-v9-semantic-attestation" signature for
LINUX_INDEPENDENT_SEMANTIC_AUDITOR with ED25519 key
SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
EXIT_CODE: 0
```

Negative control with one changed receipt byte returned exit code `255` and
`Signature verification failed: incorrect signature`.

## Eight required checks

1. **Pinned objects — PASS.** Task blob
   `f17f76aa08d2cfbf4b7dbed5b23dceb73bca9ce2` and source blob
   `255131af8f3202b45b909c67fe548facaa4a4956` match source commit
   `57b642ebd480728b8b30f5219dbcb1946b6422d5` and remain unchanged at audited
   HEAD.
2. **Public theorem surface — PASS.** The three receipt-bound public theorems
   are present with their elaborated types; all helpers and the reachability
   plant are private.
3. **Literal W02 factorization and even positivity — PASS.** The source proves
   the exact factorization
   `32 * L * sinh(L / 4)^2 * (a a^T - b b^T)`, exact annihilation of the odd
   coordinate for every literal complex reflection-even vector, and
   nonnegativity through `star A * A = normSq A`. No surrogate, approximation,
   or real-only weakening is used.
4. **Exact shifted ledger — PASS.** The source finite quadratic form is exactly
   `W02 + Arch - Prime`; the selected Rayleigh scalar times the norm form is
   subtracted exactly once.
5. **Downstream transfer — PASS.** The final theorem preserves the literal
   finite carrier, reflection equation, exact symmetrized-selected-row
   orthogonality, common real `beta`, `Filter.atTop` eventual quantifier,
   selected Rayleigh scalar, and `sourceCCMFiniteMatrix`.
6. **Hypothesis provenance and plant — PASS.** The canonical digest is
   `00eeb8a9adaea9aa686e6d831678992e23d310743dc65c9f6ffcaf15cc95ff5a`.
   The sole row is `NEW_OPEN_OBLIGATION`; its private zero-vector
   `REACHABILITY_PLANT` has scope
   `POINTWISE_ZERO_VECTOR_REACHABILITY_OF_EXACT_SELECTED_ARCHPRIME_ANTECEDENT_SHAPE_ONLY`.
   It is not an `EXACT_FIT_SUPPLIER`, nonzero inhabitant, or supplier for the
   retained-Prime floor.
7. **Closed receipt fields — PASS.** `CLOSES`, `OPENS`, normalization, domain,
   quantifiers, terminal consumer, theorem IDs, source/task pins, provenance
   digest, and admitted scope match the quarantine entry and audited Lean
   semantics.
8. **Kernel checks — PASS.** Under the pinned toolchain:

   ```text
   lake build Q3.Proofs.RouteB.G6N1SelectedFerrersEvenSectorArchPrimeReduction
   EXIT_CODE: 0
   Build completed successfully (7971 jobs)

   lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersEvenSectorArchPrimeReduction.lean
   EXIT_CODE: 0
   ```

   The source and fresh object contain no `sorry`, `admit`, `exact?`,
   `native_decide`, `unsafe`, new `axiom`, `implemented_by`, `extern`, or
   `sorryAx`. `#print axioms` for all three public theorems reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`.

## Scope exclusions

This attestation admits only:

```text
eventual selected reflection-even Arch-Prime floor
  -> exact downstream selected reflection-even heven floor
```

together with literal `W02` nonnegativity on the reflection-even sector. It
does not prove or claim the Arch-Prime floor hypothesis, a nonzero production
inhabitant, positive beta, a positive margin, eventual uniform retained-Prime
control, the open
`SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR`, Route promotion,
publication, or RH. This source record and signature do not themselves mutate
or admit the quarantine entry.

`PX_RH_CLAIM: NOT_MADE`.
