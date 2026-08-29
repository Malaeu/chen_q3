# Linux auditor return: Control-v9 signed offline attestation receipt

Answers `docs/routeB_bus/LINUX_REQUEST_CONTROL_V9_SIGNED_OFFLINE_RECEIPT_EXPORT_2026-08-29.md`
under verdict `66533ae2a009c7d495aeee2b842c85e21b2d2da0`,
operative class `TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT`.

Append-only record. Nothing here reopens W5, Route B or any RH-facing artifact.

```yaml
ATTESTATION_ID: ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1
BODY: LINUX_INDEPENDENT_SEMANTIC_AUDITOR
DATE: 2026-08-29
BASE_HEAD: d1c42021
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Authenticated bytes, recomputed from the canonical branch

Recomputed after fetching `origin/rh_clean`, not copied from the request.
All three facts match the request exactly; nothing was signed on a mismatch.

```text
PATH:    orchestrator/attestations/control-v9/ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.json
BYTES:   1435                                                     (request: 1435)
SHA256:  e02d953cc4e894da1a18ce6a3ab546f83346c5a6e568c4ceeb32480c741eee38
                                                                  (request: identical)
GITBLOB: 3fb888192ff4f1e43d3dbe27bca3c2c3e6b32547                 (request: identical)
FINAL_BYTE: 0x0a
```

The receipt bytes were re-verified unchanged after re-pointing the worktree at
`d1c42021`, so the signature is bound to the current canonical bytes.

## 2. Signature

```text
SCHEME:     OPENSSH_SSHSIG
KEY_TYPE:   ssh-ed25519
HASH:       sha512
NAMESPACE:  q3-control-v9-semantic-attestation
PRINCIPAL:  LINUX_INDEPENDENT_SEMANTIC_AUDITOR
SIG_PATH:   orchestrator/attestations/control-v9/ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.sshsig
SIG_BYTES:  334
SIG_GITBLOB: 22e60ad16c41c32842868a499df69c26df48a30a
```

Signing command, exactly as run:

```bash
ssh-keygen -Y sign -f <auditor-private-key> \
  -n q3-control-v9-semantic-attestation -O hashalg=sha512 \
  orchestrator/attestations/control-v9/ATTEST_..._V1.receipt.json
```

## 3. Public key and the exact Mac allowed-signers line

```text
PUBKEY_FINGERPRINT: SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y
```

The single active line required at
`/etc/q3-control-v9/semantic_attestation_allowed_signers` on the Mac:

```text
LINUX_INDEPENDENT_SEMANTIC_AUDITOR namespaces="q3-control-v9-semantic-attestation" ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIHuGHK0iP7MQKiXrUNMB7DBRw3Qj2P1UdooD3IycYhaA
```

No wildcard principal. No second active key.

## 4. Local verification before commit

```bash
ssh-keygen -Y verify -f <allowed_signers> \
  -I LINUX_INDEPENDENT_SEMANTIC_AUDITOR \
  -n q3-control-v9-semantic-attestation \
  -s ATTEST_..._V1.receipt.sshsig < ATTEST_..._V1.receipt.json
```

```text
Good "q3-control-v9-semantic-attestation" signature for
LINUX_INDEPENDENT_SEMANTIC_AUDITOR with ED25519 key
SHA256:dL4YF766C7C8oy7mO83ME5CZdnpE3swKEjYsauzcY5Y

EXIT_CODE: 0
```

## 5. Private key containment

The private key was never printed, attached, committed or transmitted. Only the
public half and its fingerprint appear above. `git status` in the signing
worktree shows no key material, and the key lives outside the repository tree.

## 6. Recorded deviation: interim private-key location

```text
FROZEN_PATH:  /var/lib/q3-control-v9/private/semantic-attestation-ed25519
ACTUAL_PATH:  ~/.local/share/q3-control-v9/private/semantic-attestation-ed25519
DIR_MODE:     0700
KEY_MODE:     0600
REASON:       creating the frozen path requires root; no non-interactive sudo
              is available to this body, and the owner asked for the Mac to be
              unblocked without waiting.
```

This deviation is hygiene only. It changes no signed byte, no namespace, no
principal and no verification result: the Mac never sees the private key, only
the pinned public half above. To move the key to the frozen path later, the
owner runs, as root on this host:

```bash
sudo install -d -m 0700 -o "$USER" -g "$USER" /var/lib/q3-control-v9/private
sudo install -m 0600 -o "$USER" -g "$USER" \
  ~/.local/share/q3-control-v9/private/semantic-attestation-ed25519 \
  /var/lib/q3-control-v9/private/semantic-attestation-ed25519
```

Rotation is not required by the move: the key material is unchanged.

## 7. What this record does NOT do

- The Mac trust root was not installed or modified from here.
- `SEMANTIC_QUARANTINE.json`, Lean sources, W5 mathematics and Route state are
  untouched.
- The open gap `W5_COFINAL_PACKET_BUDGET_RATE` remains open.
- Route B remains `CHALLENGER / NOT_RH`.
