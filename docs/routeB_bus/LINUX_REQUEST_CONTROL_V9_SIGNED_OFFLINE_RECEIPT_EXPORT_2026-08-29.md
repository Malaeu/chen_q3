# Linux auditor request: export the Control-v9 signed offline receipt

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Verdict: `66533ae2a009c7d495aeee2b842c85e21b2d2da0`
- Operative class: `TRY_CONTROL_V9_SIGNED_OFFLINE_ATTESTATION_RECEIPT`
- Attestation ID:
  `ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1`

This is an authority action for the independent Linux semantic auditor.  It
does not reopen W5 and does not authorize any Lean, quarantine, Route, or RH
edit.

## Exact bytes to authenticate

```text
PATH:
  orchestrator/attestations/control-v9/
  ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.json

BYTES:
  1435

SHA256:
  e02d953cc4e894da1a18ce6a3ab546f83346c5a6e568c4ceeb32480c741eee38

GIT_BLOB_BEFORE_INTRODUCING_COMMIT:
  3fb888192ff4f1e43d3dbe27bca3c2c3e6b32547

ENCODING:
  canonical UTF-8 JSON plus exactly one final LF
```

Recompute all three facts from the canonical branch after pulling.  Refuse to
sign on any mismatch.

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

If the auditor key does not yet exist, create it on the independent Linux host
under the frozen path, owned only by the auditor account.  Never print, attach,
commit, or transmit the private key.

Sign the exact tracked receipt bytes with OpenSSH `ssh-keygen -Y sign`.  Move
the detached signature to the exact tracked path:

```text
orchestrator/attestations/control-v9/
ATTEST_GOAL058_W5_B635BA98B2C465FFE271B0775AFD174F74953C19_V1.receipt.sshsig
```

Verify the signature locally before commit with an allowed-signers file whose
only active line carries the exact principal, exact namespace, and the public
half of the auditor Ed25519 key.

## Return transaction

Commit and push exactly:

1. the detached `.receipt.sshsig` file;
2. an append-only Linux source record under `docs/routeB_bus/` containing:
   - receipt SHA256 and Git blob;
   - signature Git blob;
   - public-key SHA256 fingerprint;
   - the exact single allowed-signers line needed on Mac;
   - the successful `ssh-keygen -Y verify` command and exit code;
   - confirmation that the private key never entered the repository.

Do not commit the private key.  Do not install or modify the Mac trust root.
Do not edit the receipt bytes, Lean, `SEMANTIC_QUARANTINE.json`, W5 mathematics,
Route state, or any RH-facing artifact.

## Mac handoff after the return commit

The Mac body will independently:

1. verify the returned source record and signature;
2. request action-time owner confirmation for the root-owned `/etc` trust
   installation;
3. install the one-key allowed-signers file and empty canonical revocation
   snapshot;
4. run all 111+ control tests and the strict startup gate with Linux offline.
