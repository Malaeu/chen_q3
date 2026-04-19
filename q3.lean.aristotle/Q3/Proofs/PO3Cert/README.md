# PO3Cert

Off-chain certificate layer for local `PO3` witness closures.

This directory is intentionally **not** part of the active public mainline.
Its role is narrower:

- freeze explicit numerical witness candidates for the `PO3` shell;
- record provenance (`source`, `sha256`, raw reported values);
- expose a small named certificate axiom;
- close one already-compiled shell theorem from that certificate.

Current file map:

```text
PO3Cert/
  FirstZetaGapWitness_2026_04_19_Data.lean
  README.md
```

Top-level import hub:

```text
Q3/Proofs/PO3Cert.lean
```

## Current certificate

File:
- `FirstZetaGapWitness_2026_04_19_Data.lean`

Purpose:
- package the concrete `a = 1` first-zeta decimal witness for the `prefix3`
  Suzuki shell.

Exports:
- `po3_first_zeta_gap_witness_source`
- `po3_first_zeta_gap_witness_sha256`
- `po3_first_zeta_gap_sum3_a1_decimal28_raw`
- `po3_first_zeta_gap_sum3_a1_decimal28_ne_zero`
- `po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_cert`

Upstream shell dependency:
- `Q3/Proofs/HBridge_PO3_Shell.lean`

Numerical provenance:
- `ACTIVE/pipeline/po3_gamma_gap_witness_2026_04_19.json`
- `scripts/po3_gamma_gap_witness.py`

## Usage rule

This layer is for explicit certificate experiments and local closures only.

It should:
- stay separate from `Q3.Main` and the active public theorem chain;
- carry provenance for every numeric certificate;
- expose the smallest possible certificate axiom;
- avoid mixing certificate data with the main analytic shell.

If a certificate is later replaced by a genuine proof, the intended path is:

1. remove or bypass the local certificate axiom,
2. keep the closure theorem name if possible,
3. preserve the provenance note in `docs/insights/`.
