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
  FirstZetaPrefix2_2026_04_19.lean
  FirstZetaPrefix3_2026_04_19.lean
  FirstZetaSingleton_2026_04_19.lean
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
- package the concrete `a = 1` first-zeta decimal witness for the
  `prefix2/prefix3` Suzuki shells.

Exports:
- `po3_first_zeta_gap_witness_source`
- `po3_first_zeta_gap_witness_sha256`
- `po3_first_zeta_gap_sum2_a1_decimal28_raw`
- `po3_first_zeta_gap_sum2_a1_decimal28_ne_zero`
- `po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_cert`
- `po3_first_zeta_gap_sum3_a1_decimal28_raw`
- `po3_first_zeta_gap_sum3_a1_decimal28_ne_zero`
- `po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_cert`

## Current honest singleton theorem

File:
- `FirstZetaSingleton_2026_04_19.lean`

Purpose:
- record a theorem-level local obstruction family with no external axiom:
  the decimal-28 zeta witnesses `γ₀,γ₁,γ₂` are rational, so they cannot sit on
  the manuscript `π`-lattice, and the corresponding singleton raw packets at
  `a = 1` already have nonzero anti-diagonal gaps.

Exports:
- `po3_rational_complex_ne_int_mul_pi`
- `po3_rational_complex_sin_ne_zero`
- `po3_complex_sin_ne_zero_of_ne_int_mul_pi`
- `po3_first_zeta_gamma0_decimal28_ne_int_mul_pi`
- `po3_first_zeta_gamma0_decimal28_sin_ne_zero`
- `po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma0_decimal28`
- `po3_first_zeta_gamma1_decimal28_ne_int_mul_pi`
- `po3_first_zeta_gamma1_decimal28_sin_ne_zero`
- `po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma1_decimal28`
- `po3_first_zeta_gamma2_decimal28_ne_int_mul_pi`
- `po3_first_zeta_gamma2_decimal28_sin_ne_zero`
- `po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma2_decimal28`

Upstream shell dependency:
- `Q3/Proofs/HBridge_PO3_Shell.lean`

Numerical provenance:
- `ACTIVE/pipeline/po3_gamma_gap_witness_2026_04_19.json`
- `scripts/po3_gamma_gap_witness.py`

## Current honest `prefix2` theorem

File:
- `FirstZetaPrefix2_2026_04_19.lean`

Purpose:
- remove the off-chain certificate dependency for the concrete
  `a = 1`, `prefix2` witness:
  the file proves that the two manuscript gap weights attached to
  `γ₀, γ₁` are positive real numbers, hence
  `po3_first_zeta_gap_sum2_a1_decimal28 ≠ 0`.

Exports:
- `po3_gap_term20_11_real_a1`
- `po3_gap_term20_11_real_a1_pos`
- `po3_suzuki_filtered_pm_gap_term_20_11_a1_ofReal`
- `po3_suzuki_manuscript_gap_weight_a1_ofReal`
- `po3_suzuki_manuscript_gap_weight_a1_ofReal_pos`
- `po3_first_zeta_gamma0_decimal28_real_gt_three_pi`
- `po3_first_zeta_gamma1_decimal28_real_gt_three_pi`
- `po3_first_zeta_gap_sum2_a1_decimal28_ne_zero_honest`
- `po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_sum2_honest`

Status note:
- `prefix2` now has a theorem-level closure with no external axiom;
- the off-chain file `FirstZetaGapWitness_2026_04_19_Data.lean` remains useful
  for `prefix3` and provenance, but is no longer the only closure path.

## Current honest `prefix3` theorem

File:
- `FirstZetaPrefix3_2026_04_19.lean`

Purpose:
- remove the off-chain certificate dependency for the concrete
  `a = 1`, `prefix3` witness:
  the file proves that the third manuscript gap weight attached to `γ₂`
  is also a positive real number, so the full three-term witness sum
  `po3_first_zeta_gap_sum3_a1_decimal28` is nonzero.

Exports:
- `po3_first_zeta_gamma2_decimal28_real`
- `po3_first_zeta_gamma2_decimal28_eq_ofReal`
- `po3_first_zeta_gamma2_decimal28_real_gt_three_pi`
- `po3_first_zeta_gamma2_decimal28_real_sin_ne_zero`
- `po3_first_zeta_gap_sum3_a1_decimal28_ne_zero_honest`
- `po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_sum3_honest`

Status note:
- `prefix3` now also has a theorem-level closure with no external axiom;
- the off-chain file `FirstZetaGapWitness_2026_04_19_Data.lean` remains useful
  as provenance storage for the frozen numeric snapshot, but is no longer
  needed for either `prefix2` or `prefix3`.

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
