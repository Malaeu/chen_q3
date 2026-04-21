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
  FirstZetaSquareBridge_2026_04_19.lean
  FirstZetaSingleton_2026_04_19.lean
  FirstZetaWitnessStack_2026_04_19.lean
  WindowLawCertificate_2026_04_19.lean
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

## Current honest first-zeta witness-stack package

File:
- `FirstZetaWitnessStack_2026_04_19.lean`

Purpose:
- expose the now-closed local first-zeta packet as one reusable shell-facing
  object, instead of five separate theorem endpoints;
- bundle together the honest closures for
  `singleton(γ₀)`, `singleton(γ₁)`, `singleton(γ₂)`,
  `prefix2(γ₀,γ₁)`, and `prefix3(γ₀,γ₁,γ₂)`.

Exports:
- `po3_first_zeta_initial_packet_tag`
- `po3_first_zeta_initial_packet_raw`
- `po3_first_zeta_initial_packet_profile_of_tag`
- `po3_no_suzuki_filtered_pm_candidate_of_first_zeta_initial_packet`
- `po3_first_zeta_initial_packet_raw_ne_filtered_candidate`
- `po3_no_tagged_first_zeta_initial_packet_eq_filtered_candidate`
- `po3_no_filtered_candidate_of_eq_first_zeta_initial_packet_raw`
- `po3_no_filtered_candidate_of_exists_eq_first_zeta_initial_packet_raw`
- `po3_false_of_exists_eq_first_zeta_initial_packet_raw_and_filtered_candidate`
- `po3_first_zeta_initial_packet_kernel`
- `po3_first_zeta_initial_packet_kernel_ne_filtered_candidate`
- `po3_no_filtered_candidate_of_first_zeta_initial_packet_kernel`
- `po3_false_of_first_zeta_initial_packet_kernel_and_filtered_candidate`
- `po3_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel`
- `po3_false_of_first_zeta_initial_packet_kernel_and_antidiagonal_invariant`
- `po3_first_zeta_singleton_gamma0_profile`
- `po3_first_zeta_singleton_gamma1_profile`
- `po3_first_zeta_singleton_gamma2_profile`
- `po3_first_zeta_prefix2_profile`
- `po3_first_zeta_prefix3_profile`
- `po3_first_zeta_initial_packet_kill_layer`
- `po3_first_zeta_initial_packet_kill_layer_honest`
- `po3_first_zeta_some_initial_packet_profile`
- `po3_first_zeta_some_initial_packet_profile_false_honest`

## Current `PO3-square.1` bridge for the first-zeta packet

File:
- `FirstZetaSquareBridge_2026_04_19.lean`

Purpose:
- expose the initial `a = 1` first-zeta packet stack exactly under the
  square-side shell shape needed by `PO3-square.1`;
- keep the abstract shell file free of witness-specific imports while still
  giving downstream code a named contradiction packet.

Exports:
- `po3_square1_no_filtered_candidate_of_first_zeta_initial_packet_tag`
- `po3_square1_no_antidiagonal_invariant_of_first_zeta_initial_packet_tag`
- `po3_square1_no_filtered_candidate_of_eq_first_zeta_initial_packet_raw`
- `po3_square1_no_antidiagonal_invariant_of_eq_first_zeta_initial_packet_raw`
- `po3_square1_false_of_eq_first_zeta_initial_packet_raw_and_antidiagonal_invariant`
- `po3_square1_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel`
- `po3_square1_false_of_first_zeta_initial_packet_kernel_and_antidiagonal_invariant`

## Current certificate feeder for `PO3-rig.1b`

File:
- `WindowLawCertificate_2026_04_19.lean`

Purpose:
- freeze the exact input contract for the still-missing real Q3-side coordinate
  certificate behind the compressed zero-mode window law;
- keep that contract inside `PO3Cert`, not inside the mainline shell, so that
  later Q3 data can be plugged in without changing the already-closed abstract
  linear algebra.

Exports:
- `po3_window_scalar_law`
- `PO3WindowCoordinateCertificate`
- `po3_window_scalar_law_of_certificate`
- `PO3OuterTransportWindowCertificate`
- `po3_window_scalar_law_of_outer_transport_certificate`

Status note:
- this file does **not** define the real objects `v_{a,N}` or `w_{r,0}(a)`;
- it only states exactly what a future Q3-side certificate must provide:
  two compressed pieces, one shared coordinate sequence, one shared endpoint
  profile, and one nonzero profile index;
- once such a certificate is available, the feeder theorem returns the one
  scalar window law needed by `PO3-tail.1`.

Status update:
- the same file now also contains a stronger certificate shape one level closer
  to `PO3a.4-real`:
  `PO3OuterTransportWindowCertificate`;
- this stronger contract freezes the outer transport / pullback maps, the
  transported companion-cancellation identity, one coordinate family, the
  endpoint profile, and the resulting value sequence;
- its consumer
  `po3_window_scalar_law_of_outer_transport_certificate`
  sends that data directly to the scalar window law, so the next live burden
  is no longer certificate bookkeeping but the real `PO3-tail.1` input.

## Current real tail-to-square feeder after `PO3-rig.1b.cert-real`

File:
- `TailSquareBridgeCertificate_2026_04_21.lean`

Purpose:
- freeze the exact real Q3-side data packet that the already-closed
  `PO3-tail.*`, `PO3-cauchy.1`, and `PO3-cauchy.2` shell consumers need;
- move the live burden off tail/cauchy bookkeeping and directly onto the
  square-side wall by exposing one theorem endpoint
  `∀ r > N, squareReceiver (r^2) = 0`.

Exports:
- `PO3OuterTransportSquareTailCertificate`
- `po3_tail_scalar_law_of_outer_transport_square_tail_certificate`
- `po3_square_tail_zero_of_outer_transport_square_tail_certificate`

Status note:
- this file does not add new mathematics; it only compresses the already-closed
  chain
  `outer-transport window law -> tail scalar law -> decay kill -> sampled tail
  zero -> square repackaging`
  into one honest `PO3Cert` consumer;
- once a real Q3-side record of this shape is available, the next live burden
  is no longer `PO3-tail.*` or `PO3-cauchy.*`, but the square-side node fed by
  square-tail zero.

Status note:
- the whole first-zeta `a = 1` witness stack is now packaged as one reusable
  local kill-layer inside `PO3Cert`;
- this adds no new witness mathematics, but gives `PO3-shell` both:
  one bundled kill-layer theorem and one finite tag-based raw-packet interface;
- the direct shell-consumer layer is now also present in theorem form:
  pointwise `(tag) (u)` inequality and the collapsed existential
  `¬ ∃ tag u, ...`;
- the next transport layer is also now present:
  for an arbitrary shell kernel `K`, if `K` is identified with one tagged
  first-zeta packet, then `K` is excluded from the filtered `(+,-)` candidate
  shell, both in negated-existential and direct contradiction forms;
- the next API compression layer is also present:
  the family of such kernels is now named by one predicate
  `po3_first_zeta_initial_packet_kernel`,
  and the filtered-candidate kill theorems are exported directly at that
  predicate level;
- the final local shell cleanup is now also present:
  the same named family predicate exports a direct bridge to the generic
  anti-diagonal shell criterion, so downstream code can now contradict
  anti-diagonal invariance without manually passing through
  `∃ u, K = po3_suzuki_filtered_pm_candidate u`;
- `po3_first_zeta_some_initial_packet_profile` is now the existential shell
  form `∃ tag, ...`, not a hand-written five-way disjunction.

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
