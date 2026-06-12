# Step33A.1-A Refined Subchunk Lean Emitter Guard

Guard report only.  No Lean file is written while fields are missing.

## Verdict

- schema: `q3_psdpd_step33_a_refined_subchunk_payload_lean_emitter.v37`
- status: `missing_analytic_fields_no_lean_emitted`
- proof data status: `structural_skeleton_seeded_missing_analytic_fields`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.RefinedPayloadFin`
- active subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData`
- legacy interval subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData`
- preferred direct-endpoint constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- preferred direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- generic direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_at_zero_distance`
- preferred full-cell direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- interval-bounds full-cell direct-norm constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance`
- out Lean: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaARefinedSubchunkGeneratedPayloadImport.lean`
- out Lean written: `False`
- missing total: `200284`
- missing subchunk analytic fields: `200100`
- missing parent analytic fields: `0`
- missing row analytic fields: `184`

## Missing Groups

| group | missing fields |
| --- | ---: |
| `residual_anchor_envelope` | `40020` |
| `residual_derivative_cell_norm_proofs` | `40020` |
| `residual_derivative_cell_slope_data` | `40020` |
| `row_sum_comparisons` | `184` |
| `taylor_model_data` | `80040` |

## Next Proof-Producing Target

- `covered direct parents: primary_finite row 0 parent chunk 0, primary_finite row 0 parent chunk 1`
- `current direct coverage: 110 subchunks, 220 remaining analytic fields`
- `full payload via route-A parent-refined subchunk folding`
- `hRawCenterCoeffAbs via sharp raw-center-minus-coeff0 absolute bound; Lean wrapper derives hAnchorResidual`
- `preferred proof-data constructor for hRawCenterCoeffAbs: ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData.of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
- `hRawCenterCoeffAbs local scale-interval probe supplies 110/110 diagnostic rows with shared primary/control scale theorem names`
- `hRawCenterCoeffAbs local component contract supplies 110/110 arithmetic-ready zero-distance rows through one compact LocalRawOmegaComponentIntervalCert per row; preferred cert producer is LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds with 220 open abs ball facts and arithmetic containment checks`
- `with the direct endpoint constructor, generated rows should supply LocalRawOmegaComponentDirectEndpointIntervalCert plus rational scale/corner/coeff checks instead of a standalone hRawCenterCoeffAbs proof term`
- `scalar hEnvelope exact rational arithmetic already passes in the direct overlays; future Lean emission should materialize it with norm_num`
- `scale_abs_box anchor receiver remains compiled legacy support only`
- `preferred compact route: prove one ResidualDerivativeDirectNormCert.Valid per direct subchunk, prove cellL=L and cellU=U, and feed endpoint cert + direct norm cert to ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- `shortcut compact route: prove residual-derivative lower/upper bounds on the full subchunk cell plus abs-slope comparisons and feed them to ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance`
- `fallback compact route: extract hResidualDerivBoundOnCell and feed ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- `legacy interval route remains available: direct residual-derivative lower/upper interval bounds via cancellation-preserving generator`
- `derivative abs comparisons already pass exact rational arithmetic; future Lean emission should materialize them with norm_num`
- `single-cell receiver residual_deriv_bound_on_single_cell_of_interval_bounds for current one-cell direct subchunks`
- `cell-indexed receiver residual_deriv_bound_on_cells_of_interval_bounds`
- `parent route-A fold via ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert`

## Direct Derivative Coverage

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_candidate_coverage.json`
- schema: `q3_psdpd_step33_a_refined_subchunk_candidate_coverage.v1`
- overlay files loaded: `2`
- direct subchunks loaded: `110`
- seeded fields loaded: `2090`
- remaining analytic fields loaded: `220`
- closed arithmetic fields loaded: `110`
- sample-envelope arithmetic passing: `110`
- derivative abs arithmetic passing: `220`

| field | remaining covered subchunks |
| --- | ---: |
| `hRawCenterCoeffAbs` | `110` |
| `hResidualDerivBoundOnCell` | `110` |

| field | exact arithmetic covered subchunks |
| --- | ---: |
| `hEnvelope` | `110` |

| family | row | parent | split | remaining fields | path |
| --- | ---: | ---: | ---: | ---: | --- |
| `primary_finite` | `0` | `0` | `100` | `200` | `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0_denom1e30.json` |
| `primary_finite` | `0` | `1` | `10` | `20` | `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_1_denom1e30_derivfit.json` |

## Local Component Interval Probe

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_local_component_interval_probe.json`
- schema: `q3_psdpd_step33_a_refined_subchunk_local_component_interval_probe.v2`
- status: `local_component_interval_probe_passed_not_lean_proof`
- receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at`
- scale mode: `d29_pi_p30_decimal_bounds`
- scale lower: `0.095492965855137201461330258023`
- scale upper: `0.095492965855137201461330258024`
- scale pad override: `None`
- entries: `110`
- passed at some width: `110`
- failed at all widths: `0`
- proof-safe closed fields: `0`

| family | hScaleLower | hScaleUpper |
| --- | --- | --- |
| `primary_finite` | `primaryK11Ell_div_pi_tightScaleLower` | `primaryK11Ell_div_pi_tightScaleUpper` |

Worst passing local component row:

- family: `primary_finite`
- row: `0`
- parent chunk: `1`
- subchunk: `8`
- largest passing width: `0.00000000000000000000000000000001`
- min margin: `8.312257372078911514E-32`

## hRawCenterCoeffAbs Local Component Contract

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_hraw_center_coeff_contract.json`
- schema: `q3_psdpd_step33_a_refined_subchunk_hraw_center_coeff_contract.v11`
- status: `arithmetic_ready_missing_component_interval_derivative_enclosures_not_lean_proof`
- receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at`
- zero-distance receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at_zero_distance`
- compact component receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_component_cert_scale_interval_corner_bounds_at_zero_distance`
- compact endpoint receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
- compact direct endpoint receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
- raw-center sample-envelope direct endpoint constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData.of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
- component ball cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds`
- rows: `110`
- arithmetic-ready rows: `110`
- arithmetic-failed rows: `0`
- anchor memberships passing: `110`
- scale proof references: `220`
- component interval proofs open: `440`
- component interval certs open: `110`
- compact component rows: `110`
- component ball certs open: `110`
- component ball abs facts open: `220`
- component ball containment passing: `440 / 440`
- corner arithmetic passing: `3520 / 3520`
- coeff arithmetic passing: `220 / 220`
- proof-safe closed fields: `0`

Worst contract arithmetic row:

- family: `primary_finite`
- row: `0`
- parent chunk: `0`
- subchunk: `0`
- min arithmetic margin: `0.000000000000000000E+18`

## Route-B First Direct Derivative Overlay Detail

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0_denom1e30.json`
- schema: `q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v27`
- status: `direct_derivative_overlay_seeded_missing_cell_slope_norm_proofs`
- active subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData`
- preferred cell-slope proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData`
- preferred cell-slope direct endpoint constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- preferred direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- generic direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_at_zero_distance`
- preferred full-cell direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- interval-bounds full-cell direct-norm constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance`
- subchunks: `100`
- seeded fields: `1900`
- remaining analytic fields: `200`

hEnvelope receiver support:

- signed scale-abs pilot support: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_scale_abs_box_component_bounds_at_center`
- raw integrand scale-abs pilot support: `rawOmegaAIntegrand_value_bounds_at_of_scale_abs_box_bounds`
- inactive abs-cos support: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_nonneg_abs_cos_component_bounds_at_center`
- `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_raw_center_coeff_abs_bound`
- raw/poly packaging: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_raw_poly_value_bounds_at`
- polynomial center: `RawOmegaATaylorModelCertificate.polynomial_center`

hEnvelope generated inputs:

- `prove sharp anchor raw-center-minus-coeff0 bound`
- `Lean wrapper packages hRawCenterCoeffAbs into hAnchorResidual: |cert.residual anchor| <= sampleRadius`
- `prove scalar direct envelope: sampleRadius + max 0 derivSlope[0] * mesh <= cert.remainder`
- `sample-envelope wrapper packages the direct envelope required by the one-cell receiver`

Route-B anchor residual arithmetic contract:

- preferred receiver: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_raw_center_coeff_abs_bound`
- direct raw-center-coeff abs bounds: `1`
- legacy scale-abs obligations: `15`
- total per subchunk: `1`

hResidualDeriv cell receivers:

- active single-cell interval norm: `RawOmegaATaylorModelCertificate.residual_deriv_bound_on_single_cell_of_interval_bounds`
- active all-cells interval norm: `RawOmegaATaylorModelCertificate.residual_deriv_bound_on_cells_of_interval_bounds`
- legacy raw/poly single-cell norm: `RawOmegaATaylorModelCertificate.residual_deriv_bound_on_single_cell_of_raw_deriv_and_poly_term_expr_bounds`
- legacy all-cells expr composite: `RawOmegaATaylorModelCertificate.residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds`

hResidualDeriv cell generated inputs:

- `legacy interval route only; prefer hResidualDerivBoundOnCell when possible`
- `prove cancellation-preserving derivLower i <= deriv cert.residual eta on cell i`
- `prove cancellation-preserving deriv cert.residual eta <= derivUpper i on cell i`
- `-derivSlope i <= derivLower i`
- `derivUpper i <= derivSlope i`
- `package ‖deriv cert.residual eta‖ <= derivSlope i`
- `legacy interval receiver for one-cell direct subchunks: residual_deriv_bound_on_single_cell_of_interval_bounds`
- `do not use raw/poly derivative subtraction here; feasibility audit reports 0/110 passing`

Route-B derivative arithmetic contract:

- cell-indexed receiver: `RawOmegaATaylorModelCertificate.residual_deriv_bound_on_cells_of_interval_bounds`
- degree: `16`
- term count: `17`
- derivative cells: `1`
- direct residual derivative bounds: `2`
- residual derivative abs comparisons: `2`
- total per subchunk: `4`

Route-B next proof-producing target:

- `primary_finite row 0 parent chunks 0 and 1`
- `proof-safe close hRawCenterCoeffAbs and the preferred direct residual-derivative norm bounds for the 110 covered direct subchunks`
- `hRawCenterCoeffAbs via sharp raw-center-minus-coeff0 anchor bound; Lean wrapper derives hAnchorResidual`
- `scalar hEnvelope via exact rational sample-envelope arithmetic`
- `do not use the current one-cell raw/poly derivative intervals as proof data; the feasibility audit shows cancellation loss on all 110 subchunks`
- `legacy lower/upper interval bounds may still feed residual_deriv_bound_on_single_cell_of_interval_bounds if the compact norm route fails; derivative abs comparisons are exact-passing metadata`

## Reason

Refined proof data is incomplete; writing a Lean payload now would turn missing Taylor/model or row-sum facts into a fake trusted import.

## Guard

- do not write Lean while missingTotal is nonzero
- parent fold must target RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert
- parent fold may land directly at ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
- exact-sum parent bounds build RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.of_refinedSubchunkSums
- top-level payload must keep the 26 parent chunks
- subchunk hIntegralLower/hIntegralUpper are eliminated by exact model integral bounds
- global preferred direct skeleton uses ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData and records one scalar residual-derivative norm proof input for hResidualDerivBoundOnCell
- legacy interval skeleton remains recorded as ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData
- hResidualDifferentiable is seeded globally by a checked Lean theorem in proof-data schema v17
- single-anchor geometry is seeded by anchor = center and mesh = radius
- derivative finite-cover geometry is seeded as one cell equal to the refined subchunk
- active full payload target is RawOmegaAChunkTaylorPayload.RefinedPayloadFin
- route-B hRawCenterCoeffAbs must use the sharp raw-center-minus-coeff0 receiver; hAnchorResidual is derived by the Lean wrapper
- route-B scalar hEnvelope arithmetic is exact-passing metadata, not Lean payload yet
- route-B scale_abs_box receiver is compiled legacy support, not the active full-payload blocker
- route-B nonnegative abs-cos anchor receiver is inactive for first finite chunk
- route-B polynomial anchor side should use polynomial_center when anchor = cert.center
- route-B residual derivative cells should prove hResidualDerivBoundOnCell through residual_deriv_bound_on_cells_of_interval_bounds
- route-B raw/poly derivative-cell receivers are legacy support only on this 0/110 feasibility route
- route-B scalable preferred derivative norm receiver is residual_deriv_bound_on_cells_of_interval_bounds
- route-B one-cell raw/poly derivative norm receiver is not proof-ready with current interval data; direct_receiver_feasibility_audit reports 0/110 passing
- route-B residual derivative identity is supplied by residual_deriv_eq
- route-B polynomial derivative cells should use polynomial_deriv_bounds_on_cell_of_term_deriv_bounds
- route-B polynomial derivative term bounds from explicit expressions should use polynomial_derivative_term_bounds_on_cell_of_expr_bounds
- route-B polynomial derivative identity is supplied by polynomial_deriv_eq_term_deriv_sum
- route-B monomial derivative identity is supplied by polynomial_term_deriv_eq
- route-B direct overlay is a candidate surface only, not proof data
- local component interval probe is a candidate surface only, not proof data
- hRawCenterCoeffAbs local component contract is a candidate surface only, not proof data
- do not fall back to scalePad = 1e-70 as the default scale route
- do not treat sampled derivative intervals as Lean proof data
- do not import generated refined payload until lake env lean checks it
- do not use this report as proof data
- do not mutate CSV, ARadius, radius-floor, or LDL data
