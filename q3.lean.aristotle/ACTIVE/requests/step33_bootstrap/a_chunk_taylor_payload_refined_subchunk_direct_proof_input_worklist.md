# Step33A.1-A Direct Proof-Input Worklist

Address-only worklist.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a_refined_subchunk_direct_proof_input_worklist.v19`
- status: `direct_proof_input_worklist_address_only`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.CellSlopeDirectEnvelopeRefinedPayloadFin`
- downstream Lean landing surface: `RawOmegaAChunkTaylorPayload.RefinedPayloadFin`
- active subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData`
- legacy interval subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData`
- preferred direct-endpoint constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- preferred direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell`
- endpoint direct-norm full-cell fallback: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- generic direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_at_zero_distance`
- preferred full-cell direct-norm cert constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell`
- interval-bounds full-cell direct-norm constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`
- endpoint interval-bounds full-cell fallback: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance`
- direct norm cert: `RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert`
- direct norm cert validity: `RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert.Valid`
- direct norm receiver: `RawOmegaATaylorModelCertificate.residualDerivBoundOnCell_of_directNormCert`
- direct norm interval-valid receiver: `RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert.Valid.of_interval_bounds`
- direct norm interpolation-valid receiver: `RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound`
- overlays: `2`
- subchunks: `110`
- hRawCenterCoeffAbs fields: `110`
- scalar hEnvelope arithmetic fields: `110`
- scalar hEnvelope arithmetic passing: `110`
- hResidualDerivLowerOnCell fields: `0`
- hResidualDerivUpperOnCell fields: `0`
- preferred hResidualDerivBoundOnCell fields: `110`
- derivative abs arithmetic fields: `220`
- derivative abs arithmetic passing: `220`
- raw-center-coeff abs arithmetic obligations: `110`
- scalar hEnvelope arithmetic obligations: `110`
- derivative arithmetic obligations: `220`
- preferred norm-route derivative analytic obligations: `110`
- preferred norm-route open analytic obligations: `220`
- derivative abs arithmetic obligations: `220`
- open arithmetic obligations: `330`
- total arithmetic comparisons including closed: `660`
- sampled envelope passing subchunks: `110`
- proof-safe closed fields: `0`

## Parents

| family | row | parent | split | subchunks | hRawCenterCoeffAbs | hEnvelope arithmetic | deriv lower | deriv upper | norm bound | deriv abs arithmetic | legacy open | preferred open | sampled pass |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `primary_finite` | `0` | `0` | `100` | `100` | `100` | `100` | `0` | `0` | `100` | `200` | `300` | `200` | `100` |
| `primary_finite` | `0` | `1` | `10` | `10` | `10` | `10` | `0` | `0` | `10` | `20` | `30` | `20` | `10` |

## Obligation Shape

- `hRawCenterCoeffAbs`: prove pointwise raw-value lower/upper enclosures, then use `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_raw_value_bounds_at`; Lean wrapper feeds `hAnchorResidual` into the sample-envelope receiver
- scalar `hEnvelope`: exact rational comparison `sampleRadius + max 0 derivSlope * mesh <= remainder`; recorded as passing metadata, not Lean payload
- `hResidualDerivLowerOnCell` / `hResidualDerivUpperOnCell`: cancellation-preserving direct residual-derivative interval bounds
- preferred compact route: prove `hRawCenterCoeffAbs`, prove `ResidualDerivativeDirectNormCert.Valid`, prove `cellL = L` and `cellU = U`, then feed those directly into `ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell`
- interpolation route for `ResidualDerivativeDirectNormCert.Valid`: prove an exact model-derivative norm bound and exact interpolation/error bound on the same cell, prove their sum is at most `derivSlope`, then use `ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound`
- shortcut compact derivative route: prove `hRawCenterCoeffAbs`, residual-derivative lower/upper bounds on `[L, U]`, and the two abs-slope comparisons, then feed them directly into `ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`
- endpoint fallback compact route: use the endpoint full-cell direct-norm constructor when the payload already has direct endpoint component cert fields
- lower-level fallback route: use the generic direct-norm constructor with an explicit cell-cover proof, or extract `hResidualDerivBoundOnCell` with `residualDerivBoundOnCell_of_directNormCert` and feed `ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- scalar derivative abs comparisons: exact rational comparisons `-derivSlope <= derivLower` and `derivUpper <= derivSlope`; recorded as passing metadata, not Lean payload

## Next Proof-Producing Target

- generate pointwise raw-value lower/upper enclosures and cert.coeff0 comparisons, then close hRawCenterCoeffAbs via raw_center_coeff_abs_of_raw_value_bounds_at; Lean wrapper derives hAnchorResidual
- materialize scalar hEnvelope exact rational arithmetic as Lean proof data only during payload emission
- generate cancellation-preserving residual-derivative lower/upper interval bounds
- preferred compact route: generate one ResidualDerivativeDirectNormCert.Valid proof per direct subchunk
- interpolation route: prove exact model-derivative norm and interpolation/error bounds on the same cell, then use ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound
- feed hRawCenterCoeffAbs + DirectNormCert.Valid + cellL=L/cellU=U equalities into the raw-center full-cell direct-norm exact-integral constructor
- shortcut compact route: feed hRawCenterCoeffAbs + residual-derivative lower/upper bounds + abs-slope comparisons into the raw-center interval-bounds full-cell direct-norm constructor
- fallback: extract hResidualDerivBoundOnCell with residualDerivBoundOnCell_of_directNormCert
- materialize derivative abs comparisons as Lean proof data only during payload emission
- only then convert this worklist into Lean-checked CellSlopeDirectEnvelopeRefinedPayloadFin data
- Lean converts CellSlopeDirectEnvelopeRefinedPayloadFin to RefinedPayloadFin and then to DirectTailWindowInputs

## Guard

- address-only worklist
- not Lean proof data
- proofSafeClosedFields remains zero
- sampledEnvelopePasses is diagnostic only; hEnvelopeArithmetic recomputes the rational inequality exactly
- do not emit CellSlopeDirectEnvelopeRefinedPayloadFin while hRawCenterCoeffAbs or the preferred direct residual-derivative norm bound is missing
- preferred cell-slope route may replace the two interval fields by one hResidualDerivBoundOnCell proof per direct subchunk
- interpolation diagnostics are non-proof until model and error bounds are emitted as Lean-checked exact hypotheses
- do not mutate CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3
