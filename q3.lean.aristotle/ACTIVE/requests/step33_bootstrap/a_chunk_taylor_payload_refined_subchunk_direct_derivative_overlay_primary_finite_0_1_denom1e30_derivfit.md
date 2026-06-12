# Step33A.1-A Direct Derivative Overlay

Fail-closed route-B pilot overlay for `primary_finite` row 0 parent chunk 1`, with cell-slope as the active derivative route.

## Verdict

- schema: `q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v30`
- status: `direct_derivative_overlay_seeded_missing_cell_slope_norm_proofs`
- source audit status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.CellSlopeDirectEnvelopeRefinedPayloadFin`
- active subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData`
- legacy interval subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData`
- preferred direct-endpoint constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- preferred full-cell direct-norm constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell`
- preferred full-cell direct-norm interval-bounds constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`
- endpoint full-cell direct-norm fallback: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- subchunks: `10`
- seeded fields: `190`
- remaining analytic fields: `20`
- legacy interval remaining analytic fields: `30`
- closed arithmetic fields: `10`
- legacy interval closed arithmetic fields: `20`
- sample-envelope arithmetic obligations: `10`
- sample-envelope arithmetic passing: `10`
- derivative abs arithmetic obligations: `20`
- derivative abs arithmetic passing: `20`
- route-B anchor residual arithmetic obligations: `10`
- route-B derivative arithmetic obligations: `20`
- preferred norm-route derivative analytic obligations: `10`
- route-B derivative comparisons including closed: `40`

## Seeded Fields

- `coeff`
- `remainder`
- `sampleRadius`
- `mesh`
- `anchor`
- `cellL`
- `cellU`
- `derivLower`
- `derivUpper`
- `derivCellCount`
- `derivCellLeft`
- `derivCellRight`
- `derivSlope`
- `hAnchorIn`
- `hLeftMesh`
- `hRightMesh`
- `hDerivCoverCell`
- `hDerivCoverCells`
- `hResidualDifferentiable`

## Still Missing Per Subchunk

- `hRawCenterCoeffAbs`
- `hResidualDerivBoundOnCell`

## Exact Arithmetic Fields

- `hEnvelope`

## hRawCenterCoeffAbs Receiver

- preferred sharp receiver: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_raw_center_coeff_abs_bound`
- signed scale-abs legacy support: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_scale_abs_box_component_bounds_at_center`
- raw integrand scale-abs legacy support: `rawOmegaAIntegrand_value_bounds_at_of_scale_abs_box_bounds`
- inactive abs-cos support: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_nonneg_abs_cos_component_bounds_at_center`
- raw/poly packaging: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_raw_poly_value_bounds_at`
- polynomial center: `RawOmegaATaylorModelCertificate.polynomial_center`

Required generated inputs for hRawCenterCoeffAbs:

- `anchor = cert.center`
- `prove sharp bound |step22PositiveAxisOmegaAIntegrand k ell x anchor - cert.coeff 0| <= sampleRadius`
- `payload field hRawCenterCoeffAbs feeds the sharp-anchor sample-envelope wrapper`

## Scalar hEnvelope Arithmetic

- relation: `sampleRadius + max 0 derivSlope * mesh <= remainder`
- first-subchunk lhs: `1423/125000000000000000000000000000`
- first-subchunk remainder: `1423/125000000000000000000000000000`
- first-subchunk excess: `0`
- exact pass: `True`
- proof hint: `by norm_num`

Raw-center-coeff abs arithmetic contract:

- direct raw-center-coeff abs bounds: `1`
- open anchor analytic obligations: `1`
- signed Omega majorant bounds: `2`
- shape-square upper bounds: `1`
- scale box comparisons: `3`
- majorant nonnegativity comparisons: `2`
- raw scale-abs comparisons: `2`
- center/coeff comparisons: `3`
- residual-radius comparisons: `2`
- legacy scale-abs box obligations: `15`
- total per subchunk: `1`

## hResidualDeriv Cell-Slope Receiver

- preferred proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData`
- preferred direct-endpoint constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- preferred full-cell direct-norm constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell`
- preferred full-cell direct-norm interval-bounds constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`
- endpoint full-cell direct-norm fallback: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance`
- active single-cell interval norm receiver: `RawOmegaATaylorModelCertificate.residual_deriv_bound_on_single_cell_of_interval_bounds`
- active all-cells interval norm receiver: `RawOmegaATaylorModelCertificate.residual_deriv_bound_on_cells_of_interval_bounds`
- legacy raw/poly single-cell norm receiver: `RawOmegaATaylorModelCertificate.residual_deriv_bound_on_single_cell_of_raw_deriv_and_poly_term_expr_bounds`
- legacy all-cells expr composite: `RawOmegaATaylorModelCertificate.residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds`

Required generated inputs:

- `prove cancellation-preserving norm bound ‖deriv cert.residual eta‖ <= derivSlope[0] on the one derivative cell`
- `preferred: feed hRawCenterCoeffAbs + ResidualDerivativeDirectNormCert.Valid + cellL=L/cellU=U into ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell`
- `shortcut: feed hRawCenterCoeffAbs + residual-derivative lower/upper bounds + abs-slope comparisons into ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`
- `fallback: feed hResidualDerivBoundOnCell into ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`
- `do not emit derivLower/derivUpper interval fields when the norm proof is available`

Cell-slope arithmetic contract:

- degree: `16`
- term count: `17`
- derivative cells: `1`
- preferred direct residual derivative norm bounds: `1`
- preferred open derivative analytic obligations: `1`
- legacy direct residual derivative bounds: `2`
- legacy residual derivative abs comparisons: `2`
- legacy open derivative analytic obligations: `2`
- closed derivative abs comparisons: `2`
- total per subchunk: `4`

Legacy derivative abs arithmetic:

- lower relation: `-derivSlope <= derivLower`
- upper relation: `derivUpper <= derivSlope`
- lower exact pass: `True`
- upper exact pass: `True`

## Exact Next Lean Target

- `hRawCenterCoeffAbs` via sharp raw-center-minus-coeff0 anchor bound; Lean wrapper derives `hAnchorResidual`
- `hResidualDerivBoundOnCell` via a cancellation-preserving direct residual-derivative norm bound
- shortcut: `hRawCenterCoeffAbs` plus derivative interval bounds can now land through `of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`
- materialize exact scalar arithmetic for `hEnvelope` during payload emission
- legacy interval route may still materialize `hResidualDerivLowerOnCell`, `hResidualDerivUpperOnCell`, `hDerivLowerAbs`, and `hDerivUpperAbs` if the preferred norm route fails

## Guard

- not Lean proof data
- do not emit PayloadFin from this overlay alone
- sampled derivative lower/upper values are candidates only
- coefficients are rational candidates only until Lean emission checks them
- subchunk integral comparisons are eliminated by exact model integral bounds
- slope/hSlopeNonneg are eliminated by the scalar one-cell interval wrapper
- sampleRadius is seeded; scalar hEnvelope arithmetic passes exactly but is not Lean payload yet
- hRawCenterCoeffAbs remains an analytic proof field
- derivLower/derivUpper are scalar candidate direct residual-derivative interval endpoints, not raw/poly subtraction outputs
- hDerivLowerAbs/hDerivUpperAbs pass exact rational arithmetic but belong to the legacy interval route
- preferred route must prove hResidualDerivBoundOnCell by a cancellation-preserving residual-derivative norm generator
- hResidualDerivLowerOnCell/hResidualDerivUpperOnCell remain legacy interval fields only
- hRawCenterCoeffAbs must be proved as the sharp raw-center-minus-coeff0 analytic bound, not by trusting sampled residuals
- scale_abs_box anchor receiver is compiled legacy support, not the active full-payload blocker
- anchor raw integrand scale_abs_box receiver is compiled legacy support and may be too coarse for tiny residuals
- nonnegative abs-cos anchor route is inactive for the first finite chunk because it requires 0 <= omegaLower
- polynomial anchor value should use polynomial_center because pilot anchor equals cert.center
- preferred route feeds hRawCenterCoeffAbs plus a full-cell direct norm certificate to the compact raw-center exact-integral constructor
- shortcut route feeds hRawCenterCoeffAbs plus residual-derivative interval bounds and abs-slope arithmetic to the compact raw-center interval-bounds constructor
- hResidualDerivBoundOnCell direct endpoint constructor remains fallback support
- legacy cell-indexed fallback receiver is residual_deriv_bound_on_cells_of_interval_bounds
- raw/poly derivative norm receivers are retained only as legacy support for better aligned future cells
- next Lean work must prove hRawCenterCoeffAbs, materialize scalar hEnvelope arithmetic, and prove cancellation-preserving residual-derivative norm bounds
- do not mutate CSV, ARadius, radius-floor, or LDL data
- do not route to H1/PO3 or Q3.Main from this layer
