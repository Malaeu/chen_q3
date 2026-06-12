# Step33A.1-A Direct Derivative Overlay

Fail-closed route-B pilot overlay for `primary_finite` row 0 parent chunk 0.

## Verdict

- schema: `q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v19`
- status: `direct_derivative_overlay_seeded_missing_cell_proofs`
- source audit status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.RefinedPayloadFin`
- active subchunk proof data: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData`
- subchunks: `100`
- seeded fields: `1300`
- remaining analytic fields: `200`
- route-B anchor residual arithmetic obligations: `1500`
- route-B derivative arithmetic obligations: `4000`

## Seeded Fields

- `coeff`
- `remainder`
- `mesh`
- `anchor`
- `derivCellCount`
- `derivCellLeft`
- `derivCellRight`
- `derivSlope`
- `hAnchorIn`
- `hLeftMesh`
- `hRightMesh`
- `hDerivCoverCells`
- `hResidualDifferentiable`

## Still Missing Per Subchunk

- `hEnvelope`
- `hResidualDerivBoundOnCell`

## hEnvelope Receiver

- signed scale-abs pilot support: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_scale_abs_box_component_bounds_at_center`
- raw integrand scale-abs pilot support: `rawOmegaAIntegrand_value_bounds_at_of_scale_abs_box_bounds`
- inactive abs-cos support: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_nonneg_abs_cos_component_bounds_at_center`
- `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_raw_component_bounds_at_center`
- raw/poly packaging: `RawOmegaATaylorModelCertificate.anchor_residual_abs_of_raw_poly_value_bounds_at`
- polynomial center: `RawOmegaATaylorModelCertificate.polynomial_center`

Required generated inputs for the direct anchor envelope:

- `prove anchor raw bounds using a sharp signed raw-value/raw-component receiver`
- `use polynomial_center because anchor = cert.center`
- `package |cert.residual anchor| from raw/poly anchor bounds`
- `prove direct envelope: |cert.residual anchor| + derivativeCellAutoSlope derivSlope * mesh <= cert.remainder`

Anchor residual arithmetic contract:

- signed Omega majorant bounds: `2`
- shape-square upper bounds: `1`
- scale box comparisons: `3`
- majorant nonnegativity comparisons: `2`
- raw scale-abs comparisons: `2`
- center/coeff comparisons: `3`
- residual-radius comparisons: `2`
- total per subchunk: `15`

## hResidualDeriv Cell Receiver

- identity: `RawOmegaATaylorModelCertificate.residual_deriv_eq`
- preferred all-cells expr composite: `RawOmegaATaylorModelCertificate.residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds`
- preferred expr composite: `RawOmegaATaylorModelCertificate.residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds`
- preferred composite: `RawOmegaATaylorModelCertificate.residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_bounds`
- cell raw/poly: `RawOmegaATaylorModelCertificate.residual_deriv_interval_bounds_on_cell_of_raw_poly_deriv_bounds`
- polynomial derivative identity: `RawOmegaATaylorModelCertificate.polynomial_deriv_eq_term_deriv_sum`
- monomial derivative identity: `RawOmegaATaylorModelCertificate.polynomial_term_deriv_eq`
- polynomial derivative expr bounds: `RawOmegaATaylorModelCertificate.polynomial_derivative_term_bounds_on_cell_of_expr_bounds`
- polynomial derivative term bounds: `RawOmegaATaylorModelCertificate.polynomial_deriv_bounds_on_cell_of_term_deriv_bounds`

Required generated inputs:

- `rawDerivLower i <= deriv step22PositiveAxisOmegaAIntegrand eta on cell i`
- `deriv step22PositiveAxisOmegaAIntegrand eta <= rawDerivUpper i on cell i`
- `term-wise arithmetic bounds for coeff_i * i * (eta - center)^(i - 1) on cell i`
- `monomial derivative identity supplied by polynomial_term_deriv_eq`
- `polyDerivLower i <= sum termDerivLower on cell i`
- `sum termDerivUpper on cell i <= polyDerivUpper i`
- `derivLower i <= rawDerivLower i - polyDerivUpper i`
- `rawDerivUpper i - polyDerivLower i <= derivUpper i`
- `-derivSlope i <= derivLower i`
- `derivUpper i <= derivSlope i`
- `package ‖deriv cert.residual eta‖ <= derivSlope i`
- `residual derivative identity supplied by residual_deriv_eq`
- `polynomial derivative identity supplied by polynomial_deriv_eq_term_deriv_sum`
- `preferred receiver: residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds followed by residual_deriv_bound_of_interval_bounds`

Cell-indexed arithmetic contract:

- degree: `16`
- term count: `17`
- derivative cells: `1`
- raw derivative bounds: `2`
- term expression bounds: `34`
- polynomial sum comparisons: `2`
- raw-minus-polynomial comparisons: `2`
- total per subchunk: `40`

## Exact Next Lean Target

- `hEnvelope` via raw component anchor bounds and direct residual envelope
- `hResidualDerivBoundOnCell` via cell raw/poly derivative bounds plus norm packaging

## Guard

- not Lean proof data
- do not emit PayloadFin from this overlay alone
- sampled derivative lower/upper values are candidates only
- coefficients are rational candidates only until Lean emission checks them
- subchunk integral comparisons are eliminated by exact model integral bounds
- slope/hSlopeNonneg/hDerivLowerAbs/hDerivUpperAbs are eliminated by auto-slope interval packaging
- sampleRadius/hAnchorResidual are eliminated by direct anchor-envelope packaging
- derivLower/derivUpper/hResidualDerivLowerOnCell/hResidualDerivUpperOnCell are eliminated by cell-slope derivative norm packaging
- hEnvelope must be proved through a sharp signed raw-value or raw-component receiver, not by trusting sampled residuals
- scale_abs_box anchor receiver is compiled pilot support, not the active full-payload blocker
- anchor raw integrand scale_abs_box receiver is compiled pilot support and may be too coarse for tiny residuals
- nonnegative abs-cos anchor route is inactive for the first finite chunk because it requires 0 <= omegaLower
- polynomial anchor value should use polynomial_center because pilot anchor equals cert.center
- hResidualDerivBoundOnCell should use interval derivative bounds packaged by residual_deriv_bound_of_interval_bounds
- preferred derivative-cell receiver is residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_bounds
- new preferred derivative-cell receiver is residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds
- scalable preferred derivative-cells receiver is residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds
- residual derivative identity is supplied by residual_deriv_eq
- polynomial derivative bounds should use polynomial_deriv_bounds_on_cell_of_term_deriv_bounds
- monomial derivative identity is supplied by polynomial_term_deriv_eq
- next Lean work must prove direct anchor-envelope bounds, raw derivative cell bounds, term-wise polynomial derivative arithmetic bounds, and norm packaging into hResidualDerivBoundOnCell
- do not mutate CSV, ARadius, radius-floor, or LDL data
- do not route to H1/PO3 or Q3.Main from this layer
