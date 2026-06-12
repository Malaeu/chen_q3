# Step33A.1-A Residual-Anchor Refined Subchunk Proof-Data Skeleton

Fail-closed skeleton.  This is not a Lean payload.

## Verdict

- schema: `q3_psdpd_step33_a_refined_subchunk_proof_data.v17`
- status: `structural_skeleton_seeded_missing_analytic_fields`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.RefinedPayloadFin`
- include null fields: `False`

## Counts

- families: `4`
- rows: `92`
- parent chunks: `2392`
- refined subchunks: `40020`
- seeded subchunk structural fields: `720360`
- seeded parent structural fields: `23920`
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

## Family Counts

| family | kind | rows | parent chunks | subchunks | missing analytic fields |
| --- | --- | ---: | ---: | ---: | ---: |
| `primary_finite` | `finite` | `23` | `598` | `8050` | `40296` |
| `primary_tail` | `tail` | `23` | `598` | `11960` | `59846` |
| `control_finite` | `finite` | `23` | `598` | `8050` | `40296` |
| `control_tail` | `tail` | `23` | `598` | `11960` | `59846` |

## Seeded Structural Fields

- subchunk `center`
- subchunk `radius`
- subchunk `degree`
- subchunk `hLU`
- subchunk `radiusNonneg`
- subchunk `radiusLeft`
- subchunk `radiusRight`
- subchunk `hProfileInt`
- subchunk `hResidualDifferentiable`
- subchunk `mesh`
- subchunk `anchor`
- subchunk `hAnchorIn`
- subchunk `hLeftMesh`
- subchunk `hRightMesh`
- subchunk `derivCellCount`
- subchunk `derivCellLeft`
- subchunk `derivCellRight`
- subchunk `hDerivCoverCells`
- parent `parentBoundsMode`
- parent `n`
- parent `pts`
- parent `first_eq`
- parent `last_eq`
- parent `mono`
- parent `hProfileInt`
- parent `subLowerSource`
- parent `subUpperSource`
- parent `subCertSource`
- row missing `hLowerSum`
- row missing `hUpperSum`

## Guard

- not Lean proof data
- do not emit RefinedPayloadFin while analytic fields are missing
- do not replace the top-level 26 parent chunks by a fully refined payload
- parent fold must target RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
- parent bounds build RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
- subchunk proof data must use ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
- subchunk hIntegralLower/hIntegralUpper are eliminated by exact model integral bounds
- subchunk slope/hSlopeNonneg/hDerivLowerAbs/hDerivUpperAbs are eliminated by auto-slope interval packaging
- subchunk sampleRadius/hAnchorResidual are eliminated by direct anchor-envelope packaging
- subchunk derivLower/derivUpper/hResidualDerivLowerOnCell/hResidualDerivUpperOnCell are eliminated by cell-slope derivative norm packaging
- hResidualDifferentiable is a checked structural seed, not generated numeric proof data
- single-anchor geometry uses anchor = center and mesh = radius
- derivative finite cover geometry uses one cell equal to the refined subchunk
- row hLowerSum/hUpperSum comparisons remain required for RefinedPayloadFin
- structural proof templates must still be Lean-checked in generated code
- do not mutate CSV, ARadius, radius-floor, or LDL data
- do not route to H1/PO3 or Q3.Main from this layer
