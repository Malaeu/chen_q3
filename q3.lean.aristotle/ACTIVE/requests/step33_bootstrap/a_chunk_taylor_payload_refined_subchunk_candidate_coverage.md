# Step33A.1-A Refined Subchunk Candidate Coverage

Fail-closed coverage audit.  This is not Lean proof data.

## Verdict

- status: `pilot_only_candidate_coverage_no_lean_emitted`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.RefinedPayloadFin`
- active proof-data schema: `q3_psdpd_step33_a_refined_subchunk_proof_data.v17`
- proof-safe closed fields: `0`

## Coverage

| item | count |
| --- | ---: |
| `parentChunks` | `2392` |
| `refinedSubchunks` | `40020` |
| `candidateOverlayFiles` | `2` |
| `residualAuditFiles` | `2` |
| `candidateParents` | `2` |
| `candidateResidualPassedParents` | `2` |
| `slackAuditFiles` | `2` |
| `candidateSlackFitParents` | `0` |
| `candidateSubchunks` | `110` |
| `candidateMissingParents` | `2390` |
| `candidateMissingSubchunks` | `39910` |
| `directOverlayFiles` | `2` |
| `staleDirectOverlayFiles` | `1` |
| `directParents` | `2` |
| `directSubchunks` | `110` |
| `directMissingParents` | `2390` |
| `directMissingSubchunks` | `39910` |
| `missingSubchunkAnalyticFields` | `200100` |
| `missingRowAnalyticFields` | `184` |

## Missing Groups

| group | missing fields |
| --- | ---: |
| `residual_anchor_envelope` | `40020` |
| `residual_derivative_cell_norm_proofs` | `40020` |
| `residual_derivative_cell_slope_data` | `40020` |
| `row_sum_comparisons` | `184` |
| `taylor_model_data` | `80040` |

## Family Summary

| family | parents | subchunks | candidate parents | direct parents |
| --- | ---: | ---: | ---: | ---: |
| `control_finite` | `598` | `8050` | `0` | `0` |
| `control_tail` | `598` | `11960` | `0` | `0` |
| `primary_finite` | `598` | `8050` | `2` | `2` |
| `primary_tail` | `598` | `11960` | `0` | `0` |

## Covered Parents

- candidate `primary_finite row 0 parent 0`: `100` subchunks, `0` proof-safe fields, residual audit passed `True`, slack fits current bounds `False`
- candidate `primary_finite row 0 parent 1`: `10` subchunks, `0` proof-safe fields, residual audit passed `True`, slack fits current bounds `False`
- direct `primary_finite row 0 parent 0`: `100` subchunks, `300` analytic fields still open
- direct `primary_finite row 0 parent 1`: `10` subchunks, `30` analytic fields still open

## Next Candidate Parents

- `primary_finite row 0 parent 2` split `10` interval `(2.000000000000000000E+1, 3.000000000000000000E+1]`
- `primary_finite row 0 parent 3` split `10` interval `(3.000000000000000000E+1, 4.000000000000000000E+1]`
- `primary_finite row 0 parent 4` split `10` interval `(4.000000000000000000E+1, 5.000000000000000000E+1]`
- `primary_finite row 0 parent 5` split `10` interval `(5.000000000000000000E+1, 6.000000000000000000E+1]`
- `primary_finite row 0 parent 6` split `10` interval `(6.000000000000000000E+1, 7.000000000000000000E+1]`
- `primary_finite row 0 parent 7` split `10` interval `(7.000000000000000000E+1, 8.000000000000000000E+1]`
- `primary_finite row 0 parent 8` split `10` interval `(8.000000000000000000E+1, 9.000000000000000000E+1]`
- `primary_finite row 0 parent 9` split `10` interval `(9.000000000000000000E+1, 1.000000000000000000E+2]`

## Guard

- coverage audit only
- do not import this file as Lean proof data
- do not write refined generated Lean while missingTotal is nonzero
- candidate overlays close zero proof-safe fields
- direct overlays still leave hEnvelope and hResidualDerivBoundOnCell open
- keep the 26 parent chunks; refined subchunks stay under each parent
- no CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3 mutation

## Next Generator Target

- lift candidate-overlay generation from the one pilot parent to shardable parent chunks
- for every candidate parent, produce universal hEnvelope and hResidualDerivBoundOnCell proofs
- then emit RefinedPayloadFin only after all parent and row comparisons are present
