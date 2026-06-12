# Direct Receiver Feasibility Audit

schema: `q3_psdpd_step33_a_refined_subchunk_direct_receiver_feasibility_audit.v1`
status: `route_fork_one_cell_raw_poly_receiver_loses_cancellation`

## Totals

- subchunks: `110`
- sampled envelope passing subchunks: `110`
- one-cell raw/poly passing subchunks: `0`
- one-cell raw/poly failing subchunks: `110`

## Diagnosis

The scalar envelope candidate is viable, but the preferred one-cell raw/poly derivative receiver cannot prove the tiny residual derivative from the available one-cell raw/poly intervals.  It loses cancellation across the whole subchunk.

The scalar `hEnvelope` side is still feasible, but the current
`hResidualDerivBoundOnCell` preferred receiver is not proof-ready from
the available one-cell raw/poly intervals.

## Worst Raw/Poly Cancellation Loss

- family: `primary_finite`
- row: `0`
- parentChunk: `0`
- subchunk: `0`
- interval: `(0.000000000000000000E+0, 1.000000000000000000E-1]`
- lower excess: `1.869962124102031354E-1`
- upper excess: `1.869962124102031391E-1`

## Recommended Fork Question

Switch to a cancellation-preserving residual-derivative proof surface, or generate much finer derivative cells with a receiver that preserves raw/poly alignment locally; do not mark hResidualDerivBoundOnCell proof-safe from the sampled direct pass.

## Guard

This artifact is not Lean proof data.  It must not be imported as a
trusted payload and it does not close `A hbox` or Step33A.1-A.
