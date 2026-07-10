# SymbolDiagonalCrossCheck_v1

## Verdict

`SYMBOL_MATCH`

## Reclassification

`TAUTOLOGICAL_CHANNEL`

ZeroSumCrossCheck_v1 reclassifies the previous `SYMBOL_MATCH`: the `rel_diff=2.3763e-91` match is the fingerprint of the same `tau` contraction, useful as an internal consistency check but not an independent E5 zero-sum channel.


This is a Route B diagnostic only: no RH claim, no Phase 2, no Q3 mainline edit.

## Point

- `(lambda_sq,N)=(13,120)`
- pilot dps: `191` from `out/lambda_sq_13_N_120.json:dps`
- packet: `tol_B`, constructor dps `110`, quad order `192`
- coefficient max diff vs previous quadrature: `6.12372149174e-34`

## Method

- `K` is the Fourier packet vector from true-precision `k1 = g04` (`tol_B`).
- `Omega_Q = W02_Q - WR_direct_Q` using the pilot `wr_direct` integral lifted to the diagonal quadratic form.
- `p_R_Q = WP_Q` over prime powers `k <= exp(L) = 13`.
- `a_sym = Omega_Q - p_R_Q`; the `(1/2pi)` trace normalization is the pilot `q_nm` normalization in this channel.
- No `T` matrix was built for this gate.

## Numbers

- `W02_Q = (1.51194604189973103 + 6.66464539714484283e-225j)`
- `WR_direct_Q = (1.45056048910577 + 0.0j)`
- `Omega_Q = (0.0613855527939610266 + 6.66464539714484283e-225j)`
- `WP_Q = (0.0613855527939610266 + 0.0j)`
- `a_sym = 5.37295373544202336e-59`
- `|Im(a_sym)| = 6.6646454e-225`
- matvec target `a1_raw = 5.37295373544202336e-59` from `out/packet_truth_pull_v1.json:T0_T2_main.a1_raw`
- `abs_diff = 1.2767758271e-149`
- `rel_diff = 2.37630154653e-91`
- registered tolerance: `1.0e-6`

## Interpretation

- The diagonal symbol channel matches the saved raw matvec within the registered relative tolerance.
- After `ZeroSumCrossCheck_v1`, this is reclassified as `TAUTOLOGICAL_CHANNEL`: useful internal consistency for the pilot `tau` contraction, but not an independent E5 zero-sum judge.
- State promotion already applied: `AlphaDetector`, `ZEO_v2`; `G3a` remains reduced to `TraceCompressionBound`.
