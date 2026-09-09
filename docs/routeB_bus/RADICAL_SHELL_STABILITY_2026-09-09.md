# Radical-shell stability: K36 versus K48, 2026-09-09

Authority: DIAGNOSTIC_NEVER_A_PROOF. All ratios below are raw finite-matrix diagnostics, not certified source eigenvalues.

## Frozen prediction and method

Before any numerical launch: q/lambda1 = 1.5 at a=0.75, K=48, span of g0,g2,...,g12. Frozen manifest SHA256: 92592e8037f57aff9cd71aa1dd3441cdc59ed906510dfebde03d356ecf6af3a0. Six sequential background jobs, each with three windows, all completed EXIT=0. Builder settings: base h=0.02, XI=20000; h refinement 0.01/20000; cutoff refinement 0.02/40000. Saved Q, G, eigenpairs and projected theta coefficients are retained for all jobs.

g0-g4/g8/g12 means 3/5/7 even members. Physical Gram orthogonality is used. q_cancel=(r-b*C^-1*b)/(1+||z||^2); q_direct is the Rayleigh quotient of the reconstructed trial. The absolute diagnostic rounding scale is max(eps*max(1,||L^-1 Q L^-T||2),abs(q_direct-q_cancel)), G=LL^T. It is NOT a rigorous floating-point error bound.

## Baseline comparison

| a | even shell | q/lambda1 K36 | q/lambda1 K48 | absolute scale K36 | absolute scale K48 | final status |
|---|---|---:|---:|---:|---:|---|
| 0.70 | span_g0-4 | 161.71238 | 165.25329 | 1.044991e-15 | 1.172725e-15 | UNRESOLVED / UNRESOLVED |
| 0.70 | span_g0-8 | 8.721609 | 8.9125695 | 1.044991e-15 | 1.172725e-15 | UNRESOLVED / UNRESOLVED |
| 0.70 | span_g0-12 | 1.6006434 | 1.6358137 | 1.044991e-15 | 1.172725e-15 | UNRESOLVED / UNRESOLVED |
| 0.75 | span_g0-4 | 907.60883 | 1204.2256 | 1.026565e-15 | 1.151714e-15 | UNRESOLVED / UNRESOLVED |
| 0.75 | span_g0-8 | 21.442116 | 28.452567 | 1.026565e-15 | 1.151714e-15 | UNRESOLVED / UNRESOLVED |
| 0.75 | span_g0-12 | 2.6154958 | 3.4516623 | 1.026565e-15 | 1.151714e-15 | UNRESOLVED / UNRESOLVED |
| 0.80 | span_g0-4 | -220.35027 | -98.226977 | 1.010191e-15 | 1.135609e-15 | UNRESOLVED / UNRESOLVED |
| 0.80 | span_g0-8 | -1.4166724 | -0.61947426 | 1.010191e-15 | 1.135609e-15 | UNRESOLVED / UNRESOLVED |
| 0.80 | span_g0-12 | 1.9307688 | 0.86902792 | 1.010191e-15 | 1.135609e-15 | UNRESOLVED / UNRESOLVED |

## Builder sensitivity, absolute normalized matrix scales

E_Q,h and E_Q,XI are norms of the individual Q differences in the BASE Gram-whitened coordinates, compared only at the same K and a. E_G is the corresponding normalized Gram difference. max(E_Q,h,E_Q,XI) is an empirical sensitivity gauge, NOT a joint or certified error bound. It does not justify any enclosure of the continuum eigenvalue.

| K | a | E_Q,h | E_Q,XI | max E_G | lambda base | lambda h | lambda XI |
|---:|---|---:|---:|---:|---:|---:|---:|
| 36 | 0.70 | 1.162834e-14 | 1.223270e-05 | 0.000000e+00 | 4.36748254e-13 | 4.38379498e-13 | 4.38098377e-13 |
| 36 | 0.75 | 1.333561e-14 | 9.065381e-06 | 0.000000e+00 | 3.88553744e-15 | 3.80026854e-15 | 3.82566974e-15 |
| 36 | 0.80 | 3.826671e-15 | 5.085529e-06 | 0.000000e+00 | -4.10338878e-16 | -9.93971781e-16 | -6.86825786e-16 |
| 48 | 0.70 | 2.008022e-14 | 5.136048e-05 | 0.000000e+00 | 4.27389897e-13 | 4.27586385e-13 | 4.27859770e-13 |
| 48 | 0.75 | 2.398850e-14 | 3.800391e-05 | 0.000000e+00 | 2.92847654e-15 | 4.03070945e-15 | 3.65501312e-15 |
| 48 | 0.80 | 6.132922e-15 | 2.928281e-05 | 0.000000e+00 | -9.20426786e-16 | -1.58658938e-15 | -1.61714847e-15 |

## Acceptance limits and uncovered errors

A row is UNRESOLVED if any build variant fails the local floating/solve screen, lambda1 is not above the empirical matrix gauge, or normalized Gram variation >=1e-3. Local solve screens: cond(C)*eps <=1e-3 and relative solve residual <=1e-10. This conservative diagnostic classification does not assert that the entire matrix difference acts on the ground direction. Full raw direct/cancellation values and each refinement are in the companion JSON.

The requested rigorous builder budget remains OPEN: sc_build uses binary64 special functions and quadrature and a leading asymptotic Fourier-tail correction without a total remainder enclosure. Theta derivatives/projection and infinite-tail errors are also not enclosed. Mesh/cutoff differences cannot replace these bounds. No larger K or extrapolated degree law can repair this missing certificate.

The numerical prediction is UNRESOLVED under the frozen error-based scoring rule. It is neither confirmed nor refuted by a raw ratio with unresolved denominator. Three windows do not determine cofinal m(a). At a=0.80 negative rounded eigenvalues are below the floating scale and are not evidence of a negative source form.

## Independent checks

A separate recomputation at K48,a=0.70 used polynomial derivative recursion and Gram-orthonormal coordinates: even shell ranks 3/5/7; direct ratios 165.2533199462,8.9125893409,1.6358376201. Differences from saved direct q were at most 1.54e-17, below floating scale 1.172725288e-15. The main observer separately recomputed the stored g0-g12 cancellation ratio as 1.6358136659398185.

A 70-digit eigensolve of the exact rounded K48,a=0.75 Q/G gave lambda1=0.000000000000002996589111827079995959768340279588884465245592216055227868731082252975; difference from binary64 eigensolver 0.00000000000000006811257063744142228090661288762153181280127164231165317047553935442473. This verifies only the saved rounded matrix, not source assembly.

## Decision

Retain SCHUR as an analytical proof-construction batch: fixed degree schedule, full-tail determinant, coupled signed arithmetic remainder. Do not use this table to claim the stronger unnormalized recovered-energy inequality or a lower sign. My next numerical choice is a projected/source error enclosure at a=0.75 before extending a or K. If that enclosure resolves lambda and q, test the degree law; otherwise retain the analytic tail-determinant task and classify the numerical ratio as unresolved.

## Artifacts

- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/radical_shell_stability_20260909.json
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/radical_shell_stability_20260909_manifest.json
- Matrix, eigenpair and margin outputs: /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/window_derivative_K{36,48}_codex_radical_20260909_{base,h,xi}*
- Reproduction scripts are embedded byte-for-byte with hashes in the companion JSON; the original frozen manifest is retained unchanged.
