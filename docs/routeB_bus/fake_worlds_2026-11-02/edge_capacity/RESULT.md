# EDGE_CAPACITY_v1

DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH.

Base: `1c91c4c86ef6987782c08c84e22707d1b7324646`. Inbox: `3fef776b3bd0ebeb9d87e665432ae3e423f2dfb1`. The requested identities (9)–(12) appear as (5.4)–(5.7) in the actual source verdict. Its SHA256 is `e220176efe6002006d10abff759c560645c7e4c4059b96692081a8123758d2ae`.

## Decision

Close this finite edge-capacity explanation of the observed R≈4. The endpoint constraint leaves a soft direction, and endpoint capacity does not reproduce R. This closes this diagnostic line only; no route-state or RH export is changed.

All eight requested ζ cells and thirteen DH controls are retained, including the three separate m120 cutoffs q63/q64/q65. Predictions were registered before these computations in PREDICTIONS.json.

| Prediction | Result |
|---|---|
| πT C_T/log T in [1,3] | 8/8 ζ cells pass; range 1.60414–1.71707 |
| Scaled capacity agrees with R within 1% | 0/8 pass |
| Endpoint-zero minimum ≥1000 times original minimum | 0/8 pass; actual factor 1.06064–1.33662 |

## Exact finite energy bookkeeping

With e=f(b), h=f−eχ, the same source form gives λ=H+e²C+X+V. C is evaluated by the finite arithmetic/archimedean/pole formula minus its finite low-zero head, with no independently truncated infinite zero tail. DH uses its signed zero pairing, odd gamma factor, all signed b(n), and no ζ pole. See energy/RESULT.md and ENERGY_SPLIT.csv for all raw and scaled terms.

The constant term is stable but explains only part of R. At ζ m240 the scaled terms are H=1.446943, C=1.631743, X=−3.228821, V=4.293303, giving R=4.143168. Their cancellation matters. Maximum edge-scaled identity residual is 1.08e−196; maximum precision change is 6.69e−151. These are floating arithmetic checks on the saved source data, not interval certificates.

## Capacity and endpoint constraint

The physical endpoint functional is (1,√2,…,√2)/√L. For G=U*AU and t=U*d_b, K=t*G⁻¹t and cap=1/K. The endpoint-zero problem is computed in an orthonormal basis of ker(t*). No endpoint sign alternation is inserted.

| m | q | R | cap·πT/log T | endpoint-zero/original minimum |
|---:|---:|---:|---:|---:|
| 55 | 27 | 3.580530 | 0.906173 | 1.33662 |
| 80 | 41 | 4.300051 | 0.674957 | 1.18575 |
| 120 | 63 | 4.436851 | 0.585411 | 1.15140 |
| 120 | 64 | 4.251664 | 0.505045 | 1.13448 |
| 120 | 65 | 3.925333 | 0.441833 | 1.12671 |
| 160 | 89 | 3.919362 | 0.346962 | 1.09707 |
| 200 | 115 | 4.525479 | 0.258815 | 1.06064 |
| 240 | 139 | 4.143168 | 0.237541 | 1.06081 |

The second eigenvalues are recorded in capacity/capacity.csv. There is a separated small mode, but it contributes only about 25% down to 6% of the endpoint inverse kernel. That distinction invalidates the proposed endpoint-capacity mechanism. In indefinite DH cells, positive algebraic capacity can coexist with negative constrained minima; it is not a positive variational capacity. All inverse, null-basis, and interlacing checks pass. ζ240 80/110-digit relative change is 2.51e−56; the especially ill-conditioned DH240 inverse changes by 8.52e−18.

## Rellich checks

rellich/RESULT.md records all eight ζ and thirteen DH source/constraint/projector checks. The local path fixes integer N and active zero coordinates while L dilates. All eight ζ and the two m55 DH controls additionally have transported-Rayleigh finite differences. This derivative agrees with the simple compressed eigenbranch to first order; no new large full-carrier eigensystem was computed. Other DH controls have analytic source/projector checks only.

Both actual compressed eigenbranches are recomputed in a separate m8 threshold control. Its nonzero prime-power kick is −0.524710330246889…. Requested large m are mixed-factor composites (and DH multiples of 5), so their birth kicks vanish. Source identities pass within the recorded floating tolerances. Omitting motion of J-perp can materially alter the slope: at ζ240 its correction is −2.802834e−23 versus source virial −2.937757e−23. Coarse and refined differences are both retained, including the necessary h=1e−40 high-cell refinement.

## Exploratory alternative and limits

After observing the energy decomposition, R_V=πTV/(e²log T) was registered as an exploratory alternative, explicitly after the primary experiment. It lies in [3,5] in 8/8 ζ cells but matches R within 10% in only 6/8. All six native DH controls fall outside the band, while one matched DH control enters it. Thus it is neither a uniform explanation nor a uniform discriminator across these controls. EXPLORATORY_VARIABLE.json and EXPLORATORY_RESULTS.json retain the registration and failures.

SHA256SUMS covers this packet. INPUTS.json pins selected-cell inputs; each subdirectory contains reproduction scripts, raw output, provenance and validation details. Dense source matrices are reproducible caches and are not duplicated here. All findings are finite numerical diagnostics, with no cofinal law, proof, positive-volume assertion, or unconditional Hilbert-space positivity claim.
