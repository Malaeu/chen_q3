# IDENTITY_FAILURE — fixed-Gaussian response audit

DIAG only. RH_PROVED: false. This audit does not establish RH, (7.4), or a matrix growth exponent. No source identity was retuned.

The specified finite prime sum fails every Task A gate. The omitted prime-power tail already exceeds the tolerance by a single omitted positive atom. This is a failure of the prescribed finite-sum instrument to check the full-line identity; it is **not evidence against Proshka’s full-line normalization**. That normalization remains unconfirmed by this gate.

Preregistration was committed before all numerical runs at `8e0e8da16bd0489777f3221455b854647f65b71f`. `preregistration.bundle` preserves that commit and its PREDICTIONS.md bytes. The final delivery amends that local commit to meet the single-commit request. Base `5a409f1e88439d12c5d84126e09d421781d24e26`; verdict commit `62f782316d2ba4f83d27db82d0b64e1e8361cad2`, blob `2b5e02a0aa816da34c204f2a56a9033e6ac6b542`. Exact verdict bytes are in SOURCE_VERDICT.md. Input Git blobs were verified against the request.

## Task A

Both precisions, both worlds, all eight t: **32/32 IDENTITY_FAILURE**. Full H, S, both sides, quartet terms, tolerances, omitted atom, perturbation and cancellation ratios are in `task_a.json`. Table values below use dps60; all dps80 decisions agree. Maximum absolute arithmetic change on the repeat: 4.883714e-59.

| t | zeta arithmetic − zero | zeta cancellation ratio | plant cancellation ratio | gate 60 / 80 (both worlds) |
|---:|---:|---:|---:|:---|
| 0 | 7.071074e-10 | 5.559923e+35 | 345227.3 | FAIL / FAIL |
| .5 | 4.503189e-10 | 1.747413e+35 | 70128.71 | FAIL / FAIL |
| 1 | 5.902634e-10 | 1.608758e+38 | 180661.6 | FAIL / FAIL |
| 2 | 9.464382e-10 | 1.145073e+35 | 36793.2 | FAIL / FAIL |
| 3 | 1.578994e-9 | 1.683106e+36 | 4795.482 | FAIL / FAIL |
| 4 | 2.611362e-9 | 1.346751e+34 | 10924.79 | FAIL / FAIL |
| 5 | 4.298974e-9 | 1.018782e+35 | 148.7494 | FAIL / FAIL |
| 6 | 7.093186e-9 | 2.031401e+32 | 12.92313 | FAIL / FAIL |

Cancellation ratio uses (|H|+|S|)/|h_zero|; JSON also supplies the misleadingly smaller truncated-arithmetic ratio. No modulus square is substituted for F(u)^2. The quartet arithmetic moments are computed independently by full-line quadrature of g; the zero side uses F. Its polarized form is 2 Re(F(u)^2(e^{ut}+e^{-ut})), matching the builder’s 4 Re(ccᵀ) on the even sector.

The cutoff is exactly floor(exp(t+9)). C(v) has polynomial v^8−28.5v^6+217.5625v^4−442.875v²+112.6875, times exp(−v²/2)/sqrt(2π). It is positive for |v|≥9, so every omitted prime-power term is positive. Every row’s first omitted atom alone exceeds its gate budget. The observed residual is consistent with this omitted tail; it was not subtracted from the gate.

The zero tail uses Nζ(T)≤T² for T≥60, a loose consequence of classical explicit Riemann–von Mangoldt counting bounds (e.g. Rosser, “Explicit bounds for some functions of prime numbers”, 1941). For each integer shell k≥60, use 2(k+1)² times (k²+1/4)²(k²+1/2)² exp(1/8−k²/2+t/2). The polynomial times Gaussian decreases on these shells; the remaining shell sum past100 is dominated by the recorded factor 1.0000000001. The uniform bound for t≤6 is 5.298872e-763. This is an analytic tail bound evaluated numerically, not an interval enclosure of the quadrature.

Changing c_* by +1e−30 changes arithmetic by −1e−30 C(t). All 32 perturbed gates fail. Its isolated change exceeds the gate budget by at least 1.396392e+9. The already failed baseline means this plant is **not a clean pass-to-fail validation**; the perturbation is masked by the much larger cutoff omission.

## Task B

Unnormalized w_m from (6.1), as requested; these q values are not the graph-unit q in (6.5). The reference 2W[g]+2h(log m/2) is evaluated from the absolutely convergent zero formula for comparison only; all computed window forms retain literal arithmetic, Gamma tail and poles. This reference use does not turn the failed Task A gate into a pass.

Components telescope as W[chi f]−W[f], W[P chi f]−W[chi f], the e0 correction, then the e1 correction. Values are signed. Projection residuals near 1e−12 reflect the numerical resolution.

| world | m | return error | chi | cosine projection | e0 | e1 |
|:---|---:|---:|---:|---:|---:|---:|
| zeta | 16 | 0.7744905 | 0.02579846 | -0.0002373876 | 0.1356114 | 0.613318 |
| plant | 16 | 3.580604 | 2.123212 | -0.0001793689 | 0.4901027 | 0.9674688 |
| zeta | 64 | 0.170571 | 0.1242645 | -4.951066e-7 | -0.04046422 | 0.08677119 |
| plant | 64 | 6.294542 | 0.7387408 | 1.704356e-6 | 2.454006 | 3.101793 |
| zeta | 300 | 0.007321006 | 0.005398805 | 8.715667e-13 | 0.001555694 | 0.0003665076 |
| plant | 300 | 9.297408 | 8.745693 | 1.259437e-12 | -1.037109 | 1.588824 |
| zeta | 1000 | 0.0364833 | 0.001515171 | 7.517389e-13 | -0.0001596862 | 0.03512781 |
| plant | 1000 | 6.37653 | 4.134849 | 1.212364e-12 | 0.0466069 | 2.195074 |
| zeta | 3000 | 0.02776512 | 1.513483e-5 | 1.831573e-12 | 0.000691708 | 0.02705827 |
| plant | 3000 | 1.815177 | 1.11158 | 1.845191e-12 | 0.153691 | 0.5499061 |

Fresh pinned 256-bit arithmetic matrices are used for m≤300; function-level finite-cosine correlation W is used above300. At300 the largest crosscheck discrepancy is 2.908672e-12. Across all three crosschecks the maximum is 3.104408e-9. FFT-size and cutoff-quadrature repeats and integration error estimates are recorded. Results are numerical DIAG, not interval certificates.

The bound crosses1e−30 at L=363.8803637220 (zeta) and363.9726782972 (plant); it is strictly below for larger L. First integer L=364. Explicit bound derivation and constants are in `task_b_notes.md`; the same bound is consumed in Task C. Its purpose is a conservative regime map, not a useful error estimate at these finite m.

## Task C

The table uses the declared magnitude envelope for the total on-line response, with zero-tail allowance, plus the explicit return-error bound. Thus it is an envelope visibility threshold; it does not certify an actual oscillatory negative response at m*. The DH entries use the supplied numerical census and the specified Task B comparison budget; this is not a separately computed DH literal window bound. See `task_c_notes.md` for tail counting and scope. Log means natural log.

| world / pair | sigma_right | gamma | log(m*) envelope crossing |
|:---|---:|---:|---:|
| dh 1 | 0.8085172 | 85.69935 | 23574.72 |
| dh 2 | 0.6508301 | 114.1633 | 85908.47 |
| dh 3 | 0.5743561 | 166.4793 | 371639.6 |
| dh 4 | 0.7242577 | 176.7025 | 138862.8 |
| dh 5 | 0.8695306 | 240.4047 | 156162.2 |
| dh 6 | 0.8195496 | 320.8765 | 321920.0 |
| dh 7 | 0.7682231 | 331.0503 | 408247.8 |
| dh 8 | 0.6285081 | 366.6409 | 1045313.0 |
| dh 9 | 0.8158737 | 411.7967 | 536544.4 |
| dh 10 | 0.7088822 | 440.4845 | 928414.5 |
| dh 11 | 0.5159183 | 520.9438 | 1.704216e+7 |
| dh 12 | 0.8469538 | 531.2797 | 813243.0 |
| dh 13 | 0.7295334 | 548.9068 | 1312218.0 |
| dh 14 | 0.7865591 | 566.5097 | 1119601.0 |
| dh 15 | 0.5828557 | 595.0234 | 4271895.0 |
| dh 16 | 0.628252 | 611.7751 | 2917430.0 |
| dh 17 | 0.6107646 | 646.9868 | 3778179.0 |
| dh 18 | 0.7605972 | 657.1084 | 1656533.0 |
| dh 19 | 0.7887031 | 692.8925 | 1662592.0 |
| dh 20 | 0.7773601 | 737.767 | 1962051.0 |
| dh 21 | 0.8530015 | 783.653 | 1739385.0 |
| dh 22 | 0.6685515 | 811.7658 | 3908934.0 |
| dh 23 | 0.5619479 | 847.4657 | 1.159185e+7 |
| dh 24 | 0.8561094 | 857.2959 | 2063546.0 |
| dh 25 | 0.6808998 | 864.1181 | 4127102.0 |
| dh 26 | 0.6884301 | 892.149 | 4223429.0 |
| planted_quartet 1 | 0.8333333 | 7.0 | 293.8259 |

Crossings are continuous L values. The formal smallest integer is floor(exp(L_cross))+1 (subject to m≥3); its exact giant integer is not constructed or claimed from rounded L. JSON records rounding-scale information. The table assumes census completeness as supplied; the census itself is numerical, not certified. Dominating an envelope is stronger than dominating the phase-dependent absolute sum; no smallest crossing of that oscillatory sum is claimed.

## Reproduce and verify

From repository root: run `python docs/routeB_bus/prove_rh_response_audit_2026-11-05/scripts/task_a.py`, then task_b.py, task_c.py `--bound explicit`, and report.py. Dependencies: Python, mpmath, NumPy, SciPy; pinned matrix checks also require gmpy2 and python-flint. Preserve the preregistration before any rerun. SHA256SUMS covers all delivered artifacts except itself. Source and raw results remain unchanged after the reported failure.

AUTOPSY: dropped=NUMERICAL_SURROGATE; note=finite prime cutoff cannot resolve this full-line response at the prescribed gate; no RH sign or normalization conclusion is admitted.
