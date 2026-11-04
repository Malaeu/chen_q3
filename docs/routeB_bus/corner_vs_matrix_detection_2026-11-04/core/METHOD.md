# B+ finite core diagnostics

DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER_NOT_RH. PX_RH_CLAIM: NOT_MADE. This worker produces finite numerical values and witnesses; the parent owns all K1-K4 scoring.

## Source and preregistration

The pre-run receipt is `../ADDENDUM_PRE_RUN_RECEIPT.json`, prediction commit `44e89c1277dde897816b35c637fa7c926ed5d2c6`. The driver checks the current PREDICTIONS bytes against that receipt before computation. The earlier gate is checked against `../producer_history/PREDICTIONS_before_addendum.md` by `../gate/verify_existing_gate.py`; no historical gate values were recomputed.

The mathematical source is `../inputs/PROSHKA_VERDICT_TWO_CORES_2026-11-04.md`: section 1 lines 120-138 fixes basis, W=I+X, decomposition and pole; section 2, equation (2.1), fixes the physical p-null quotient; section 4.1 fixes A(u)=H+pp^T-uB; section 9 requires DH's own gamma, signed coefficients and absent pole. Exact source and code SHA-256 values are in `core_results.json`, alongside each builder's returned source metadata. Source assembly is exclusively the released `../builder/core_components.py` API. Its independently produced validation files remain in builder/.

Use j=0,...,m, L=log(m), d_0=1 and d_j=sqrt(2) otherwise, omega_j=2*pi*j/L, and phi_j=d_j*(-1)^j*cos(omega_j*x)/sqrt(L) on [-L/2,L/2]. Matrices retain physical L2 normalization. W is diagonal with entries 1+omega_j^2; S=W^(-1/2). The source-native zeta pole is p_j=sqrt(2/L)*d_j*sinh(L/4)/(omega_j^2+1/4). DH has its own H and signed B, conductor 5, odd gamma, and exactly p=0.

## Constraints and finite extrema

The primary physical constraint is p^T z=0. With y=W^(1/2)z, this becomes (S p)^T y=0. A unit Householder reflector R maps q=S p onto the first coordinate axis; its last n-1 columns form an orthonormal basis of q-perp. For DH, q=0 and the full n-dimensional space is used. No pole functional is added to DH.

B+1 reports the largest eigenvalue of restricted S B S. For a quartet, c_j is the same multiplicity-one stable-sinc coefficient used by the physical-kernel gate, Q=4*Re(c*c^T), and the effective arithmetic form is B_eff=B-Q. Thus the normalized rank-two update is -4*(S Re c)*(S Re c)^T+4*(S Im c)*(S Im c)^T. Original B is reported once per world and m in `Cstar_original_B` rows, independently of every plant. Effective rows are `Cstar_effective_B_minus_Q`. They do not alter or replace the original B rows.

B+2 reports the smallest eigenvalue of S(H+pp^T-0.9B+Q)S on q-perp as `physical_pole_null`. The physical pole is retained in the assembled matrix before restriction. The separate literal as-written convention restricts the same normalized matrix to p-perp, labelled `literal_normalized_p_perp`. It is not called physically pole-null. A physical vector is always saved as z=S R[0;v], or z=S v for the full-space case.

At restricted dimension at most 128, extrema use dense scipy.linalg.eigh. Larger dimensions use scipy.sparse.linalg.eigsh with a full-matrix LinearOperator, deterministic initial vector, tolerance 1e-11 and at most 1000 iterations. The operator multiplies the full normalized source plus the exact finite rank-two update before applying the restriction; no frequency truncation is introduced. Every row contains the Ritz residual and normalized constraint residual. Residuals above 5e-9 fail the run. These numerical eigensystems are not certified enclosures or cofinal statements.

## Gate and weak first cells

Before the grid, the m=16 source gate compares the Householder calculation against an independently constructed physical null-space basis and generalized eigh of (N^T M N,N^T W N). Both worlds and both original-B maximum and weak-form minimum are checked. The largest source comparison error is 2.776e-17; an additional generic seven-dimensional test gives 6.662e-16. Fresh p and exact H+pp^T-B reconstruction are also checked. The complete values are in `normalization_gate.json`.

The distinction between q and p is numerically visible at m=16: the literal weak-minimizing vector has physical p^T z=-0.07697079, while the primary vector has p^T z=5.58e-18. They are different conventions.

The weak detector threshold is strictly below -1e-6. Unplanted u=0.9 triggers at its first cell m=16. All three gamma=14 plants trigger at first admissible m=16; all three gamma=50 plants trigger at first admissible m=21. Both constraint conventions trigger there. Consequently none of these first-threshold claims skips a predecessor in its admissible domain. Saved vectors and values are indexed by `first_weak_detections` in `core_results.json`; high-precision confirmations are assigned to the parent and are not claimed here. Negative unplanted u=0.9 values are behavior of the changed form, not failed original-zeta controls.

The B+1 grid is the preregistered set plus the supplied original-task first thresholds. The driver also computes m=21 to service the explicitly prescribed B+2 admission cell. The exact processed grid, individual entries, source-assembly costs, run budget and failures are in `core_results.json`; `core_cells.csv` contains the same finite extrema in table form. Grid corner entries do not substitute for the parent's exhaustive integer scalar scans.

## Reproduction and retained failure

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 python3 docs/routeB_bus/corner_vs_matrix_detection_2026-11-04/core/core_diagnostic.py --budget 300

An initial attempt completed the small numerical gate but failed when serializing a NumPy boolean before the grid. Its traceback is preserved in `initial_serialization_failure.log`; its CPU cost was not instrumented separately. The JSON scalar converter was corrected, and the gate and full run were restarted. No tolerance, mathematical formula, or grid was changed. The successful run's process CPU and wall time are recorded separately from that failed attempt.

The completed core grid used 58.5746 process CPU seconds and 59.2720 wall seconds for 25 m values and 541 rows. Its largest Ritz residual was 4.856e-14 and largest normalized constraint residual 6.045e-16.

## Exhaustive high-precision scalar corners

`scalar_corners.py` uses the unchanged pinned `inputs/analytic_source.py` coefficient producer `coefficients(3000,256)` for both zeta and DH. It builds full signed prefixes S0=sum(b_n/sqrt(n)) and S1=sum(b_n*log(n)/sqrt(n)); the arithmetic corner is B00=2*(S0[m-1]-S1[m-1]/L), retaining every n<m. DH is not restricted to prime powers. Actual MPFR working precision is 296 bits (about 89 decimal digits), special functions use 328 bits, and the endpoint-tail cutoff is the source's 2^-304.

For alpha=1/2 (zeta) or 3/2 (DH), define a_k=alpha+2k. The complete scalar archimedean term is

    H00 = c_world + trigamma(alpha/2)/(2L)
          - (2/L)*sum exp(-a_k*L)/a_k^2
          - 2*sum exp(-a_k*L)/a_k
          + 2*[atanh(exp(-L/2)) +/- atan(exp(-L/2))].

The plus sign is zeta, with c_zeta=-EulerGamma-log(8*pi)-pi/2; the minus sign is DH, with c_DH=-EulerGamma-log(8*pi/5)+pi/2. Zeta's physical pole corner is 32*sinh(L/4)^2/L and DH's is exactly zero. The changed zeta corner is H00+pole00-(9/10)*B00+Q00, with exact MPFR division for u=9/10 and a=1/3. DH uses u=1 and no quartet. Q00=4*Re([2*sin(z*L/2)/(sqrt(L)*z)]^2), z=gamma+i*a.

Before scanning, freshly assembled full pinned matrices at m=80, 256 source bits, are compared to the independently computed u=1 scalar corner in both worlds with absolute tolerance 1e-60. Exact differences and source metadata are in `scalar_validation.json`. This compares the source corner, rather than validating a changed-form formula against itself.

Every integer 16..3000 is evaluated for the unplanted zeta u=0.9 form, all six zeta quartet forms, and raw DH. Plants are included only for strict T_m>gamma, so gamma14 starts at 16 and gamma50 at 21. The 23,865 rows retain about 89-digit scalar values and raw strict-sign flags in `scalar_corners.csv`; no sign is decided after conversion to float. All eight scalar cases have no negative corner through 3000 and are reported as censored `>3000`. The unchanged zeta u=1 native corner is separately checked positive at every integer. This finite censoring is not a cofinal positivity claim.

The scalar run used 13.3280 process CPU seconds of the remaining 240-second budget and 14.5160 wall seconds. `scalar_summary.json` records all counts, admissions, minima, strict signs, source pins, and finite scope. No K prediction is scored here.
