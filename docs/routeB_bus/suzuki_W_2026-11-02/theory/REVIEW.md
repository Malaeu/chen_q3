# Independent W implementation review

2026-11-02. **PASS for the stated finite implementation and reporting scope.** This is a finite Galerkin diagnostic review, not a continuum deficiency-vector certificate or proof of Theorem1.5/Corollary1.6.

Reviewed `W/prototype.py` core SHA256: `b68cc41885954395f2bf4e6009e62eb5fd96a12e07c3a9c750268ba019eba56b`. Producer files were not edited.

## Full-parity source

The even basis is phi_n=d_n(−1)^n cos(2πnx/L)/sqrtL; the odd basis is psi_n=sqrt(2/L)(−1)^n sin(2πnx/L), n≥1. Their physical L2 mass matrices are identities. For r=s/L, odd correlations are

    Qodd_nn=2(1−r)cos(2πnr)+sin(2πnr)/(πn),
    Qodd_ik=(2/π)[i sin(2πkr)−k sin(2πir)]/(i²−k²).

Consequently the odd source diagonal differs from the even positive-index diagonal by−2 beta_n/(πn), and its off-diagonal is2[k beta_i−i beta_k]/[π(i²−k²)], with beta the combined arch/arithmetic sine moments. The implementation agrees. The original source constant, all arithmetic coefficients and full infinite arch tail are retained. DH has its odd conductor5 gamma kernel and no pole.

The zeta odd-pole contribution is negative:−q q^T. Direct overlap with sqrt2 sinh(x/2) gives

    q_n=−32πn sqrtL sinh(L/4)/(L²+16π²n²).

The prototype uses the globally opposite q vector; its outer product is exactly the same, so this is not a bug. Omitting this odd pole would change the source, but it is present correctly.

## Resolvent loads and norm

For the stated phased basis, the e^x loads are

    b_even,n=2d_n sinh(L/2)/[sqrtL(1+omega_n²)],
    b_odd,n=−2sqrt2 omega_n sinh(L/2)/[sqrtL(1+omega_n²)].

Thus the prototype's combined vector is v_+ proportional to(A_N−lambda I)^−1 P_N e^x, matching the+i deficiency label for D=i d/dx. Negating its odd coefficients gives the reflected v_- with load e^−x. The energy normalization sqrt(b_even·c_even+b_odd·c_odd) equals the T norm of the raw solution; reflection gives equal T norms. Euclidean normalization is not substituted. The prototype correctly labels its main shifts as not continuum-admissibility-certified merely by finite positivity.

## Independent physical m20 check

A separate read-only calculation constructed both parity source matrices from physical overlap integrals C_ik(s)=integral psi_i(x)psi_k(x+s)dx, Q=C+C^T, instead of using the prototype's closed modal correlation formulas. It used128-point x quadrature,128-point s quadrature on8 panels, direct physical pole integrals and direct e^x loads. No new eigensystem was needed.

|world|block|max absolute entry difference|Frobenius difference|
|---|---|---:|---:|
|zeta|even|4.85e−13|7.79e−12|
|zeta|odd|2.42e−13|8.35e−13|
|DH|even|5.33e−13|8.21e−12|
|DH|odd|2.49e−13|8.42e−13|

Direct load differences were≤1.49e−13 for the even loads and≤3.07e−14 for odd loads. This float64 consistency check supports the sign/normalization derivation; it is not an outward interval source enclosure. Arithmetic recurrence correctness was checked algebraically in AUDIT.md/NORMALIZATION_DH.md; this physical overlap check focuses on parity, arch and pole normalization.

## Independent multiprecision solve and saved-cell controls

`W/validation_audit.py` independently rebuilds both m20 blocks at80dps, GL128 on8 panels, and solves at each saved shift without an eigensolve. Against the float profiles, coefficient relative physical L2 differences are2.54e−15(zeta) and9.08e−16(DH); maximum coefficient differences1.23e−15 and3.93e−16. The float profiles' T-norm-square errors in the multiprecision source are1.15e−15 and1.19e−16. Output/provenance is `W/validation_audit_m20.json`. This validates the bounded m20 case, not a continuum limit or all large-m quadrature errors.

Across all442 saved finite cells, the reported normalized T-norm-square differs from1 by at most8.89e−16, linear solve residual is at most7.54e−15, and finite spectral gap is at least0.9999999999996. These are saved float consistency diagnostics, not interval estimates of the continuous operator.

## Target, phase and root code inspected

`W/diagnostics.py` uses the correct plus-exponent transform. Its sine part S is the real coefficient of i in the odd transform, so v_+ has transform C+iS and v_- has C−iS. On the real axis the dephased expression for full phase θ is

    exp(−iθ/2)W/2=cos(θ/2)(zC+S)+sin(θ/2)(zS−C).

The implementation's πj/16 half-angle matches its2πj/16 θ grid. Both target formulas differentiate xi with respect to s correctly, and the special s=0,1 limits use the correct xi'/xi value. The normalization is a constant anchored at i/4, not a free pointwise analytic fit; θ is selected on the calibration subset and measured on the heldout subset. Such restricted diagnostics do not test every admissible φ in the corollary. The historical v1 and current v3 target labels must remain explicit.

`W/circle.py` uses the actual off-line DH node with its real displacement retained. Its coordinates are rounded to float, which the output labels. Sampled shrinking-circle error growth is finite numerical evidence; eight boundary samples and float W values are not an argument-principle or interval certificate.

Real-root lists are found from sign changes on a finite grid. They can miss closely spaced paired roots or tangencies; they are not complete zero censuses. Negative coordinates are also evaluated at−conjugate(z). Target reflection follows the real completed-function functional equation; W is evaluated independently. No arbitrary-θ symmetry of W is assumed.

`W/weak.py` correctly uses endpoint-zero H1 tests psi_n and phi_n−sqrt2 phi_0. The desired+i relation is pairing(u',v_+)+pairing(u,v_+)=0; the wrong-sign plant reverses that sign. These tests and their derivatives lie inside the Galerkin space, so passing follows from the finite resolvent equations and integration by parts of the e^x loads. It is an internal sign/control check, not additional control of high modes or the full continuous adjoint domain.

## Exact flat-metric baseline

For the abstract control T=I, v_±=exp(±x) and

    Wθ=−i[(e^a+e^{iθ}e^−a)e^{iaz}
            −(e^−a+e^{iθ}e^a)e^−iaz].

Its zeros have spacingπ/a=2π/L; θ=0 gives the integer lattice and θ=π the half-integer lattice. An80dps check gives formula discrepancy below1.89e−80 and residual at those analytic lattice points below1.20e−79 (`flat_control.json`). This baseline explains why a window-frequency lattice is not automatically zeta alignment; it is not asserted to be the source W's asymptotic law.

## Final report and scope

Final `W/RESULT.md` and all32 expanding/fixed-grid diagnostic JSONs were inspected. The report separates finite shift positivity from continuous admissibility, labels the roots and derivative references as incomplete numerical lists, includes a fixed-grid control in addition to the expanding range, and treats the shrinking DH circles as finite sampled diagnostics. It does not infer real-zero theorems, the absence of spurious nonreal roots, or failure of every analytic gauge from a failed constant-gauge fit. The source labels and differing v1/v3 targets are explicit. No substantive correction is required.

The DH s=1 removable value was independently checked from D(s)=5^(−s)Σa_k zeta(s,k/5): D(1)=−Σa_k psi(k/5)/5 and D'(1)=−log5 D(1)−Σa_k gamma_1(k/5)/5. The implementation's generalized-Stieltjes sign agrees. The ξ s=0,1 limits likewise have the correct logarithmic derivative signs. The historical z=0 target is understood by its removable limit; current numerical grids are inside the upper half-plane.

The finite experiment's unresolved mathematical steps are unchanged: a continuously admissible shift, approximation of the genuine deficiency vectors with domain/energy control, a justified gauge family and limiting topology. Finite source/solve agreement and the exact flat-metric baseline do not establish those steps. No RH or cofinal claim is certified by this review.

## Nearest-zero postprocess

The independent nearest-neighbor postprocess `root_comparison.py` correctly checks the two sorted-reference neighbors and permits many W roots to choose the same reference. It leaves the original W roots and xi-prime comparison fields unchanged. Its distances are descriptive, not a one-to-one spectral identification: a denser W list can improve nearest-reference distances by itself. For a positive-band count, the seeded theta0 origin must be excluded or labeled separately; the featured theta=pi count has no origin and is unaffected. No new eigenproblem or zero-completeness claim is introduced.

All32 final diagnostic JSONs were batch-checked for shape, finite selected metrics and actual calibration-minimum selection. Each contains32 phase/target rows,2 selected rows and16 real-root lists. Those checks passed.
