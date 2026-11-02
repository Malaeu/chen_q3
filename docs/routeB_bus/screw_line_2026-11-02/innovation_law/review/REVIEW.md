# Independent conventions and numerical-method review

DIAGNOSTIC_NEVER_A_PROOF. Scope: the prediction functional used by this diagnostic, its coordinates, and the finite planted control. This is not a complete audit of every theorem in the source and supplies no missing arithmetic positivity bound.

## Coordinates and previous onset reports

The anchored point Gram K(i h,j h)=g((i-j)h)-g(i h)-g(j h) is related to the increment Toeplitz Gram T by K=S T S^T, where S is the lower-triangular matrix of ones. Every leading S has determinant one. Consequently the point-kernel Schur pivot equals det(T_n)/det(T_(n-1)), whenever the previous block is invertible. The last increment and last point differ by an already observed point, so the variational prediction errors also agree when the past is positive. This confirms the coordinate use in SOURCE_PREDICTION.md lines 198–214.

The former DH onsets 5.45 on h=.025, 4.296875 on h=1/64, and 3.78125 on h=1/128 are measurements on different meshes. They are not evidence that point prediction and increment prediction are different objects. A mesh change changes both the approximation of the observed history and the next prediction horizon. The continuum first failure is not located by these finite onsets.

Both source implementations use the same DH constant: log(5/pi)+psi(3/4) = -EulerGamma-log(8*pi/5)+pi/2. The zeta pole contribution in g is -16 sinh²(t/4); DH has none. The plant is 4 Re[(cos(wt)-1)/w²] with w=2pi/log2+i/4. No zero table or RH assumption is needed to evaluate these entries.

## Three distinctions needed for interpretation

1. After the past becomes indefinite, the infimum of the signed residual quadratic over predictor coefficients is -infinity. A later positive nonsingular Schur pivot is only an algebraic pivot. Negative inertia is cumulative; it cannot be reset by a later positive row. Source lines 80–112 and 177–185 carry the necessary positivity/range guards. The singular anchored t=0 row is structurally zero with zero coupling and can be removed. An unresolved nonstructural pivot must not be silently truncated by a numerical pseudoinverse.
2. Source (11), lines 164–171, differentiates with respect to an arithmetic coefficient c_n, holding the time and other source terms fixed. It gives partial sigma²/partial c_n = -Q_f(log n) at a stationary predictor and a genuine minimum when the past is positive. It is not the derivative with respect to the new time. With a fixed history, sigma² is continuous at a source hinge. At an isolated unshifted hinge t=log n its slope jump is -2 c_n(1-sum_i a_i); a shifted hinge t=s_i+log n contributes -2 c_n a_i. Coincident events add. At the unshifted birth Q_f(t)=0, so the coefficient derivative can vanish while the endpoint slope has a nonzero jump. Changing the history between adjacent grid rows is a separate operation from differentiating that fixed-history function.
3. Source (17), lines 226–255, fixes a finite positive history and then sends the extra step h to zero. Its remainder constant depends on the inverse past Gram. It does not predict a uniform h log(1/h) ratio when the entire history is simultaneously refined. The same local cusp law holds in the planted world. Therefore such a local fit alone fails the planted-world discriminator.

Positive nonincreasing innovations on a fixed stationary positive grid are a general prediction property. They do not by themselves reveal a zeta-specific source mechanism. Similarly the reflection recursion v_n=v_(n-1)(1-alpha_n²) makes |alpha_n|<1 a reformulation of positive continuation while the previous pivot is positive, not a new arithmetic estimate.

## Full-history planted factorization control

The rank-one expression (29) in the source is stated in even measure coordinates. The full one-sided grid in this task is not an even-sector restriction. For h fixed, set q=8(1-cos(w h))/w². The quartet increment contribution is Re[q cos(w(i-j)h)]. Write phi=arg(q)/2 and use the two complex features cos(w i h), sin(w i h). Their rotated real parts give two positive columns V, and their rotated imaginary parts give two negative columns U, each scaled by sqrt(|q|). Thus the numerical implementation checks

T_plant = T_zeta + V V^T - U U^T = C - U U^T.

This is rank at most four, with at most two negative directions. With C positive, Theta_n=U_n^T C_n^{-1} U_n is a two-by-two matrix. The diagnostic compares its eigenvalues with one and uses the determinant identity

sigma²_plant,n = sigma²_C,n det(I-Theta_n)/det(I-Theta_(n-1)).

The tested C is positive by a successful ordinary floating Cholesky and small residual; this is numerical evidence, not an interval certificate. Conditional on RH, the underlying zeta part is positive and adding V V^T preserves positivity. No unconditional positivity of all zeta prefixes is inferred from finite factorization.

The whitened load Y=L_C^{-1}U satisfies Theta_n=sum_(j<=n) Y_j^T Y_j. This lets one examine every prefix after one Cholesky, with no repeated dense solve. The observed monotone risk accumulates even while the most recent signed pivot may return positive. It is a useful explanation of the planted failure. It is not a universal source law distinguishing zeta and DH, because the DH-minus-zeta source is not this finite-rank quartet perturbation.

## Executed checks

`planted_hazard.py` read the independently generated 100-digit g/r samples and used a separate dense Cholesky and two-column whitening. It tested all 2,880 prefixes across four meshes. The crossing index and cumulative negative inertia agree with the arbitrary-precision Levinson outputs in every row.

| Mesh denominator | First Theta_max > 1, time | Theta_max at prior point | Theta_max at crossing | Theta_max at t=6 |
|---:|---:|---:|---:|---:|
|32|1.4375|0.8718653894|1.0016441966|63.77490487|
|64|1.203125|0.9608481299|1.1678771793|142.75099845|
|128|1.046875|0.9917082605|1.1316379792|524.05132797|
|256|1.03125|0.9782750835|1.0635713165|2191.38261756|

All Theta_max increments were positive. The maximum relative error in reconstructed signed pivots was 1.86e-11, the quartet matrix reconstruction error at most 6.25e-17, the relative Cholesky residual at most 3.84e-16, and the relative whitening residual at most 2.12e-15. Direct signed-kernel smallest eigenvalues on both sides of each crossing had the expected signs; their values are retained in the JSON files. The fine-mesh sign gaps exceed the measured matrix construction errors by many orders, but no directed-rounding enclosure is claimed.

Independent 80-digit dense low-rank controls at mesh32 prefixes24 and46 gave factorization Frobenius errors below1.73e-81 and determinant-ratio relative pivot errors below5.11e-77. They check the rank-four normalization, phase rotation and determinant sign. The larger meshes remain floating diagnostics validated against the separate high-precision recurrence; the source samples are shared inputs and are not advertised as an independent source derivation.

Source code, both precision reports, every prefix hazard, and input hashes are retained in this directory. The principal limitation remains: a finite positive baseline and a planted low-rank explanation do not provide an arithmetic estimate that forces the actual zeta continuation to stay positive.
