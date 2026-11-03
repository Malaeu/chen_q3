# Normalization and interpretation

DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH.

The two experiments deliberately have different carriers. B compares its two coordinate systems inside one full real step carrier on [0,log m]. C retains the original even literal CCM Fourier carrier on [-log(m)/2,log(m)/2], N=m. No eigenvalue, quiet-space dimension or residual is transferred between B and C.

All physical bases are L2-orthonormal. Fourier evaluation means the unnormalized integral of f(x)exp(itx). In the even carrier, a critical zero pair supplies one real evaluation row, with form weight 2 times its multiplicity. An off-line quartet supplies raw real and imaginary rows, with weights +4 and -4 times multiplicity. In the full real step carrier one must also impose the conjugate off-line evaluation: four real constraints per quartet. Raw singular values in C use no sqrt(2) row scaling.

Three cutoff schedules are fixed throughout: c=1/4, c=1/2, and c=0, where T=(1+c(1+log L)/L)2pi m/L and L=log m. The strict convention is gamma<T. The supplied numerical zero censuses are inputs, not interval-certified completeness claims. All m in this experiment have L<16 and lie outside the asymptotic regime specified in the shrinking-kappa verdict.

For orthonormal Q spanning J and U spanning its complement, retain D=Q*AQ, B=U*AQ and G=U*AU. The full quiet residual is ||AQ||, not ||D||. At threshold C, S_C=G-CI-B(D-CI)^(-1)B* is used only when the eliminated block is separated from zero. The exact nonsingular-block inertia identity is

    N_A(C) = n_-(D-CI) + n_-(S_C).

Subtracting dim J from both sides does not replace n_-(D-CI) by dim J without its separate hypothesis. A singular eliminated block cannot be handled by an unqualified pseudoinverse.

In B, the section residual has fresh-coordinate norm one. Its reported sigma_section is f*Af, not f*Af/||f||^2. If the old block is indefinite, this stationary completion is not a minimizer: the unrestricted old-coordinate infimum is minus infinity. Both coordinate inertia ledgers are compared at the same threshold, separately at 0 and 2.

In C, lambda_r is the zero-based sorted eigenvalue at r=dim J, not an eigenvalue of G. An arbitrary interpolation complement is not the orthogonal complement of the actual first r eigenvectors. In particular lambda_r is not automatically a lower bound for G. Coupling and the full residual must remain in any analytic consumer. When lambda_r is negative, the signed ratio 2 sigma^2/lambda_r is merely an algebraic diagnostic and is not a positive capacity lower bound.

Float matrix radii and residual tolerances are diagnostic guards, not outward-rounded enclosures. MP source assembly, eigenvalue replays and sigma replays are consistency controls. The SOS audit in the separate first_step_log3_sos_audit folder has a different, analytic operator-certificate status. Its short-support bound does not automatically apply to a long section residual merely because the newly appended interval is short.
