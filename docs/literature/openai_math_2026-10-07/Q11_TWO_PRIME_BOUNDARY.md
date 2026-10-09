# Two-prime actual boundary: keep the mixed correlation and its direction

2026-10-09. Independent read-only q05_moment_audit PASS for exact T1–T4,
convergence and consumer direction.
Same Q10(18) consumer; no gain or RH/SP claim. Not sent after rollover Q1.

Fix distinct active good prime ideals p,r outside R, with nonzero actual
psi_u values, delta=1/10, v=1_(N<=D0) M_u^[R](N;W).
Write c_p=psi_u(p)/sqrt(qp), c_r similarly, Q_jk=qp^j qr^k.
All coefficients, original masks and W are unchanged.

For N>D0 the exact pair tail is

 B_pr(N)=A_p A_r v(N)
   =sum_(j,k>=1, Q_jk>=N/D0) c_p^j c_r^k M_u^[R](N/Q_jk;W).  T1

Without this coupled cutoff, the sum is
 M_u^[Rpr](N)-M_u^[Rp](N)-M_u^[Rr](N)+M_u^[R](N).
Thus T1 equals that mixed-mask difference minus the lower-product terms
Q_jk<N/D0. It is not a single shell evaluation of M^[Rpr].

Let E_p and sigma_p=lambda_p/(1-lambda_p), lambda_p=qp^(delta-1),
be the shell energy and geometric coefficient in P3 of
Q10_ACTUAL_PRIME_BOUNDARY.md. The TWO-prime operator has exactly

 I_out,{p,r}=-sigma_p E_p-sigma_r E_r+C_pr,
 C_pr=integral_D0^infinity |B_pr(N)|^2 N^delta dN/N >=0.       T2

The full cross-term formula is

 C_pr=sum_(j,k,j2,k2>=1) c_p^j c_r^k conjugate(c_p^j2 c_r^k2)
   * integral_D0^(D0 min(Q_jk,Q_j2k2))
       M_u^[R](N/Q_jk) conjugate(M_u^[R](N/Q_j2k2))
       N^delta dN/N.                                       T3

No phases or cross terms are omitted. Weighted dilation norms give
sum_(j,k>=1) |c_p|^j |c_r|^k Q_jk^(delta/2)<infinity.
By Cauchy-Schwarz this justifies absolute summation of the integrated
cross terms for compactly truncated v. Zero-character branches vanish;
primes dividing R are absent, not inverted.

## The direction needed by the consumer

W5 returns window energy as full weighted energy MINUS I_out.
An upper bound for the window therefore needs a LOWER bound for I_out.
The exact positivity of C_pr gives only

 I_out,{p,r} >= -sigma_p E_p-sigma_r E_r.                    T4

Applying the accepted old moment to these two shell energies retains
its old exponent. No power improvement follows from T4.

For comparison, eta_p=qp^(-9/20)/(1-qp^(-9/20)) gives
C_pr<=eta_p^2 eta_r^2 ||v||_delta^2. This is an UPPER bound on C_pr
and hence an upper bound on I_out, the wrong direction for W5.
A sufficient condition for I_out<=0 is likewise not a sufficient
condition for the requested upper window estimate. It must not be
credited as progress toward Q10(18).

A useful stronger lower bound would have to show that the actual C_pr
compensates the singleton shell costs to the required precision, under
the original outer arithmetic weights. T3 exposes that correlation but
does not estimate it. The full finite-prime family additionally has
all higher subsets with alternating signs: even a two-prime bound
cannot be iterated without retaining those terms and their constants.
