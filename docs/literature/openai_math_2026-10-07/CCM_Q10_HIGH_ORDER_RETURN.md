# Post-Q09 attempt3: higher-order smoothing must pay the original endpoint

2026-10-21. Original full CCM, fixed epsilon, N=m,L=log m,
M=R=floor(m^epsilon), original P. Root calculation; q10_higher_smoothing bounded PAPER review PASS for
the interior repair and endpoint discriminator, not a full-source bound.
No new unconditional arithmetic gain. This tests an actual repair of the
first-order return, not a change of source or a numerical experiment.

## Exact interior repair

For a smooth compactly supported matrix weight w on [X,2X], away from the
original endpoint m, define
 A_h w(t)=h^(-1) integral_(t-h)^t w(x) dx,
 B_(k,h)w=sum_(j=1)^k alpha_j A_(jh)w,
 alpha_j=(-1)^(j+1) binom(k,j).
Fix the integer k before m grows; assume kh<=X. Finite differences give
sum alpha_j=1 and sum alpha_j j^r=0 for 1<=r<k. Taylor's integral remainder
therefore gives
 ||w-B_(k,h)w||_infinity <= C_k h^k ||w^(k)||_infinity.
The kernel is signed; positivity of the averaging operator is NOT used.

For E=psi-(x-1), Fubini gives exactly
 integral B_(k,h)w dE
 =sum_j alpha_j/(jh) integral w(x)[E(x+jh)-E(x)] dx.
All over-cutoff atoms are part of this identity, not silently discarded.
For ||w||<=C X^(-1/2), Cauchy gives
 ||integral B_(k,h)w dE|| <=C sum_j |alpha_j| sqrt(J_(jh)(X))/(jh).
No independence of primes or coefficients is assumed. All matrix mixed
terms survive because the estimates are operator-norm bounds.

On an ordinary smooth interior dyadic weight, direct differentiation of
the finite Fourier overlap gives
 ||w^(k)||<=C_k X^(-k-1/2)(1+Omega)^k.
Boundary differentiation of that overlap costs at most (2M+1)/L times
Omega^(k-1), absorbed into C_k(1+Omega)^k for L>=1. This statement does
not apply across the zero-extension edge x=m. Total mass dpsi+dx on an
O(X) interval is O(X), so the interior reconstruction costs
 C_k sqrt(X)[h(1+Omega)/X]^k.

Granting, only hypothetically, J_(jh)(X)<=C_k jh X log²(2X) for every
j=1,...,k and all required blocks, the complete INTERIOR budget is
 C_k [sqrt(X/h)log(2X)+sqrt(X)(h(1+Omega)/X)^k].
Its power-optimal h is X^(2k/(2k+1))(1+Omega)^(-2k/(2k+1)), and its price
 X^(1/(4k+2))(1+Omega)^(k/(2k+1)), up to logarithms.
Thus the interior formal exponent can tend to zero if k=k(epsilon) grows
as epsilon tends to zero, while remaining fixed for each epsilon. Constants
C_k may depend on k. This does not supply the hypothetical arithmetic input.
A mere J_(jh)<=C_A(jh)^2 X/log^A X still leaves sqrt(X)/log^(A/2) X in
this bound: order cancellation alone does not improve that input.

## Exact source discriminator at m

The existing admissible sine vector in CCM_Q03_ONE_SIDED_PRIMITIVE_CONE_TEST.md
satisfies all three original constraints and f'(0)=-3(2pi/L)^3 !=0.
Its literal overlap has q(L-u)=-|f'(0)|² u³/3+O_L(u^4).
For H_c(x)=q(log x)/sqrt(x), this means, as z=m-x tends to zero,
 H_c(m-z)=-|f'(0)|² z³/(3m^(7/2))+O_m(z^4).
The zero extension is C² but its third derivative has a nonzero jump.
Consequently it is not C³, and a global fourth-order Taylor remainder
cannot be claimed. Additional original contacts do not remove this vector.
This is a geometric obstruction to the uncorrected transfer, not a lower
bound for actual CCM or a proof that all smoothing mechanisms fail.

A smooth cutoff or a jet correction needs its own quantitative return.
CCM_Q06_ONE_SIDED_EDGE_BUDGET.md already pays the full thin prime shell
with power1/2+5epsilon-6kappa when its logarithmic width is m^(-kappa).
That shell estimate does not pay derivatives of a replacement cutoff, nor
the continuous term removed with it. The full continuous integral equals
-P H_decay P only BEFORE deleting any part. Its signed shell must return.
The fifth-order positive null direction in CCM_Q03_ENDPOINT_SIGN_TEST.md
also prohibits throwing away the entire endpoint on the cubic sign alone.

## Decision

The higher-order interior repair is real and conditional. Its extrapolation
to the full source is unpaid at the cutoff, and its strong arithmetic
variance is not supplied. No global subpower estimate is established.
After three distinct post-Q09 tests (second moment, first-order variance
return, higher-order endpoint repair), escalate this concrete remaining
bridge to the same living Proshka chat; do not repeat global scalar caps.
AUTOPSY: dropped=NO_DERIVATION; note=Higher-order interior cancellation does not supply the arithmetic variance or the original endpoint return.

## Candidate for Q10, NOT an accepted bridge

The reviewer suggested geometrically spaced shells at distance d from m.
For a bump supported on length O(d), a crude ||w||_2<=C sqrt(d/m) combines
with a global dyadic variance bound to give sqrt(d/h), not sqrt(m/h).
Taking h approximately min(d,m/(1+Omega))*m^(-gamma) could therefore let
high-order reconstruction pay its derivatives without the one-block loss.
All cutoffs, overlap, small d, atoms, and the continuous main need checking.
For the final thin shell, the elementary absolute overlap bound is
 |q(L-u)|<=((2M+1)/L)Omega² u³/3,
from |f(t)|<=||f'||_infinity |t| near either endpoint. Integrating its
continuous shell gives O(sqrt(m)((2M+1)/L)Omega² delta^4).
At delta=m^(-1/8-epsilon) this is O(m^(-epsilon)) up to logs;
Q06's discrete one-sided shell fee is then O(m^(-1/4-epsilon)) up to logs.
These ingredients suggest a conditional cutoff repair; they have NOT been
assembled or independently audited as a full operator bound. The strong
short-interval variance remains unproved even if this repair succeeds.
Q10 should test this explicit scheme and its exact arithmetic input.
