# Positive transport cost versus collective quadrature on the actual CCM kernel

2026-10-08. Root calculation and independent read-only restricted_transport_cost audit PASS, with the exact mass-balance repair below incorporated. This is a method discriminator on the literal full N=m kernel, not a prime spectral estimate or a replacement of Lambda by one. RH/SP remain OPEN. Q6 processed; no Q7 sent.

## Exact target and envelope

Keep L=log m, d=2m+1 and the original Q(s) of CCM_PRIME_TRANSITION_TEST.md. Let P be the actual codimension-at-most-three projection in CCM_RESTRICTED_PRIME_RECEIVER.md, and put F(u)=P Q(log u)P/sqrt(u), 1<=u<=m. The already checked derivative estimate gives

    ||F(u)-F(v)|| <= c_m(u,v),
    c_m(u,v)=min(2/sqrt(u)+2/sqrt(v),
                   (1+D_m)|u-v|/min(u,v)^(3/2)),
    D_m=(2+8pi m)/L.                                         (1)

The minimum retains both the separate norm envelope and the derivative envelope. It is an UPPER bound on actual matrix distance. A lower bound for its total cost is not a lower bound for the matrix difference.

## 1. The positive-envelope payment cannot be polylogarithmic

Let m>=8 be integer. Consider ANY positive transport measure gamma on [ceil(m/2),m] times {1,...,m} whose first marginal is Lebesgue du on that interval. No condition on its integer target masses is needed. This relaxed class includes more destinations than prime powers; exact prime marginal mass balance is not asserted.

Since u,v<=m, the first entry of the minimum is >=4/sqrt(m). The second is >=(1+D_m)dist(u,Z)/m^(3/2). Both are >=dist(u,Z)/(sqrt(m)L): for the first use dist<=1/2 and L>=log8, and for the second use (1+D_m)/m>=1/L. Therefore

    integral c_m dgamma >= 1/(sqrt(m)L)
                            integral_ceil(m/2)^m dist(u,Z)du
                         = floor(m/2)/(4sqrt(m)L)
                         >= sqrt(m)/(16L).                    (2)

The last deliberately loose constant uses floor(m/2)>=m/4. Thus no choice of positive matching to integer locations makes THIS envelope payment polylogarithmic. A power-sized charge fed into T8 would give a moment exponent depending on the order, not the required common exponent.

For a nonnegative fixed smooth chi supported inside (1/2,1), positive on an interval [a,b] with chi>=c0>0, the same argument applies to first marginal chi(u/m)du. For m>=4/(b-a), there are at least (b-a)m/2 complete integer cells within [am,bm], giving cost >=c0(b-a)sqrt(m)/(8L). This statement still concerns only the envelope (1), not actual operator distances.

## 2. Collective signed quadrature has a much smaller error

Fix any chi in C_c^infinity((1/2,1)), independent of m, and form the UNWEIGHTED integer baseline

    E_m=sum_n chi(n/m)Q(log n)/sqrt(n)
            -integral chi(u/m)Q(log u)/sqrt(u)du.              (3)

Only integers in the original upper block occur. This is not the prime source: Lambda(n) has deliberately been replaced by one for a diagnostic comparison of proof methods. For every fixed R>0 there is C_(chi,R) with

    ||E_m|| <= C_(chi,R) m^(-R)                               (4)

for integer m with L>=8. Orthogonal compression by the actual P preserves this upper bound.

Here is a uniform proof, including the growing Fourier band. Each Q entry is a linear combination of exponentials exp(+-i omega_j log u), |omega_j|<=2pi m/L. Offdiagonal coefficients have magnitude <=1/pi because |j-k|>=1. Diagonal entries carry 2(1-log(u)/L); after u=my this is -2log(y)/L. Thus it is enough to estimate scalar sum-integral discrepancies with amplitudes chi(y)y^(-1/2) or that amplitude times log(y)/L. Their fixed derivative norms are uniform for L>=8.

Poisson summation after u=my expresses the scalar discrepancy as the sum over nonzero integers h of

    m^(1/2) exp(i omega log m)
       integral a_L(y) exp(i m phi_(xi,h)(y))dy,
    xi=omega/m, phi_(xi,h)(y)=xi log y-2pi h y.                 (5)

On the compact support, |xi/y|<=4pi/L<=pi/2, so

    |phi'|>=2pi|h|-pi/2 >=(3pi/2)|h|.

All higher derivatives of phi are uniformly bounded, while every fixed derivative of 1/phi' is O_n(1/|h|). Repeated integration by parts with (i m phi')^(-1) d/dy has no boundary terms. After J integrations each integral in (5) is bounded by C_(chi,J) m^(-J)|h|^(-J). Choose J>=2 to sum over h. Every matrix entry of E_m is consequently O_(chi,J)(m^(1/2-J)), uniformly in both indices. The row-sum bound gives

    ||E_m|| <=d max_jk |(E_m)_jk|
             <= C_(chi,J) m^(3/2-J).                         (6)

Choosing fixed J>R+3/2 proves (4). The order is chosen before m grows. This uses the literal diagonal/offdiagonal formula, not a false commutation of window projections with translations.

## Exact mass balance for the positive comparison

For a nonzero nonnegative chi, the continuous mass is M_c=m integral chi and the discrete mass is M_d=sum_n chi(n/m). They need not be exactly equal. The same scalar Poisson proof at omega=0 gives M_d-M_c=O_(chi,J)(m^(1-J)) for every fixed J. Eventually M_d>0. Reweight the integer endpoint by the positive scalar alpha=M_c/M_d. Then alpha-1=O_(chi,J)(m^(-J)), the masses agree exactly, and changing the matrix endpoint costs at most |alpha-1| sum_n 2chi(n/m)/sqrt(n)=O_(chi,J)(m^(1/2-J)). Thus the superpolynomial quadrature conclusion survives exact mass balance. A positive coupling now exists, for example the normalized product of the two marginal measures, and every such coupling still has the lower envelope charge. No prime-mass normalization is used or asserted.

## Consequence and precise next entrance

The same smooth upper-block baseline has unavoidable power-sized positive envelope charge but a superpolynomially small collective signed matrix error. Therefore a failure of (1)-based transport payment does not show that accurate source transport is impossible. The missing information is cancellation before taking norms.

For the actual source the remaining upper-block term is exactly

    sum_n (Lambda(n)-1)chi(n/m)Q(log n)/sqrt(n),                (7)

plus the already small error (3) when compared with the corresponding continuum block. Neither Poisson calculation above nor integer spacing bounds (7). Lower blocks, the full prime source, the projection and its endpoint returns are still required. A useful matching/alias supplier must estimate the actual signed weighted block collectively or provide a better source-specific metric; iterating the positive T6 envelope cannot supply the desired common exponent.

This is one bounded method test within the current full-source investigation. It does not activate a new Pro phase or assert a full restricted prime upper bound.

## Bounded shelf return

Three structural queries through ask.sh --defer-external: prime Dirichlet polynomial uniform frequency window; signed quadrature Wasserstein oscillatory kernel; nonstationary phase prime exponential sum. Each returned ASK_STATUS INCOMPLETE because q3_docs semantic freshness failed. The literal candidates include existing shifted-rank-one and signed-kernel identities, not an admitted estimate of (7). This is not evidence of literature absence. No external theorem is imported: the method control above has its complete Poisson/IBP proof here. The next supplier must retain Lambda, joint frequency dependence and the actual compressed spectral consumer; weight-one quadrature cannot be substituted.

AUTOPSY: dropped=THEOREM_SHAPE; note=positive T6 envelope transport incurs at least sqrt(m)/log(m) even for a baseline with superpolynomial collective quadrature error.
