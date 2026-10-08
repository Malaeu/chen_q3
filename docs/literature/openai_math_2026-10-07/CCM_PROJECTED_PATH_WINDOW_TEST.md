# Same-sign paths: finite Fourier projection is not the physical window

2026-10-08. Root calculation and independent read-only restricted_transport_cost audit PASS, including conjugation, constants, actual prime-power weight and scope. Own waiting test for Q7, not sent to Pro. Full N=m source, original Pi, no restricted-prime consumer switch. This tests exact path geometry only; it supplies no full moment estimate.

## Literal operators

Let H be multiplication by 1_[0,L] on L2(R), T_s f(t)=f(t-s), and F the original finite Fourier isometry with phi_j(t)=L^(-1/2)exp(i omega_j t)1_[0,L], j=-m,...,m, omega_j=2pi j/L. Put Pi=I-bb*, E=F Pi F*, and

    R_s=Pi F* T_s F Pi,    Pi Q(s)Pi=R_s+R_s*.

For s>L/2, the physical-window path H T_s H T_s H vanishes because two positive shifts exceed L. The actual finite projected path R_s² need not vanish: E is not H.

Define the evaluation vector psi(t)=Pi(exp(i omega_j t))_j/sqrt(L). Its periodicity is literal, psi(0)=0, and

    d=psi'(0)=(i omega_j/sqrt(L))_j,
    D=||d||²=4pi² m(m+1)(2m+1)/(3L³),
    Omega=max_j |omega_j|=2pi m/L.

The mean derivative vanishes because sum j=0. The exponential Taylor remainder and contraction by Pi give, for real t,

    ||psi(t)-t d||<=Omega t² sqrt(D)/2.                     (1)

All formulas use the unchanged basis and normalization.

## Explicit finite-projection leakage

Take s=L-epsilon with 0<epsilon<L/2. For t=L-r, the overlap integral is

    R_s=integral_0^epsilon conjugate(psi(-r))
                               psi(epsilon-r)^T dr.

The leading term is -(epsilon³/6)conjugate(d)d^T. Since d is purely imaginary, conjugate(d)d^T=d d*. Let u=d/sqrt(D), a=D epsilon³/6. Multiplying the two Taylor expansions from (1), and integrating their norm errors, gives

    R_s=-a u u*+J_s,
    ||J_s||<=D[Omega epsilon⁴/12+Omega² epsilon⁵/120]
             =a[Omega epsilon/2+(Omega epsilon)²/20].        (2)

Here integral r(epsilon-r)dr=epsilon³/6 and integral r²(epsilon-r)²dr=epsilon⁵/30. If Omega epsilon<=1/4, the bracket is <=41/320<1/6. Thus, without assuming R_s Hermitian,

    |u*R_s²u-a²|<=2a||J_s||+||J_s||²<=13a²/36,
    |u*R_s²u|>=23a²/36>0.                                 (3)

This proves that the exact finite Fourier/flat compression retains this path even though the physical-window-only path is zero.

## Actual prime-power subsequence and size

Choose original cells m=2^k+1 and the actual prime power n=m-1=2^k. Then s=log n, L=log m, epsilon=log(m/(m-1))<=1/(m-1), and s>L/2 for m>=3. For m>=2,

    Omega epsilon<=4pi/L.

Hence L>=16pi ensures every hypothesis of (2)–(3). The atom belongs to the actual Q5 long interval for every fixed p>=4, once its original domain m>=2^(p-1) is also met. Its Mangoldt weight is log(2)/sqrt(2^k), not log(n)/sqrt(n). This distinction is essential: n is a power of2, not a prime.

Along this subsequence a is asymptotic to (4pi²/9)L^(-3). The weighted path w_n² R_s² therefore has a nonzero tested matrix element of order 1/(m L^6), up to fixed constants, where w_n=log(2)/sqrt(m-1). This is small and summable on this subsequence. The result does NOT prove that a quantitative physical-window approximation is unaffordable. It proves that exact deletion without a return term is false. It also is not a lower bound for the full signed moment: other orientations, atoms and continuous terms remain.

## Q7 audit use

When reading Q7, distinguish E=F Pi F* from H at every intermediate step. A same-sign physical support argument alone does not delete R_s². A valid approximation must explicitly pay its finite Fourier projection return, together with all other paths. No extra Pro question is sent while Q7 is running.
