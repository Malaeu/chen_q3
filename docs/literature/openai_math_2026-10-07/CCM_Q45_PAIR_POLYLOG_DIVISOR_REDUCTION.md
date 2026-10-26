# While Q45 runs: polylogarithmic second index for the actual pair

2026-10-26. Root derivation; bounded conditional PAPER PASS after independent
q44_bounded_audit review of A1–A6. No new all-P bound or RH claim.
Sources: Q18 verdict(1.3) exact Phi; Q17 actual g,k, zero moments, separate
normalizations and receiver; Q19 M_C; CCM_Q45_PAIR_SHORT_DIVISOR_QUADRATURE.md.
This uses quantitative analyticity, not an unsupported growing-order use of
fixed-derivative constants. No extra message to the live Q45 chat.

## Fixed strip of the actual source

The exact source is Phi(z)=sum_(j>=1)(4pi²j⁴ exp(9z/2)-6pi j² exp(5z/2))
exp(-pi j² exp(2z)), G=-4Phi, F0=(partial²-1/4)G. On every closed strip
|Im z|<=a<pi/4 this series and each FIXED derivative converge normally on
compact sets. For Re z>=0, cos(2Im z)>=cos(2a)>0 gives a bound
C_a exp(-c_a exp(2Re z)), after absorbing the polynomial-exponential factor.
Inherited real evenness and the identity theorem extend this bound to Re z<=0.
A slightly wider closed strip first gives the same two-sided bound for F0.

For each fixed actual w and its partner v, the r-fold horizontal inverse
integral defining g,k is holomorphic in the same open strip. The vanishing
moments int s^j exp(ws)F0(s)ds, j<r (and similarly v), persist on horizontal
lines by contour rectangles whose vertical edges vanish by these strip tails.
They let one use the left integral at Re z<0 and the right integral at Re z>0.
Consequently |g(x+it)|+|k(x+it)|<=C_(w,a)exp(-c_(w,a)exp(2|x|))
on any narrower closed strip. Both separate nonzero normalizers are included
in C_(w,a); no uniformity as w varies is asserted.

Thus C(z)=int_R conjugate(g(t))k(t+z)dt is holomorphic in a fixed strip and
 |C(x+it)|<=C_w exp(-c_w exp(|x|)), |t|<=a0,                (A1)
for some fixed a0>0. Dominated holomorphic integration is justified by the
same tails; the inequality exp(2|t|)+exp(2|t+x|)>=2exp(|x|) pays the x-tail.

## Uniform derivative budget, including growing orders

For t>0 define A0(t)=t^(-1/2)C(-log t), A1(t)=log(t)A0(t).
These are analytic in a fixed sector about the positive axis. In a disk of
radius theta*t, fixed small theta>0, (A1) bounds their moduli by
 C t^(-1/2)(1+|log t|)exp[-c(t+1/t)].
Cauchy's formula and integration over t>0 imply for every integer q>=1
 ||A0^(q)||_1+||A1^(q)||_1 <= C0^(q+1)(q!)².               (A2)
Indeed Cauchy contributes q! theta^(-q)t^(-q); splitting the resulting
integral at1 and substituting u=1/t on(0,1) bounds it by C1^(q+1)q!.
The logarithm contributes only a factor absorbable into C1^q. This proves
uniformity in q, rather than assuming it from the old fixed-order receiver.
Both functions and all derivatives vanish at0 and infinity.

## Whole smooth k-sum and finite original cutoff

Keep L=log m, y=L-2log L and original R=floor(m^epsilon),P unchanged.
Choose only an auxiliary D=floor(m/L^6), eventually >=R. For d<=D put
K_d=exp(y)/d and
 f_d(t)=log(t)/sqrt(dt) C(y-log(dt))
       =exp(-y/2)[log(K_d) A0(t/K_d)+A1(t/K_d)].
Here L^4<=K_d<=exp(y), so |log K_d|<=L eventually. From (A2),
 int_0^infty|f_d^(q)(t)|dt
 <= C0^(q+1)(q!)² L exp(-y/2) K_d^(1-q).                 (A3)

The whole continuous integral is EXACTLY zero:
 int_0^infty f_d(t)dt=exp(y/2)/d
   [(y-log d) M_C(-1/2)-M'_C(-1/2)]=0.
Both contacts are those of the actual complex C, not a positive surrogate.
All endpoint derivatives vanish at0 and infinity. For even q>=2,
Euler–Maclaurin with the bounded periodic Bernoulli remainder yields
 |sum_(k>=1) f_d(k)| <= [2zeta(q)/(2pi)^q] int|f_d^(q)|.
The infinite k-sum here is absolutely convergent by C tails. This is not
an infinite prime/forcing-inverse interchange; it is the already formed C.

Sum over d<=D using |mu(d)|<=1 and sum d^(q-1)<=D^q. With an enlarged
fixed constant C2,
 |sum_(d<=D)mu(d)sum_(k>=1)f_d(k)|
 <= C2 L exp(y/2)[C2 q² D/exp(y)]^q.                     (A4)
Choose an even integer q=2floor(c0 L²/2), with fixed c0>0 sufficiently small
that C2 c0²<=1/4. For large m, q>=2 and the bracket is <=1/4 since
D/exp(y)<=L^-4. Hence (A4)<=C_w sqrt(m)exp(-c_w L²)=o(1).
The source and original-P receiver remain fixed; only a now UNIFORMLY
controlled quadrature order grows with m.

Return the entire removed k>m/d tail explicitly. In log-product blocks
[L+j,L+j+1], their coefficient mass for each d is at most
C (sqrt(m)exp(j/2)/d+exp(-(L+j)/2))(L+j+1).
Since |y-log(dk)|>=2log L+j, summing the C-tail and then d<=D costs
C_w sqrt(m)L² exp(-c_w L²)=o(1). This includes the fractional final cell and
all integer product edges. The reverse-time ORIGINAL contribution is bounded
by C_w sqrt(m)L² exp(-c_w m/L²)=o(1), because dk>=1 and y+log(dk)>=y.
It was not extended to an integral through t=0 or silently discarded.

Therefore the complete actual cross-term prefix obeys
 |sum_(d<=D)mu(d)/sqrt(d)sum_(k<=m/d)log(k)/sqrt(k)
     [C(y-log(dk))+C(y+log(dk))]|=o(1).                   (A5)

## Exact remaining source and full return

For d>D, dk<=m implies k<=floor(m/(D+1))<L^6. Thus
 J(h;m)=sum_(k<L^6)log(k)/sqrt(k)
          sum_(D<d<=m/k)mu(d)/sqrt(d)
            [C(y-log(dk))+C(y+log(dk))]+o(1),            (A6)
where an empty inner range is zero. All mixed phases remain; no prime powers
were deleted from the exact mu*log identity. D is auxiliary, not production R.
Return this scalar cross term BEFORE original-m projection. The additional
mixed fee is twice (A5), plus the inherited rho_K+rho_S=o(1) once. Original
full self terms stay O_w(1) and archimedean O_w(L) is paid once. No separate
short-sector operator norm is claimed on all P.

An independent directed estimate for the long-mu sum in (A6) remains unpaid.
Polylogarithmically many k-values do not imply cancellation of their long d
sums. The inherited endpoint and all-P fallback exponents are unchanged.
This candidate reduction must not be called a new full CCM degree or RH proof.


## Audit and completion budget

Independent q44_bounded_audit checked A1–A6 at pre-header-update SHA256
 e872807bad092b7dd6bc3e03e81186f0c6cf9f17e592360b6d8ad4301a8b8f6a:
no material findings. Separate q45_primitive_screen check established A1 from
the exact Q18 theta source and actual resolvents. Inherited source identities
and original receiver remain dependencies; no whole-chain recertification.
No executable tests, Lean, Arb or full CCM spectrum runs performed.

The already checked Stieltjes transfer S8 in the companion short-divisor note
applies with k<L^6 and this D. A HYPOTHETICAL |M(t)|<=K t^beta would give
 |J_long|<=C_(w,beta)K exp((beta-1/2)y)
                         sum_(k<L^6)log(k)/k^beta+o(1).
For fixed1/2<=beta<1 its price is
 O_(w,beta)(K m^(beta-1/2)L^(7-8beta)log L)+o(1).
A strict beta-1/2<delta would suffice for o(X). Such an improved Mertens
premise is NOT supplied. The trivial beta=1 gives only
O_w(sqrt(m)(log L)^2/L), worse than the retained endpoint sqrt(m)/L price.
Polylogarithmic support removes the prior short-index POWER cost; it does
not establish the missing signed arithmetic estimate. Original all-P goal OPEN.


## Literal all-P transfer check

2026-10-26. Root check with independent read-only q45_all_p_transfer_screen.
The original sparse P imposes endpoint zero and two Laplace contacts on the
zero-extended Fourier synthesis f on [0,L]. For its autocorrelation C_f,
M_Cf(z)=conjugate(M_f(-conjugate(z))) M_f(z), so the two contacts do give
double zeros at +/-1/2. These cancellations are not exclusive to the pair.
However C_f is supported in [-L,L] and C_f(0)=1 for a unit vector. A
holomorphic extension to a strip containing the real axis would vanish on
(L,infinity), hence identically, a contradiction. Therefore A1 cannot be
transferred literally to all unit vectors of P; A2 and the growing-order
quadrature argument require a different uniformly paid extension/edge estimate.
Sources: CCM_SPARSE_BAND_RECEIVER.md, CCM_CONTINUOUS_RANK_TWO_TEST.md and
CCM_Q09_AUTOCORRELATION_PREFLIGHT.md. This is only a limitation of this proof
transfer, not a lower bound for the original operator or a new no-go. The
pair reduction and the open all-P objective are unchanged. No Proshka send.
