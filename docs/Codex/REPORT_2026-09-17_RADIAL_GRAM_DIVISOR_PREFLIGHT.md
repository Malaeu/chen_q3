# Radial Gram divisor preflight for the original full V

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed Q1--Q8.
SOURCE_BASE: 8e63d0a557758bd61c307f5bfa9156194ecfea72.
Date: 2026-09-17. Original V sign and RH remain open.

## Q1. Exact question and inputs

Keep the complete normalized theta source f=Phi/A, A=||Phi||_2>0, and

    V(x,y)=int_0^infinity (2t+x+y) f(t+x)f(t+y) dt,
    G(x,y)=int_0^infinity f(sqrt(s+x^2))f(sqrt(s+y^2)) ds,
    I=(-log(2)/2,0),  S={z: |Im z|<pi/4}.

G is the already constructed positive radial Gram from FULL_V_RANK_TWO,
not a new normalization or a truncated source. On real pairs its entries
are positive, G(x,x)=V(x,x)>0. The accepted strict concavity of
log f(sqrt(s)) gives 0<V(x,y)<G(x,y) for x!=y. Thus

    R(x,y)=V(x,y)/G(x,y), R(x,x)=1, 0<R(x,y)<1 (x!=y).

R is PSD on every two-node family. The precise all-rank question is
whether R is PSD on every finite complex row in I. If it were, the Schur
product G R=V would give the desired original V positivity.

We prove that this PARTICULAR sufficient mechanism is false: R is not
PSD on any nonempty real open interval. This does not make V negative.

Named inputs, with independently accepted scopes:
- REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md R1--R8: G, diagonal match,
  entry comparison and two-node positivity.
- REPORT_2026-09-16_LOGVCURV_INTAKE.md I1--I3 and its unchanged raw
  PROSHKA_RESPONSE_GOAL058_LOGVCURV_2026-09-16.md LV2, LV12--LV18:
  full f is even, real, holomorphic on S; it has a nonreal zero z0 in S;
  the complete positive real tail and complex strip envelopes below.
- REPORT_2026-09-16_PAIRZERO_GEOMETRY.md P9: ordinary same-Hilbert
  feature continuation. Q3 below supplies the needed quotient extension;
  it does not apply an analytic-kernel theorem across unremoved poles.

No simplicity of the source zero, RH, all-rank positivity of V, global
zero-free complex product, or derivative of an asymptotic error is used.
The zeros below are spatial-source/kernel zeros, not zeros of xi.

## Q2. Holomorphic radial features, including the square-root branch points

For z in S define g_z(s)=f(sqrt(s+z^2)), s>=0. Both square-root choices
agree because f is even. If z=a+ib and sqrt(s+z^2)=u+iv, then

    v^2 = (sqrt((s+a^2-b^2)^2+4a^2b^2)-(s+a^2-b^2))/2 <= b^2.

Indeed the square root on the right is at most s+a^2+b^2: after squaring
the difference is 4 s b^2>=0. Thus each root stays inside S. Away from
s+z^2=0 local holomorphic square-root branches give holomorphic g_z(s).
At a branch point the even Taylor series of f at zero expresses it as a
convergent power series in s+z^2. This removes the apparent singularity.

On every compact Q contained in S, as s->infinity the root with positive
real part is sqrt(s)+O_Q(s^(-1/2)). The full-source bound LV2 therefore
gives a common integrable envelope of the form

    |g_z(s)| <= C_Q exp(C_Q sqrt(s)-c_Q exp(2 sqrt(s))), c_Q>0

for large s; a finite common bound covers the remaining s interval.
Consequently z->g_z is holomorphic with values in L^2([0,infinity),ds),
and G(z,w)=int g_z(s)g_w(s)ds is holomorphic on S x S. In particular

    G(conj(z),z)=int |g_z(s)|^2 ds >0.                  (Q2)

For strictness, zero norm would make the continuous g_z zero for all s.
Taking s on a large finite open interval gives an accumulating curve of
zeros of the nonzero holomorphic f inside S, a contradiction.

## Q3. Necessary zero divisibility for a positive quotient

Lemma. Let N,D be holomorphic on a conjugation-stable simply connected
complex domain S x S, with real symmetric kernels on real pairs and
Hermitian polarization. Suppose D(conj(z),z)>0 for every z in S.
If N/D is PSD on all finite complex rows of a real open interval where
it is defined, then a global holomorphic Gram kernel H exists with

    D(z,w)H(z,w)=N(z,w) throughout S x S.              (Q3)

Hence every pair zero of D is a zero of N, with the required divisibility.
No global holomorphy of N/D is a premise.

Proof. Near a real diagonal point p, D is nonzero on a product disk.
PSD and real finite differences make all finite mixed Taylor matrices
of N/D there PSD. Their compatible Gram realization gives vectors v_j
in one Hilbert space. A Cauchy bound |N/D|<=M on a product disk of radius
rho gives ||v_j||<=sqrt(M)rho^(-j). Thus F(z)=sum v_j(z-p)^j is a
holomorphic feature near p, and ||F(z)||^2=N(conj(z),z)/D(conj(z),z).

The latter quotient g(z) is real analytic and finite on all S because
its denominator never vanishes on the Hermitian diagonal. At a point
p reached by F, uniqueness of local polarization and Cauchy's bound give

    ||F^(j)(p)/j!||^2
      = partial_1^j partial_2^j(N/D)(conj(p),p)/(j!)^2
      <= M rho^(-2j).

Here rho,M come from a local product disk about (conj(p),p), not from
a distant off-diagonal quotient. The SAME Hilbert-valued Taylor series
therefore extends F to the radius-rho disk, preserving its norm identity
by the full double Taylor series. On any compact path the Hermitian
diagonal graph is compact; D is bounded away from zero there. Common
rho,M on a neighborhood of that graph let finite overlapping disk chains
continue F along the path. All continuations stay in the same Hilbert
space. Hilbert-valued monodromy on simply connected S follows by the
usual disk-chain power-series argument (or bounded scalar functionals).
It makes F single-valued globally.

Finally H(z,w)=<F(conj(z)),F(w)> is jointly holomorphic and agrees with
N/D on the initial product disk. The holomorphic identity DH=N extends
from that disk to the connected S x S. Only at this final step are all
possible off-diagonal quotient poles proved removable. No positivity
on new real nodes, nor positivity of g away from the initial disk, was
assumed: it is forced by the continuation if the PSD premise holds.

## Q4. Exact full-source localization scale and majorants

Write, exactly for real t>=1,

    r(t)=4 pi^2 t exp(-pi t) H(t),
    H(t)=1-3/(2 pi t)+R_full(t),
    0<=R_full(t)<=C_* exp(-3 pi t),
    0<h_-=1-3/(2pi)<=H(t)<=1+C_*, H(t)->1.

These are full n>=2 tail bounds from LV18, not a one-mode source.
Since f(x)=A^(-1) exp(5x/2) r(exp(2x)), for every x>=0 and Delta>=0,

    f(x+Delta)/f(x)
     = exp(9 Delta/2-pi exp(2x)(exp(2Delta)-1))
       *H(exp(2x+2Delta))/H(exp(2x)).                  (Q4)

Set lambda=2 pi exp(2x), epsilon=x/lambda, x->+infinity.
No logarithmic-derivative asymptotic is required. For fixed v>=0,

    f(x+v/lambda)/f(x) -> exp(-v),
    f(sqrt(x^2+2 epsilon v))/f(x) -> exp(-v).          (Q5)

Both ratios are at most C exp(-v/2) for all v>=0 and all sufficiently
large x, C=(1+C_*)/h_-.
For the first bound exp(2Delta)-1>=2Delta with Delta=v/lambda suffices.
For the second let Delta=sqrt(x^2+2epsilon v)-x. If x>=1/2, then

    exp(2Delta)-1 >= 2Delta+2Delta^2
                    >= 2Delta+Delta^2/x = 2v/lambda,
    Delta <= v/lambda.

The exponent in Q4 is therefore <=-v+9v/(2lambda)<=-v/2 when lambda>=9.
For fixed v, lambda Delta->v, yielding the second limit in Q5. This
supplies a global full-integral majorant without differentiating H.

## Q5. The Gram and V transport one source zero at different scales

Choose the accepted nonreal zero z0 of f in S. It is nonzero and has
some finite order m>=1. Write a_m=f^(m)(z0)/m! !=0. For w in any fixed
compact subset of C, put z=z0+epsilon w. We claim the locally uniform
limits

    G(x,z0+epsilon w)/(2 epsilon f(x) a_m epsilon^m)
       -> P_m(w):=int_0^infinity exp(-v)(w+v/z0)^m dv, (Q6)

    V(x,z0+epsilon w)/((x+z0)f(x)a_m epsilon^m/lambda)
       -> w^m.                                      (Q7)

For Q6 set s=2epsilon v in the original full G. Its first factor,
divided by f(x), converges to exp(-v) with the bound Q5. Choose a small
fixed delta>0 so that the local square root of z^2+s near (z0,0) has
value z0 at s=0. For bounded v,w,

    sqrt((z0+epsilon w)^2+2epsilon v)
      = z0+epsilon(w+v/z0)+O(epsilon^2),

uniformly on those bounded sets. The zero-order Taylor factorization
of f then gives the pointwise limit (w+v/z0)^m after dividing by
 a_m epsilon^m. On 0<=s<=delta, |w|<=R, for small epsilon the same local
branch and factorization yield

    |f(sqrt((z0+epsilon w)^2+s))| <= C_R(epsilon R+s)^m.

Consequently the normalized integrand is bounded by
C_R exp(-v/2)(R+2v)^m on this growing v interval. On s>=delta the
features g_z(s) are uniformly bounded for z in a compact disk in S
by Q2; its normalized tail is bounded by

    C_R epsilon^(-m) int_(delta/(2epsilon))^infinity exp(-v/2)dv ->0.

This proves Q6 uniformly on |w|<=R, paying the small denominator rather
than applying dominated convergence to an unbounded quotient.

For Q7 set t=v/lambda in the original full V. Its normalized integrand is

    [(x+z0+epsilon w+2v/lambda)/(x+z0)]
    [f(x+v/lambda)/f(x)]
    [f(z0+epsilon w+v/lambda)/(a_m epsilon^m)].

The three factors tend to 1, exp(-v), and w^m: here
(v/lambda)/epsilon=v/x->0. On 0<=t<=delta the last factor is bounded
by C_R(R+v/x)^m<=C_R(R+v)^m for x>=1. The weight is bounded by C_R(1+v).
The middle factor has the global Q5 envelope. On t>=delta the complex
strip bound LV2 gives a uniform bound for f(z+t), and the normalized
tail is at most

    C_R epsilon^(-m) int_(delta lambda)^infinity (1+v)exp(-v/2)dv ->0.

Thus Q7 is also locally uniform, with the whole linear weight and t=0
boundary retained. Multiplicity m is arbitrary and fixed.

## Q6. Actual unmatched complex zero and all-rank obstruction

P_m is a monic degree-m polynomial:

    P_m(w)=sum_(k=0)^m binom(m,k) k! w^(m-k)/z0^k,
    P_m(0)=m!/z0^m !=0.

It has at least one root w*, and no root is zero. Choose a small closed
disk B around a root, avoiding zero and with P_m nonzero on its boundary.
For all sufficiently large finite x, Q6 and Rouche give a zero w_x in B
of the full G(x,z0+epsilon w). Q7 and the strictly positive minimum of
|w^m| on B show that the full V has no zero there. Therefore

    G(x,z_x)=0, V(x,z_x)!=0, x in R, z_x in S.        (Q8)

This is exact analytic existence for the full source. No numerical zero
location or effective threshold x is asserted.

If R were PSD on any real open interval J, Q2 and Q3 with N=V,D=G
would imply GH=V throughout S x S, contradicting Q8. Hence R is not
PSD on any such J, including the original I. It follows that a finite
real coefficient row in J has negative R energy. Real coefficients
suffice since R is real symmetric; a complex negative vector splits
into its real and imaginary parts. No rank bound or explicit node list
is supplied. Two-node positivity of R shows that after merging repeated
nodes such a row needs at least three distinct nodes.

## Q7. Scope: no positive tensor repair of this exact radial Gram

Even allowing arbitrary nonzero node factors eta(x) and a PSD kernel M,
there is no identity on I

    V(x,y)=conj(eta(x))eta(y)G(x,y)M(x,y).

Dividing the positive real G entries would make R a diagonal congruence
of M, hence PSD, contrary to Q6. No analyticity of eta or M is assumed.
This rules out exact tensor/multiplicative repairs of this specified G.
It does not rule out different Gram features, nonlocal changes mixing
signals, sums/differences with controlled signs, or positivity of V.

## Q8. Decision and arithmetic use

The rank-two entry estimate remains correct, but cannot be upgraded to
all-rank positivity by this positive Schur multiplier. No lower bound
for original V has improved and no negative original-V witness has been
obtained. Full V positivity and RH remain open; no Lean or canonical
admission is claimed. This is an analytic route exclusion only.

The exact square rates enter through the already verified full theta
source zero (periodicity/parity plus Jacobi reciprocity) and the complete
real tail. No new property of prime factorization is asserted. A future
positive energy representation must reproduce V's interaction and pair
zero geometry; positivity of a nearby kernel and entrywise comparison
alone do not transfer the sign.

Search coverage is incomplete: the registered mgrep provider last failed
with expired JWT/login required. This proof uses directly read named
inputs and local analysis only, not an assertion that no published
analogue or previous project result exists. No search repair or external
premise was introduced. No new Proshka proof request is dispatched here.

## Independent acceptance

Candidate SHA256: `5ad591b682967eed85ada4f667c77dbbe624fca66a4644a905f52b5075229bce`.
Full review SHA256: `b64401d2bf77a7b414ef1df44ab2f0aed878f0542443e2ff694247ce3b9b27a4`.
Verdict: `ACCEPT_RADIAL_GRAM_QUOTIENT_OBSTRUCTION_ONLY`.
The quotient-continuation lemma was also separately accepted under
`ACCEPT_CONDITIONAL_PSD_QUOTIENT_POLE_REMOVAL_LEMMA`, review SHA256
`a0757c728d2ffd5ba03b1c2b6a6f739c3a63b80e18df4641b293e9475b631f4a`. Both complete reviews are embedded in the paired
certificate. The parent independently checked the square-root strip map,
the exact full-source global exponential majorants, both small-scale
zero-order limits and their tail budgets, Rouche separation, and the
conditional same-Hilbert continuation. No rank bound or original-V
negative witness is supplied. Original V positivity and RH remain open.
