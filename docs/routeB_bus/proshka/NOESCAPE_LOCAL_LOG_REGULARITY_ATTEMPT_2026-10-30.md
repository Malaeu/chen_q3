# Local logarithmic regularity: exact source ledger after GREEN

Status: own conditional source calculation; uniform bound and local mass OPEN.
Original full real-even CCM source, N=m, L=log m, unit exact bottom f,
lambda=k[f]. No modification of prime weights, poles or carrier.
This tests the regularity side of GREEN (9.1), not its still-unproved mass.

## Archimedean energy controls the required logarithmic norm

For zero-extended z let

    H[z]=integral_0^infinity j(s)||z-T_s z||² ds,
    a(t)=2 integral_0^infinity j(s)(1-cos(ts)) ds.

Plancherel gives H[z]=(1/2pi) integral a(t)|hat z(t)|² dt.
For 0<s<=1, j(s)>=exp(-1/2)/(2s). If T=|t|>=1,

    a(t)>=exp(-1/2) integral_0^T (1-cos v)/v dv
         >=exp(-1/2)(log T-2).

The last estimate follows by integration by parts:
|integral_1^T cos(v)/v dv|<=2. For T<1 use a>=0. Thus for all real t,

    log(2+|t|)<=exp(1/2)a(t)+2+log3.                  (L1)

No asymptotic digamma estimate or unproved spectral assumption is used.

Choose fixed even 0<=chi<=1, smooth, supported on [-R,R], and m so large
that this support lies inside the original window. Put z=chi f.
The source restricted to z has prime correlations only for log n<2R.
The endpoint log n=2R has zero correlation in the integral sense.
Evenness makes the odd pole vanish; the positive even pole is retained:

    k[z]=H[z]-c_*||z||²-sum c_n Q_zz(log n)+|<p,z>|².

Since |Q_zz|<=2||z||²,

    H[z]<=k[z]+K_R||z||²,
    K_R=c_*+2 sum_{2<=n<=exp(2R)} Lambda(n)/sqrt(n).   (L2)

This constant is independent of m. All prime powers permitted by the support
are included. Combining L1–L2 gives an explicit route from an upper bound
on the full LOCAL energy k[chi f] to logarithmic Fourier regularity.

## Exact stationarity exposes the remaining term

Let P=P_m^E and s=(I-P)(chi²f). Projected stationarity gives
k(f,P(chi²f))=lambda||chi f||², hence exactly

    k[chi f]=lambda||chi f||²+Re k(f,s)+M_chi(f),      (L3)
    M_chi(f)=k[chi f]-Re k(f,chi²f).

The full-source expression for M_chi is

 integral_0^infinity j(a) integral_R
       (chi(x)-chi(x+a))² Re(conj(f(x))f(x+a)) dx da
 +sum_{2<=n<=m} c_n integral_R
       (chi(x)-chi(x+log n))² Re(conj(f(x))f(x+log n)) dx
 +|<p,chi f>|²-Re(<f,p><p,chi²f>).                  (L4)

This is half of the previously checked physical double-commutator formula.
The odd pole cancels by parity. The diagonal constant cancels algebraically.
The arch integral still runs to infinity; terms vanish by the actual support
where appropriate. L4 is signed, even though its jump weights are positive.

Consequently the sufficient regularity bound is a uniform upper bound on

    lambda||chi f||²+Re k(f,(I-P)chi²f)+M_chi(f).      (L5)

The fixed-theta trial bounds lambda from above by o(1). The OTHER TWO terms
in L5 have no uniform source bound yet. Dropping the projection term would
replace the exact finite eigen-equation by an unproved ambient equation.
Merely naming L5 the desired bound does not supply it.

## What the elementary absolute estimates actually pay

For K=||chi'||_infinity, the arch part of L4 has absolute value at most
integral_0^infinity j(a) min(K²a²,1) da, a fixed finite constant.
For a nonzero prime cross term, one point must meet [-R,R] and both must
lie in the original window. Hence log n<=L/2+R. Cauchy–Schwarz gives

    |prime part of L4| <=sum_{n<=exp(R)sqrt(m)} c_n
                        <=2 sqrt(N)log N,
    N=exp(R)sqrt(m),                                (L6)

using Lambda(n)<=log N and sum n^-1/2<=2sqrt(N).
This is O_R(m^(1/4)log m), not a uniform bound. The pole part costs at most
||p chi||²+||p||_{L²(I)}||p chi²||=O_R(1+m^(1/4)).
These are separate absolute budgets ONLY; a successful proof may exploit
their joint cancellation. No cancellation is claimed lost by necessity.
The mixed projection term in L5 remains in addition to these costs.

This improves the geometric support of the crude prime budget from n<=m
to n<=exp(R)sqrt(m), but does not close even the regularity half of GREEN.
An independent source estimate must control the signed combination L5,
not replace the full form by the positive archimedean energy.

## Scope and controls

L3 uses exact stationarity, not exact MINIMALITY. For a unit trial q with
matrix residual r=(A-rho)q, it acquires the additional term
Re<r,P(chi²q)>, bounded by ||r|| because ||chi||<=1. Therefore an estimate
using only L3 and small residual would apply equally to escaping radical
trials; it cannot force their local mass positive. Exact bottom minimality
would have to enter an additional signed estimate or a competitor comparison.

Even a uniform logarithmic bound alone does not imply NOESCAPE: translated
radical packets have vanishing mass in every fixed central observation.
Local mass remains a separate requirement. No normalized competitor or
negative energy direction has been constructed here.
For the GREEN response z_m, its relation to f_m subtracts a_m e1,m. Weak
escape of e1,m alone gives neither strong local decay nor a bounded local
logarithmic norm, so the regularity of chi f_m and chi z_m cannot be
silently identified. This is another explicit transfer cost to retain.

## What direct minimality adds to this localization test

Put e=(I-P)(chi f), v=P(chi f). If v is nonzero, g=v/||v|| is an
admissible normalized even competitor in the SAME original carrier. Exactly,

 k[g]-lambda = N_chi/||v||²,
 N_chi=k[chi f]-lambda||chi f||²
       -2 Re k(chi f,e)+k[e]+lambda||e||²
      =Re k(f,s)+M_chi(f)-2 Re k(chi f,e)+k[e]+lambda||e||². (L7)

Here orthogonality gives ||v||²=||chi f||²-||e||²; no return cost
or normalization error has been suppressed. Exact minimality says N_chi>=0.
Thus its direct consequence is a LOWER bound on the local energy after
return, whereas L1-L2 require an UPPER bound. This is not an impossibility
result for a joint source estimate: a negative source upper bound on N_chi
would instead give the requested variational contradiction immediately.
No such upper bound follows from the absolute budgets L6.

For a trial q replace lambda by rho=k[q]. L7's first equality still holds,
but its last expression has the additional Re<r,P(chi²q)> from L3.
The assertion N_chi>=0 is absent for a quasimode. This separates the precise
minimality input from the residual estimate without claiming either supplies
the missing sign. If v=0 the proposed normalized competitor is undefined;
escape alone does not rule out that case or provide a denominator bound.

Independent bounded read-only audit confirmed L1-L4 and the conditional
L5 implication, including parity, support and projection sign. L7 is an
own algebraic continuation of the existing exact return formula, not a new
accepted source bound. Next unpaid step: joint signed control of L5 or L7;
separate absolute estimates and stationarity alone do not pay it.

## Joint physical pole cancellation (continuation 2026-10-31)

The shelf already contains the corresponding coordinate-amplitude cancellation
in BOUNDARY Lemma 8, equations (6.2)-(6.7). Its physical-cutoff counterpart
can be derived directly, without assuming its reciprocal-cutoff symmetry.
For real even f define, with b=L/2,

 C(s)=integral_{-b}^{b-s} (chi(x)-chi(x+s))² f(x)f(x+s) dx,
 D(s)=sum_{2<=n<=exp(s)} Lambda(n)/sqrt(n)-2(exp(s/2)-1).

Then C(0)=C(L)=0 and C(s)=0 for s>b+R. The original finite Fourier f is
smooth on the closed window. Differentiating this moving-endpoint integral
shows that C is absolutely continuous, despite the zero extension of f.
In particular its derivative includes the boundary term

 -(chi(b-s)-chi(b))² f(b-s)f(b),

as well as the integral of the differentiated integrand. It is not legitimate
to replace this by a whole-line derivative that drops the endpoint term.

The even pole part of L4 equals

 -1/2 integral_I integral_I p(x)p(y)(chi(x)-chi(y))² f(x)f(y) dxdy
 =-integral_I integral_I cosh((x-y)/2)(chi(x)-chi(y))² f(x)f(y) dxdy
 =-2 integral_0^L cosh(s/2) C(s) ds.

For the middle equality use p(x)p(y)=cosh((x+y)/2)+cosh((x-y)/2)
and y->-y, with actual evenness of BOTH chi and f. Therefore exactly

 M_chi(f)=integral_0^L j_+(s) C(s) ds - integral_0^L D(s) C'(s) ds, (L8)
 j_+(s)=j(s)-exp(-s/2)=exp(-5s/2)/(1-exp(-2s)).

Indeed add and subtract exp(s/2) ds in the complete prime measure, then
integrate C dD by parts. The endpoint atom at n=m is retained with C(L)=0.
All other prime powers remain in D. No PNT approximation is used. Near zero
C(s)=O(s²), so the j_+ singularity is integrable. C need not have either
sign or the symmetry C(L-s)=-C(s); the paired discrepancy from BOUNDARY
cannot be imported here without an additional identity.

Now the reference integral has the m-independent absolute bound
integral_0^infinity j_+(s) min(||chi'||² s²,1) ds. Thus L8 removes the
separate growing pole/prime main terms BEFORE taking any inequality.
The remaining local regularity debt is the joint upper bound

 Re k(f,(I-P)chi²f) - integral_0^L D(s) C'(s) ds <= constant_chi. (L9)

Together with the known upper bound on lambda, L9 suffices for L5.
L9 is UNPROVED: escape supplies no variation bound for this adaptive C,
and the endpoint term and finite-carrier projection remain material.
For strict descent use L8 in L7 and keep its other three return terms;
no negative numerator has been established. This refines the actual signed
object to estimate, rather than asserting that algebraic cancellation pays it.

Exact finite algebra check: L=2, unit f=1/sqrt(2), chi=x² on I gives
C(s)=s²(2-s)³/6. SymPy returns exactly zero for the difference between
the direct pole expression and -2 integral_0^2 cosh(s/2)C(s)ds
(both approximately -0.39472409212258470105). This checks factors only;
this cutoff is not the fixed compact cutoff used for the cofinal bounds.

Negative control: for the nonnegative escaping radical trials, C(s)>=0,
so the deterministic j_+ integral is NONNEGATIVE. It cannot supply a
negative localization gain on that class by itself. L8 holds for these
trials too: no stationarity or minimality was used to derive it. Exact
minimality first enters through N_chi>=0 in L7, while a source proof of
N_chi<0 would still need the discrepancy and every return term. For signed
bottoms no positivity of C is asserted. Thus cancellation has not silently
introduced a discriminator between bottoms and small-residual trials.

Independent read-only audit of L8-L9 confirmed pole factors, moving endpoint,
absolute continuity, full prime measure, conditional bound and negative control.
No discrepancy estimate, strict descent or NOESCAPE conclusion was accepted.

## Nonzero returned competitor: a small correction to the scope guard

For this specific cutoff one can settle v!=0 without an escape estimate.
Choose chi nonzero as well as smooth and nonnegative. Since the finite
Fourier synthesis f is nonzero and real analytic on I, it cannot vanish on
the open interval where chi>0. Therefore

 <f,P(chi f)>=<f,chi f>=integral_I chi(x)|f(x)|² dx>0,
 ||P(chi f)||>=integral_I chi(x)|f(x)|² dx>0.

Thus g=P(chi f)/||P(chi f)|| in L7 is always defined for these finite cells.
This refines the earlier generic zero-denominator guard: that guard matters
for zero or sign-changing cutoffs, but nonzero nonnegative chi excludes it.
No uniform lower bound is obtained; the displayed integral can tend to zero
under escape. The strict sign of N_chi remains the decisive unpaid step.
This repeats the nonvanishing mechanism already present for fixed-sign G
in DIRECT_THETA_LOCALIZATION_AUDIT_2026-10-06.md, rather than a new supplier.

## Focused shelf return while LOCALIZE runs

Semantic refresh completed with 3752 indexed files and 26481 vectors, PASS.
Three deep queries then completed with ASK_STATUS:HITS: signed nonlocal IMS
localization Caccioppoli; spectral projection commutator localization error;
prime discrepancy compensated quadratic form. Concurrent qmd calls failed
for two queries; sequential repeats succeeded. Logs are
/tmp/rh_localize_ims_ask_retry.txt, /tmp/rh_localize_projection_ask.txt,
/tmp/rh_localize_compensation_ask_retry.txt. Hits are not supplier acceptance.

The direct-theta localization audit supplies the nonvanishing observation
above and excludes carrier-uniform repair; its selected-bottom bound is OPEN.
The regional-energy verdict of 2026-09-07, Theorem U1 and sections 7–8,
works on a special three-lobe, two-total-pole-null class. It explicitly leaves
universal signed localization unpaid. chi f here need not have that support
or pole-nullity, so its positive local floor cannot be used in L9.
The first-omitted-compression verdict of 2026-09-26 gives form continuity for
fixed G/G'' projection errors, not for the adaptive error (I-P)chi²f_m;
its section 1 uses a different N=6m-1 source schedule. No automatic transfer
of that selected compression estimate to literal N=m is admitted.
This bounded return found useful scope controls, not a new joint source bound.
The pending LOCALIZE request is unchanged and has not been resent.
