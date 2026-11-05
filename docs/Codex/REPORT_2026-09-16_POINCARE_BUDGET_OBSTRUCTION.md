# The unweighted derivative budget is too strong for the full micro term

STATUS: INDEPENDENTLY_REVIEWED_PAPER_OBSTRUCTION_ONLY; exact payload and scope in the accompanying certificate.
Date: 2026-09-16. Source base: 69cddb064f6d7f0504c0afe6de0360b510e965f8.
Scope: the actual full theta source, one specified stronger comparison.
No negative original V witness, no RH conclusion, no Lean admission.

## 1. Claim and its narrow implication

Keep the source, likelihoods and physical measure of
REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md. Let

    M[c]=2 Re integral conjugate(G)(XG+B) d eta,
    D_X[c]=integral X|partial_s G|^2 d eta,
    G=sum c_i g_xi, B=sum c_i x_i g_xi,
    I=(-log(2)/2,0).

Claim: for every fixed kappa>0 there is a finite real-node, complex-
coefficient family inside I for which M[c]-kappa D_X[c]<0.
The proof gives existence, not an explicit rank or coefficient bound.

In particular, the newly proposed sufficient lower envelope

    L_pi[c]=M[c]-(D_X[c]+sqrt(D_G[c]D_B[c]))/(2*pi^2)

cannot be nonnegative on every original row. Indeed choose
kappa=1/(2*pi^2) and use D_G,D_B>=0. L_pi<=M-kappa D_X.
L_pi is not generally a quadratic form; analytic positivity propagation
will be applied only to the quadratic kernel M-kappa D_X.
Since L_pi<=V, a negative L_pi is NOT a negative V witness.

## 2. Full-source bounds used in the proof

Write U=E_1/pi+Y, Y=sum_(n>=2) E_n/(pi*n^2), and

    h(u)=2*pi*exp(-pi*u)*chi(u),
    chi(u)=(1/2) E[exp(pi*Y) 1_(Y<u)].

The exact product E exp(pi Y)=product_(n>=2)(1-1/n^2)^(-1)=2
gives 0<chi(u)<=1, monotonicity, and chi(u)->1. Split the next
exponential out of Y. The remaining sum has a finite moment at 4*pi,
since product_(n>=3)(1-4/n^2)^(-1)<infinity. Thus the density of Y
is bounded by C exp(-4*pi*u), and consequently

    1-chi(u)=O(exp(-3*pi*u)),
    chi'(u)=O(exp(-3*pi*u)),
    ell(u):=h'(u)/h(u)=-pi+O(exp(-3*pi*u)).                 (D1)

The source identities also give the exact normally convergent expansions

    h(z)=2*pi*sum_(n>=1)(-1)^(n+1)n^2 exp(-pi*n^2*z), Re z>0,
    h(z)=z^(-5/2) sum_(k>=0)[pi(2k+1)^2/2-z]
                           exp(-pi(2k+1)^2/(4z)).         (D2)

Use the principal powers on the right half-plane. Their equality follows
from the Laplace transform sqrt(pi*s)/sinh(sqrt(pi*s)), or the accepted
full-source Jacobi formula; these are full series, not truncations.
On closed smaller sectors the series and their derivatives converge
normally on compact sets, and the first-term bounds are uniform as z->0
or Re z->infinity within the corresponding bounded-angle scales.
In particular on the positive real axis

    h(u)~(pi/2)u^(-5/2)exp(-pi/(4u)) as u->0,
    r(t)<=4*pi^2*t*exp(-pi*t),
    r(t)/(4*pi^2*t*exp(-pi*t)) ->1 as t->infinity.          (D3)

The middle bound is immediate from h<=2*pi exp(-pi*u) in its convolution.
For the last limit, the ratio equals
integral_0^1 chi(ts)chi(t(1-s))ds; dominated convergence applies.

## 3. Analytic continuation of the ACTUAL weighted kernels

This pays an extra domain obligation; the older sufficient a>1/2 bound
does not establish it. Define

    Omega={z in C: Re z<0, |Im z|<pi/8}, a_z=exp(2z),
    g_z(t,s)=exp(9z/2) h(a_z ts)h(a_z t(1-s))
                            /[h(ts)h(t(1-s))].

For z in Omega, Re(a_z)>0 and Re(1/a_z)>1/sqrt(2)>1/2.
The denominators here are positive REAL h, independent of z. No
division by possibly complex-zero h(a_z u) is used in the holomorphy proof.

With u=ts, v=t(1-s), the fixed physical measure is

    d eta=1_(u+v>=1) (u+v)^(3/2) r(u+v)h(u)h(v)du dv/(2*A^2).

Define holomorphic candidates using two UNBARRED variables:

    M(z,w)=integral (log t+z+w)g_z g_w d eta,
    D_X(z,w)=integral (log t/2)(partial_s g_z)(partial_s g_w) d eta. (D4)

On real nodes these are the real symmetric kernels of the quadratic
forms in section 1. We verify joint holomorphy on Omega x Omega by
local uniform integral domination, with the original t>=1 cutoff.

For compact z,w sets, put sigma=Re(a_z)+Re(a_w). Its infimum is positive;
Re(1/a_z)+Re(1/a_w)-1 also has positive infimum. Formula (D2) gives,
uniformly in those compact parameters,

    |h(a_z u)h(a_w u)|/h(u)
      <= C u^(-N)exp(-delta/u),                         0<u<=1,
      <= C exp[-pi*(sigma-1)*u],                       u>=1,  (D5)

for some finite N,C and delta>0. The same type of estimate, allowing
larger inverse powers and powers of t, holds after each one s-derivative.
To check this without complex logarithmic derivatives, differentiate the
numerator products directly. Derivatives of real denominators contribute
h'(u)/h(u)=O(1+u^(-2)); the h'(a_z u) series have the same exponential
budgets as h(a_z u), times fixed powers near zero.

Multiplication by r(t)<=C t exp(-pi*t) cancels the possible growth in
the large-u and large-v factors. When both exceed 1 the result is a
polynomial times exp(-pi*sigma*t). If one is <=1 the other has the same
decay and the small variable retains exp(-delta/u) or exp(-delta/v).
If both are <=1 the range t>=1 is bounded and both endpoint budgets
remain integrable. Fixed polynomial and log(t) factors are harmless.
Thus (D4) converges locally uniformly, including all s-endpoint regions.
Integrals over compact subdomains are holomorphic and their tails are
uniformly small; hence M,D_X and K_kappa=M-kappa D_X are jointly
holomorphic on Omega x Omega. In particular their actual integrals are
finite for ALL real x,y<0, not just on I.

## 4. A distant single shift: M stays bounded

Let x<0, a=exp(2x), and change variables U=a ts, W=a t(1-s), T=U+W.
Then g_x^2 d eta is exactly

    d nu_a=1_(T>=a) a*T^(3/2)/(2*A^2)
             *r(T/a) h(U)^2 h(W)^2/[h(U/a)h(W/a)] dU dW.  (D6)

Here dt ds=dU dW/(a*T), with no omitted cutoff Jacobian. Since
2(X+x)=log T,

    M(x,x)=integral log(T) d nu_a.                         (D7)

For 0<a<=1, chi(U/a)>=chi(U) and the same holds for W. From (D3),

    d nu_a <= (2*pi^2/A^2) T^(5/2) exp(-pi*T) h(U)h(W)dU dW. (D8)

The factor |log T| times T^(5/2)exp(-pi*T) is bounded on (0,infinity),
and h(U)h(W) is a probability density. Therefore (D7) is uniformly
bounded in absolute value for all 0<a<=1. This also pays the small-T
region introduced by the change of variables; no boundary term was dropped.

On each compact rectangle in U,W>0, (D1)--(D3) give uniform convergence

    d nu_a/dU dW -> T^(5/2)h(U)^2h(W)^2/(2*A^2)=:j_0(U,W)>0. (D9)

## 5. On the same shift, D_X grows without bound

For real a, the logarithmic s derivative of g_x in the new variables is

    Q_a(U,W)=T[ell(U)-ell(W)]
              -(T/a)[ell(U/a)-ell(W/a)].                   (D10)

By (D1), on any fixed compact rectangle R in (0,infinity)^2,
Q_a converges uniformly to Q_0=T[ell(U)-ell(W)]. The exponential error
is bounded by C a^(-1) exp(-c/a), which tends to zero.

ell is not constant on (0,infinity): otherwise h would be a single
exponential, contradicting its strictly positive interior and flat zero
at the origin in (D2). Choose U_0,W_0 with ell(U_0)!=ell(W_0). By
continuity choose a compact rectangle R of positive area around this pair
such that |Q_0|>=q_0>0. Positivity in (D9) and uniform convergence then
give, for sufficiently small a, a fixed C_R>0 with

    integral_R Q_a^2 d nu_a >= C_R.                        (D11)

The whole rectangle lies in T>=a for sufficiently small a. Also
X=(log T)/2-x. Its infimum on R is at least -x+C_0 for a fixed finite C_0.
On the rest of the original domain X>=0, so its contribution to D_X is
nonnegative. Therefore

    D_X(x,x)>=(-x+C_0)C_R ->infinity as x->-infinity.       (D12)

Combining (D7)--(D12), for every fixed kappa>0,

    K_kappa(x,x)=M(x,x)-kappa D_X(x,x)->-infinity.           (D13)

Only a compact rectangle was used to lower-bound the derivative energy;
no interchange of its full infinite-domain limit and integral was assumed.

## 6. Return to finite families inside the required interval

Suppose K_kappa were PSD for every finite family on I. By section 3 and
the accepted analytic propagation lemma A1 in
REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md, it would then be PSD
on all J=(-infinity,0). That lemma includes mixed old/new evaluations and
uses finite differences followed by convergent Taylor series. Its
conclusion is all finite complex rows, with no uniform rank bound.
It would in particular give K_kappa(x,x)>=0 for every negative x,
contradicting (D13). Consequently a finite K_kappa-negative row exists
in I. No far-negative node is passed off as an originally admissible node.
This proves the claim in section 1 at PAPER scope if the independent
review accepts the domain and source bounds above.

## 7. What this removes and what it preserves

This rejects a FIXED positive multiple of the globally integrated
s-derivative budget D_X as a lower comparison for M on all rows.
In particular it rejects the sufficient sign condition L_pi>=0, including
any larger Young-inequality envelope replacing sqrt(D_G D_B).
It does not reject the proved upper bound L<=B_pi, the conditional
Poincare inequality, all coefficient choices depending on t, a different
source-defined norm, or a signed estimate keeping covariance cancellation.
It proves no negative V row and no failure of RH.

The structural reason to retain the mixed sign is visible on the distant
single shift: B=xG and the exact loss uses X+x, whereas the modulus
envelope uses X+|x|. Their cancellations differ. The all-rank analytic
argument makes the resulting over-strong comparison fail even within I.
This explanation is a diagnosis of the bound, not a new proof of V>=0.

Source properties used: the exact two-copy likelihood, full physical
weight, source holomorphic/endpoint estimates, and the leading exponential
tail with nontrivial logarithmic derivative. No specific prime property
or new Euler-product sign mechanism is used by this obstruction.
