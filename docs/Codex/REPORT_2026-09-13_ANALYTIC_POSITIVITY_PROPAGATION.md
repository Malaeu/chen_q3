# Any open interval already carries the full all-rank sign question

STATUS: ACCEPTED_CONDITIONAL_CONSUMER_BRIDGE_PAPER.
GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. ALL_ORDER_SOURCE_SIGN: OPEN.
RH: OPEN. PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

This is a conditional consumer bridge for the pending TWOCHANNEL request,
not a new source-sign attempt. The sent request and its input report remain
unchanged at de2271bebae87c24ca0dfd3d02ae885de8db1b11.

## A1. Analytic propagation lemma, with the all-rank hypothesis exposed

Let J be a nonempty open real interval, Omega a complex open set containing
J, and K holomorphic on Omega x Omega. Suppose K(x,y)=conjugate(K(y,x))
for real x,y in J. If the restriction of K to I x I is positive semidefinite
for EVERY finite family of nodes and complex coefficients on one nonempty
open subinterval I of J, then K is positive semidefinite on all of J.

Here holomorphic refers to both unbarred complex variables. Equivalently
K(conjugate(z),w) is a sesquiholomorphic kernel on conjugation-stable pieces;
the proof below only forms Gram matrices at real nodes.

Proof. Assume K is PSD on an open interval B contained in J. Fix a in B
and eta>0 such that the complex disk |z-a|<eta is contained in Omega.
For each integer n>=0, forward differences at a give functionals

    ell_(n,h)(g)=sum_(k=0)^n (-1)^(n-k) binom(n,k) g(a+kh)/(n! h^n)
                  -> g^(n)(a)/n! as h->0 through real positive h. (A1)

For any fixed maximum order M and any fixed collection of old nodes in B,
all nodes a+kh lie in B for sufficiently small h. Applying these functionals
and the old evaluations to BOTH variables of the PSD kernel, then taking
h->0, gives a PSD block matrix of old evaluations and derivative evaluations.
In particular its derivative block is

    B_mn=partial_x^m partial_y^n K(a,a)/(m! n!), 0<=m,n<=M.     (A2)

This uses only finite congruences and a finite-dimensional matrix limit.
The coefficients of ell are real; arbitrary complex vectors remain allowed.

For finitely many new real nodes y_j with |y_j-a|<eta and y_j in J,
replace each new evaluation by the finite Taylor functional

    L_(M,y_j)(g)=sum_(n=0)^M (y_j-a)^n g^(n)(a)/n!.

Together with any old evaluations this again gives a PSD matrix. Its
new/new entries are the double Taylor partial sums using (A2). They tend
to K(y_i,y_j) by absolute convergence on the polydisk at (a,a).
Its old/new entries tend to K(x_i,y_j) by the one-variable Taylor series
in the SECOND variable, with old x_i fixed in B. The radius eta is valid
for every such old x_i because the domain is the product Omega x Omega.
Taking M->infinity thus proves positivity on

    B union ((a-eta,a+eta) intersection J).                    (A3)

This includes all mixed old/new matrices, not just positivity separately
on two overlapping intervals. The order of limits is fixed: first h->0
for each finite M, then M->infinity. No bounded inverse, uniform bound on
Taylor coefficients in M, or exchange of those limits is assumed.

Finally fix any desired finite node family in J. The real segment joining
it to an interior point of I is compact in J and in Omega. A sufficiently
small uniform disk radius therefore works at every point on that segment.
Repeated applications of (A3) with overlapping intervals, in finitely many
steps, include the entire family. This proves the lemma.

## A2. The actual full theta kernel has the required analytic extension

The exact source and consumer are those of
REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, sections1--2 and10,
at 667c22a589336a584ee31a84ab42a9ad9d1bcbf3, 15303bytes/335LF,
SHA2561e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.
That independently accepted report fixes f=Phi/A, A=||Phi||_2, and

    Phi(z)=sum_(n>=1) [4pi^2 n^4 exp(9z/2)-6pi n^2 exp(5z/2)]
                       exp(-pi n^2 exp(2z)),
    V(z,w)=integral_0^infinity (z+w+2t) f(z+t)f(w+t)dt.         (A4)

Let S={z:|Im z|<pi/4}. On each compact subset of S, Re(exp(2z)) has
a strictly positive lower bound. The full series in (A4) converges normally
there and defines a holomorphic Phi; it is not a finite theta approximation.

More explicitly, for z in a fixed compact subset of S and t>=0, let
m<=Re z<=M and |Im z|<=theta<pi/4. With c=pi exp(2m)cos(2theta)>0,
the absolute sum for Phi(z+t) is bounded by

    C exp(9t/2) sum_(n>=1)(n^4+n^2) exp(-c n^2 exp(2t))
      <= C' exp(9t/2) exp(-(c/2) exp(2t)).                    (A5)

Indeed split the exponent in half and use exp(2t)>=1 in the summable
n-dependent half. For any compact pair (z,w), the product of two bounds
(A5), times a constant multiple of 1+t, is integrable in t. The integrals
over finite t-intervals are holomorphic in both variables; their tails
converge uniformly on compact subsets of S x S. Thus V is jointly
holomorphic on S x S. On real nodes V is real symmetric.

Applying A1 to Omega=S, J=R proves, for EVERY nonempty open interval I,

    [all finite V matrices on I are PSD]
       iff [all finite V matrices on R are PSD].              (A6)

By the already accepted full-sign transfer and its named classical Weil
criterion dependency, either side of (A6) is equivalent to RH. This is an
equivalence only: neither side's positive sign is supplied here.

In particular an all-rank theorem on x>R, on |x|>R, or on any fixed open
window suffices for the full consumer. Conversely, if there is a negative
V witness somewhere, every nonempty open interval contains some finite
complex negative witness. A1 gives no useful bound on its rank, coefficient
size or conditioning. This does not contradict positive fixed-rank regions.

## A3. Application to the exact pending relative comparison

The independently accepted global W is T12--T14 in
REPORT_2026-09-13_TWOCHANNEL_LAPLACE_BRIDGE.md at de2271bebae87c24ca0dfd3d02ae885de8db1b11,
11996bytes/245LF, SHA256
e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908.
It is PSD on all real nodes. Consequently, if some delta>0 satisfies
V>=delta W as forms for ALL finite complex families on an exterior interval,
V is PSD there and A2 already supplies the full consumer bridge.

The same delta in fact propagates, provided this particular W is retained.
To verify the extra analytic hypothesis, fix a compact real interval [-L,L].
The analytic D(z)=V(z,z) is strictly positive for real z: by evenness
D(x)=D(|x|)=integral_(|x|)^infinity 2u f(u)^2 du>0.
Hence D has a holomorphic square root on a sufficiently thin rectangle
around [-L-1,L+1]; shrink the rectangle until Re D>0 there.

Every real square-root argument in T12--T13 is strictly positive there:
r_x=sqrt(x^2+4)>=2, cosh x>=1, 1-1/r_x>=1/2, and N_x^2>=1.
By compactness and continuity, shrink the same rectangle so all their
chosen positive branches extend holomorphically. Also choose it so
|Im(r_z-r_w)|<pi/2 for every z,w in it. Then C=sech and
T(d)=d/sinh(d) (with the removable value at zero) are holomorphic at every
required difference. Formula T13 therefore extends W holomorphically on
the product of that rectangle with itself.

For fixed delta, K=V-delta W now satisfies A1 on that rectangle. Starting
from any smaller source interval where the presumed inequality holds,
choose L large enough to include it and any desired finite target family.
Propagation proves V>=delta W for that family, with the SAME delta.
The rectangle may depend on L; delta does not. This pays the exterior-to-
global relative-bound bridge without assuming the relative bound itself.

## Evidence and boundaries

Registered shelf query `analytic kernel positivity continuation` returned
INCOMPLETE due semantic-index freshness, receipt SHA256
1943b29a213ff8c9b8475fcdf971ae1d6c898f351251a4e292b40b022c912be2.
The existing ALL_ODD_TO_RH report's section4 proves a local Loewner/Hankel
continuation for a different kernel; it was not silently applied to V.

A neighbouring primary source was checked to avoid reversing a theorem's
premise: Buescu--Paixao--Oliveira, arXiv:1802.07092v1,
https://arxiv.org/pdf/1802.07092, 261826bytes, SHA256
d1ab51b841e276613fc48205d38547aaf7e81c3b16c39f6480efe59049e08282.
Read scope: introduction pp1--2, Theorems3.20--3.22 and Remark3.23,
printed/PDF pp18--20. Theorem3.20 already requires a positive definite
kernel on its whole domain and propagates regularity. It is not a source
for our converse-direction A1. A1--A3 above are direct root proofs with no
novelty claim; no unverified literature theorem supplies the missing sign.

No numerical evaluation, finite-matrix scan, or Lean run was needed.
No full-source sign, relative bound, or original negative witness is proved.
The source-sign counter stays5; TWOCHANNEL is still the one pending third
construction since owner resumption. No new Pro request is sent.

## Independent acceptance receipt

The complete draft SHA256
cc0faac5bdcdaf301574ddd3f7297eac7ff3d7a5ce402094c965130ac2ff48e8
was independently CLEAN as ACCEPTED_CONDITIONAL_CONSUMER_BRIDGE.
Review SHA256
e1277e4153f97bf703f076e4fdca927b4578920858a057d90c1e939551b26da7.
The sole checker verified the mixed old/new blocks, ordered limits and
finite continuation chain; full theta holomorphy; and the thin-rectangle
square-root branches for propagation of the same assumed delta.
Only the acceptance status and this receipt were added afterward.
