# Proshka Context Pack
Generated: 2026-09-16T09:47:51
Repo: /Users/emalam/.codex/visualizations/2026/09/12/01a092ef-bf89-7693-aca8-42c3b691138a/gamma-reciprocity-worktree
Branch: codex_mac/gamma-reciprocity-20260914
HEAD: 338ab1d7
Range: 1112f4b07bb1cbedbf6abc18d92a44ac166c1dfa..338ab1d74115fabd05a7ee3af4e455ba74acfb73

## Working tree
```text
## codex_mac/gamma-reciprocity-20260914
```

## Commit list (oneline)
```text
338ab1d7 [CODEX_MAC][gamma-reciprocity] Rank five full-V work items with exact first test
```

## Range diff summary
```text
.../PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES.md      | 174 +++++++++++++++++++++
 .../FIVE_FULL_V_CANDIDATES_20260916.json           |  18 +++
 2 files changed, 192 insertions(+)
```

## Per-commit stats
```text
338ab1d7 [CODEX_MAC][gamma-reciprocity] Rank five full-V work items with exact first test
 .../PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES.md      | 174 +++++++++++++++++++++
 .../FIVE_FULL_V_CANDIDATES_20260916.json           |  18 +++
 2 files changed, 192 insertions(+)
```

## File snapshots

### docs/Codex/REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md
```text
# Full two-energy dilation: exact source fit and the conditional covariance still to control

STATUS: ACCEPTED_PAPER_SOURCE_FIT_AND_EXACT_CONDITIONAL_REMAINDER.
SOURCE_BASE: 9864a5052eaa23790d8719d3beb548e084eee24d.
GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. RH: OPEN. PX_RH_CLAIM: NOT_MADE.
Isolated mathematical derivation; no Lean or canonical admission.

This concretizes the full conditional-operator suggestion in section 12 of
the original BROWNIANHODGE response. That suggestion is not new. The new
content here is an explicit product likelihood for simultaneous dilation
of both energies, its complete-source domain proof on a useful interval,
the exact target identity including the conditional covariance, and a
precise difference from the known negative Gaussian controls. No positive
source-sign budget follows just from this change of representation.

## 1. Pinned inputs

Read at SOURCE_BASE:

- `docs/Codex/REPORT_2026-09-13_BROWNIANHODGE_INTAKE.md`: full nu density,
  conditional law, tilt, normalization, and the excluded one-half map.
- `docs/Codex/REPORT_2026-09-13_BROWNIAN_PRIMITIVE_FORM.md`: the form H
  on the original measure and its exact primitive positivity scope.
- `docs/Codex/REPORT_2026-09-13_BROWNIAN_SCALE_DIFFERENCE.md`: neither
  of the two fixed-step difference maps realizes V.
- `docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md`, A1--A2:
  all-rank PSD of V on one nonempty open interval suffices for all real nodes.
- `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, Theorem T
  and section 10: all-finite V positivity has the original Weil consumer.
- `docs/Codex/REPORT_2026-09-13_DEFORMED_SOURCE_ZERO_WITNESS.md`: for each
  epsilon<0, exp(epsilon*x^2)f has negative V rows. No such row is known for f.

Let alpha=1/4 and nu=law(U), where U=sum_(n>=1) E_n/(pi n^2) and the E_n
are independent unit exponentials. Let U' be an independent copy. Denote
the positive density of nu by h, and that of U+U' by r=h*h. The accepted
full-source identities give

    Phi(x)=exp(5x/2) r(exp(2x)),
    Z=int_R Phi(x)dx, A=||Phi||_2, f=Phi/A,
    C=E(U+U')^alpha=2Z.

On pairs (u,v)>0 define the probability measure

    dmu(u,v)=(u+v)^alpha h(u)h(v)du dv/C.                 (1)

Write T=u+v and X=(1/2)log T. Under mu, X has density Phi/Z. Let
mathcal C be conditional expectation with respect to T (equivalently X).
The conditional law of u at T=t has density h(u)h(t-u)/r(t), 0<u<t.

## 2. Exact simultaneous dilation likelihood

For a=exp(2x)>0 define

    ell_a(u)=a h(au)/h(u),
    G_x(u,v)=a^alpha ell_a(u)ell_a(v).                   (2)

Every h denominator is positive on (0,infinity). The pushforward of mu by
(u,v)->(u/a,v/a) has density G_x relative to mu: its Lebesgue density is
a^(alpha+2)(u+v)^alpha h(au)h(av)/C. In particular E_mu G_x=1.

Conditioning on T=t and changing variable z=au gives

    (mathcal C G_x)(t)
      =a^(alpha+2)/r(t) int_0^t h(au)h(a(t-u))du
      =a^(alpha+1) r(at)/r(t)
      =Phi(X+x)/Phi(X)=f(X+x)/f(X).                     (3)

This matches each actual source translate exactly, not only its diagonal
or an end asymptotic. It retains a product of the likelihoods of BOTH
energies before conditioning. No positivity of V is assumed.

## 3. A sufficient complete-source domain

Use the nonempty open interval

    I=(-(log 2)/2,0), hence 1/2<a<1.                     (4)

The full accepted density is h(u)=2pi exp(-pi u)chi(u), where chi is
positive, bounded by 1, and nondecreasing. Consequently, for 0<a<=1,

    ell_a(u)=a exp(pi(1-a)u) chi(au)/chi(u)
      <=a exp(pi(1-a)u),
    0<G_x(u,v)<=a^(alpha+2)exp(pi(1-a)T).                (5)

The nu exponential moment is finite for every kappa<pi. For 0<=kappa<pi,
split U=E_1/pi+W and use the accepted E exp(pi W)=2 and independence.
The T moment follows by taking a product. Multiplying by a fixed power of
T does not affect finiteness below pi, by slightly increasing kappa.

Define the bounded nonnegative weight

    w(X)=1_(X>=0) Z Phi(X)/A^2.                         (6)

For every x in I, (5) and 2pi(1-a)<pi show that G_x and X G_x are in
L2(w dmu). On T>=1, log(T) is bounded by a polynomial in T; no small-T
logarithmic issue is hidden by this step. The same bounds hold uniformly
for x in a compact subset of I. A finite node family needs only finitely
many such bounds.

Conditional expectation C is an orthogonal projection in L2(w dmu):
the weight is measurable with respect to X, so weighted Jensen and
orthogonality follow from the ordinary conditional expectation identities.
Functions can be taken zero on X<0 in this weighted space. This asserts
neither a bounded inverse nor surjectivity onto arbitrary translate families.

## 4. Exact all-rank target and the retained covariance

For any finite x_i in I and c_i in C define the two functions

    G_c=sum_i c_i G_(x_i),
    B_c=sum_i c_i x_i G_(x_i),
    D_c=X G_c+B_c.

They are given directly by the finite list; no well-defined operator
G_c->B_c on equivalence classes is assumed. By (3),

    C G_c=P_c(X)/f(X),
    C D_c=Q_c(X)/f(X),
    P_c(t)=sum_i c_i f(t+x_i),
    Q_c(t)=sum_i c_i(t+x_i)f(t+x_i).

Since the X density under w dmu is 1_(X>=0) f(X)^2, the exact target is

    V[c]=sum_ij conjugate(c_i)V(x_i,x_j)c_j
        =2 Re <C G_c,C D_c>_(w dmu).                    (7)

All products are integrable by section 3 and Cauchy--Schwarz. Write
G_c^perp=(1-C)G_c and B_c^perp=(1-C)B_c. Multiplication by X commutes
with C on the functions in question. Orthogonality then gives

    V[c]=E_micro[c]-E_loss[c],                          (8)

    E_micro[c]=2 Re E_mu[w conjugate(G_c)(X G_c+B_c)],
    E_loss[c]=2 E_mu[w X |G_c^perp|^2]
                 +2 Re E_mu[w conjugate(G_c^perp)B_c^perp].

The first term of E_loss is nonnegative because X>=0 wherever w!=0.
The second, mixed conditional-covariance term has no established sign.
E_micro itself also has no established sign. Naming these quantities
energies does not assert positivity.

The single remaining inequality in this representation is

    E_micro[c]>=E_loss[c]                              (TARGET)

for EVERY finite node family in I and all complex coefficients. By the
pinned analytic propagation and full-sign transfer, TARGET would imply
the original all-test positivity and RH. These are conditional arrows;
neither (8) nor ordinary Jensen proves TARGET.

## 5. What differs from the negative Gaussian controls

For epsilon<0 let Phi_epsilon(X)=exp(epsilon X^2)Phi(X), normalized to a
probability density. Its natural lift is

    dmu_epsilon=exp(epsilon X^2)dmu/E_mu exp(epsilon X^2).

Conditioning on T is unchanged. The simultaneous dilation likelihood of
mu_epsilon, computed as in section 2, is exactly

    G_(x,epsilon)(u,v)
      =G_x(u,v) exp(epsilon[(X+x)^2-X^2])
      =exp(epsilon x^2) T^(epsilon x) G_x(u,v).          (9)

For x!=0 and epsilon!=0, the extra factor T^(epsilon x) cannot factor
into a product of a function of u and a function of v. To see this without
assuming differentiability of proposed factors, put k=epsilon x!=0.
Choose positive u1!=u2 and v1!=v2. Product separability would require

    [(u1+v1)(u2+v2)]^k=[(u1+v2)(u2+v1)]^k.

The bases differ by (u1-u2)(v2-v1)!=0, and a positive number's nonzero
real power is injective. This is impossible. Dividing by the positive
separable G_x proves the stated failure for G_(x,epsilon) itself.

Thus (2) has an exact two-factor structure which (9), on this natural
lift, lacks. The generic conditional-expectation identities survive;
they alone cannot distinguish the known negative controls. This
factorization is only one candidate structural input, not a theorem
implying TARGET. Similar product likelihoods exist for other choices of
nu, so the actual complete law with rates pi*n^2 must still be used.

## 6. Mathematical boundary for the next request

The source fit in (3), the domain (4)--(6), and the full accounting (8) are
paid. The sign of TARGET is not. The original positive primitive form H
uses the kernel (u+v)^alpha on nu tensor nu; (8) also contains w(X),
the cutoff X>=0, and the conditional projection. Its positivity cannot
be transferred to these weighted terms without a new proof.

A useful next result must prove a genuine comparison controlling the
mixed conditional covariance, or derive a new sign-producing identity
from the exact two-energy source. It must not merely rename (7) or (8),
apply Jensen to only one of the terms, discard the cutoff/weight, or
assume positivity of the target to construct its Hilbert space.

This is source-fit progress and a precise localization of the still-open
sign problem; it is not a new positive budget, a negative V witness, or
an additional completed sign-construction attempt by itself.

## Independent mathematical read

The sole read-only reviewer `/root/sibling5_check` returned CLEAN on the
complete proof draft SHA256
b5d949a29d09d52cea59acbf8a9c68ead2516e7340244fe92f0bacf4f524274f.
The review checked the RN derivative, exact conditional source identity,
the squared-likelihood exponent in the weighted L2 domain, all covariance
signs, and nonseparability of the deformed natural lift. TARGET remains
unproved. Only the status and this receipt were added after that read;
no mathematical proof bytes were changed. No canonical admission follows.
```

### docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md
```text
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
```

### docs/Codex/REPORT_2026-09-16_POINCARE_TRANSFER_PREFLIGHT.md
```text
# Quick energy-transfer test on the actual conditional fields

Date: 2026-09-16. Base: `105062d6f55bd75b96d4c2485749e2f07022c891`.
STATUS: INDEPENDENTLY_REVIEWED_ANALYTIC_PREFLIGHT; exact scope and reviewed hash in the accompanying certificate.
Scope: an explicit primitive of the existing conditional fluctuation, its
Dirichlet gap, and its exact location in V=M-L. No RH, full-V sign, Lean or
canonical admission. This does not exclude other energy representations.

## P1. Exact inputs, with the mean retained separately

Use the full source and definitions of REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md
sections 1-4 and REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md R1-R5.
For t=exp(2X), X>=0, and s in (0,1),

    p_t(s)=t h(ts)h(t(1-s))/r(t),  r=h*h,
    g_x(t,s)=a^(9/4) h(ats)h(at(1-s))/(h(ts)h(t(1-s))), a=exp(2x),
    g=sum_i c_i g_xi, b=sum_i c_i x_i g_xi,
    m=E_t g, beta=E_t b.

All families are finite, c_i complex, x_i in I=(-(log 2)/2,0).
p_t, g and b are reflection symmetric under s->1-s. For fixed t the
profiles extend continuously to both endpoints, by the full-source estimates
in R2-R3. In particular they are in L2(p_t ds).

Let H_t(s)=integral_0^s p_t(v)dv and q_t its inverse. Here H_t is a CDF,
not a Hankel operator, and q_t is a quantile, not f'/f. Positivity of p_t
makes H_t continuous and strictly increasing; symmetry gives
q_t(1-v)=1-q_t(v). Define, for v in [0,1],

    z_g(v)=g(t,q_t(v))-m,
    u_g(v)=integral_0^v z_g(w)dw,

and the same definitions for b. Values at v=0,1 are interpreted by limits.
The probability change of variables sends p_t ds exactly to dv. Therefore

    integral_0^1 z_g=0,
    u_g in H_0^1(0,1),  u_g'=z_g,
    Var_t(g)=integral_0^1 |u_g'|²=:E[u_g],
    Cov_t(g,b)=integral_0^1 conjugate(u_g')u_b'=:E(u_g,u_b).    (P1)

This is a source-defined linear map on the entire finite family. It uses
the conditional field, not a rough Brownian sample path. Its derivative
energy is finite on every fixed fibre without a new smoothness assumption.

## P2. Symmetry removes the first sine mode

z_g(1-v)=z_g(v), and its integral is zero. Hence

    u_g(1-v)=-u_g(v),   u_g(0)=u_g(1/2)=u_g(1)=0.

The same holds for u_b and every complex linear combination. In the
Dirichlet sine expansion only even indices n survive, since
sin(nπ(1-v))=(-1)^(n+1)sin(nπv). Parseval on H_0^1 yields

    E[u_g] = sum_(n even, n>=2) π²n² |a_n|²
           >=4π² sum_(n even, n>=2) |a_n|²
           =4π² integral_0^1 |u_g|².                         (P2)

The coefficient is sharp on the full antisymmetric H_0^1 subspace, by
u(v)=sin(2πv). We do not claim that this equality profile is attained by
the particular theta likelihood span, or that 4π² is optimal on that span.
The ordinary π² spectral statement is classical; its explicit sine basis
also appears in Habermann, Brownian bridge expansions, §2.1 [S1].

## P3. Where the energy actually occurs in the target

The complete source identity, with the physical weight and cutoff, becomes

    L[c]=2 integral_0^infinity f(X)²
             [X E[u_g]+Re E(u_g,u_b)] dX,                    (P3)
    M[c]=2 integral_0^infinity f(X)²
             [X (|m|²+E[u_g])+Re(conjugate(m)beta+E(u_g,u_b))] dX,
    V[c]=M[c]-L[c]
        =2 integral_0^infinity f(X)²
             [X |m|²+Re(conjugate(m)beta)] dX.               (P4)

These are exact equalities, with no integration by parts in X and no
discarded boundary. The original weighted L2 bounds for G,XG,B ensure
absolute integrability of all displayed terms; the mixed energy is bounded
by sqrt(Var_t(g)Var_t(b)). The means have the corresponding Jensen bounds.

P2 provides a LOWER bound on the variance energy appearing inside L. It
provides neither an upper bound on the complete mixed expression L nor a
lower bound M>=L. M itself has not been proved nonnegative. In P4 the
fluctuation energy cancels exactly, and the sign is in the means and their
node-weighted companion beta. The likelihood family links these means to
fluctuations, but P2 alone establishes no useful inequality for that link.

No prime-specific input is used in P1-P2: symmetry and probability
normalization suffice. The known Gaussian-deformed controls keep the same
p_t and multiply each g_x by a fibre-constant factor. Thus P1-P2 also hold
there, while earlier project results give negative full-V rows. This is a
reused discrimination test, not a new negative witness for the true source.

## P4. Cheap null-profile check on an exact energy identity

At the limiting node x=0, g_0=1, hence u_g=0. Nevertheless

    V(0,0)=2 integral_0^infinity X f(X)² dX>0.                (P5)

This endpoint is not in I; the mismatch is a legitimate limiting test.
As x->0 from I, g_x->1 on each fibre and Var_t(g_x)->0. For x in a fixed
compact interval [x_0,0], exp(2x_0)>1/2, the established full-source bound
g_x<=exp(π(1-exp(2x_0))t) and the theta decay of f² give an integrable
dominating function after multiplication by (1+X)f². Consequently

    integral_0^infinity (1+X)f² E[u_gx] dX ->0,
    integral_0^infinity (1+X)f² ||u_gx||² dX ->0,
    V(x,x)->V(0,0)>0.

The second limit uses P2; the last follows directly from the full-source
shift integral and its uniform tail bound. Therefore V cannot equal a
fixed finite linear combination of these two fluctuation-only energies.
This excludes that exact identification. It does NOT exclude a lower
comparison, a map retaining the means, singularly rescaled maps with
separately checked domains, or a different full-field energy.

## P5. What an admissible rebuild of V must accomplish

Changing coordinates with an invertible S on a finite row gives
W[d]=V[Sd], matrix W=S*KS. This preserves positivity in BOTH directions:
each old vector is Sd for some d. It may reveal a proof, but cannot erase
a negative direction. A common linear source map into a Hilbert space
also suffices if an independently proved identity V[c]=positive_energy(Tc)
holds for every original finite family, including all boundaries.

A different object W is useful only with a proved sufficient arrow back
to the original target, for example V[c]>=W[Tc]>=0 for all c. Positivity
of W alone is insufficient. This is not hypothetical: the already accepted
HANKEL_JORDAN_PREFLIGHT H2-H4 proves V(x,y)/(x+y) positive on reflected
positive nodes, but multiplying entries back by x+y does not generally
preserve positive matrices. Do not repeat that normalization as a solution.

Fast checks for a concrete proposed map, before deepening:

1. Write the complete matrix/energy identity, not only its diagonal.
2. Test its null profiles and boundary traces. A source-limit mismatch
   rejects an exact identity immediately, as P5 does for this named map.
3. Verify that the bound controls a subtracted quantity FROM ABOVE or a
   remaining quantity FROM BELOW, retaining the mixed term and mean part.
4. Check whether the same premise holds for a known negative control;
   if it does, identify the additional source relation actually being used.

Outcome: the actual conditional primitive has the proved P2 bound, but
this bound by itself does not pay the full-V transfer. No new full-V
positive budget or negative true-source witness is supplied. No new route
family, Proshka dispatch, goal or counter reset is selected by this report.
The exact remaining design question is to couple the mean sector in P4
to a source-derived positive energy; whether this is possible is OPEN.

## Source pins

- REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md:
  `8ea7ed0b70f57d271b09cb44f53156cd50b71aa6511bd1fd4077111ba5bef5ef`.
- REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md:
  `7aaf8e43faa5bfd37954d6076db3acb1801325777bd9d989b25d75c9a9466c14`.
- REPORT_2026-09-15_HANKEL_JORDAN_PREFLIGHT.md:
  `c39016a5ba57aaa9e60f56682d11a9eebde9ee3202e4b2294c4e5beb156bc2c3`.
- [S1, Habermann §2.1](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/brownian-bridge-expansions-for-levy-area-approximations-and-particular-values-of-the-riemann-zeta-function/6C1D65580D064B415E14AF19DAE55517):
  classical sine basis and reciprocal eigenvalues. P1-P5 are direct
  calculations here, not claims attributed to that article.
```

### docs/Codex/PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES.md
```text
# Five concrete work items after the Poincare transfer test

Date: 2026-09-16. Base: `1112f4b07bb1cbedbf6abc18d92a44ac166c1dfa`.
STATUS: INDEPENDENTLY_REVIEWED_WORKITEM_RECONCILIATION_ONLY; exact scope and reviewed hash in the accompanying certificate.
Purpose: answer which existing constructions are worth a bounded next test.
Ranking is research judgment about readiness and source content, not a
probability of RH and not five new or already positive representations.
No new mathematical sign theorem, source-sign attempt, dispatch or goal.

The unchanged target is the complete theta V on every finite complex row
with nodes in I=(-log(2)/2,0). A candidate means a specified representation
plus a proposed missing sign mechanism. A general mechanism with no source
map is labelled construction-needed, not a built candidate.

## 1. Source renewal: compensate the averaged two-channel blocks

Existing object: the literal cutoff-aware fields F_(c,m) in the SIZEBIASCOMP
response §3 and §7, with the same moving conditional projection and physical
weight at each S_m. Equations (39)-(41) prove an absolutely convergent exact
telescope for V. Both mean and fluctuation channels and the boundary survive.

Input using the full source: T*=law T+H T*, independently on the right,
with density h^(-1/2)-1 for H on (0,1). This is the particular hyperbolic
law from the complete rates πn², not generic reflection symmetry. It supplies
the 1/6 and 1/15 moment factors; actual cutoff error has nonzero 6^(-m)
leading order. No new direct prime-factorization lemma is used here.

Proposed mechanism, UNVERIFIED: derive one source-dependent comparison for
averaged blocks of the two channels, retaining the trace. §11 gives an exact
martingale alternative: level increments are orthogonal across levels, but
their internal form uses J(a,b)=(b,a) and is signed. That orthogonality is
available; positivity inside a level is not.

First bounded test, specified before evaluation: group the FIRST TWO renewal
increments, starting from E_0=0. For independent T_1,T_2 with the full source
law and H with the law above, set S_2=T_1+H T_2. In the notation of §9,

 K_2(x,y)=E[1_(S_2>=1) psi_xy(S_2)]
        =psi_xy(1) P(S_2>=1)
          +integral_1^infinity P(S_2>=t) psi_xy'(t)dt.

The second equality is the same finite bulk/trace identity, now with S_2;
the bounded derivative and integrable survival tail justify Fubini. This
is exactly the sum of the first two expected original telescope increments,
not a new source substituted into V. Check a two-node K_2 diagonal and
determinant analytically first. A negative result rejects this proposed
two-step positive-block rule only. A positive result is only a necessary
check; arbitrary ranks and the remaining blocks would still need one common
rule. No sign of K_2 is asserted here. Simply restating the terminal
bulk/trace inequality (43) supplies no new hypothesis.

Do not repeat: almost-sure positive increments (already false); absent trace;
full-field 15^(-m); positivity from summability or from martingale orthogonality.
Priority 1: source-specific law and the entire target are already on one
space. This does not mean its missing sign is known to be easier.

## 2. Coupled full-source ladder: use an equation linking the channels

Existing object: REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION, L11,
the U_(alpha,k)(X) fields for alpha=2,4,... built from full convolution powers
r_alpha and the same finite coefficients. The exact ladder is

 alpha(alpha+1)U_(alpha+2,k)
 =[(partial_X+alpha+2k)^2-1/4]U_(alpha,k)
  -(alpha²π/2)(partial_X+2k-1/2)U_(alpha,k+1).

With E_c(k)=integral_0^infinity |U_(2,k)|², L12 gives
||Phi||_2² V[c]=-E_c'(0)/2. Source input: the complete sinh product over
πn² and the associated convolution recurrence. This is stronger structural
input than the first Dirichlet eigenvalue alone; a sign does not follow yet.

Proposed mechanism, UNVERIFIED: a common energy identity for the linked
channels proving the derivative sign AT k=0 with the exact X=0 traces.
First bounded test: the alpha=2,4 equations must exhibit a specified repeated
cancellation/weight rule. Calculate the uncancelled channel and all boundary
terms explicitly. If it merely asks for a new unknown sign at alpha=6, no
reduction is established; adding more levels is not the default continuation.

Do not repeat: scalar homogeneous Sturm equation (forcing is nonzero and
the tested scalar energy is negative); raw all-k energy decay (false already
on one negative shift). Only the local derivative sign is required by L12.
Priority 2: exact source equations exist, but a positive coupled energy does not.

## 3. Original interaction operators: a sign condition for the actual pair

Existing object: HANKEL_JORDAN_PREFLIGHT H1-H5. Reflect nodes into
J=(0,log(2)/2). H_f has kernel f(x+t), H_g has kernel (x+t)f(x+t), and
V is the kernel of H_f H_g+H_g H_f. There is also an explicit positive
Gram kernel L(x,y)=V(x,y)/(x+y); exactly K=DL+LD on each node list.

Proposed mechanism, UNVERIFIED: a property of these actual source-built
operators or feature vectors that forces their symmetrized product positive.
First bounded test: state such a property in terms of f, not in terms of
the desired K>=0, and verify it against the known negative control f0.
Without a source condition or explicit common factorization, there is no
new sign candidate to test; merely renaming K as an operator is insufficient.

Do not repeat: positive L implies positive DL+LD (false), commuting shortcut
(the actual pair does not commute), or positive Hilbert-Schmidt operator
quadratic form implies preservation of positive matrices (different claims).
Source distinction still missing: this representation works for the negative
control too. Priority 3: compact exact object; no discriminating input supplied.

## 4. Fourier representation with the endpoint contribution retained

Existing object: INTEGRATED_SIGN_HUNT H9-H11. For the zero-extended half-line
profiles P_c,Q_c, V[c]=(1/pi)Re integral conjugate(hat P_c)hat Q_c. The
exact A_x,B_x include the node-dependent missing finite interval and
B_x=i partial_omega A_x+x A_x.

Proposed mechanism, UNVERIFIED: an augmented transform that retains the
boundary information and produces a nonnegative matrix energy. A source-built
transform and its finite or infinite channel space still need construction.
First bounded test: specify the additional channel, expand its kernel, and
check all off-diagonal coefficients against V. If a two-channel model closes,
then check its 2-by-2 spectral symbol; existence of such closure is not assumed.

Do not repeat: a common scalar B_x=m(omega)A_x (false even for Gaussian f),
or omission of the cutoff term. Generic Fourier identities use no special
property of primes. Priority 4: exact transform available, positive map absent.

## 5. Pairwise difference energy on a new field

Existing mechanism only: INTEGRATED_SIGN_HUNT H7, the nonlocal ground-state
identity from Frank--Seiringer. It expresses an energy minus its matched
potential as integral integral omega(r)omega(s)k(r,s)|v(r)-v(s)|², k>=0.
No such source-defined k,omega and c->v map giving our full V has been built.

Proposed mechanism, UNVERIFIED: combine a source-built difference energy with
the independently accounted mean/boundary part, and prove exact equality or
a sufficient lower comparison to V. The kernel and map must be explicit
before this can be called a constructed theta candidate.
First bounded test: source equation, limiting zero-shift row, then the full
two-node identity. A map losing the means fails the zero-shift equality test;
passing it remains only necessary. Reject a kernel defined using an assumed
positive square root of V. Generic ground-state algebra has no prime-specific
input; the required distinguishing source property is still unprovided.
Priority 5: a verified general compensation method, with the source map unpaid.

## Decision and scope

Use 1 first for one explicitly written block comparison; keep 2 as the next
source-specific option if 1 gives no new sign premise. This is a recommendation
and a test specification, not a report that the block inequality was tried
or proved. Items 3-5 are conditional reserves, not equally prepared candidates.
Do not run five open-ended proof tasks. The user's Poincare-only fluctuation
candidate is already diagnosed; improving its constant is not a sixth route.

The required invariant for every item remains the entire original V or a
proved sufficient implication to the original RH criterion. An invertible
change of coordinates can expose a sign but cannot erase a negative direction.

## Evidence and search status

This is reconciliation of project reports and existing mechanism cards. No
new literature-discovery claim or exact-fit admission is made. The existing
INTEGRATED_SIGN_HUNT brief and its recorded three shelf queries were reused;
their INCOMPLETE freshness status remains unchanged. New mgrep retrieval
failed with authentication and exhausted-credit errors. No alternative search
tool, new paid search, index repair or absence claim was used.

Known source locators read directly:

- PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md, §§3,7-11;
  exact full-field identity, correction rates, and explicitly signed J.
- REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md, L1-L20, plus its
  independent certificate; Pitman--Yor Theorem1(ii) and Proposition12(iv)
  were already source-locked in that report, not newly discovered here.
- REPORT_2026-09-15_HANKEL_JORDAN_PREFLIGHT.md, H1-H6 and certificate.
- REPORT_2026-09-15_INTEGRATED_SIGN_HUNT.md, §§3-6 and its saved brief;
  existing source quotes/hashes and theta/control mappings reused.
- REPORT_2026-09-16_POINCARE_TRANSFER_PREFLIGHT.md, P1-P5.

Independent checking of this comparison does not prove any missing sign.
```
