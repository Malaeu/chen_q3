# PROSHKA EVIDENCE PACK
Generated: 2026-09-15 17:52:55
Repo: /Users/emalam/.codex/visualizations/2026/09/12/01a092ef-bf89-7693-aca8-42c3b691138a/gamma-reciprocity-worktree

EVIDENCE PACK ONLY. This is not the authoritative Proshka request, not a dispatch payload, and not a transport/front door. The exact request must be a separately source-locked UTF-8 .txt validated by workflow_runtime.py review-plan in the existing living phase chat.


## Git status

## codex_mac/gamma-reciprocity-20260914


## Git log




## File: docs/Codex/REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md

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
