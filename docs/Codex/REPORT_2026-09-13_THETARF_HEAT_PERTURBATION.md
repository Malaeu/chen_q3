# Gaussian source deformation is not small relative to the fixed RF carrier

STATUS: ACCEPTED_PERTURBATION_DIAGNOSTIC_PAPER.
SCOPE: ISOLATED_PAPER_PERTURBATION_DIAGNOSTIC.
RF: OPEN. GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. RH: OPEN.
PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

This checks a possible objection to the pending THETARF problem. It does
not change that problem, the chosen carrier, or the live Proshka request.
It proves that one tempting uniform perturbation argument cannot work.

## H1. Exact objects

The original request at bc02022d75f61d08bc4508372b11f43d86b67799 is
docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_THETARF_2026-09-13.txt,
13056 bytes / 152 LF, SHA256
25f9265100eb7b2dd4e9346481abe1482750d09e1860d05f6ad3050caf28da79.
It fixes the full even theta source f=Phi/A, A=||Phi||_2, and

    V_0(x,y)=int_0^infinity (x+y+2t) f(x+t)f(y+t) dt,
    D_0(x)=V_0(x,x)>0,
    W_0(x,y)=sqrt(D_0(x)D_0(y)) Ghat(x,y), Ghat(x,x)=1.   (H1)

Ghat is exactly T12--T13 of
docs/Codex/REPORT_2026-09-13_TWOCHANNEL_LAPLACE_BRIDGE.md,
11996 bytes / 245 LF, SHA256
e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908.
Its finite matrices at distinct nodes are positive definite independently
of the open sign of V_0. In particular W_0(x,x)=D_0(x).

For real a define f_a(u)=exp(a u^2) f(u), and define V_a by substituting
f_a for f in (H1). This convention leaves the original A fixed. A separate
normalization back to unit L2 norm is treated below. The full theta tails
decay faster than exp(-b u^2) for every b>0, so these integrals exist for
every a. For x>=0 a change of variable gives the exact positive diagonal

    D_a(x)=V_a(x,x)=2 int_x^infinity u exp(2a u^2) f(u)^2 du. (H2)

No truncation of the source, zero hypothesis, or matrix-sign assumption
is used. Evenness also gives D_a(-x)=D_a(x).

## H2. The diagonal already prevents uniform relative continuity

For every a<0 and x>=0, (H2) implies

    0<D_a(x)/D_0(x)<=exp(2a x^2) -> 0 as x->infinity.     (H3)

Consequently

    sup_x |V_a(x,x)-V_0(x,x)|/W_0(x,x)=1   for every a<0. (H4)

For clarity, define the extended relative form bound of a Hermitian B by

    ||B||_[W_0]=sup |B[c]|/W_0[c],                       (H5)

where the supremum ranges over finite distinct real nodes and nonzero
complex coefficient vectors. W_0[c]>0 on this domain. The supremum may
be infinite. Single-node vectors c=(1) in (H4) prove

    ||V_a-V_0||_[W_0]>=1 for every a<0.                  (H6)

Thus there is no modulus omega(a)->0 as a tends to zero from below such
that |(V_a-V_0)[c]|<=omega(a) W_0[c] for every such family.
This fails already at rank one as the node escapes to infinity. It is
not a claim about a numerical small eigenvalue or a large-rank experiment.

For a>0 the reversed pointwise weight inequality in (H2) gives
D_a(x)/D_0(x)>=exp(2a x^2), so ||V_a-V_0||_[W_0]=infinity.
Differentiation at a=0, justified by the same full theta tail, yields

    (partial_a D_a(x)|_(a=0))/D_0(x)
       =4 int_x^infinity u^3 f(u)^2 du / D_0(x)>=2x^2.   (H7)

The first variation therefore has no finite W_0-relative form bound.

If instead f_a is normalized to unit L2 norm, set
k_a=1/||exp(a u^2)f(u)||_2. Then k_a is positive and finite for fixed a,
and the new diagonal is k_a^2 D_a. For a<0 its ratio to D_0 still tends
to zero, and the corresponding relative difference bound is at least 1.
For a>0 that ratio still diverges. No scalar normalization repairs this.

Each fixed finite matrix nevertheless tends entrywise to V_0 as a->0,
by dominated convergence. Entrywise continuity has no uniform conclusion
over arbitrary node locations; (H3)--(H6) supply an explicit obstruction.

## H3. What this says about the de Bruijn--Newman comparison

Rodgers--Tao, The De Bruijn--Newman constant is non-negative,
https://arxiv.org/abs/1801.05914v5, abstract, defines H_t using
exp(t u^2) Phi_RT(u), states the all-real-zero threshold t>=Lambda,
and establishes Lambda>=0. Read scope here is the abstract and version
metadata, not an independent verification of their full proof.
The retrieved HTML has 42316 bytes, SHA256
497d83aaca310cc9697102f3d5624a055192185f3cf94f329307e8d09b317a0e.

Term by term in the displayed full source series,
Phi(x)=2 Phi_RT(x/2). Hence, with our fixed A,

    F_a(tau)=int_R exp(a x^2) f(x) exp(-i tau x) dx
            =(8/A) H_(4a)(2 tau).                       (H8)

This identifies the deformation exactly, without suggesting that RF
automatically persists under it. The originally sought V_0>=delta W_0
would force delta<=1 just by taking a single node. A proposed stability
proof using one bound |(V_a-V_0)[c]|<=epsilon W_0[c] for all finite families,
with epsilon<delta, is impossible by (H6), for every negative a. This
excludes a uniform relative norm bound below delta; it does not exclude
pointwise strict inequalities whose supremum could equal delta=1.

This does not refute RF. It does not prove V_a is indefinite, and it does
not identify a negative witness for the original V_0. A proof concerning
a changing carrier W_a or a different transport would need its own exact
comparison. Any zero-location inference for deformed V_a also needs its
own theorem; the accepted original theta/Weil equivalence cannot simply
be applied to every deformed source.

The contribution is only the exact failure of this proposed perturbation
step. No new source-sign attempt is counted and no new Pro message is sent.

## Independent acceptance receipt

The sole independent checker fully reviewed the 5424-byte / 118-LF draft,
SHA256 9203d37ffe800c71d0af6f2e4b4e34111fdfef3a2e29aaa5c7d4f8f5ed5d841a,
and returned CLEAN_PERTURBATION_DIAGNOSTIC_ONLY. The converged review
explicitly checks the distinction between a bound with epsilon<delta and
pointwise strict inequalities with supremum delta=1. Review receipt SHA256:
b196f2e79da63788dbf7d953e2bbcbed85ac5c6d2e47d63a68fcc07b3eab547f.
Only the status and this receipt were appended after that exact review.
