# A nonreal transform zero gives a finite negative source-kernel witness

STATUS: ACCEPTED_DEFORMED_SOURCE_WITNESS_PAPER.
SCOPE: ISOLATED_PAPER_DEFORMED_SOURCE_DIAGNOSTIC.
ORIGINAL_RF: OPEN. GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. RH: OPEN.
PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

## Z1. Transfer without an arithmetic or Weil premise

Let g be a nonzero real even smooth function such that, for every b>0,
|g(x)|<=C_b exp(-b|x|). Define

    F(z)=int_R g(x) exp(-izx) dx,
    V_g(x,y)=int_0^infinity (x+y+2t)g(x+t)g(y+t) dt.       (Z1)

F is entire and real on the real axis, and V_g is real symmetric and
continuous. Local differentiation of F and continuity of V_g follow by
domination using the displayed envelopes. F is not identically zero by
Fourier uniqueness. We prove the implication

    F has a nonreal zero => some finite complex row has V_g[c]<0. (Z2)

For h>0, H_h(x,y)=exp(h(x+y))V_g(x,y) belongs to L1(R^2). Indeed, insert
the absolute value inside (Z1) and change X=x+t,Y=y+t. The resulting bound
is

    ||H_h||_1 <= (1/(2h)) int int |X+Y| |g(X)g(Y)|
                                      exp(h(X+Y)) dX dY < infinity. (Z3)

Thus all interchanges in the following diagonal Fourier computation are
absolutely justified. For z=u+ih, h>0, set

    B_h(u)=int int H_h(x,y) exp(iu(x-y)) dx dy
          =[conj(F(z)) iF'(z)+conj(iF'(z)) F(z)]/(2h)
          =-Im(conj(F(z))F'(z))/h.                       (Z4)

The first equality to the quotient uses the same X,Y substitution: the
t-integral is int_0^infinity exp(-2ht)dt=1/(2h), and X+Y separates the
two source moments. It is a formula for a possibly signed form.
Where F(z) is nonzero, it is equivalently

    B_h(u)=-|F(z)|^2 Im(F'(z)/F(z))/h.                  (Z5)

Suppose z_0=u_0+iv_0, v_0>0, is a zero of order m>=1. Locally write
F(z)=(z-z_0)^m G(z), with G holomorphic and nonvanishing. At
z=z_0-i epsilon, for sufficiently small epsilon>0,

    Im(F'(z)/F(z))=m/epsilon+Im(G'(z)/G(z))>0,
    h=v_0-epsilon>0, F(z) != 0.                         (Z6)

The holomorphic remainder is bounded near z_0, so one can fix such an
epsilon. Equations (Z5)--(Z6) give B_h(u_0)<0. A zero below the axis has
a conjugate zero above it, since g is real and even. Multiplicity poses
no exception and no division is performed at a zero.

## Z2. The negative integral really reaches finite admissible rows

Fix h,u for which B_h(u)<0. By (Z3), the square-truncated integral over
[-R,R]^2 tends to B_h(u). Fix R large enough that this integral is negative.
For N>=1 put Delta=2R/N and, for k=0,...,N-1,

    x_k=-R+k Delta, c_k=Delta exp((h-iu)x_k).             (Z7)

Then V_g[c]=sum_jk conj(c_j)V_g(x_j,x_k)c_k is the ordinary two-variable
Riemann sum for that truncated integral. Continuity on the compact square
implies convergence as N->infinity. It is therefore negative for all
sufficiently large N. Each row is finite with distinct real nodes and
complex coefficients; every source term in (Z1) remains present.
The order is fixed: choose epsilon, then R, then N. No uniform bound on
rank, support size or coefficient norm is asserted. This proves (Z2).
Equivalently, all-finite positivity of V_g forces all zeros of F to be real.
The converse is not needed and is not asserted for this general class.

## Z3. Application to the exact nearby heat family

Retain the full source and original normalization

    Phi(x)=sum_(n>=1)(4pi^2 n^4 exp(9x/2)-6pi n^2 exp(5x/2))
                                 exp(-pi n^2 exp(2x)),
    A=||Phi||_2, g_a(x)=exp(a x^2)Phi(x)/A.              (Z8)

For every real a, the source is even, nonzero, smooth and satisfies Z1's
envelopes. Jacobi evenness and the full theta tail are proved in section2
of REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, SHA256
1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.
Multiplication by exp(a x^2) preserves these envelopes. No assertion about
the arithmetic Weil form of g_a is required.

By the exact change x=2u, Phi(x)=2Phi_RT(x/2) and

    F_a(z)=(8/A) H_(4a)(2z).                            (Z9)

Rodgers--Tao, https://arxiv.org/html/1801.05914v5, introduction (3)--(4)
and the following threshold statement, defines this H_t and states that
its zeros are all real if and only if t>=Lambda. Their Theorem1 proves
Lambda>=0. These are named published dependencies; their full classical
proofs are not reconstructed here. The source definitions, threshold and
Theorem1 statement were read directly, independently of any RH premise.
The fetched versioned HTML has 1296373 bytes, SHA256
9f7ac85fd7f21ae044bf5da47e2fa4a3d92dac1a5d40886d2ca771fa38c16125.

For every a<0, 4a<Lambda, so H_(4a) has a nonreal zero. By (Z9), so does
F_a, and (Z2) gives a finite negative row for V_(g_a). This is an existence
theorem for every fixed negative parameter, with the reduction (Z6)--(Z7)
from a nonreal zero. It does not supply numerical coordinates for that zero
or a particular finite row. Positive scalar L2 renormalization preserves
the conclusion.

There is also a precise localization consequence: for every a<0 and every
nonempty open real interval I, some finite row with all nodes in I has
V_(g_a)[c]<0. To justify it, retain the generic analytic propagation lemma
A1 in REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md, SHA256
fb83c216aef4687425074732904f9d2f52aac77527a926e7556fb0067335e2bd.
For each fixed a the full g_a is holomorphic on |Im z|<pi/4, and V_(g_a)
is holomorphic on the product strip: the compact-strip full theta bound
is C exp(9t/2-c exp(2t)); the additional Gaussian factor is at most
exp(C_a(1+t^2)), so the defining integral still converges locally uniformly.
If every finite matrix on I were PSD, A1 would propagate that sign to all
real nodes, contradicting Z2--Z3. This proves the localization consequence.
It gives no effective rank or coefficients in I. The rows (Z7) themselves
are not claimed to lie in an arbitrarily prescribed I.

## Z4. Boundary at the original source

The result does not include a=0. It supplies no negative witness for the
original V_0, no RF refutation, and no full IC or ODD2 sign. In particular,
negative rows for a sequence a->0- cannot be passed to a negative row at
a=0 without additional strictness and compactness control; Z2 provides
neither. Pointwise convergence of kernel entries is insufficient.

This pays the specific deformed-source zero-to-form step left open in
REPORT_2026-09-13_THETARF_HEAT_PERTURBATION.md at becc5019d9502b525799d7a7449882a440e26f14.
That report's fixed-W_0 perturbation obstruction remains unchanged.
No new construction is submitted to Proshka and no original-source sign
attempt is counted. The pending THETARF source-property problem is unchanged.

## Independent acceptance receipt

The sole checker read the complete 6697-byte / 135-LF draft, SHA256
a1487e1f48750fbeb498eac9dca0e47f3f39f4816c941d5a9c4c579582d1ef24,
and returned CLEAN_DEFORMED_SOURCE_ZERO_TO_FINITE_WITNESS_ONLY.
The review includes the added interval localization and its use of generic
A1, as well as the Fourier sign, multiplicity, finite-row limits and a<0
boundary. Review receipt SHA256:
33d780c0a7c94686f758a89182887bedcb6f8a7af93f33c6e25c0cfce06ae0cc.
Only the status and this receipt were appended after the exact review.
