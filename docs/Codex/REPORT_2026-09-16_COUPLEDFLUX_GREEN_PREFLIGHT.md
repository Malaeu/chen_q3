# Independent Green-identity check for the coupled full source

STATUS: INDEPENDENTLY_REVIEWED_PAPER; NATURAL_GREEN_PAIRING_SCOPE_ONLY.
Date: 2026-09-16. Private preparation for the already sent COUPLEDFLUX request;
not a second request, new route, sign proof, or canonical admission.
Source base: c29f1198f0c4e4613b0eebbe1c401efd459fa8d1.
Source: docs/Codex/REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md,
L1, L6, especially L11-L12; SHA256
feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21.

## The bounded test

Check the natural weighted Green pairing of the exact source equation with
its parameter derivative. Does this pairing itself supply a nonnegative
bulk energy that controls the desired local k-flux? This calculation prepares
a literal reference identity for reviewing Proshka's response. It does not
exclude other pairings or combinations of coupled fields.

For a fixed finite complex row, alpha=2,4,... and real k, put

 U=U_(alpha,k), P=U_(alpha+2,k), Z=U_(alpha,k+1),
 W=partial_k U_(alpha,k), R=partial_k U_(alpha+2,k),
 Y=partial_k U_(alpha,k+1).

In the last expression the derivative is with respect to the displayed k:
Y is the derivative of the profile at parameter k+1. All fields use exactly
the same coefficients and shifts, not independently chosen test functions.
Let

 a=alpha+2k, b=alpha^2*pi/2, A=alpha(alpha+1),
 L=D^2+2a D+a^2-1/4, B=D+2k-1/2,
 w(X)=exp(2a X), D=partial_X.

The source identity and its k derivative give, respectively,

 LU=A P+b BZ,                                             (G1)
 LW=A R+b BY+2b Z-4(D+a)U.                               (G2)

The coefficients 2b and 4 are important: partial_k B=2 and
partial_k L=4(D+a). Differentiating U_(alpha,k+1) does not change its
coefficient to a derivative with respect to alpha.

## All endpoint and differentiation operations

For each fixed alpha=2n the density is a finite convolution power of r_2.
The established flat zero endpoint and exponentially decreasing differentiated
tails imply that every fixed X derivative of Phi_alpha(X+x_i) decays faster
than exp(-C X) for every C>0 as X tends to infinity. One may, for example,
use any density tail exp(-lambda t), 0<lambda<pi, before t=exp(2(X+x_i)).
A k derivative introduces only -2(X+x_i). On a compact real k interval
these facts dominate the finite row, its first two X derivatives and their
k derivatives after multiplication by w and any displayed polynomial in X.
Thus differentiation and all integrations below are absolutely justified.

There is no limit X->-infinity in this calculation. At X=0 the actual
finite row traces remain, and are not prescribed to vanish. At X->infinity
all products displayed below, including w times them, tend to zero.

## Exact Green balance

Since w'=2a w, direct differentiation gives

 D[w(conj(U)W'-conj(U')W)]
       =w[conj(U)LW-conj(LU)W].                            (G3)

Integrate over [0,infinity), take real parts, and substitute G1-G2. The
result before simplifying the same-channel term is

 -Re[conj(U(0))W'(0)-conj(U'(0))W(0)]
 = A Re int w[conj(U)R-conj(P)W]
   +b Re int w[conj(U)BY-conj(BZ)W]
   +2b Re int w conj(U)Z
   -4 Re int w conj(U)(D+a)U.                             (G4)

All integrals in this document run from 0 to infinity unless stated
otherwise. The last integral is entirely a boundary term, exactly:

 Re int w conj(U)(D+a)U
   = (1/2)[w|U|^2]_0^infinity=-|U(0)|^2/2.               (G5)

Consequently the full balance is

 A Re int w[conj(U)R-conj(P)W]
 +b Re int w[conj(U)BY-conj(BZ)W]
 +2b Re int w conj(U)Z
 =-Re[conj(U(0))W'(0)-conj(U'(0))W(0)]-2|U(0)|^2.        (G6)

This includes the complete physical boundary. It is valid for arbitrary
finite complex rows, with no hypothesis on the zeros of xi.

## Explicit first two levels at k=0

For alpha=2: (A,b,a)=(6,2pi,2), w=exp(4X), B=D-1/2.
The three coefficients on the left of G6 are 6, 2pi, 4pi;
the next-level pair is (U_(4,0),partial_k U_(4,k)|_0).

For alpha=4: (A,b,a)=(20,8pi,4), w=exp(8X), B=D-1/2.
The three coefficients on the left of G6 are 20, 8pi, 16pi;
the next-level pair is (U_(6,0),partial_k U_(6,k)|_0).

Both have their own right-hand traces from G6. Their weights differ.
The alpha=2 next-level cross term and the alpha=4 next-level cross term
are different integrands, not equal terms whose cancellation follows just
from assigning opposite scalar coefficients to the two equations.

## What this check settles and what it does not

At alpha=2,k=0 the target is

 ||Phi||_2^2 V[c] = -Re int conj(U_(2,0)) W_(2,0).          (G7)

The obvious Green pairing G3 cancels the same-channel bulk term; G5 leaves
only a trace. G6 contains neither a retained nonnegative bulk norm nor the
target diagonal mixed integral G7. It is an exact constraint involving
cross-channel integrals and boundary terms. Simply presenting G6 as an
energy positivity theorem would therefore be unjustified.

This is a scope check of this one pairing, not an impossibility theorem
for all coupled energies. The source constraints might allow another
identity or inequality; this computation supplies none and rules none out.
No sign is assigned to the individual mixed terms in G6. In particular
r_(alpha+2)>0 as a scalar density does not make its complex finite-row
cross terms positive. No additional alpha level is opened by this note.

No V>=0 or negative V witness is obtained. No new external theorem is used:
the derivation is differentiation and weighted integration by parts applied
to the already reviewed exact full-source ladder.

## Independent acceptance and publication

Complete private candidate SHA256: `f597188296a896887a68e531741281f7683a5dd93e0bc5f15aaec95a75145076`.
Independent reviewer: `/root/sibling5_check`; review SHA256: `46ec4e0bbb5437f3b7097b6000e9840dcdfb6e5858f23e20f73c473689896728`.
The parent independently derived the parameter derivatives, weighted Green
identity, all X=0 terms and exact flux normalization. Only the status line
and this publication receipt differ from the frozen candidate. The review
text is preserved in the certificate. This is an analytic reference check
for the already pending COUPLEDFLUX response, not a new source-sign route.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The natural weighted Green balance is not the target diagonal local flux; its valid cancellation supplies no full-V sign.
