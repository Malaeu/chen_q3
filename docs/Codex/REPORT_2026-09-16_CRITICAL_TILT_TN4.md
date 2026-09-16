# The critical Mellin weight already destroys additive TN4

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; ACTUAL_POWER_TILT_ADDITIVE_TN4_OBSTRUCTION_ONLY.
Base: 6269c6c024441e254983c8ea83136798cbf7fe9e.
Scope: one actual-source operation before the logarithmic coordinate change.
No negative original-V row, RH result or rejection of every joint-source
mechanism is asserted. The complete theta source is retained throughout.

## T0. Exact source, normalization and the operation being tested

Use the accepted full density r of T=sum Gamma(2,1)/(pi*n^2),
 r(t)=sum_(n>=1)(4*pi^2*n^4*t-6*pi*n^2)*exp(-pi*n^2*t),
 r(1/t)=t^(5/2)*r(t),
 M(s)=integral_0^infinity t^(s-1)*r(t)dt=2*xi(2s-2).
The additive translation kernel r(u-v), with r=0 on t<=0, is TN-infinity.

For real beta set Z_beta=integral_0^infinity t^beta*r(t)dt>0 and
 k_beta(t)=t^beta*r(t)/Z_beta for t>0, zero for t<=0.    (T1)
Every Z_beta is finite: the full large-t exponential bound and reciprocal
small-t bound dominate every power. This is a normalized probability law,
not the L2 normalization f=Phi/||Phi||_2 in the target V.

At the critical tilt beta=1/4, put X=log(t)/2. The density of X under T1 is

 2*exp(5X/2)*r(exp(2X))/Z_(1/4)=Phi(X)/integral_R Phi,

and therefore, for real z (and by the tails for all complex z),

 E_(k_1/4) exp(-izX)
   =M(5/4-iz/2)/M(5/4)=xi(1/2-iz)/xi(1/2).          (T2)

Thus T1 at beta=1/4 is the exact probability change leading to the xi
transform; it is not an auxiliary convenient density.

Inversion of T1 gives the density t^(-2)*k_beta(1/t), which equals
t^(1/2-beta)*r(t)/Z_beta. Substitution t=1/u gives
Z_beta=Z_(1/2-beta), so inversion sends k_beta to k_(1/2-beta).
In particular k_1/4 is self-reciprocal as a probability density, and
k_1/2 is the density of 1/T; Z_0=Z_1/2=1.             (T3)

## T1. Explicit obstruction on the actual tilted source

Theorem: for every fixed beta in (0,1), k_beta is not additive TN4.
In particular both the exact critical tilt beta=1/4 and the reciprocal
probability density beta=1/2 fail this property.

Let p=beta+1 in (1,2), C=4*pi^2/Z_beta, and
g(t)=exp(pi*t)*k_beta(t). The complete source series gives

 g(t)=C*t^p-(6*pi/Z_beta)*t^(p-1)+R_beta(t),
 g^(j)(t)=C*(p)_j*t^(p-j)+O(t^(p-j-1)), 0<=j<=6,    (T4)

as t tends to infinity; (p)_j=p(p-1)...(p-j+1), (p)_0=1.
These derivative bounds retain all modes. To see this, differentiate the
remaining n>=2 series finitely many times. For t>=1 its jth derivative
is bounded by a constant depending on beta,j times
t^(beta+1)*exp(-3*pi*t): after extracting that exponential, the remaining
polynomial-in-n series is summable uniformly for t>=1. This exponentially
small bound is O(t^(p-j-1)); the displayed n=1 correction has that same
power bound. No termwise expansion at t=0 is used.

Define the confluent ordered-minor matrix

 A_beta(T)=[(-1)^j*k_beta^(i+j)(T)]_(i,j=0,1,2,3).

Multiplication by exp(-pi*t) gives unit-triangular binomial row and column
changes in this derivative matrix. Their determinants are 1, so

 det A_beta(T)=exp(-4*pi*T)
              *det[(-1)^j*g^(i+j)(T)]_(i,j=0..3).    (T5)

Factoring C*T^(p-i) from row i and T^(-j) from column j in T4 gives

 det A_beta(T)=C^4*exp(-4*pi*T)*T^(4p-12)*(Delta_p+O(1/T)),
 Delta_p=det[(-1)^j*(p)_(i+j)]_(i,j=0..3)
        =12*p^3*(p-1)^2*(p-2)<0.                    (T6)

For completeness, factor (p)_i from row i, using
(p)_(i+j)=(p)_i*(p-i)_j. The remaining column j is a polynomial in i
of degree j, with leading coefficient 1 after its factor (-1)^j.
Its determinant is the Vandermonde determinant at 0,1,2,3, namely 12.
This proves the determinant evaluation with no sign convention left implicit.
In particular Delta_(5/4)=-1125/1024 and Delta_(3/2)=-81/16.
Thus det A_beta(T)<0 for every sufficiently large fixed T.

## T2. Transfer from the derivative matrix to finite ordered nodes

For such a fixed T, choose h>0 with 3h<T and increasing node lists
 u_i=T+i*h, v_j=j*h, i,j=0,1,2,3.
Their actual ordered translation minor is

 B_beta(T,h)=[k_beta(T+(i-j)*h)]_(i,j=0..3).

Successive divided differences in both node lists give the confluent limit

 lim_(h downarrow 0) det B_beta(T,h)/h^12=det A_beta(T). (T7)

Indeed the two Vandermonde products each equal 12*h^6, while the derivative
normalizing product is (0!*1!*2!*3!)^2=144. These factors cancel, leaving
exactly T7. Smoothness through derivative order six near T suffices; all
arguments stay positive. Hence for every sufficiently small h>0 this is
a strictly negative finite ordered 4-by-4 minor of the ACTUAL k_beta.
The proof has the order: fix beta, choose large T, then choose small h.
It asserts existence analytically without a numerical T or zero scan.

These u,v are tests of the additive kernel of k_beta. They are NOT original
admissible nodes in I for V; their negative determinant is not a V witness.

## T3. Independent transform-side explanation

The already shelved primary is K. Groechenig, Schoenberg's Theory of Totally
Positive Functions and the Riemann Zeta Function, arXiv:2007.12889v1,
https://arxiv.org/pdf/2007.12889v1 . Local PDF:
docs/routeB_bus/litreview/pdfs/2007.12889.pdf,
SHA256 e610f7a0de324a610fd24ee9fafa4356e5005a9af811245f016d6c0d791ed3a2.
Theorem 1(i), printed p2, equation (4); quote:
"is the reciprocal of a function".
Printed pp1-3 were reread; the theorem page was also checked visually.

Schoenberg's necessary condition says an integrable additive PF-infinity
function has Laplace transform 1/Psi, Psi entire of Laguerre-Polya type.
For the same k_beta, ordinary real Laplace asymptotics at q=-pi yield

 L_beta(-pi+delta)~C*Gamma(beta+2)*delta^(-(beta+2))
 as delta downarrow 0.                              (T8)

This follows by splitting the integral at a fixed large T and squeezing
exp(pi*t)*k_beta(t) between (C+/-epsilon)*t^(beta+1).
The bounded initial interval vanishes after multiplication by delta^(beta+2).
The defining transform is holomorphic on Re(q)>-pi. If it equalled 1/Psi
near zero, the identity L_beta*Psi=1 would hold on that whole half-plane.
T8 would force Psi(-pi+delta) asymptotic to a positive constant times
delta^(beta+2). An entire function vanishing at -pi has an integer zero
order, contradicting beta+2 in (2,3). Thus PF-infinity fails independently.
Unlike this transform argument, T6-T7 explicitly locate failure at order 4.

## T4. What is learned for the goal

The pre-existing RH_ROUTE_AUDIT section 4.1 already proved that the final
logarithmic density Phi/integral Phi is not PF-infinity. The new point is
earlier and sharper: the exact power change of measure already fails TN4
BEFORE the logarithmic coordinate change, even though the centered law has
the exact reciprocal symmetry. This identifies a specific non-preserving
operation rather than treating the whole source transfer as a black box.

The claim 'additive PF-infinity is preserved by the required power tilt or
by probabilistic reciprocal inversion on this source' is therefore false.
An exponential tilt exp(a*t) is a different operation: its row/column
factors preserve additive minors. t^beta is not that exponential tilt in
the additive t coordinate.

The broader premise 'additive TN-infinity of r together with its exact
weighted reciprocity implies a useful DIFFERENT property after transfer'
remains open. These proofs do not refute it, nor RH, nor the original V.
Any future supplier must name that different property and its exact map;
it cannot reuse unmodified additive minors of k_1/4 as the entrance.
No Lean run, canonical admission, new Proshka dispatch or full-V sign gain.

Source pins:
- REPORT_2026-09-14_EXACT_RECIPROCAL_PAIRING.md R2-R7,
  SHA256 3eaccc08a8ee5ced8d828340ba866a16f39d33c7e088c9b324b0bb62c4d7357a.
- REPORT_2026-09-16_MELLIN_EDGE_PREFLIGHT.md E0-E2,
  SHA256 a7dfba76bd7018100d312f198987a35e4a08ed163d8f5ade43d0f9244b14c1ff.
AUTOPSY: dropped=OBJECT_IDENTITY; note=The critical Mellin power tilt of the actual additive PF source has a negative ordered TN4 minor. Probabilistic reciprocity and symmetry do not preserve that minor class; the original full-V sign remains unpaid.

## Independent acceptance

Candidate SHA256: `17eaddaaeea3cef60f85311d7ea9184a707489eba754d9e4da3da9612fa0a4b1`.
Reviewer `/root/sibling5_check`; review SHA256: `8022cd266a4431547c568e36840cac6da090679077c4feaf390d4c5dff506e30`.
Verdict: ACCEPT_ACTUAL_POWER_TILT_ADDITIVE_TN4_OBSTRUCTION_ONLY.
The parent independently checked T1-T8, derivative signs, both numerical
fractions, the exact confluent normalization and the source/target distinction.
Only the status and this receipt were added after review.
