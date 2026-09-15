# Hankel/Jordan sibling: a positive normalized kernel and the inverse-sign obstruction

STATUS: ANALYTIC_PAPER; independently accepted in the exact scope recorded by the adjacent certificate.
Base: 50b9eab917502a5cec4d8c96ad20c2fec0dc7c1b.
Brief: docs/Codex/BRIEF_2026-09-15_HANKEL_JORDAN_PREFLIGHT.md, SHA256 76c1995a566295a45c5187a26cc766ddcf1bbdcd1476acaca730d6740d5360d8.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; no canonical admission, Proshka request, or new goal. Full V and RH remain open.

## H1. Exact operator language for the original integral

Keep the full normalized, positive, real, even source f=Phi/||Phi||_2. The already proved reflection identity V(-x,-y)=V(x,y) carries original negative nodes to J=(0,log(2)/2). It follows directly by setting u=t+(x+y)/2: the product of the two shifted even sources is even in u, and the negative and positive central intervals cancel.

On H=L2(0,infinity) define Hankel operators
(H_f a)(x)=integral_0^infinity f(x+t)a(t)dt,
(H_g a)(x)=integral_0^infinity (x+t)f(x+t)a(t)dt, g(u)=u f(u).
Their squared Hilbert-Schmidt norms are respectively integral_0^infinity u*f(u)^2 du and integral_0^infinity u^3*f(u)^2 du. Both are finite by the full theta tail. They are bounded self-adjoint operators; both products are trace class. Direct kernel multiplication gives the continuous kernel identity

(H_f H_g+H_g H_f)(x,y)
=integral_0^infinity (2t+x+y)f(t+x)f(t+y)dt=V(x,y).       (H1)

Products converge absolutely by Cauchy-Schwarz. Local uniform domination follows from the complete tail, so the kernels are continuous. No boundary integration or omitted term is involved. The matrix Jordan product convention divides H1 by 2; H1 itself uses the anticommutator with no such division.

The original goal concerns the kernel on J, not an unlabelled stronger positivity claim on all of H. Kernel positivity for all finite complex rows in J is equivalent to positivity of the integral-operator compression to L2(J): Riemann sums give one direction on compact supports, and normalized small bumps approximating each point give the converse. Density and boundedness extend from compact supports to L2(J). No arbitrary-N claim is inferred from one operator matrix entry.

## H2. A genuine positive sibling for every finite family

For x,y>0 set L_f(x,y)=V(x,y)/(x+y). It has an explicit common Gram representation:

L_f(x,y)=integral_0^infinity f(t+x)f(t+y)dt
 +integral_0^infinity integral_0^infinity
       2t*exp(-s*x)*f(t+x)*exp(-s*y)*f(t+y) ds dt.        (H2)

Indeed integral_0^infinity exp(-s(x+y))ds=1/(x+y). For the actual positive source Tonelli applies; the finite-row identity also follows from the square-integrable feature vectors
Psi_x=(f(t+x), sqrt(2t)*exp(-s*x)*f(t+x))
in L2(dt) direct_sum L2(dt ds). Their norms are finite for each x>0, since
||Psi_x||^2=integral (1+t/x) f(t+x)^2 dt.
Thus for every finite complex row c,

sum conjugate(c_i)L_f(x_i,x_j)c_j=||sum c_i Psi_(x_i)||^2>=0. (H3)

There is no uniform bound claimed as x approaches zero. H2-H3 use neither square-rate spacing nor theta reciprocity beyond the reflection into positive coordinates: they work for any real continuous source with the required tails. This universal validity is also the limitation of the proposed backward transfer.

## H3. The backward step is a Lyapunov map, and is not positive in general

For any fixed finite node list let D=diag(x_1,...,x_N), L=[L_f(x_i,x_j)], K=[V(x_i,x_j)]. Exactly,

D L+L D=K,
L=integral_0^infinity exp(-sD) K exp(-sD) ds.             (H4)

The second identity is entrywise integration, legitimate since every x_i+x_j>0. Positive K implies positive L. The direction needed here is the reverse, which is false without a further source property.

For an exact finite matrix control, choose D=epsilon*diag(1,2), L=[[1,1],[1,1]], epsilon>0. Then L>=0 and
D L+L D=epsilon*[[2,3],[3,4]], det=-epsilon^2<0.
The vector (3,-2) gives -2epsilon. Choosing epsilon<log(2)/4 puts both nodes in J. This matrix is a control of the map, not an asserted theta kernel.

There is also a source-level control: the reviewed f0(u)=exp(-u^2)-exp(-2u^2)/4 has a negative finite four-node V row. It has the same H2-H3 positive normalized kernel, after reflecting its admissible nodes. Therefore even existence of the full source-generated positive sibling L_f does not imply the original sign. The special size-biased renewal law is not assumed for f0.

The semigroup exp(-sD)L exp(-sD) preserves positive matrices. Its derivative has sign determined by -exp(-sD)K exp(-sD); positivity of the semigroup values does not make this derivative nonpositive. Claiming Loewner monotonicity of these values would assume precisely the unpaid K>=0.

## H4. Published sibling and the important distinction of meanings

Primary source: Jiyuan Tao and M. Seetharama Gowda, A Representation Theorem for Lyapunov-like Transformations on Euclidean Jordan Algebras, International Game Theory Review 15(4), 1340034 (2013), DOI 10.1142/S0219198913400343.
URL: https://userpages.umbc.edu/~gowda/papers/trGOW12-01.pdf
PDF SHA256: 64f8fc0d4c240e9cb4f35f3e390313fa84ff58dcc13bbd4e165895226b9f62ab.
Read Introduction pp1-2, Theorem1/Proposition2 p3, and Theorem2 p7. Short quote, Theorem2, printed p1340034-7: "if and only if there exists an".

Theorem2 identifies Lyapunov-like linear transformations on real, complex or quaternionic Hermitian matrices as A X+X A*. The definition tests an orthogonality relation between elements of the positive cone; it does not say that every positive X is sent to a positive matrix. Our finite-row mapping uses A=D, X=L, so there is no normalization change in H4. The theorem is a source-verified classification/name for the exact map, not a sign theorem or an infinite-dimensional theta result. The matrix and source controls in H3 satisfy this Lyapunov-like framework and still have negative output.

Independently, D positive makes the superoperator X -> D X+X D positive definite in the Hilbert-Schmidt inner product: Tr(X*D X)+Tr(X*X D)>0 for X nonzero. That is a scalar quadratic statement about the matrix variable X. It is not the cone-preserving assertion D X+X D>=0 for every positive X. H3 explicitly distinguishes them. No claim from the publication is used to reverse this implication.

## H5. A commuting-operator shortcut also fails for the actual pair

The source-built operators in H1 satisfy

(H_g H_f-H_f H_g)(x,y)
=(x-y) integral_0^infinity f(t+x)f(t+y)dt.                (H5)

Since the full source is strictly positive, H5 is nonzero for every distinct positive x,y. Continuity then shows the operator commutator is nonzero. Consequently a theorem requiring this actual pair to commute cannot supply H1. The same noncommutation holds for a Gaussian, whose V is positive rank one, so commutation would be an unnecessarily strong sufficient route, not a necessary condition for V positivity. Neither positivity nor negativity of the anticommutator follows from H5.

## H6. Search receipt, outcome and stopping rule

One new registered shelf query covered Hankel Jordan product / positive anticommutator / Lyapunov inverse / Cauchy Schur multiplier. It returned exit2, ASK_STATUS INCOMPLETE because semantic-index freshness failed, not absence. Raw stdout SHA256 0172a80299cb92307cb0c2b7f992c3483ea8b362914e95274588912182083f62; stderr empty. Existing SPACE_SIBLING, ANCHORED_CONTRACTION, INTEGRATED_SIGN and SIGNED_SCHUR records were read first. Local filename screening provided no specifically named new primary; this is not an exhaustive shelf absence claim.

One bounded external batch used two exact object queries. The Tao-Gowda primary was fetched and the stated sections were read. Other hits were not promoted to verified mechanism candidates. No shelf mutation, index refresh, numerical theta scan or Lean run occurred.

The analytical preflight supplies H1 and the positive sibling H2-H3, then identifies the exact non-positive backward map H4. It also excludes literal commutation for the actual pair. No new theta-specific sufficient inequality has been found. The next step cannot be another appeal to generic Lyapunov positivity, cone preservation of the flow, or existence of the normalized Gram kernel. It would need a new source condition on this prescribed L_f ensuring H4 has positive output; the present bound and the previous full-field convergence do not provide one.

This is a completed diagnostic sibling test, not a new full-V sign supplier, a route-family impossibility result, or a negative theta witness. Preserve all historical and parked Barvinok counters; do not send a new Proshka task on the strength of H2 alone.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The positive normalized Gram kernel and positive Hilbert-Schmidt superoperator do not give positivity of the original Lyapunov output matrix.
