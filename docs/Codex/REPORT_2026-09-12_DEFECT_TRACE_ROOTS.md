# What a finite Mellin defect retains about off-circle roots

STATUS: PAPER_CANDIDATE_PENDING_INDEPENDENT_REVIEW.
REQUEST_CONTEXT: REQ-2026-09-12-MATGOAL; independent work while its reply is running.
SOURCE_BASE: 7653a3503d20be4dba91a333ff96e5eea30c738c.
PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

This is a finite-dimensional operator calculation, not a claim that a general
Deitmar cutoff has already been identified with its hypothesis. The exact
cutoff identification currently exists in our packet only for one F9(t)
character. No novelty relative to the literature is asserted.

## Exact question

If a candidate proof identifies a cutoff defect with the vanishing conditions
of a polynomial, does orthogonal projection automatically recover the
polynomial's power sums? No. The following calculation gives the exact loss.
It is useful as a check on a proposed source-to-trace bridge, not as an extra
positive supplier for the Riemann hypothesis.

## Theorem

Let P have distinct nonzero complex roots lambda_j of multiplicities d_j,
and let d=sum d_j. For N with 2N+1>=d, put H_N=ell2({-N,...,N}) and
F_xi(z)=sum xi_n z^n. Let R_N be the orthogonal projector, extended by zero
to ell2(Z), onto the orthogonal complement of

    {xi : F_xi^(k)(lambda_j)=0, 0<=k<d_j, all j}.

Let V be the bilateral shift (V xi)_n=xi_(n-1). Define

    b(lambda)=lambda               if |lambda|<=1,
              1/conjugate(lambda)  if |lambda|>1.

Then for every fixed positive integer m,

    lim_N Tr(R_N V^m)=sum_j d_j b(lambda_j)^m.             (1)

For m=0 the trace is exactly d; for negative m it is the complex conjugate
of the positive-|m| formula. The same statement includes multiple roots
on the unit circle.

The limit is not uniform in a moving m or in roots approaching the unit circle.
Those limits are not used here.

## Proof

Use inner product <u,v>=sum conjugate(u_n)v_n, linear in v. Because every
lambda_j is nonzero, the ordinary derivative conditions are equivalent to
(z d/dz)^k F(lambda_j)=0. Their Riesz vectors are

    a_(j,k)(n)=n^k conjugate(lambda_j)^n, 0<=k<d_j.

They are linearly independent when 2N+1>=d: multiply F by z^N and apply
ordinary Hermite interpolation to degree at most2N. Multiplication by z^N
is invertible on the jets at the nonzero roots. Thus rank R_N=d.

Choose another basis for the same span, separated into three groups:

L: |lambda|<1,
    u_(j,k,N)(n)=(n+N)^k conjugate(lambda_j)^(n+N).
R: |lambda|>1,
    w_(j,k,N)(n)=(N-n)^k conjugate(lambda_j)^(-(N-n)).
C: |lambda|=1,
    v_(j,k,N)(n)=N^(-1/2)(n/N)^k conjugate(lambda_j)^n.

Here N>=1. Polynomial translation or reflection and multiplication by a
nonzero scalar preserve the span for each root.

Let A_N be the matrix with these basis columns, G_N=A_N* A_N and
B_(N,m)=A_N* V^m A_N. In fixed dimension d,

    Tr(R_N V^m)=Tr(G_N^(-1) B_(N,m)).                     (2)

We now take limits of both matrices, without taking limits of a nonorthogonal
list as if it were an orthonormal basis.

### Gram matrix

For L, move to l=n+N. The basis converges in ell2(N_0) to
l^k conjugate(lambda_j)^l. These exponentially decreasing polynomial sequences
are linearly independent (a confluent Vandermonde matrix on l=0,...,d_L-1
already has full rank). Their limiting Gram matrix is positive definite.
For R, move to l=N-n; the same assertion applies to
l^k conjugate(lambda_j)^(-l).

For C, within one root, the Gram entry tends by Riemann sums to

    integral_(-1)^1 x^(k+l) dx.

This moment matrix is positive definite on polynomials of degree below d_j.
Between distinct unit roots, summation by parts bounds the corresponding
oscillating sum by O(1/N): partial sums of the nontrivial geometric phase are
bounded, and the sampled polynomial has uniformly bounded total variation.

An L or R column has uniformly bounded ell1 norm. Each C column has sup norm
at most N^(-1/2), so all cross entries with C are O(N^(-1/2)). L-R entries
tend to zero: their mass is concentrated at opposite endpoints; split at
n=0 and use the exponentially small tail of one factor and the bounded
ell2 norm of the other. Fixed polynomial factors do not spoil exponential
decay. Therefore G_N tends to a block diagonal positive definite matrix.
The same cross estimates hold in B_(N,m) for fixed m, since shifting moves
an endpoint only a fixed distance and preserves the stated bounds.

### The left endpoint

Let S be the unilateral right shift on ell2(N_0), with S e_l=e_(l+1).
The L limit of V^m is S^m. The limiting span W_L is invariant under S*:

    S*[l^k conjugate(lambda)^l]
       =(l+1)^k conjugate(lambda)^(l+1).

Its triangular diagonal on each root block is conjugate(lambda), repeated
d_j times. Hence

    Tr(P_(W_L) S^m)=conjugate(Tr((S*|W_L)^m))
                  =sum_(|lambda_j|<1) d_j lambda_j^m.

The trace is of the finite compression; invariance of S* justifies the power
formula. It is not an assertion that S preserves W_L.

### The right endpoint

Now V^m corresponds to (S*)^m. The R limit span is invariant under S*, whose
triangular diagonal is 1/conjugate(lambda), repeated with multiplicity.
Its contribution is

    sum_(|lambda_j|>1) d_j conjugate(lambda_j)^(-m).

### The unit circle

For a C column, away from the finitely many shifted endpoints,

    V^m v_(j,k,N)(n)
      =lambda_j^m N^(-1/2)((n-m)/N)^k conjugate(lambda_j)^n.

Subtract lambda_j^m v_(j,k,N). The polynomial change has ell2 norm O(1/N);
the finitely many boundary values have ell2 norm O(N^(-1/2)). Therefore
B on this root block tends to lambda_j^m times its limiting Gram block.
Equation(2) gives contribution d_j lambda_j^m. Cross blocks vanish as above.

Combining the three groups proves(1). Finally, R_N is self-adjoint and finite
rank, so Tr(R_N V^(-m))=conjugate(Tr(R_N V^m)); cyclicity involves a finite
rank factor and is valid. This proves the remaining cases.

## What equality of source and defect traces would still have to prove

Assume additionally product_j |lambda_j|^(d_j)=1. This is an explicit extra
hypothesis here, not something inferred from the positivity of R_N.
Then the following are equivalent:

(a) all roots lie on the unit circle;
(b) for m=1,...,d, lim_N Tr(R_N V^m)=sum_j d_j lambda_j^m.

(a) implies(b) by(1). Conversely,(b) equates the first d power sums of the
two size-d multisets {lambda_j with multiplicity} and {b(lambda_j) with
multiplicity}. Newton identities give equal monic polynomials, hence equal
multisets. Every b(lambda) has modulus at most1. Thus every lambda has
modulus at most1; the product-modulus hypothesis forces each modulus to1.

This finite test list concerns exact analytic limits for a fixed polynomial,
not finitely sampled N values, not a numerical root certificate, and not a
uniform statement over conductors or curves.

## Explicit control

Let r>1 be real and P(z)=(z-r)(z-r^(-1)). Both roots are nonzero and their
product is1. For all sufficiently large N, R_N is an honest positive
orthogonal projector of rank2. Nevertheless,

    lim_N Tr(R_N V)=2/r,
    sum roots=r+1/r,
    difference=(r+1/r)-2/r=r-1/r>0.

Thus positivity and the correct defect dimension by themselves cannot supply
the missing source/defect trace equality. The discrepancy is already visible
at the first fixed test. This control is not the L-polynomial of a claimed
curve and refutes no actual-source theorem.

In the F9(t) example lambda=-1 has multiplicity2. Formula(1) yields
2(-1)^m, consistent with our exact finite trace calculation. The example sits
on the equality locus; it does not force other source objects onto that locus.

## Consequence for the pending Proshka review

Do not accept the following step: 'R_N is positive with the right rank, so its
limiting shifted traces equal the required L-power sums.' The theorem locates
the unpaid equality precisely. A geometric argument which genuinely proves
all normalized source roots have modulus1 is an additional sign-producing
input. Renaming the trace equality as a positive projection is not that input.

This is a diagnostic lemma only. It does not generalize the actual-source
Mellin image identification, prove general Deitmar trace equality, or provide
an archimedean transfer. Those remain open. The pending request is not changed
or resent while Proshka is reasoning.

## Parent rational orientation check

For r=2 set M=2N+1 and A=sum_(n=-N)^N 4^n. Directly forming
G and B for the unscaled columns 2^n,2^(-n) gives

    Tr(R_N V)=[A*((5/2)A-(1/2)4^(-N)-2*4^N)
                  -(5/2)M(M-1)]/(A^2-M^2).

Since A/4^N tends to4/3 and M/A tends to0, this tends to1=2/r,
not5/2=r+1/r. Python Fraction direct matrix summation independently
matched the displayed formula at N=2,8,32; these arithmetic checks only
check orientation/algebra, while the preceding proof supplies the limit.

## Final independent PAPER review receipt

CURRENT_DISPOSITION: ACCEPTED_AT_DIAGNOSTIC_LEMMA_SCOPE. The candidate header
above records its creation status; this receipt records the completed review.

The unchanged preceding 8796 bytes have SHA256 8dfe85544b37aa028433f33975ca6055073ef79f2b51525449c416b410a5c48a.
The independent read-only checker /root/sibling5_check confirmed CLEAN and
independently recomputed this exact digest. It checked the shift orientation,
confluent multiplicities, Gram and cross-block limits, unit-circle boundary
error, and Newton/product-modulus corollary. No source/Lean/production
admission is inferred. Parent separately reproduced the rational r=2 test.

Decision effect: a proposed proof using positive finite Mellin projectors must
still supply source-to-trace equality; correct rank and projection positivity
are insufficient. No new Proshka message was sent and no RH claim made.
