# A primitive-sign brother in the exact two-copy Brownian energy law

STATUS: ACCEPTED_PARTIAL_PAPER_PRIMITIVE_SIGN_AND_NAMED_EMBEDDING_MISMATCH.
Source commit:59c7f0eceaf250d5b6d866965bc56c18b0a661bd.
This is a concrete form with a proved candidate sign mechanism and an unpaid
map to the original form. No RH, IC, ODD2, source-sign or production admission.
Canonical plan remains HOLD/NODE_REGISTRY_EXACT_EDGE_REQUIRED with foreign
writer ownership. The root works only in its authorized isolated math branch.

## B1. Exact source, probability and Brownian dictionary

Keep Z=int_R Phi=xi(1/2)>0 and A=||Phi||_2; these are different constants.
The accepted BP1-BP3 in docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md
supply the entire fixed source law, not just its first moment:

    U=sum_(n>=1) E_n/(pi*n^2),     E_n iid Exp(1),
    V an independent copy of U,  T=U+V,
    L(s)=E exp(-sU)=sqrt(pi*s)/sinh(sqrt(pi*s)), L(0)=1.

The positive sums converge almost surely, E U=pi/6, and they have all positive
moments: for 0<a<pi the convergent product
E exp(aU)=product_(n>=1)(1-a/(pi*n^2))^(-1) is finite. The law nu of U is
nondegenerate and continuous (convolve the first exponential with the rest).
The density of T is the exact r with
Phi(x)=exp(5x/2)r(exp(2x)). Under the tilted joint probability

    dP_*(u,v)=(u+v)^(1/4) dnu(u)dnu(v)/C,  C=E T^(1/4)=2Z,

X=(log T)/2 has density Phi/Z. This is the same complete theta source.

External dictionary: Biane--Pitman--Yor, arXiv:math/9912170v1,
https://arxiv.org/abs/math/9912170, section4.4, printed/PDF22.
Existing local pdfs/math_9912170.pdf:351648bytes, SHA256
04a444275e5522cef9a1ba9f7d1b9f20a752764d3548f9c48be6dbc055bb12ea.
The full section4.4 was read and page22 rendered. Quote (8 words):
"Taking two and four independent copies respectively gives".
The displayed Parseval sum has a printed n=0 typo; the preceding Fourier
series and following product start at n=1. No zero mode is imported.

For independent standard real Brownian bridges B_1,...,B_4 on [0,1],

    U=(pi/2) int_0^1 (B_1(t)^2+B_2(t)^2)dt,
    V=(pi/2) int_0^1 (B_3(t)^2+B_4(t)^2)dt.

Indeed the source Fourier expansion has coefficients sqrt(2)Z_n/(pi*n).
Parseval gives int B_j^2=sum Z_(j,n)^2/(pi^2*n^2), and each pair of squares
is twice Exp(1). The factor pi/2 yields exactly the rates pi*n^2 above.
Reflection below SWAPS THE TWO INDEPENDENT COPIES; it is not reflection of
Brownian time at a midpoint and introduces no unproved conditional boundary law.
The source paper provides this probability dictionary, not the following
primitive-form theorem or any Weil positivity assertion.

## B2. Fractional sum form: one positive direction

For 0<alpha<1 put D_alpha=L2((1+u^alpha)dnu(u)) and

    Q_alpha(F,G)=int int (u+v)^alpha conjugate(F(u))G(v)dnu(u)dnu(v).

This is a well-defined Hermitian form on all complex F,G in D_alpha.
Use (u+v)^alpha<=u^alpha+v^alpha and Cauchy--Schwarz; the required
integrals of |F| and u^alpha|F| are finite. Write m(F)=int F dnu and
ell_F(s)=int exp(-su)F(u)dnu(u). The elementary identity

    t^alpha=c_alpha int_0^infinity (1-exp(-st))s^(-1-alpha)ds,
    c_alpha=alpha/Gamma(1-alpha)>0,

follows by substitution and integration by parts, with vanishing endpoint
terms since 0<alpha<1. If m(F)=m(G)=0, it gives the exact formula

    Q_alpha(F,G)=-c_alpha int_0^infinity
                  conjugate(ell_F(s))ell_G(s)s^(-1-alpha)ds.       (B2)

The interchange is legitimate even for complex F,G: the integral of
|F(u)G(v)|(1-exp(-s(u+v))) over s,u,v equals the finite constant times
int int |F(u)G(v)|(u+v)^alpha dnu(u)dnu(v). Thus B2 is not a formal
subtraction of divergent terms. The integral on its right is absolutely
convergent by the same argument or polarization/Cauchy--Schwarz.

For F nonzero with m(F)=0, B2 is strictly negative. Otherwise continuity
makes ell_F(s)=0 for all s>0. Uniqueness of the Laplace transform of the finite
complex measure F dnu implies F=0 nu-almost everywhere. For completeness,
push that measure by u->exp(-u): its integer moments and mass vanish, so
polynomial density in C[0,1] makes the measure zero.

Consequently Q_alpha has positive index exactly one: Q_alpha(1,1)>0, while
every two-dimensional positive-definite subspace would intersect the
codimension-one hyperplane m(F)=0 nontrivially, contradicting B2. This means
positive index on every finite-dimensional restriction, not an unsupported
spectral assertion about an unbounded operator. An explicit full negative
copy-reflection witness is F(u)=u-pi/6, which belongs to D_alpha and is nonzero.
At alpha=1/4, Q_alpha/C is the expectation under the actual tilted law P_*.
This negative witness is for the NEW reflection form, not for V_f or Weil Q.

## B3. The Hodge-style projection and an explicit positive Gram carrier

Let C_alpha=Q_alpha(1,1)>0 and project away the positive vector using the
form itself:

    P_alpha F=F-[Q_alpha(1,F)/C_alpha]1,
    H_alpha(F,G)=Q_alpha(F,1)Q_alpha(1,G)/C_alpha-Q_alpha(F,G)
                 =-Q_alpha(P_alpha F,P_alpha G).                 (B3)

This H_alpha is positive semidefinite on all D_alpha, with radical exactly
the constants. Here is a direct proof that pays the projection sign.
Put f=F-m(F), g=G-m(G), b_f=Q_alpha(1,f), b_g=Q_alpha(1,g). Expansion and B2
produce the complete Gram identity

    H_alpha(F,G)=conjugate(b_f)b_g/C_alpha
       +c_alpha int_0^infinity conjugate(ell_f(s))ell_g(s)s^(-1-alpha)ds. (B4)

Both pieces are positive Gram forms. The integral is strictly positive on
any nonzero centered f, so H_alpha(F,F)=0 exactly for constant F. In particular
Q_alpha is strictly negative on the Q_alpha-orthogonal complement of 1.
This is the precise one-positive-direction/negative-primitive mechanism;
no algebraic surface, Frobenius action or arithmetic intersection pairing
is inferred from it.

At alpha=1/4 every input is fixed by the actual source. For the explicit
bounded observables E_a(u)=exp(-au), a>0, write

    D_a(s)=L(a+s)-L(a)L(s),
    b_a=-c_alpha int_0^infinity L(s)D_a(s)s^(-1-alpha)ds.

Then

    H_alpha(E_a,E_b)=b_a*b_b/C_alpha
       +c_alpha int_0^infinity D_a(s)D_b(s)s^(-1-alpha)ds.          (B5)

The sign and constants follow by applying the fractional identity to
Q_alpha(1,E_a-L(a)); no assumed positive source matrix is used. These
integrals converge by B2-B4 (also directly from the fixed hyperbolic L).
Thus an explicit same-source positive kernel is available without roots,
Cholesky factors of the target, or assuming the desired sign.

## B4. Cheapest transplant test: the bare exponential family does not fit

The existence of H_alpha is not an identity with the original kernel

    V_f(x,y)=int_0^infinity (x+y+2t)f(x+t)f(y+t)dt, f=Phi/A.       (B6)

A simple proposed identification E_(exp(2x)), even with positive diagonal
multipliers depending on x, already fails. The same holds for E_(exp(-2x)).
Here is a full asymptotic mismatch, not a finite numerical test.

As a,b->0, E_a=1-aU+o(a) in D_alpha: use
|exp(-au)-1+au|<=a^2*u^2/2 and the finite weighted fourth moment.
Since H annihilates constants and is continuous on D_alpha,

    H(E_a,E_b)/(ab)->H(U,U)>0,
    H(E_a,E_b)/sqrt(H(E_a,E_a)H(E_b,E_b))->1.                     (B7)

For the actual full source, its complete positive-tail series gives
q(x)=-(log f)'(x)~2pi exp(2x), and q is increasing for x>=0 by the already
accepted strict log-concavity. For y=x+d with fixed real d, x->infinity,
change variable t=u/q(x) in B6. On bounded u the two density ratios tend
to exp(-u) and exp(-exp(2d)u); monotonicity of q bounds the product by
exp(-(1+q(y)/q(x))u). The remaining linear factor divided by x+y is bounded
by 1+2u for all large x, providing an integrable majorant. Consequently

    V_f(x,y)~(x+y)f(x)f(y)/(q(x)+q(y)),
    V_f(x,x)~x*f(x)^2/q(x),
    V_f(x,x+d)/sqrt(V_f(x,x)V_f(x+d,x+d))->sech(d).                (B8)

All tails are the full theta series; this does not replace Phi by a finite
model. Evenness of f gives V_f(-x,-y)=V_f(x,y): after shifting t to the
midpoint coordinate, the omitted interval integrates an odd integrand.
For exp(2x) use x->-infinity in B7-B8; for exp(-2x) use x->infinity.
For every fixed d!=0 the two normalized limits disagree, 1!=sech(d).
Positive diagonal weights cancel from this comparison. Thus neither of
these two bare exponential embeddings, including arbitrary positive
node normalizations, transports B5 to B6. No other embedding is excluded.

## B5. Scope, negative controls, and the next exact question

The existing fc has an inverse positive-variable mean above3/2, whereas the
fixed U+V mean is pi/3<4/3; accepted BP3 therefore excludes fc from this exact
law. BP3b separately shows that matching that mean is insufficient. B2-B4
are general in nu: their abstract availability does not by itself distinguish
Phi from every control or prove a statement about V. The actual fixed L and
an explicit equality to the all-complex target must both be spent.

The missing object is a source-defined linear map from original tests (or
all finite node vectors) into this primitive space that preserves the
original quadratic form, with all boundary terms and normalizations paid.
Abstract Gram factorization after assuming V>=0 is circular. A new test may
use a different explicit observable family or derive the exact residual of
such an attempted map, but B7-B8 rule out rerunning the bare exponentials.
Neither the earlier stationary jump energy DN21 nor this Hodge carrier is
itself the missing equality. No larger polynomial or finite-matrix sweep.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The bare exponential Brownian carrier has limiting normalized correlation one, while the actual V has sech(d); no full-form transfer is supplied.

Discovery receipts: the three new registered queries in the appended
source-sign brief all returned INCOMPLETE due to semantic-index freshness;
no absence claim or index repair. Existing BPY media and the direct proof
above provide the evidence at paper scope. No CLOSES/OPENS line is permitted
while the production theorem/consumer edge is unbound. This is one bounded
parent construction-and-fit audit; independent acceptance remains pending.


Independent acceptance: sole sibling5_check read all198LF and accepted B1-B5
at exact candidate SHA256d845f5685a88bb4e6ec2711c387e1f197d9f2644880800c912a88d27f7ede71b.
Receipt SHA2566ab76484d545e3ed636072397480c05bdecfa0da4b86637b937acc646d432814.
Only the status and this receipt are changed after that audit. This completes
one new primitive-carrier theorem and rejects the named bare embeddings;
the original source-sign interface remains open, with no counter reset.
