# Full theta sign to Weil sign — direct audit of the terminal transfer

STATUS: PAPER_AUDIT_PENDING_INDEPENDENT_CHECK.
SOURCE_BASE: 7653a3503d20be4dba91a333ff96e5eea30c738c.
PX_RH_CLAIM: NOT_MADE. No Lean certification or canonical admission.

This audits the previously inherited SLACK arrow. The result is an equivalence
between two all-test signs, not a proof of either sign. It reduces a named
audit dependency of GOAL_MAT and does not reset the open ODD2 sign counter.
The argument below needs no radical theorem, central/far allocation,
finite-field analogy, or bounded inverse multiplier on a function space.

## 1. Statement and exact objects

Let theta(t)=sum_(n>=1) exp(-pi n^2 t), t>0, and define

    r(t)=4t theta''(t)+6 theta'(t),
    Phi(x)=exp(5x/2) r(exp(2x)), A=||Phi||_2, f=Phi/A.

Thus Phi is exactly the full source

    sum_(n>=1) (4pi^2 n^4 exp(9x/2)-6pi n^2 exp(5x/2))
                   exp(-pi n^2 exp(2x)).

Define alpha(t)=exp(-t/2)/(1-exp(-2t)), c_A=gamma+log(8pi)+pi/2,
w_n=Lambda(n)/sqrt(n), and M_+/-(g)=integral g(x)exp(+/-x/2)dx.
For complex compact smooth g, let

    D(g)=integral_0^infinity alpha(t)||g(.+t)-g||_2^2 dt,
    Q(g)=D(g)-c_A||g||_2^2 +2Re(M_+(g)conj(M_-(g)))
         -2 sum_(n>=2) w_n Re integral conj(g(x))g(x+log n)dx.

Set

    V(x,y)=integral_0^infinity (x+y+2t) f(x+t)f(y+t)dt.

**Theorem T.** The following assertions are equivalent:

1. Q(g)>=0 for every g in C_c^infinity(R;C).
2. For every N>=1, real x_1,...,x_N, and c in C^N,
   sum conj(c_i)V(x_i,x_j)c_j>=0.

Together with the classical Weil criterion, these are equivalent to classical
RH. The theorem is an exact transfer; assertion2 is still unproved. The ODD2
subspace is necessary for assertion2 and is not substituted for it.

## 2. Source normalization and decay without a critical-strip premise

Use the Jacobi identity

    1+2theta(t)=t^(-1/2)(1+2theta(1/t)).

It is DLMF20.7.32 at z=0, tau=it with the positive square root. Differentiating
twice gives `r(1/t)=t^(5/2)r(t)`, hence Phi(-x)=Phi(x).
For t>=1 every term of r is positive: 2pi n^2 t-3>0. Reciprocity then gives
r>0 everywhere. The series and its fixed derivatives converge locally
uniformly for t>0. For x>=0, each fixed x-derivative of Phi is bounded by a
finite sum of terms C n^M t^M exp(-pi n^2 t), t=exp(2x)>=1.
The sum of n^M exp(-pi(n^2-1)) is finite; absorbing t^M into exp(pi t/2)
gives a bound C_k exp(-(pi/2)exp(2x)). Evenness gives the same bound at the
other end. This proves every exponential-weighted fixed derivative moment
needed below, and 0<A<infinity.

For Re(s)>1 put a=s/2. Two integrations by parts give

    integral_0^infinity t^a r(t)dt
      =(4a(a+1)-6a) integral_0^infinity t^(a-1)theta(t)dt
      =s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)=2xi(s).

All boundary terms vanish: near zero theta=O(t^-1/2), theta'=O(t^-3/2)
by Jacobi; the factors in both integration-by-parts boundaries are
O(t^((Re(s)-1)/2)). At infinity the series decays exponentially. Absolute
Fubini for the last equality follows from Re(s)>1 and the gamma integral.
With the Fourier convention F(z)=integral f(x)exp(-izx)dx, t=exp(2x) gives

    F(z)=(1/(2A)) integral t^(1/4-iz/2)r(t)dt
         =xi(1/2-iz)/A

whenever Re(1/2-iz)>1, in particular in an open neighborhood of Im(z)=2.
F and its derivatives exist everywhere by the proved envelopes, but no
critical-strip zero location is used in this calculation.

## 3. The control space and the unchanged full pairing

Let X be the space of measurable functions with

    ||g||_X^2=||exp(|x|)g||_2^2+D(g)<infinity.

Its inner product is the weighted L2 inner product plus the L2 pairing of
translation differences with measure alpha(t)dt dx. It is complete: the map
g -> (exp(|x|)g, (g(x+t)-g(x))) has a closed graph in the product L2 space,
as follows by distributional testing (or subsequences and Fubini) from a
convergent sequence in both coordinates.

Polarization of Q defines an antilinear-first Hermitian B on X. Write
W_g=||exp(|x|)g||_2. Then

    |integral conj(g(x))k(x+t)dx| <= exp(-|t|)W_g W_k,
    |M_+/-(g)| <= sqrt(4/3)W_g,
    |B(g,k)| <= (|c_A|+14)||g||_X||k||_X.                 (T1)

The first bound uses |x|+|x+t|>=|t| and Cauchy-Schwarz. The pole norm follows
from integral exp(+/-x-2|x|)dx=4/3. The two prime correlations cost at most
2 sum_(n>=2)(log n)n^-3/2 W_gW_k <10 W_gW_k by the integral test; the D
pairing is bounded by sqrt(D(g)D(k)). Thus every prime is present with an
absolutely convergent bound on X. For original compact tests the sum is in
fact finite. The constant14 is a harmless explicit upper bound.

Translation tau_b g(x)=g(x-b) has norm at most exp(|b|) on X and leaves B
unchanged. Its D-part is translation invariant, as are the correlations;
the two pole moments acquire opposite factors exp(+/-b/2).
Translations are strongly continuous: in the D-part apply ordinary L2
translation continuity to each difference g(.+t)-g, dominated by its
fourfold squared norm. Weighted L2 translation continuity follows by
compact L2 approximation and the displayed locally uniform operator bound.
This argument precedes and does not presuppose smooth density.

For a smooth cutoff chi_R tending to1, with bounded derivative O(1/R),
expand the translated difference of (chi_R-1)g. One term is bounded by
4|g(x+t)-g(x)|^2 and converges to0; the commutator term is bounded by
min(C^2t^2,4)|g(x)|^2 and converges to0. Both are integrable against
alpha(t)dt dx. Weighted L2 convergence is dominated convergence. Thus
chi_R g -> g in X. Mollifying each compactly supported chi_R g converges in
X by strong translation continuity and Minkowski's inequality. Consequently
C_c^infinity(R;C) is dense in X. This licenses later discontinuous atoms;
it is not an assumption that X=L2 or that derivatives must lie in L2.

## 4. Exact atoms with both poles and the grouped archimedean constant

Fix h=2 (the formulas below also hold for fixed h>1), sigma=h+1/2, and set

    q_(h,u)(x)=1_[0,infinity)(x) exp(-hx+iux), u in R,
    R_h(u)=1/(sigma-iu)+1/(sigma-1-iu)-log(pi)/2
           +psi((sigma-iu)/2)/2
           -sum_(n>=2) Lambda(n)n^(-sigma+iu),
    K_h(u,v)=(conj(R_h(u))+R_h(v))/(2h+i(u-v)).

The q atoms belong to X. Direct integration gives

    ||exp(|x|)q_(h,u)||_2^2=1/(2(h-1)),
    D(q_(h,u))=(1/h) integral alpha(t)(1-exp(-ht)cos(ut))dt,
    ||q_(2,u)||_X <= sqrt(6)*sqrt(1+u^2).                 (T2)

Indeed 1-exp(-ht)cos(ut)<=ht+u^2t^2/2,
integral t alpha(t)dt<5, integral t^2 alpha(t)dt<18, by the positive
geometric expansion and decreasing-tail integral tests.

Let d=2h+i(u-v). The atom mixed L2 product is1/d. The two translated
correlations are exp(-(h-iv)t)/d and exp(-(h+iu)t)/d. The D numerator is
integral alpha(t)(2-exp(-(h-iv)t)-exp(-(h+iu)t))dt.
Each pole product has denominators a,b with a+b=d. Multiplying it by d
therefore gives1/a+1/b. This produces all four reciprocals in
conj(R_h(u))+R_h(v); neither pole is discarded.

For the archimedean terms use DLMF5.9.16:

    psi(z)+gamma=integral_0^1 (1-t^(z-1))/(1-t)dt, Re(z)>0.

At z=1/4 substitute t=v^4. The resulting rational integral gives
psi(1/4)=-gamma-3log2-pi/2. Subtracting this value in the same convergent
integral yields, for Re(s)>0,

    (psi(s/2)-psi(1/4))/2
       =integral_0^infinity (exp(-t/2)-exp(-st))/(1-exp(-2t))dt.

Apply this to s=sigma-iv and its u conjugate. Their sum, minus log(pi),
is exactly the D numerator minus c_A. The small-t differences remain
grouped throughout. The prime part equals the original two translated
correlations term by term, with absolute convergence. Hence

    B(q_(h,u),q_(h,v))=K_h(u,v).                           (T3)

This is a pairing for a form whose sign is unknown; no positive Gram
representation was assumed.

## 5. Every original complex test is reached in the correct norm

For an original g choose b so g_b=tau_b g is supported strictly in (0,infinity).
Let G(u)=F_(g_b)(u+ih), the Fourier transform of exp(hx)g_b(x). It is Schwartz.
By T2 the Bochner integral

    g_b=(1/(2pi)) integral G(u)q_(h,u)du                   (T4)

converges absolutely in X. Evaluation in weighted L2 and ordinary Fourier
inversion identify this integral with g_b: on x>0 multiply the inversion
of exp(hx)g_b by exp(-hx); both sides vanish for x<0. The endpoint is null.

T1–T3 now give, with absolute convergence,

    Q(g)=(1/(4pi^2)) integral integral conj(G(u))K_h(u,v)G(v)du dv. (T5)

For completeness, this is also a finite-coefficient limit. Tail truncation
at |u|<=M has X error at most
sqrt(6)/(2pi) integral_(|u|>M)|G(u)|sqrt(1+u^2)du.
The map u->q_(2,u) is continuously differentiable in X with derivative ixq:
xq has weighted norm squared1/4, and its weak x-derivative has L2 norm
squared(4+u^2)/32. Its value is0 at the jump point, so no delta derivative is
present. The bound on integral t^2 alpha gives

    ||xq_(2,u)||_X^2 <= 5/2+9u^2/16.

Dominated difference quotients give the asserted X derivative. Riemann
sums on [-M,M] therefore converge in X; for mesh delta their extra error is

    (2M delta)/(2pi) sup_(|u|<=M)
       (|G'(u)|sqrt(6(1+u^2))+|G(u)|sqrt(5/2+9u^2/16)).

If the total X error is e, T1 bounds the quadratic error by
(|c_A|+14)e(2||g_b||_X+e). All estimates are for each fixed arbitrary complex
test and retain every source term. A test-dependent support shift is valid
because B is translation invariant; no uniform inverse bound is asserted.
It follows that Q is nonnegative on all original tests iff every finite K_h
matrix is PSD: use T4 for one direction, and X-density to approximate any
finite sum of q atoms for the other.

## 6. The only division is on finite coefficient spaces

The Euler product on Re(s)>1 is absolutely convergent with a nonzero value;
its logarithmic derivative is -sum Lambda(n)n^-s. Gamma has no zeros there
(and its reciprocal entire product proves this classical fact). Thus the
nonzero F_h(u)=F(u+ih)=xi(sigma-iu)/A obeys

    R_h(u)F_h(u)=iF'(u+ih)=integral x f(x)exp(hx-iux)dx.   (T6)

Differentiation is justified by section2. For every finite node set the
diagonal matrix diag(F_h(u_i)) is invertible. Therefore the finite K_h
matrices are PSD iff the finite matrices of

    W_h(u,v)=conj(F_h(u))K_h(u,v)F_h(v)

are PSD. The inverse is allowed to depend on the chosen finite nodes. There
is no map sending a general Fourier coefficient G to G/F_h in this proof.

## 7. The exact physical kernel and its sign transfer

Expand T6 in the numerator of W_h and insert

    1/(2h+i(u-v))=integral_0^infinity exp(-2ht-iut+ivt)dt.

Absolute Fubini is bounded by

    (1/(2h)) integral integral |X+Y| |f(X)f(Y)|exp(h(X+Y))dX dY <infinity.

Substitute X=x+t, Y=y+t. The result is

    H_h(x,y)=exp(h(x+y))V(x,y),
    W_h(u,v)=integral integral H_h(x,y)exp(iux-ivy)dx dy.  (T7)

The same estimate proves H_h in L1(R^2); compact-local tail domination
proves its continuity. These two facts suffice for all following limits;
a global L2 realization of Q or an inverse function-space multiplier is
unnecessary.

Finite H_h matrices are PSD iff its quadratic form is nonnegative on all
complex compact smooth spatial tests. Forward: compact rectangle Riemann
sums. Reverse: smooth approximate point masses at a finite set, combining
coefficients if nodes repeat; continuity controls the limit.

A nonnegative H_h form gives finite W_h PSD: use spatial tests
chi_R(x)sum_j c_j exp(-iu_j x). Dominated convergence with H_h in L1 gives
exactly sum conj(c_i)W_h(u_i,u_j)c_j.
Conversely, finite W_h PSD gives nonnegative frequency integrals against
compact smooth coefficients by Riemann sums. W_h is bounded by ||H_h||_1,
so L1-tail truncation extends this to Schwartz coefficients. For a compact
smooth spatial a choose

    eta(v)=(1/(2pi)) integral a(y)exp(ivy)dy.

It is Schwartz and a(y)=integral eta(v)exp(-ivy)dv. T7 and absolute Fubini
identify its nonnegative frequency form with integral conj(a(x))H_h(x,y)a(y).
No sign assumption was used to justify a limit.
Finally, finite H_h matrices are congruent to finite V matrices by the
positive diagonal exp(hx_i). Combining sections5–7 proves Theorem T.

## 8. Connection to the published final consumer

For C_g(t)=integral g(x)conj(g(x-t))dx, C_g(-t)=conj(C_g(t)). Substituting this
into Suzuki's explicit formula(3.3) gives precisely Q above. The constant
conversion uses

    2 integral_0^infinity (1-exp(-t/2))alpha(t)dt=log2+pi/2.

The pole integrals give 2Re(M_+ conj(M_-)); both prime-power sums give the
stated real correlation sum. The introduction states the classical Weil
criterion for all complex compact smooth tests. Thus its scope matches T1,
not only the odd or even sector. The published explicit formula and Weil
criterion remain named primary theorem dependencies; their entire classical
proofs are not reconstructed here.

## 9. Evidence, delta, and limits

Full SLACK producer49446bytes/657LF was read and rehashed:
1d658eb3d6d828d3bc651967087dabf8e2f9774d179b02c7607f25c7ffe54588.
Current full SLACK check37796bytes/467LF was rehashed:
14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc.
Its earlier acceptance is context; the transfer proof is rederived above.

Primary formulas read directly on 2026-09-12:
- [Jacobi modular identity, DLMF20.7.32](https://dlmf.nist.gov/20.7#E32).
- [Digamma integral, DLMF5.9.16](https://dlmf.nist.gov/5.9#E16).
- [Euler product, DLMF25.2.11](https://dlmf.nist.gov/25.2#E11).
- [Suzuki, introduction and(3.3)](https://arxiv.org/html/2301.00421).

Classical background used: Fourier inversion/uniqueness, elementary Lebesgue
convergence theorems, completeness of L2, the gamma integral and nonvanishing
of Gamma on Re(s)>0. No RH-equivalent spectral theorem is hidden among these.

Before this audit GOAL_MAT inherited V=>Q only by the SLACK receipt. This note
rederives the source normalization, complete arithmetic pairing, all-test X
limit, finite congruence, and spatial/frequency transfer in one proof.
This is an audit completion at PAPER scope if independently accepted.
It supplies no new proof of V>=0, no result of the pending ODD2 request, and
no reset of the same-obstacle mathematical counter. No new Proshka send.

## 10. Independent audit acceptance

This receipt supersedes the initial pending status, preserving the preceding
14110bytes unchanged. ACCEPTED_PAPER_TRANSFER_AUDIT for Theorem T and its
source normalization/domain proof. The sole read-only checker
`/root/sibling5_check` checked exact SHA256
`8c0ff365de0838fb922a05c21ada76665935998bd6ecae5117f3fd7910703b60`
and returned ACCEPT: Mellin IBP coefficient/boundaries, noncircular X density,
atom jumps, both poles and digamma constant, X limits, finite nonzero
congruence, exact Fourier signs, H in L1 and both PSD transfer directions.
It retained the named DLMF/Suzuki formulas as published dependencies; their
historical full proofs were not reconstructed. Parent also checked the
Jacobi differentiation and all constant factors directly.

The parent additionally read [DLMF5.2(i)](https://dlmf.nist.gov/5.2#i),
including Euler's gamma integral and the explicit nonvanishing statement,
on 2026-09-12. This makes the gamma background source locator explicit; it
does not add a zero-location premise for zeta.

No sign premise was proved. No ODD2 result or no-progress counter reset is
claimed. The active all-test RH goal remains incomplete.
