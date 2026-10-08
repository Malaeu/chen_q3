# Exact density pairing and the cost of forgetting arithmetic signs

2026-10-08. Owner-directed next analytical test. Baseline 7c25bdd7.
PAPER D1-D7 independently checked. No new Pro send; RH/SP OPEN.
This is the full N=m source, not a random-prime model or a restricted carrier.

## 1. Exact positive measures and a free endpoint balance

Fix an even moment order r>=4, m>=2^(r-1), L=log m, x=m^(1/(r-1)).
Use the same Pi, Q, V and W=S_-^(r-1) as CCM_PRIME_TRANSITION_TEST.md.
For real t in [x,m], define A(t)=Pi Q(log t)Pi/sqrt(t). In particular A(m)=0.
Changing variables in BOTH continuous terms gives the exact signed source

    V = integral_[x,m] A(t) (dalpha(t)-dbeta(t)),
    alpha=sum_(x<n<=m) Lambda(n) delta_n,
    beta=(1-1/t)1_[x,m](t)dt.                            (D1)

Both measures are nonnegative since x>=2. Every prime-power atom is retained;
an atom at x is excluded, as required by the original short/long convention.
Let Delta=alpha([x,m])-beta([x,m]), and write Delta_+=max(Delta,0),
Delta_-=max(-Delta,0). Then

    alpha'=alpha+Delta_- delta_m,
    beta'=beta+Delta_+ delta_m                            (D2)

have the same finite mass T>0 and still represent exactly V because A(m)=0.
No estimate for Delta has been assumed, and no residual boundary fee is hidden.

Let a(z),b(z), 0<z<T, be the generalized inverse cumulative functions of
alpha',beta'. Pair a(z) with b(z) using Lebesgue measure dz. Its marginals are
exactly alpha',beta', hence

    V=integral_0^T [A(a(z))-A(b(z))]dz.                   (D3)

Thus the requested positive pairs really have been constructed, including
both original continuous terms. The endpoint after subtraction is zero;
the whole nonzero matrix is the sum of paired differences, whose size is
NOT yet estimated by D3 alone.

## 2. Exact optimal scalar distance for the previous derivative certificate

The previous note proves ||A'(t)||<=(1+D_m)t^(-3/2),
D_m=(2+8pi m)/L, on the original full carrier. Set

    F(t)=integral_x^t u^(-3/2)du=2(x^(-1/2)-t^(-1/2)),
    D(t)=alpha([x,t])-beta([x,t])
        =psi(t)-psi(x)-(t-x)+log(t/x), x<=t<m.

The endpoint-balancing atoms affect neither D(t) for t<m nor the next integral.
For any positive coupling pi of alpha',beta', layer-cake gives

    integral |F(u)-F(v)| dpi(u,v)
      =integral_x^m t^(-3/2) [mass crossing t in either direction]dt
      >= J_m:=integral_x^m |D(t)|t^(-3/2)dt.              (D4)

The monotone pairing D3 has no crossings in opposite directions at any cut,
so it attains equality. This proves the relevant one-dimensional transport
formula directly; it does not depend on a guessed distribution law for primes.
The scalar-distance certificate from the previous derivative estimate is
therefore exactly

    E_deriv=(1+D_m)J_m,
    ||V||<=E_deriv,  |Tr(WV)|<=Tr(W)E_deriv.              (D5)

Equivalently, entrywise Stieltjes integration by parts gives
V=-integral_x^m D(t) A'(t)dt; the lower endpoint has D(x)=0 and the upper
endpoint has A(m)=0. D5 takes absolute values in this exact signed integral.
A lower bound on E_deriv is NOT a lower bound on ||V|| or the signed pairing.
Nor is it a lower bound on the optimal actual matrix-distance cost
integral ||A(u)-A(v)||dpi: the derivative distance is only its majorant.

## 3. An elementary granularity obstruction to this scalar certificate

Between consecutive integers, the atomic cumulative alpha is constant and

    D'(t)=-(1-1/t)<=-1/2, t>=2.

For any full unit cell [n,n+1] and any additive value of D at its left edge,

    integral_n^(n+1) |D(t)|dt >=1/8.                     (D6)

Proof: if D has a zero z in that cell, |D(t)|>=|t-z|/2 and the integral is
at least [(z-n)^2+(n+1-z)^2]/4>=1/8. If it has no zero, the same slope bound
and the nearest endpoint give at least 1/4. Endpoints do not change the integral.
This uses integer support only, not an unproved fact about prime gaps.

The interval [2x,4x] lies in [x,m] because m/x>=2^(r-2)>=4. It contains
floor(4x)-ceil(2x)>=2x-2>=x full unit cells. On it t^(-3/2)>=(4x)^(-3/2).
Consequently

    J_m>=1/(64 sqrt(x)),
    E_deriv >= (pi/8) m/(L sqrt(x))
             = (pi/8) m^(1-1/[2(r-1)])/L.              (D7)

Thus this particular uniform derivative-distance certificate cannot have a
polylogarithmic total cost, even for ideally arranged positive integer atoms.
Its optimistic power beta=1-1/[2(r-1)] would already give a Young-return
power 1+r beta, dependent on r. This is a failure of this certificate,
not a proof that sharper matrix pairing, signed grouping, or RH is impossible.
Changing positive matching alone cannot improve D4 in the same scalar metric;
monotone pairing is already optimal for it.

## 4. What can still change the estimate

The useful next object must exploit something D5 discarded: sign or phase
cancellation among several paired differences, or a sharper estimate for the
actual W, not a uniform Lipschitz bound for every PSD W. Prime density can help
with the cumulative imbalance, but cannot remove the unit-cell effect in D6.
Ramanujan sums are relevant as an exact way to group divisibility phases
BEFORE absolute values. They are not permission to replace Lambda by a
truncated expansion and forget the high-denominator return.

A bounded next candidate must exhibit an exact decomposition V=V_model+R,
a proved one-sided estimate for V_model, and a signed estimate for Tr(WR)
with the actual adaptive W and all continuous terms. A density approximation
with only unweighted L2 accuracy has not yet met this interface.

## Search evidence and status

Three local ask.sh queries (Kantorovich Rubinstein arithmetic signed measure;
monotone transport prime counting density; Ramanujan density approximation
weighted matching) returned ASK_STATUS: INCOMPLETE because q3_docs semantic
freshness validation failed. Literal local source definitions were read.
This is not evidence of literature absence. Existing scalar Mobius quadrature
is a different calculation and is not rerun here.

External discovery reference: S. S. Vallander, Calculation of the Wasserstein
distance between probability distributions on the line, Theory Probab. Appl.
18(4),784-786 (1974), DOI 10.1137/1118101. The publisher/index abstract describes
the cumulative-distribution formula; original full text was not recovered in
this pass. Therefore it is EXCLUDED as an archived verified source card.
D4 is proved directly above rather than importing that unrecovered theorem.
URL: https://www.mathnet.ru/php/archive.phtml?jrnid=tvp&option_lang=eng&paperid=4387&wshow=paper

During this test the concurrent Q6 workflow completed its independent audit
and committed 6ebccfe9. CCM_MOMENT_Q06_CONCLUSION.md rejects a standalone
product total-variation estimate and retains the signed credits. That separate
result is NOT a premise of D1-D7. Q6 is processed; no Q7 was sent by this task.

## Independent audit

Read-only nonauthor density_pairing_audit returned PASS for D1-D7, including
both continuous densities, endpoint balancing, optimal scalar coupling, real-x
cell count, constants and restricted conclusion. Reviewed pre-verdict file
SHA256 c8eada11e43ed8329aaa641a96fd45995fda69817833a5453db0e7216f3f75ba.
The cell values in D6 are interior one-sided limits; endpoint atom jumps do
not affect its integral. No lower bound for the matrix norm was proved.

## 5. A concrete Ramanujan square-density construction

This bounded algebraic test passed an independent read-only check. Let R>=1 be an integer, P_R=lcm(1,...,R), and define

    lambda_R(n)=sum_(q<=R) mu(q)c_q(n)/phi(q),
    C_R=sum_(q<=R) mu(q)^2/phi(q)>0,
    nu_R(n)=lambda_R(n)^2/C_R.                            (R1)

All c_q(n) are real. On a complete residue period P_R, elementary character
orthogonality gives

    average c_q(n)c_k(n)=1_(q=k)phi(q),
    average lambda_R=1, average nu_R=1, nu_R>=0.           (R2)

Indeed c_q is the sum of primitive additive characters a/q; a/q+b/k is an
integer precisely when q=k and b=-a modulo q (including q=k=1). No assertion
of uniform prime distribution is involved in this finite identity.

For EVERY prime p>R, c_q(p)=mu(q) for q<=R. Consequently

    lambda_R(p)=C_R, nu_R(p)=C_R.

The nonnegative model

    b_R(n)=log(n)*lambda_R(n)^2/C_R^2, n>=2               (R3)

therefore agrees EXACTLY with Lambda on every prime p>R. It generally gives
positive weights to composites too; it is not a proved approximation error
bound. R2 is a full-period mean for nu_R, not a short-interval mean for b_R.
The growing period P_R and the extra log n factor cannot be ignored.

For every n with no prime divisor <=R, the same calculation gives
lambda_R(n)=C_R and b_R(n)=log n. It includes products of two distinct primes
larger than R, where Lambda(n)=0. The construction preserves those primes
by also admitting these rough composites. This is the precise extra source
to control, not an unspecified symbolic remainder.

Its full exact return is

    V = [sum_(x<n<=m) b_R(n) A(n)-integral_x^m A(t)(1-1/t)dt]
          + sum_(x<n<=m) [Lambda(n)-b_R(n)]A(n).          (R4)

Every n and prime power stays present. There is no assumption that b_R
majorizes Lambda at all small primes or prime powers. No convergence of an
infinite Ramanujan series is used.

A cheap sign test prevents an invalid use of the nonnegative density:
set r=4, m=225, R=2, n=15, v=(e_1-e_(-1))/sqrt(2), W0=vv*.
Then Pi v=v, log n=L/2, and

    Q(log15)_(1,1)=Q(log15)_(-1,-1)=-1,
    Q(log15)_(1,-1)=0,
    v*A(15)v=-1/sqrt(15).

Here lambda_2(15)=2, C_2=2, b_2(15)=log15, Lambda(15)=0, and
225^(1/3)<15<225. Thus this positive composite density alone contributes
-log15/sqrt15 in that actual projected quadratic form. Pointwise positive
extra density does not give a positive matrix contribution. This refutes
term-by-term PSD domination, NOT the sign of the full summed model error and
NOT a claim about the actual W=S_-^3.

Decision: retain R4 as an exact, positive-density candidate with primewise
agreement. Its unresolved input is the SIGNED rough-composite contribution,
together with the rest of R4 and an independently bounded model endpoint.
Do not turn positivity of b_R into matrix positivity. The next analytical
map should group the Ramanujan phases of those composite terms before any
absolute-value bound; a new sufficient hypothesis must be derived, not assumed.

## 6. External suppliers checked against this construction

### Ramanujan local density: Laporta (2022)

Original: https://arxiv.org/pdf/2204.01581v1,
On Ramanujan expansions and primes in arithmetic progressions,
archive docs/routeB_bus/litreview/pdfs/2204.01581v1.pdf,
SHA256 f79ed7856dc9dd073d44c7ff6112a117e1bac34cb22322b1ab6d34e4bcad9608.
Root read equations (4)-(7), pp.2-3, and the conditional Theorem 1.
Quote, equation (7) discussion: "deviation of the Ramanujan sum".
Its exact reduced-residue centering is

    average_(a mod q, (a,q)=1) c_q(a+h)=mu(q)c_q(h)/phi(q).

Its finite Lambda_N expansion agrees with the complete-cutoff identity already
in our screen. Theorem 1 requires a Delange summability hypothesis on a shifted
Lambda correlation. No proof of that hypothesis for our adaptive CCM pairing
was supplied. This is a useful exact centering identity, not an unconditional
signed estimate. The shifts, residue averaging and actual rho_W coefficients
still require a complete map. We do not discard the research goal merely
because it is strong; we do not import its open hypothesis as a premise.
The source discovery was independently read by ramanujan_density_supplier;
the elementary R1-R4 construction above is proved directly here.

### Density on short intervals: Guth--Maynard (2026 version)

Original: https://arxiv.org/pdf/2405.20552v2,
New large value estimates for Dirichlet polynomials,
published https://annals.math.princeton.edu/2026/203-2/p06,
existing archive docs/routeB_bus/litreview/pdfs/2405.20552.pdf,
SHA256 915392cf7d0ecd108479814a9a1481e23423ef63415776471cec3975ae482cae.
Root checked Corollary 1.4, printed/PDF page3; v2 revised2026-04-07.
Quote: "Count of primes in 'almost-all' short intervals".
For fixed epsilon>0 it gives prime counts for lengths
X^(2/15+epsilon)<=y<=X^0.99 at all but
O(X exp(-(log X)^(1/4))) integer starts in [X,2X].
This is unconditional density information, not zero exclusion or arbitrary
adaptive-weight control.

On t~X our literal modes have phases 2pi j log(t)/L, |j|<=m;
the highest-mode local wavelength is of order XL/m, at X=m of order L.
The theorem's cells are much longer than this. Knowledge of each cell's
prime mass alone does not control its oscillatory weighted sum. The actual
W might suppress high modes, but no such suppression is established here;
exceptional starts must also be paid. A second-moment/Fourier envelope returns
only the previously known square-root-m scale and a moment power depending
on r. It supplies no new full floor.

Nine total local shelf queries across root and both researchers returned
INCOMPLETE due to semantic-index freshness. Original external PDFs and actual
source formulas were therefore checked directly. This is bounded source-map
research, not an exhaustive absence claim or an audit of entire papers.

## 7. A model endpoint that can actually be evaluated on a smooth upper block

After the concurrent commit 7a7d7986, root read its independently checked
CCM_TRANSPORT_QUADRATURE_CONTROL.md. Its weight-one Poisson calculation suggests
this further finite Ramanujan calculation; it does NOT replace Lambda by one.
Let chi in C_c^infinity((1/2,1)) be fixed, and restrict R to

    1<=R, R^2<=L/8.

Expand nu_R as a finite sum of additive characters exp(2pi i theta n).
Its zero-frequency coefficient is exactly1 by R2. Every nonzero frequency
has reduced denominator <=R^2, and the sum of absolute coefficients is
at most R^2/C_R: the lambda_R expansion has coefficient l1 norm
sum_(q<=R)|mu(q)|<=R before squaring.

For the literal uncompressed Q, define

    E_nu=sum_n chi(n/m)nu_R(n) Q(log n)/sqrt(n)
          -integral chi(t/m)Q(log t)/sqrt(t)dt.

For every fixed integer J>=2, finite character expansion and Poisson summation
prove

    ||E_nu||<=C_(chi,J) m^(3/2-J) R^(2J+2)/C_R.           (R5)

Proof: for |omega|<=2pi m/L, rescale t=my, xi=omega/m. The Fourier integral
for character theta and Poisson integer h has phase

    m[ xi log y + 2pi(theta-h)y ].

If delta=theta-h !=0, then |delta|>=1/R^2 and
|xi/y|<=4pi/L<=(pi/2)|delta| on the support. Hence the phase derivative in
brackets has magnitude >=(3pi/2)|delta|. Its higher derivatives are bounded
by constants times |delta|. Integrating by parts J times gives a scalar bound
C_(chi,J)m^(1/2-J)|delta|^(-J), with no boundary terms. Summing over h costs
at most C_J R^(2J). The case theta=0,h=0 is precisely the retained integral;
all other integer h are treated in the same way. The actual diagonal Q
amplitude contains -2log(y)/L and has uniformly bounded derivatives.
Offdiagonal coefficients are bounded since |j-k|>=1. Multiply by the character
coefficient l1 bound and d=2m+1 for the row-sum estimate to obtain R5.
Orthogonal compression by Pi (or the actual restricted P) preserves R5.

The prime-matching model b_R=(log n/C_R)nu_R has the corresponding explicitly
smooth endpoint

    B_model=sum_n chi(n/m)b_R(n) A(n)
      =integral chi(t/m)[log(t)/C_R] A(t)dt + E_b,
    ||E_b||<=C_(chi,J) m^(3/2-J) L R^(2J+2)/C_R^2.       (R6)

The extra amplitude (L+log y)/C_R costs at most C L/C_R in every fixed
derivative norm. With R^2<=L/8, both errors decay faster than any fixed
negative power of m by choosing fixed J sufficiently large first.
These are bounds for the model on this smooth upper block, not the full V.

For m sufficiently large that R<m/2, b_R agrees with Lambda at every prime
in this block. The exact full arithmetic block therefore becomes

    sum_n chi(n/m)Lambda(n)A(n)
      -integral chi(t/m)(1-1/t)A(t)dt
    =integral chi(t/m)[log(t)/C_R-1+1/t]A(t)dt + E_b
       +sum_n chi(n/m)[Lambda(n)-b_R(n)]A(n).            (R7)

The last sum contains composites and prime powers, but NO primes in this
upper block. For rough integers with at least two distinct prime divisors the coefficient
is exactly -log n; for rough prime powers p^k it is -(k-1)log p. This
answers the construction question locally: the model is explicit and its
quadrature error is controlled. The smooth integral in R7 is retained; it is
not claimed small or favorable. The remaining signed composite term must be
estimated jointly with that smooth integral. Their cancellation is not proved.
Lower dyadic blocks and the complete source return are also still required.
No arbitrary high cutoff R or full-period averaging is used in R5-R7.

## Extension audit and integration

The same independent nonauthor density_pairing_audit separately checked
section5 (R1-R4 and m225 counterexample) and section7 (R5-R7). Algebra,
cutoffs, frequency spacing, all-mode bounds and source return passed. The
review caught an overbroad sentence about rough composites: the exact
coefficient is -log n only with at least two distinct prime divisors; rough
prime powers have -(k-1)log p. That sentence is corrected above; R7 always
retained the exact Lambda(n)-b_R(n). No full signed estimate was proved.
