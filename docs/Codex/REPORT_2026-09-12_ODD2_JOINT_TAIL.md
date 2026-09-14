# Joint tail through the diagonal — PAPER candidate

Status: ACCEPT_JOINT_TAIL_ODD2_ALL_SUFFICIENTLY_LARGE_NODE_PAIRS.
Author: parent mathematical task. No canonical admission or RH claim.
Consumer: actual ODD2 for all sufficiently large positive node pairs,
including arbitrarily small separation and all complex coefficients.
The threshold below is existential, not a computed numerical threshold.

## Source pins and proposed delta

The unchanged f, V, K=V(s,t)-V(s,-t), OD1 and source derivative bounds are
those accepted in REPORT_2026-09-12_ODDCURV_INTAKE.md and its exact response
SHA256 3309c6fb3f5c3a0e20979c14b9a36471e753feed18a42017b4f211fafe6ea840.
Regional ODD2 min4/gap4 is accepted in
REPORT_2026-09-12_ODD2_REGIONAL_INTAKE.md, response SHA256
2281280161631905987633e895c34e980470bbeda517e3bc4c1df2ce2d0e9833.
Base own-branch commit: 2b2c4e10bcb5705118c8b225bf999c11b6f0e2b8.

Proposed new theorem: for each fixed D>0, uniformly for |s-t|<=D and
m=(s+t)/2 tending to infinity,

    C(s,t)=partial_s partial_t log K(s,t) -> sech(s-t)^2.       (T)

In particular there exists M_D such that C>=sech(D)^2/2 whenever m>=M_D
and |s-t|<=D. With D=4 and regional min4/gap4 this proves ODD2 for every
x,y>=S, for one finite S=max(4,M_4). It does not prove global IC, ODD2 on
the axes/remaining small-node region, arbitrary odd matrix sizes, full V PSD
or RH. A new factorization alone would not establish (T); the differentiated
uniform remainder below is the substantive proposed input.

## 1. Full H on its entire domain

Write q=pi exp(2x), C0=4pi^2/A. The full theta series gives, for every real x,

    f(x)=C0 exp(9x/2-q) H(q),
    H(q)=sum_{n>=1}(n^4-3n^2/(2q)) exp(-(n^2-1)q).           (1)

The series and all fixed derivatives converge locally uniformly for q>0.
The accepted evenness f(x)=f(-x) gives the exact reciprocity

    H(q)=(pi/q)^(9/2) exp(q-pi^2/q) H(pi^2/q).               (2)

For q>=pi every summand in (1) is positive. Equation (2) gives H(q)>0
for every q>0. At infinity, for every fixed j>=0,

    (q partial_q)^j [H(q)-1+3/(2q)] = O_j(exp(-2q)).          (3)

For (3), differentiating a summand a fixed number of times produces a
finite sum of polynomial factors in q,n and 1/q multiplying
exp(-(n^2-1)q); for q>=pi, absorb these polynomials into exp(q), and sum
the remaining Gaussian n tail. The n=2 exponent starts at 3q. This proves
the displayed, weaker exp(-2q) bound with a finite j-dependent constant.
Equation (2) and (3) show that H and every Euler derivative are flat at 0.
On compact subintervals of (0,infinity) they are continuous. Consequently

    sup_{q>0} |(q partial_q)^j H(q)| < infinity              (4)

for every fixed j. Also H(q)->1 as q->infinity. No theta mode has been
discarded in (1)-(4).

## 2. A smooth variable at the diagonal

Set d=s-t, m=(s+t)/2, alpha=pi exp(2m), c=cosh(d). Define for c>=1

    B_alpha(c)=H(alpha exp(w)) H(alpha exp(-w)),
    w=arcosh(c),
    phi(c)=arcosh(c)/sqrt(c^2-1),  phi(1)=1.                (5)

The product defining B is even in w. It is smooth as a function of c at 1.
For every fixed pair of nonnegative integers a,b,

    sup_{alpha>0,c>=1}|(alpha partial_alpha)^a
                         partial_c^b B_alpha(c)| < infinity. (6)

Here is a derivative justification, including c=1. If
F_alpha(w)=H(alpha exp(w))H(alpha exp(-w)), all its w derivatives and
mixed Euler-alpha derivatives of any prescribed finite order are bounded
uniformly by (4). For |w|<=1, F is even; writing
F'(w)/sinh(w)=[w/sinh(w)] integral_0^1 F''(tw) dt shows the first c
derivative is smooth and bounded. Iteration, or the even Taylor formula
with integral remainder through order 2b+2, gives the same result for b
derivatives using finitely many bounded w derivatives. For w>=1,
partial_c=(sinh w)^(-1) partial_w has bounded coefficients and bounded
derivatives of every fixed order. This proves (6), also after applying
Euler-alpha derivatives, which commute with partial_c.
The same argument, or its elementary formula at infinity, proves that phi
is smooth with bounded derivatives of every fixed order on [1,infinity).

Fix D>0, C_D=cosh(D). For alpha sufficiently large and c in [1,C_D],
B_alpha(c) is bounded below by a fixed positive constant, since both
arguments of H are at least alpha exp(-D). Its reciprocal and every fixed
mixed derivative in (6) are then uniformly bounded as well.

## 3. Exact Laplace integral for the normalized kernel

Let G(s,t)=K(s,t)/(f(s)f(t)). First the direct term, with u=exp(2v)-1, is

    V(s,t)/(f(s)f(t))
      = integral_0^infinity [m+log(1+u)/2](1+u)^(7/2)
          exp(-2alpha c u) B_{alpha(1+u)}(c)/B_alpha(c) du.  (7)

For the reflected term use evenness to write f(v-t)=f(t-v), and put
w=d+2v. The exponent becomes -2alpha(cosh w-c). Thus

    V(s,-t)/(f(s)f(t))
      = (1/2) integral_d^infinity w exp(-2alpha(cosh w-c))
                      B_alpha(cosh w)/B_alpha(c) dw.

The integrand is odd in w, so the lower endpoint can be changed from d
to |d|, even for negative d. With z=cosh w-c this becomes exactly

    (1/2) integral_0^infinity phi(c+z) exp(-2alpha z)
                           B_alpha(c+z)/B_alpha(c) dz.     (8)

In particular (8) keeps the whole reflected tail, including v>t; (2)
justifies using the same source expression there. At d=0 the substitution
has a zero derivative at its endpoint, but w/sinh(w)->1 makes (8) regular.

Putting z=cu in (7) and subtracting (8) yields

    G = integral_0^infinity exp(-2alpha z) J(m,alpha,c,z) dz,

    J = 1/B_alpha(c) * {
          [m+log(1+z/c)/2](1+z/c)^(7/2)/c
                            * B_{alpha(1+z/c)}(c)
          - phi(c+z) B_alpha(c+z)/2 },

    J(m,alpha,c,0)=m/c-phi(c)/2.                           (9)

## 4. Uniform differentiated remainder

Treat m and alpha as temporarily independent. Let E=alpha partial_alpha.
Equations (6), the lower bound for B_alpha(c), and c>=1 imply that, for
each fixed finite collection of a,b,r and c in [1,C_D],

    |E^a partial_c^b partial_m^r partial_z J|
       <= L_D (m+1)(1+z)^N,  z>=0, m>=1,                 (10)

with one finite L_D and integer N for that collection. It suffices to take
a+b+r<=2; one extra c derivative is allowed where partial_z acts on the
reflected term. Derivatives in m here act only on its explicit linear
occurrence. For the direct B term, differentiating the moving scale uses
partial_z log(alpha(1+z/c))=1/(c+z),
partial_c log(alpha(1+z/c))=-z/[c(c+z)], and their bounded derivatives.
The elementary powers and logarithm have polynomial growth. These facts
prove (10) without a large-z truncation or an unbounded H derivative.

Let R=G-[m/c-phi(c)/2]/(2alpha). Subtracting the exact z=0 value in (9)
and integrating (10) gives, uniformly on the specified c interval,

    |E^a partial_c^b partial_m^r R| <= L'_D (m+1)/alpha^2
                          for a+b+r<=2, alpha>=alpha_D.  (11)

For clarity, E also differentiates exp(-2alpha z). Each such derivative
multiplies that exponential by a fixed polynomial in alpha z. The
integrand after subtracting its z=0 value has the extra factor z from
(10). Substitution t=alpha z bounds each resulting integral by alpha^-2
times a finite polynomial moment of exp(-2t), uniformly for alpha>=1.
This proves all differentiated estimates in (11), not just the value.

Now impose alpha=pi exp(2m), so the actual m derivative is partial_m+2E,
and compose c=cosh d for |d|<=D. The chain rule preserves (11) through
total order two. Therefore

    G = [2m sech(d)-d/sinh(d)]/(4alpha)
                         + O_{C^2(m,d),D}((m+1)/alpha^2), (12)

where d/sinh(d)=1 at zero. In this notation each partial derivative
through total order two of the remainder obeys the same displayed bound.

## 5. Actual curvature and actual ODD2 consumer

Define S(m,d)=2alpha G/m. From (12), through two m,d derivatives,

    S(m,d)=sech(d)-phi(cosh d)/(2m)+O_D(1/alpha),
    S -> sech(d) in uniform C^2 on |d|<=D as m->infinity.   (13)

The limit is bounded below by sech(D)>0. Hence log S and its derivatives
through order two converge uniformly to log sech(d). Since

    log G=log m-log(2alpha)+log S,
    partial_s partial_t=(1/4)partial_m^2-partial_d^2,

and log f(s)+log f(t) has zero mixed derivative, the exact curvature is

    C(s,t)=-1/(4m^2)+(1/4)partial_m^2 log S
                              -partial_d^2 log S.         (14)

Equations (13)-(14) prove (T). Choose finite M_D>=max(1,D) so that the
uniform error from sech(d)^2 is at most sech(D)^2/2 for m>=M_D. This gives
the claimed strictly positive curvature strip, including d=0.

For D=4, set S0=max(4,M_4). If x,y>=S0 and 0<|x-y|<=4, the whole square
between x and y lies inside this strip. The accepted exact rectangle
identity then gives the quantitative statement

    log[K(x,x)K(y,y)/K(x,y)^2] >= sech(4)^2 (x-y)^2/2,
    Delta(x,y) >= K(x,y)^2
                    [exp(sech(4)^2 (x-y)^2/2)-1] > 0.      (15)

For |x-y|>=4 the previously accepted regional theorem applies. At x=y,
Delta=0 exactly. Positive diagonal entries and Delta>=0 prove the actual
two-node Hermitian matrix is PSD on all complex coefficients. The
corresponding original four-node odd V form is exactly twice this form.

Unpaid: a usable numeric value of S0; IC outside the fixed-width strip;
all ODD2 pairs with min(x,y)<S0; full higher-rank odd and even sectors.
No negative witness for actual IC/ODD2/V/Q is asserted. This proof is
existential on a cofinal consumer family, not a finite verification grid.

## Acceptance receipt

Sole read-only independent checker /root/sibling5_check accepted the complete
209-line, 9441-byte candidate with SHA256
c40c40f3bee7c60257f4bf0fddc88be494221ff2b5da10c4bd3748b7e8728f75.
The mathematical text above is unchanged; only its status and this receipt
were added after acceptance. The parent separately rechecked reciprocity
powers, both Laplace Jacobians, the c=1 endpoint, Euler derivatives of the
Laplace exponential, conversion to actual m derivatives, and the complete
ODD2 square/factor2 implication. The checker was not an author of this proof.

Accepted scope is (T), the strictly positive fixed-width joint-tail IC strip,
and its stated cofinal ODD2 consequence using the already accepted regional
theorem. No numeric S0, full-quarter IC, small-node ODD2, higher odd/even
matrix positivity, Lean certification, canonical admission or RH is claimed.
This adds a new actual consumer sign family; it is not a repetition of the
known diagonal Taylor identity or a surrogate integrand-positivity claim.
