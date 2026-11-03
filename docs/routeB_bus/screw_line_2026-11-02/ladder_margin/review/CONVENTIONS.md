# Finite ladder certification, between-node scope, and spectral controls

DIAGNOSTIC_NEVER_A_PROOF. Route B remains CHALLENGER / NOT_RH.
This is a normalization and numerical-certificate scope review. The bounds
below are ordinary analytical error budgets; no global kernel positivity
or RH conclusion is asserted.

## What a finite Arb certificate establishes

Let the exact, distinct, nonzero nodes be t_1,...,t_N in[0,T]. Directed-rounding
interval LDL with strictly positive pivot balls establishes positive
definiteness of that one source matrix K(t_i,t_j). Symbolic node identities,
exact removal of duplicates and the structural node0 matter. A certificate
for a matrix with rounded nodes instead certifies that rounded-node matrix
unless the node error has also been enclosed.

The smallest LDL pivot is not the smallest eigenvalue. If K=L D L^T,
an appropriate finite spectral lower bound is

    lambda_min(K) >= min(D_ii) / (||L^-1||_1 ||L^-1||_infinity).

Both inverse norms need valid upper enclosures before this is an interval
certificate. This distinction remains necessary even when the resulting
bound is too small to support useful between-node perturbations.

The source's shifted prime events occur at t=s+log q. Closing a finite
node family under these shifts samples important source breakpoints; it
does not remove the smooth intervals between them or supply all possible
linear combinations on those intervals. Finite shift closure does not
change the cardinality of the certified mathematical statement.

## Explicit modulus retaining cusp, hinges and poles

For the zeta source and t>=0, write

    g(t)=c_star*t/2 - A(t) - 8(cosh(t/2)-1)
         + sum_(log n<=t) [Lambda(n)/sqrt(n)](t-log n),

    A(t)=sum_(k>=0) (1-exp(-(2k+1/2)t))/(2k+1/2)^2,
    c_star=EulerGamma+log(8*pi)+pi/2.

The archimedean contribution is increasing and concave, with A(0)=0.
For0<=s,t<=T and |s-t|<=epsilon, its difference is at most A(epsilon).
The identity

    A(epsilon)=integral_0^epsilon u*j(u)du
                +epsilon*integral_epsilon^infinity j(u)du,
    j(u)=exp(-u/2)/(1-exp(-2u)),

gives the explicit usable upper budget

    A(epsilon) <= epsilon*[exp(3epsilon/2)/2
                    +atanh(exp(-epsilon/2))+atan(exp(-epsilon/2))].

Here u*j(u)<=exp(3u/2)/2 follows from exp(2u)-1>=2u; the tail integral
is retained exactly. Each arithmetic hinge is globally Lipschitz with
constant Lambda(n)/sqrt(n), including when an interval crosses its birth.
The pole derivative is bounded by4sinh(T/2). Therefore a valid modulus is

    omega_T(epsilon)=epsilon*[exp(3epsilon/2)/2
                         +atanh(exp(-epsilon/2))+atan(exp(-epsilon/2))]
          +epsilon*[c_star/2+4sinh(T/2)
                         +sum_(n<=exp(T)) Lambda(n)/sqrt(n)].

This tends to zero like epsilon log(1/epsilon). It does not pretend that
g has a finite derivative at0. Even extension preserves the same modulus
because ||s|-|t||<=|s-t|. All terms have nonnegative coefficients in this
upper budget, making outward evaluation straightforward.

For DH the same archimedean upper bound is conservative because its jump
kernel has exp(-3u/2) in the numerator. Replace c_star by the absolute
value of the DH source constant, omit the zeta pole term, and use the
sum of absolute DH arithmetic coefficients. For the specified plant add
4*nu*cosh(eta*T)/|w| to the Lipschitz bracket. These replacements are
error budgets for the given source functions, not positivity statements.

If s,t are each moved by at most epsilon inside the same window,

    |K(s,t)-K(s_grid,t_grid)|
      <= omega_T(2epsilon)+2omega_T(epsilon) = E_T(epsilon).

For two N-by-N matrices built from corresponding node lists, this yields
||Delta K||_2<=N*E_T(epsilon). A valid finite eigenvalue margin lambda_* thus
permits that corresponding N-node perturbation only when
lambda_*>N*E_T(epsilon). Neither lambda_* nor N may be silently replaced
by the smallest LDL pivot or an infinite-cardinality quantity.

The table in modulus_budget.csv evaluates this conservative expression
at80decimal digits for T=log3,log5,log7 and epsilon=1/(2M), M32,64.
These particular decimal values are diagnostics, not outward-rounded
intervals. The certificate worker can evaluate the same positive formula
in Arb if a rigorous numerical comparison is desired. The direct source
checks at the cusp, prime-power hinges and fixed interior samples all lie
below the bound; they check normalization, not the universal quantifier.

For M32 the entry budgets are approximately0.6260,0.7720,0.8778. With
the finite shift-closure count upper bounds49,107,166, the corresponding
spectral error budgets are30.676,82.599,145.713. Merely refining to M64
reduces the entry error but also increases the matrix size; those count-based
budgets are31.395,83.686,147.897. These crude continuity budgets are not
promising replacements for a source-relative coercivity estimate.

## Why this does not certify all nodes in a window

An arbitrary finite set can have arbitrarily many nodes, including pairs
arbitrarily close together. Their Euclidean Gram eigenvalues then approach
zero. Node0 is an exact zero direction, and repeated nodes give further
structural zeros. There is no uniform positive Euclidean eigenvalue margin
over all cardinalities and separations, even for a genuinely positive
continuous kernel.

Projecting such a node set to a fixed grid can collapse distinct nodes to
the same grid point. The reference matrix with repeated grid indices is
then singular, so a strict finite Weyl reserve is unavailable. For distinct
projections, the N*E penalty still depends on N. These are quantifier and
normalization obstructions to this particular finite perturbation argument;
they are not counterexamples to kernel positivity.

Thus an Arb certificate on the complete finite ladder, plus the explicit
modulus, remains a certificate for that ladder and possibly specified
finite perturbations satisfying a quantitative margin. It is not a
certificate for all real nodes or all finite cardinalities in[0,T].

The previous passive-section source supplies a different kind of estimate:
for one fixed finite positive past C, all fresh nodes in a sufficiently
short new interval satisfy S>=(beta-rho)M_h when beta-rho>=0. Its lower
bound uses the physical step-function norm M_h, so it accommodates
collisions and arbitrarily many fresh nodes without a Euclidean gap.
However its length depends on the full finite old history. Applying it
after a finite set of anchors does not include every unobserved point in
all earlier grid cells. Gluing local certificates into an entire continuum
window requires the additional uniform or full-operator comparison that
the source explicitly leaves unpaid.

## Spectral fake worlds: density, weights and omitted tails

A real positive frequency pair gamma,-gamma of multiplicity nu contributes

    g_gamma(t)=2nu*(cos(gamma*t)-1)/gamma^2,
    K_gamma(s,t)=2nu/gamma^2 * u_gamma(s) dot u_gamma(t),
    u_gamma(t)=(cos(gamma*t)-1,sin(gamma*t)).

This fixes the pair normalization and the 1/gamma^2 weight. A finite
positive-frequency list of J entries produces a PSD Gram of rank at most2J.
After more than2J nonzero anchored nodes, exact linear dependence forces
zero innovations whenever the previous predictor problem is well posed.
Even before that rank threshold, a finite band-limited feature family can
be extremely ill-conditioned on a short interval. Tiny innovations can
therefore be a truncation/rank artifact rather than a zeta-specific law.
Precision repeats cannot repair a model that has omitted the rough tail.

For a defined all-real positive spectrum, omitting its tail gives a PSD
matrix tail with each diagonal at most

    8*sum_(gamma>H) nu/gamma^2.

The N-node operator norm is consequently at most8N times that sum. Adding
a PSD tail can increase the optimized innovation; a tiny truncated
innovation is not an upper bound for the complete one. The normalized
extension margin changes both its fresh Gram and its coupling, so it
does not inherit a simple monotonic ratio rule from this observation.

For actual zeta, treating every uncomputed zero as a real positive spectral
tail would itself import RH. The unconditional arithmetic g is the
appropriate complete-source reference. A zero-list fake world must be
explicitly defined as an all-real constructed model, with its truncation
and tail status stated separately. DH must not be replaced by an absolute
square sampling Gram at off-line zeros: that erases its signed quartet.

Fair spectral controls should match the positive-frequency counting scale,
pair weights, observation window and mesh; use the same high-height cutoff
and stated tail construction. Repeating larger cutoffs is essential when
the tested innovation is comparable to the omitted-tail budget or the
feature rank is comparable to the node count. A finite cutoff with H*h
small or fixed misses precisely the high-frequency contribution behind
the logarithmic cusp. Agreement of coarse spectral density alone does not
bound that error or control correlations between nearby frequencies.

An all-real positive-spectrum fake world is positive by construction; its
passing a positivity check is not evidence for the zeta arithmetic sign.
Its role is to test whether a proposed quantitative decay or ladder law is
specific to the complete source rather than a generic PSD or truncation
effect. No new universal decay law or between-node sign is supplied here.
