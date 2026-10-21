# Post-Q09: test a mean-square supplier before claiming easier cancellation

2026-10-21. Original full CCM sparse P, N=m,L=log m,M=floor(m^epsilon),
fixed epsilon. No new full power, no Q10 send. Independent bounded source/bridge review PASS; no Lean/Arb claim.
This is a supplier-strength audit, not a new RH criterion discovery.

## Exact object and source-preserving bridge

The desired one-sided form is S=P A_prime P. Write
H_m(x)=P Q_M(log x)P/sqrt(x), E(x)=psi(x)-(x-1).
All prime powers and all mixed entries are retained; P is fixed at this m.
The already checked full-source Abel identity and derivative bound are

 S=-P H_decay P-integral_1^m E(x) H_m'(x) dx,
 ||H_m'(x)||<=C(1+Omega)x^(-3/2), Omega=2pi M/L.

Endpoint terms are zero because E(1)=0 and Q_M(L)=0. References:
CCM_C5_CANCELLATION_LITERATURE_AUDIT.md, Candidate1;
CCM_CONTINUOUS_RANK_TWO_TEST.md. H_decay is positive, norm<=4.
No dyadic boundary terms are deleted: split the already integrated expression,
not separate integrations by parts on each dyadic block.

Define J_E(X)=integral_X^(2X)|E(x)|^2 dx. For any unit c in ran P,
Cauchy on a block contained in[X,2X] gives

 |integral E(x)<c,H_m'(x)c>dx|
 <=C(1+Omega) sqrt(J_E(X))/X.

This is uniform over c at the same m. It is not an average over vectors or m.
If J_E(X)<=C_theta X^(2theta+1), fixed1/2<theta<1, dyadic summation gives

 S <= C_theta(1+Omega)m^(theta-1/2)P.

Finite initial blocks are covered by the constant. At theta=1/2 an extra
log m is needed. The power is theta-1/2+epsilon. Short/arch/F2 returns are
exactly those of Q09: short once only for scalar T, arch50L+8 for direct K,
F2 only for V. Absolute Cauchy is sufficient, not necessary for the source.

## Why the required cumulative variance is not a supplied weaker premise

Suppose for every delta>0, all sufficiently large dyadic X satisfy
J_E(X)<=C_delta X^(2+2delta). This family is already RH-equivalent.
Here is the forward argument, without extracting a pointwise bound from L2.
For any fixed theta=1/2+delta, block Cauchy gives, sigma>theta,

 integral_X^(2X)|E(x)|x^(-sigma-1)dx <=C_theta X^(theta-sigma).

The Mellin integral F(s)=integral_1^infinity E(x)x^(-s-1)dx therefore
converges locally uniformly and is holomorphic for Re s>theta.
Initially for Re s>1, absolute Dirichlet convergence and integration give

 F(s)=-zeta'(s)/(s zeta(s))-1/(s-1)+1/s.

Consequently -zeta'/zeta=sF(s)+s/(s-1)-1 extends meromorphically to
Re s>theta with no poles except the known one at1. A zeta zero in that
region would force a nonremovable logarithmic-derivative pole, contradiction.
Taking every fixed delta>0 and using the functional equation gives RH.
This is a conditional implication, not proof of the variance hypothesis.

Conversely RH gives E(x)=O_delta(x^(1/2+delta)) for each delta>0, hence
J_E(X)=O_delta(X^(2+2delta)). The pointwise RH criterion is the existing
DLMF25.16.4 source, rechecked2026-10-21:
https://dlmf.nist.gov/25.16#E4 . Quote: "for every" epsilon>0.
Exact psi definition25.16.1 includes every prime power. The archived source
and its hash are already in CCM_LONG_MOBIUS_PRIMITIVE_TEST.md.

This extends the shelf's already known absolute-primitive warning to the
proposed cumulative L2 replacement; it is not a second independent
arithmetic mechanism. RH-equivalence is NOT a reason to declare the route
impossible, but it forbids treating the needed variance as a weaker known
input without an actual proof.

## Negative control and remaining distinction

Synthetic E(x)=x^sigma-1, fixed1/2<sigma<1, has J_E(X) of orderX^(2sigma+1)
and Mellin pole at s=sigma. It fails the required variance family. This is
outside the actual arithmetic class, not a counterexample to primes/CCM.
Ordinary PNT bounds only give cumulative J_E(X)<=C X^3 exp(-c sqrt(log X));
the block bridge retains half-power, with the band derivative cost.

Short-interval variance integral |psi(x+h)-psi(x)-h|² dx is a DIFFERENT
object. It cannot replace J_E in the above line without smoothing/inversion,
all boundary terms and a full quantitative return. A published conditional
Selberg bound cannot silently become an unconditional cumulative supplier.
Actual coupled signed testing can be weaker than absolute L2 Cauchy; it
remains the intended source target. No full-source route is killed.

## Concrete first-order short-interval transfer (hypothetical input test)

To avoid merely naming the missing smoothing bridge, let w(x)=chi_X(x)H_m(x)
on a dyadic block X>=2, with a bounded-overlap smooth partition, support
[X,2X], |chi_X'|<=C/X. Extend H_m by zero for x>m. Its value at m is zero,
so the extended weight is Lipschitz, although higher derivatives need not
match. On this block ||w||<=C/sqrt(X), Lip(w)<=C(1+Omega)X^(-3/2).
The fixed initial range can be paid directly. Use1<=h<=X and define

 w_h(t)=(1/h)integral_(t-h)^t w(x) dx.

Fubini for the finite signed measure dE gives the EXACT identity

 integral w_h(t)dE(t)
 =(1/h)integral w(x)[E(x+h)-E(x)]dx.

If J_h(X)=integral_X^(2X)|E(x+h)-E(x)|²dx, then this piece costs
C sqrt(J_h(X))/h in operator norm. The reconstruction costs

 ||integral(w-w_h)dE||<=C h(1+Omega)/sqrt(X),

using the elementary total mass dpsi+dx on[X,2X+h]. The smoothed weight may
reach beyond m; all such atoms are included in this error and cancel in the
exact recombination. They are not a change of the source cutoff. Partition
terms and endpoint m are kept; this uses no higher-jet assumption.

Even the HYPOTHETICAL strong variance J_h(X)<=C hX log²(2X) gives only

 C[sqrt(X/h)log(2X)+h(1+Omega)/sqrt(X)].

Ignoring logarithms, optimizing this available budget chooses
h=X^(2/3)(1+Omega)^(-2/3) and costs X^(1/6)(1+Omega)^(1/3).
Blocks where this h<1 are paid directly, total O(sqrt(1+Omega)); bounded
overlap and dyadic summation add logs. At the top scale the power is
1/6+epsilon/3, not a power tending to zero. This is a lower limitation of
THIS displayed upper-budget optimization, not an actual CCM lower bound.
The strong variance is not asserted unconditionally or consumed as a proof.
Higher-order smoothing or direct signed coupling is not ruled out here.
If only J_h<=C_A h²X/log^A X is supplied, the first term still costs
sqrt(X)/log^(A/2)X, independent of h; no fixed saving results.

This is a second substantive post-Q09 bridge test, distinct from the
second-moment cap: a real source-preserving local-average reconstruction
has now been priced. The cumulative RH-strength observation above is only
a warning about a different supplier, not counted as a separate attempt.
Independent bounded source/bridge review by q10_average_supplier: PASS on
the Abel/Cauchy bridge, Mellin implication and first-order smoothing return.
Root checked the primary-source hypothesis separately. No Q10 sent.

## Primary-source crosswalk (bounded, not an unconditional supplier)

Brent, Platt and Trudgian, The mean square of the error term in the prime
number theorem, J. Number Theory238 (2022),740–762,
https://doi.org/10.1016/j.jnt.2021.09.016 . Author-hosted final PDF:
https://maths-people.anu.edu.au/~brent/pd/rpb274-final.pdf .
Archive: sources/brent_platt_trudgian_2008_06140_final.pdf;
SHA256: 4be3667cbe07ab6a24930e8835923362ae12af946b622fa73c89fd654e9fae34.

Page741, definition(2) uses I(X)=integral_X^(2X)(psi(x)-x)^2 dx.
Theorem1 explicitly says "Assume the Riemann hypothesis". Its eventual
upper bound is I(X)/X²<=0.8603; the accompanying lower bound is
unconditional. Neither that lower bound nor the title supplies the needed
unconditional upper estimate. This source concerns cumulative error, not J_h.
Our shift E=psi-x+1 satisfies J_E<=2I+2X. Thus its conditional upper gives
O((1+Omega)log m)=O(m^epsilon) after the full dyadic bridge, still conditional
on RH. The source does not discharge our arithmetic obligation.

Bounded shelf queries returned INCOMPLETE because of q3_docs freshness;
this is not absence of literature. No verified unconditional supplier was
found in this bounded check. The mathematical route remains OPEN.
