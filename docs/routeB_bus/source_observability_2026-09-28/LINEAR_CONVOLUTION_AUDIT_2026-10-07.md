# Rollover answer1: exact cofactor collapse and total-variation obstruction

Source: PROSHKA_LINEAR_CONVOLUTION_INLINE_2026-10-07.md.
Question: GROWTH_ROLLOVER_QUESTION1_2026-10-07.md and its byte-exact pack.
Same full complex carrier, same original eventual cells, SP/G1/G3/RH OPEN.

## Quadrature, checked independently once

growth_symbol_attempt checked inline§2 and the full preview§4 constant ledger.
For X=m/U,z=ceil X^(1/3),V0=X/z<=V<=X, a nonempty dyadic w-box R
forces d<=m/(aR). Q10 odd discrepancy is halved to512(t^(1/6)+R^(1/4)+1).
Partial summation by log(dw) costs2L with every clipped endpoint retained.
Sum d^-1/2<=2sqrt(m/(aR)), then int |drho|/a<=2h_U(1+L), gives
4096h_U L(1+L)sqrt m[(t^(1/6)+1)R^-1/2+R^-1/4].
Geometric sums<4V^-1/2 and<7V^-1/4 prove the primitive bound; factor4
from the accepted joint d,h map pays the whole carrier including cross modes.
Low |t|<=V/4 costs<=512h_U(1+L)^2sqrt m/V. V=X has zero exact error.
At V0, E_V<=2e6h_U m^(1/3)L^(13/6) eventually. This is an additional
component budget, not a floor; Delta10 is retained. Pass.

## Root independent pass: complete residual atoms and TV kill

Root read inline§4 and complete preview§8, including its elementary
central-binomial proof of the quantitative dyadic prime count.
Let R0=sqrt(X)/16. Prime intervals (U,2U],(R0,2R0],(4R0,8R0] are
disjoint eventually; choose ell,p,q respectively and n=ell*p*q.
Then m/64<n<=m/8, p,q>z, all three single primes lie in(U,A0),
and every pair product exceeds A0=ceil sqrt m. For example
ell*p>sqrt(m)*sqrt(U)/16>A0 eventually, and pq>X/64>A0.
Conversely ell*p,ell*q<V0 eventually, because their ratio to V0 is
O(m^(-1/6)U^(7/6)). All upper ceilings are absorbed in eventual thresholds.
The only original atomic a-divisors are ell,p,q, each with alpha_U=-1.
For pq the only possible cofactor d<X/V<=z in the collapsed long term
is1, since p,q>z; beta_V(pq)=-log(pq)*1_(pq>V).
For ell*p and ell*q belowV, beta_V=Lambda=0.
Thus the COMPLETE residual atom is
 tau_V({n})=[6+log(pq)*1_(pq>V)]/sqrt n,
including the three discrete -2 terms. The continuous a-measure and
Gamma_V dx are nonatomic after multiplication, so cannot cancel this atom.
The Q-correction atom is -log(pq)*1_(pq>V)/sqrt n; their sum is exactly
sigma_*({n})=6/sqrt n. This is not the atom of the complete original Weil
measure: the other components remain in F10. No carrier witness is inferred.

For completeness, the elementary prime count used by the answer is sound.
Central binomial bounds give theta(N)<=theta(ceil(N/2))+N log2;
iteration gives theta(x)<=x log4+O(logx). In binom(2n,n), primes<=sqrt(2n)
cost at most(2n)^sqrt(2n), primes in(2n/3,n] cost nothing, and remaining
primes<=n cost at most exp(theta(2n/3)). Since binom(2n,n)>=4^n/(2n+1),
 theta(2n)-theta(n)>=(n/3)log4-O(sqrt n log n).
Dividing by log(2n) gives at least R/(8logR) primes in(R,2R] eventually;
rounding real R changes only boundedly many endpoints and the constant has slack.
Unique factorization across the disjoint intervals makes all products distinct.
Their count is at least U*R0*(4R0)/(8^3 logU logR0 log(4R0))
 >=m/(32768L²logU).
Each atom is>=6/sqrt m, so the weaker claimed lower bound
 ||tau_V||TV>=2^-16 sqrt m/(L²logU)
holds uniformly for ALL V in[V0,X]. If V<=X/128, pq>X/64>V and
log(pq)>=L/2 eventually, giving2^-16 sqrt m/(L logU).
Therefore no cutoff choice in this family admits TV<=C m^eta for fixed
eta<1/2 eventually. This kills ONLY the total-variation sufficient bound.
It says nothing about a lower bound for ||C[tau_V]|| or actual Schur sign.
No RH, prime-pair conjecture, density of exceptional vectors or atom test
inside the carrier is assumed. Root pass: accepted in this precise scope.

## Own input retained for the next question

LINEAR_SECTOR_CANCELLATION_OWN_2026-10-07.md proves, with one independent
check, that exact sector cancellation already occurs at b=q p³ for growing
free cutoff6<=T<=X^(1/4)/4: short coefficient=-logq, long=+logq.
This is a different (smaller) cutoff range than the new V>=V0~X^(2/3).
Do not use this witness as a contradiction to the new cofactor identity.
It supplies a source-specific check against losing signed recombination.

## Independent algebra pass

causal_algebra_audit passed §§1,3,5–6 once: the long nonlog positions
supply +mu(q)logq; the two-factor formula has no z-cutoff on its first
Möbius variable; Gamma has Jacobian1/a and strict a<x/V; odd support and
continuous A_U da remain. Schur signs and the unchanged J_r are correct.
The Mellin polynomial equality is coefficientwise through b<=X only.
The coarse TV upper bound32h_U(1+L)^3sqrt m is valid but not a signed bound.
Together with the separately checked quadrature and root TV proof, answer1
is accepted PAPER in its stated scope. SP/G1/G3/RH remain OPEN.

## Alias return and selected bounded test

mobius_source_audit searched finite Dirichlet/Möbius products, finite causal
inverse/commutator with hyperbolic cutoff, and Poisson–Mellin odd-lattice
endpoint formulas. All three fresh shelf queries were INCOMPLETE (freshness
failure), not evidence of absence. The bounded lookup found no new primary
supplier for Eq17 plus the original a-flux, compensator and actual J_r.
The worked quadrature mechanism only pays sigma_Q, not tau. The previous
causal-dressing source inequality remains open and inverse transfer is killed.
Root's JOINT_MELLIN_OWN attempt, independently checked once, preserves the
finite product exactly but shows why inversion/nilpotence alone supplies no
sign. Question2 executes the complete signed product test with cutoff tails,
all carrier cross modes and the entire Schur error budget retained.
