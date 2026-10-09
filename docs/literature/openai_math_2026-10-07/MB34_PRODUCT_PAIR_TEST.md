# MB34 product regrouping: cubic divisor phase, retained reciprocal poles

2026-10-09. Own bounded attempt after aa83cc84. Independent
mobius_short_transfer P1–P3 PASS (P3 only under its explicit hypothetical
uniform inverse bounds). RH/SP/MB34 OPEN; no Pro question sent.

The remaining task is a joint upper bound, not eliminating an algebraic
remainder. Consumer: original Q1 MB29–MB34, same good Eisenstein ideals,
Omega-lambda, row units, all zero masks and common derivative profiles.
Test: combine two Mobius columns before estimating either one.

## P1. Exact product and common-divisor coordinates

For squarefree b,c write b=gn,c=gm, where g,n,m are pairwise coprime
and squarefree. Put k=nm. Then k is squarefree, (g,k)=1, m|k, and b!=c
is exactly k!=1. Ordered divisors m retain both original orientations.
The signs and amplifier masks become

    mu(b)mu(c)=mu(k),       w_P(bc)=w_P(gk).

On a fixed row v put psi_v(n)=nu(n)chi_n(v)^epsilon, with the original
zero extension. Define the finite divisor sum

    C_v(g,k;L)=sum_(m|k) conjugate(psi_v(m))^2
        W(q_g q_k/(q_m L)) conjugate(W(q_g q_m/L)).

Then the original ordered pair factor is exactly

    mu(k) 1_((v,g)=1) psi_v(k) C_v(g,k;L).

No inverse of a zero character is taken. The factor psi_v(k) already
annihilates rows sharing a prime with k; common-g zeros are explicit.
Thus MB29 is L^-1 Re sum_(g,k sf, (g,k)=1, k!=1) mu(k) times

    [w_P(gk) sum_(u sixth-free) rho(q_u/U) 1_((u,g)=1)
         psi_u(k) C_u(g,k;L)
     -lambda sum_(v in V_H) 1_((v,g)=1) psi_v(k) C_v(g,k;L)].

The original factor nu(g) cancels against its conjugate. Every unit orbit
is still summed; no new unit projector or factor six is inserted. The
diagonal k=1 is exactly the already paid b=c term, not another free credit.
Support implies q_g^2 q_k is between alpha²L² and beta²L², while both
individual profile conditions remain. They cannot be replaced by product
support alone. The character part conjugate(chi_m)^2 is cubic; the fixed
nu(m) twist need not be cubic. The outer psi_v(k) is still present.

This exposes a cubic divisor sum, but no sign: even the unwindowed
one-prime divisor sum combined with psi(p) is psi(p)+conjugate(psi(p)),
which takes both signs. This is a local algebraic negative control, not
a counterexample on the original averaged row family. Absolute summation
still costs at most the old crude PUL envelope, without a new exponent.

## P2. Exact coprime Euler factorization for one frozen row

Fix g and its coprimality mask first. Let psi be the original completely
multiplicative row character including that fixed mask. On every good
prime |psi(p)| is zero or one. For Re s,Re t>1 the absolutely convergent
coprime two-column series is

    Z_psi(s,t)=sum_((n,m)=1) mu(n)mu(m)psi(n)conjugate(psi(m))
                  /(q_n^s q_m^t) = product_p (1-a_p-b_p),
    a_p=psi(p)q_p^-s,   b_p=conjugate(psi(p))q_p^-t.

Write L_psi(s)=product_(psi(p)!=0)(1-a_p)^-1 and let zeta_mask use
the same surviving primes. Direct local algebra gives

    Z_psi(s,t)=K_psi(s,t)/[L_psi(s)L_conjugate(psi)(t)zeta_mask(s+t)],
    K_psi=product_p (1-a_p-b_p)/[(1-a_p)(1-b_p)(1-a_p b_p)].

The difference of the local numerator and denominator is
-(a_p² b_p+a_p b_p²-a_p² b_p²). Hence K converges normally on
Re s,Re t>0, 2Re s+Re t>1, Re s+2Re t>1. On fixed compact margins
its convergence bounds are uniform under deleting any primes. The finite
early factors can vanish in this general domain; no global nonvanishing
is claimed there. This product statement does not continue either L.

On t=conjugate(s), Re s=sigma>=1/2, good prime norms are at least7.
Every K factor is positive: numerator1-2Re(a_p)>=1-2/sqrt(7)>0,
denominator |1-a_p|²(1-|a_p|²)>0. The log of each factor is
O(q_p^-3sigma), uniformly, so K is bounded above and away from zero
uniformly in height and deleted primes on this diagonal half-plane.

Consequently a zero of L_psi at s0 with Re s0>1/2 is NOT cancelled by
this correction: K(s0,conjugate(s0)) is nonzero and zeta_mask(2Re s0)
is finite and positive. Any meromorphic continuation using the usual
Hecke L-functions retains that pole. Claiming holomorphy of the whole
paired series there would already rule out those zeros; it is not a
free consequence of normal convergence of K. No uniform moving-Hecke
nonvanishing or inverse bound has been imported.

Restoring all shared-g states in the absolutely convergent, unwindowed
double series restores the local term a_p b_p. The full factor becomes
1-a_p-b_p+a_p b_p=(1-a_p)(1-b_p), exactly the original two reciprocal
L-functions. Thus the extracted zeta factor is tied to coprimality, not
a new cancellation of the full pair. The compact profiles in P1 cannot
be dropped in order to spend that unwindowed identity on MB34.

For application to the first MB29 term, expand w_P(gk) exactly as the
sum of 1_((a,gk)=1) over good a<=P. Freeze a,g,u, keep the outside masks
1_((a,g)=1)1_((u,g)=1), and use
psi(n)=nu(n)chi_n(u)^epsilon 1_((n,ag)=1) in P2.
For the comparison term freeze g,v and use only the g-mask, with the
outside 1_((v,g)=1); there is no amplifier sum in that term.
Mellin inversion of the two profiles on initial lines Re s,Re t>1
uses the two separate transforms of W and conjugate(W), with factor
(L/q_g)^(s+t). The coprime off-diagonal series is Z_psi(s,t)-1,
since n=m in a coprime pair means n=m=1. All original finite outside
sums and the prefactor1/L remain. This is an absolute-convergence
identity only; no shift or growing-mask uniform inverse bound follows.

## P3. Price of an optimistic absolute contour bound (conditional test)

Assume, solely for this test, that both contours can be moved without
unpaid poles to a fixed sigma>1/2 and that every frozen row and ag-mask
satisfies |1/L_psi(sigma+it)|<=U^epsilon(1+|t|)^A uniformly.
This strong hypothetical estimate is NOT inferred from any zero-free
region. On both sigma-lines K and 1/zeta_mask(s+t) have uniform upper
bounds from their absolutely convergent products. Smooth Mellin decay
absorbs the fixed height powers, and the subtraction of1 is retained.
Absolute summation then gives

    |Doff| <= C P U L^(2sigma-1) U^epsilon,

because sum_(g sf) q_g^-2sigma is bounded, the first outside row/amplifier
mass is O(PU), and lambda times the comparison-row mass is O(PU).
This is already an optimistic envelope: no moving-mask cost is charged
beyond the explicitly hypothetical U^epsilon bound.
At L=D=U^r, spending it on H U^-eta requires

    sigma <= 1/2 + (5p-eta)/(2r),    eta=1/200.

The endpoint ceilings are22783/42000 at r=28/25 and493371/904000
at r=113/100. Uniform use on the whole band needs the smaller ceiling,
about0.54245238. Even granting the optimistic contour estimate at7/8
would leave a power deficit at least297629/400000, about0.7440725.
This rejects this absolute-envelope entrance as a consequence of a7/8
input; it does not refute the true joint sum or assert Hecke uniformity.
The simultaneous centered row average would need to be used before
taking these absolute values to improve this calculation.

## Bounded alias return: one actual cubic Gram lemma

Three fresh shelf dictionaries were actually run with ask.sh
--defer-external: `multiplicative dispersion sparse perfect-power rows`,
`coprime Mobius pair product regrouping bilinear cubic character divisor sum`,
and `trace-function bilinear correlations`. All returned INCOMPLETE due
to q3_docs freshness validation; exact receipts are saved in
MB34_PRODUCT_ALIAS_RECEIPTS.json. No absence claim follows. The useful
source below was verified directly in the local pinned OpenAI corpus.

Source inspected independently by long_positive_alias and root:
OpenAI, An unconditional first moment for cubic Gauss sums (2026-09-25),
corpus adc7f1241b42e322a6451854ab7e4b4c146bf78a, build/sections/dual.tex149–245.
SHA2561209fd17cee79f4a21b71d66d3d8b60b210216fa783ec555959d2ebff2fba483.
Pinned source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/build/sections/dual.tex
Lemma `An off-diagonal Gram estimate` states, for squarefree primary
p,p' of norm X, cubic characters and smooth full primary rows of scale Z,

    sum_(p'!=p) |T_pp'|² <=(XZ)^epsilon Z[X+(X³/Z)^(2/3)].

Quote, line165: “The same bound holds with a subset of the available $p'$.”
The proof removes shared-prime masks, kills the nonprincipal zero Poisson
frequency, retains the primitive Gauss factor as a row scalar, and uses
a cubic large sieve on the dual frequency polynomial. This is verified
source content, not independent certification of all analytic dependencies.

Partial analogue only. The P1 divisor phase is cubic, but the outer
sextic psi_v(k), outer mu(k), divisor condition and two coupled profiles
remain. Simply identifying p with an original MB29 column would instead
mistake its sextic character for the lemma's cubic character. Moreover
the lemma has smooth full primary rows, not the centered sixth-free and
raw-element comparison measures. Fixed subset closure does not supply
all these transfers or the original amplifier-mask uniformity.
No exact theorem-to-MB34 map is established; no new supplier admitted.

Even a hypothetical direct Gram replacement with X=L,Z=U and unchanged
bound would, by Frobenius/Cauchy over O(L) columns, give only an operator
envelope O((LU)^epsilon[U^1/2 L+U^1/6 L^3/2]), before P. The normalized
column coefficient vector has bounded squared norm. Thus a generic
absolute matrix aggregation is too weak; one must exploit the actual
coefficient and divisor structure rather than merely this row-square bound.
This aggregation and its insufficient powers were independently checked
by mobius_short_transfer; the external lemma's analytic proof was not
independently certified.

## Decision and next discriminator

P1 is a possible interface to a joint cubic-divisor estimate, not such
an estimate. P2 rules out treating the convergent Euler correction as
automatic removal of reciprocal-L singularities. A valid supplier must
handle the outer mu(k), two coupled profiles, actual row masks and exact
w_P(gk), uniformly before the common-profile and finite inverse returns.
Stop this attempt if only independent absolute bounds or pole-free contour
movement without a proved reciprocal-L input is available.
AUTOPSY: dropped=COUPLING; note=product regrouping retains a signed cubic divisor sum and the reciprocal-L factors carrying the unpaid analytic information.
