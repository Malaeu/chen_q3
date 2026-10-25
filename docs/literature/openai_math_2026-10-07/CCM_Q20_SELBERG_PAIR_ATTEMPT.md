# Q20 own candidate: Selberg symmetry on the actual full pair

2026-10-25. Primary source verified; bounded read-only selberg_pair_source transfer check PASS.
Source/consumer unchanged: Q19 centered pair, original sparse P, both times,
complex phase, all prime powers, finite upper hyperbola. No Pro send.
Shelf: three ask dictionaries (Selberg symmetry, generalized Mangoldt semiprime,
renewal/log weights) INCOMPLETE due q3_docs freshness. Literal CCM search found
no direct symmetry application, not a global absence claim. Existing sieve,
Abel and weight-one quadrature results are not claimed new.

## Exact arithmetic and attempted use

Write Lambda2(n)=(mu*log²)(n). Exact divisor convolution gives
 Lambda2(n)=Lambda(n)log n+sum_(uv=n) Lambda(u)Lambda(v).
In particular both RHS terms nonnegative as SCALAR coefficients. The second
sum is over all ordered prime-power pairs, not just distinct primes. At p²
its pair contribution is (logp)²; at pq,p!=q it is2logp logq.
Let ell(n)=logn and D a(n)=a(n)logn. From ell=1*Lambda and the
convolution product rule, D ell=ell*Lambda+1*(Lambda log). Convolve
with mu: mu*ell=Lambda and mu*1=convolution identity give the stated
formula. No analytic continuation is required.

For the same COMPLEX f_y(x)=x^-1/2[C(y-logx)+C(y+logx)], y=2a,
define h_y(x)=f_y(x)/logx on x>=2. Then exactly
 J(a;m)+P2(a;m)=sum_(n=2)^m Lambda2(n)h_y(n),
 P2=sum_(u,v>=2,uv<=m) Lambda(u)Lambda(v) f_y(uv)/log(uv).
All terms have the same source weight, both temporal orientations and the
finite hyperbolic edge. P is applied to the whole original source pair only;
P2 is a scalar bookkeeping sum, not a product of compressed operators.

External input: A2(x)=sum_(n<=x)Lambda2(n)
=2xlogx+O(x). If valid with absolute constant, Abel transfer gives
 J+P2=integral_2^m (2logx+2)h_y(x)dx
      +H(m)h_y(m)-H(2-)h_y(2)-integral_2^m H(x)h'_y(x)dx,
 H(x)=A2(x)-2xlogx, H(2-)=-4log2.
Lower endpoint convention includes the n=2 atom exactly. No modulus yet.

## Price of the supplied O(x) remainder

For a>=2, split x at exp(a); m>=exp(2a) in our original translation range.
On2<=x<exp(a), y-logx>=a; source double-exponential decay makes the
whole contribution negligible, even after elementary x powers/log denominators.
On x>=exp(a), logx>=a. With g=|C|+|C'|, direct differentiation bounds
 x|h'_y(x)| <=const x^-1/2/a [g(y-logx)+g(y+logx)].
Substitution logx=s gives integral <=C_w exp(a)/a, using fixed weighted
integrability of C,C'. The upper endpoint also obeys C_w exp(a)/a:
sqrt(m)|C(y-L)|=exp(a)exp((L-y)/2)|C(y-L)|<=C_w exp(a),
and reverse-time term is smaller; logm>=2a. Lower endpoint is negligible.
Thus the fully returned Selberg remainder costs at most C_w exp(a)/a.

The density term is 2 integral_2^m f_y +2 integral_2^m f_y/logx.
The first is Q19's paid continuous term minus its negligible [1,2] piece.
The second, bounded with the same split, costs <=C_w exp(a)/a.
Hence the external formula would supply
 |J(a;m)+P2(a;m)|<=C_w exp(a)/a + paid negligible endpoints.
After actual phase and averaging, with h-T>=h/2,
 |B_T+B2_T|<=C_w exp(h)/(T(h-T))+o(1).
This is a logarithmic improvement for a DIFFERENT combination, not a bound
for B_T alone. Completing independently pays |B2_T|<=C_w exp(h)/T:
use sum_(n<=x)(Lambda*Lambda)(n)<=A2(x)=O(xlogx), divide by logn,
and the same unit-log-shell argument. All pairs and prime powers remain.
Thus B_T >= -C_w exp(h)/T - C_w exp(h)/(T(h-T))-o(1),
which returns only the inherited sqrt(m)/L²+L full K floor after
self, arch once and original-P rho_S=o(1). No new full exponent.

## Missing sign and negative-control discrimination

Scalar Lambda(u)Lambda(v)>=0 does not imply Re(exp(2i gamma a)f_y(uv))>=0.
For unrestricted complex weights even a single negative real value defeats
that inference; this is OUTSIDE the actual source class and only diagnoses
the invalid generic positivity inference, not a counterexample to CCM.
Needed: an upper signed bound for B2_T jointly with the Selberg remainder,
sufficient to make B_T small below. Neither exact coefficient positivity nor
the symmetry asymptotic supplies it. Do not discard P2 or the hyperbola.
This is one candidate arithmetic pairing, not a new interpretation of the
previous lattice error. Bounded read-only check confirms identity, all-power extension, weighted
remainder, endpoints and no-gain completion. Target and RH OPEN.

## Primary-source evidence and exact map

Atle Selberg, An elementary proof of the prime-number theorem, Annals of
Mathematics50(1949),305–313; printed p309 equation(2.8), proof pp307–309.
Primary scan: https://www.math.lsu.edu/~mahlburg/teaching/handouts/2014-7230/Selberg-ElemPNT1949.pdf
Local sources/selberg_1949_annals.pdf
SHA25647de9d3c50d48e57fde27058d37a487b9414a67c8aace831c02ffba29ef8e6e6.
Short verbatim quote p309: “Now (2.6) yields”. Display(2.8) is the PRIME-ONLY
sum log²p + sum_(pq<=x) logp logq =2xlogx+O(x).
Do not falsely attribute the all-prime-power form literally to that display.

Extension: extra first-sum prime powers cost O(sqrt(x)log²x)=O(x).
Pairs with at least one proper prime power cost at most
2 sum_(p,k>=2,p^k<=x) logp psi(x/p^k)
<=C x sum_p logp/[p(p-1)]=O(x), using elementary Chebyshev psi(t)<=Ct.
The ordered-pair double count only enlarges this positive ERROR bound.
This supplies exactly the all-power A2 input, keeping the error uniform in x.
Root read source text around(2.6)–(2.8); researcher inspected printed formula.
Verified discovery evidence/partial bridge, NOT an exact supplier for CCM.

Search hints, not established mechanisms: (i) UNVERIFIED renewal equation
for the signed centered prime-pair weight; (ii) UNVERIFIED multiplicative
convolution comparison of P2 to J on actual source-pair. Neither is admitted
as a sign estimate. Three dictionaries were arithmetic Lambda2/semiprimes,
weighted Selberg symmetry, and renewal/log-weight compensation. All ask
semantic searches incomplete; no claim of literature absence.

## Shelf correction: do not iterate an already tested coarse recurrence

The subsequent literal crosswalk found
`docs/routeB_bus/source_observability_2026-09-28/PRIME_PREFIX_ENERGY_OWN_2026-10-07.md`,
already recorded in PAPER_CHAIN under the October 7 ordered Stieltjes test.
It verifies Selberg's printed (2.12) and tests its O(x) remainder with
actual prime weights. Thus the present pair-weight transfer is a useful
specialization, not a newly discovered arithmetic mechanism. Do not count
repeating that recurrence toward three distinct post-Q19 attempts.

The same information-loss test retains ALL prime powers. For 1/2<sigma<1,
gamma real, let f(x)=x^sigma cos(gamma log x), x>=1, and use the actual Lambda:

 T_Lambda f(x)=f(x)log x+sum_(n<=x) Lambda(n)f(x/n).

If psi(t)<=C t, partial summation gives
 sum_(n<=x) Lambda(n)n^-sigma
 <=C x^(1-sigma)/(1-sigma).
Also x^sigma log x<=x/[e(1-sigma)]. Therefore

 |T_Lambda f(x)|<= [C+1/e]x/(1-sigma).

Adding a fixed multiple of f to a solution of an O(x)-tolerant LINEAR
recurrence preserves that remainder class. This does not preserve the exact
arithmetic definition of the discrepancy, so it is NOT a counterexample to
the actual pair, primes, CCM, or RH. It only prevents using the approximate
recurrence alone to exclude these sublinear oscillations. Repeated algebraic
use of that same supplied information cannot remove this ambiguity.

Decision: keep the exact J+P2 formula and its paid full return; abandon the
proposed coarse-renewal iteration before further computation. Any renewed
Selberg approach must use an additional exact source constraint or a sharper
signed remainder, not silently strengthen O(x). Original P and all mixed
terms remain as above. No new exponent, no Pro question sent by this check.

Independent bounded crosswalk: selberg_recurrence_crosswalk PASS the all-Lambda bound, historical duplication and narrow information-loss scope.

## Exact local cancellation before any O(x) remainder

This tests the exact arithmetic identity rather than iterating the coarse
recurrence. It is a local analytic diagnostic, not a contour estimate for
the finite source. On Re(s)>1 put F(s)=-zeta'(s)/zeta(s). Absolute convergence
and differentiation of the Euler product give

 DS[Lambda log]=-F', DS[Lambda*Lambda]=F^2,
 DS[Lambda2]=F^2-F'=zeta''/zeta.

At a hypothetical zero rho of multiplicity r>=1, write z=s-rho,
zeta(s)=z^r a(z), a(0)!=0, b=a'/a analytic. Exactly,

 -F'=-r/z^2+b',
 F^2=r^2/z^2+2r b/z+b^2,
 F^2-F'=r(r-1)/z^2+2r b/z+b^2+b'.

For r=1 the double poles cancel; a simple pole remains unless b(0)=0.
For r>=2 the double pole survives. No simplicity assumption is admissible.
The actual coefficient in P2 includes division by log n. Accordingly define

 H(s)=sum_(n>=2) (Lambda*Lambda)(n)/(log n) n^-s
     =integral_0^infinity F(s+t)^2 dt, Re(s)>1.

Then H'=-F^2. On a slit neighborhood after local continuation, its singular
part is r^2/z-2r b(0)log z. Thus F+H has singular part

 r(r-1)/z-2r b(0)log z.

For r=1, the simple pole of F is canceled by the opposite pole of H; a
logarithmic branch can remain. This explicitly explains how the COMBINATION
can lose a leading term while the original single-prime sum retains it.
It supplies neither a favorable sign of P2 nor a bound for J alone.

All Dirichlet series identities here start in their absolute convergence
domain. The finite sums with n<=m (and uv<=m) are entire; they have no such
poles. Turning this diagnostic into a finite weighted formula would require
a paid truncation/contour argument, both time orientations and every other
zero contribution. None is silently supplied here, and no off-line zero is
asserted to exist. Original P is unchanged; no compressed operators were
multiplied. The fully justified finite budget remains the earlier
O_w(sqrt(m)/L^2+L) after P2, self, arch and projection return. This local
cancellation is not another full-gain attempt or a reason to ignore P2.

Symbolic check (existing SymPy environment): expanding F=-r/z-b(z) reproduces
all three displayed Laurent identities. This is algebra verification only.

Bounded independent check selberg_pole_budget: PASS signs, /log integration, multiplicity distinction and finite-source limitation.
