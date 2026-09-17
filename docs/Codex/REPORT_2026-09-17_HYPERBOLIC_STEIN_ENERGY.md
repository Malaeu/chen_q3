# The source's signed Stein energy is negative on actual mean columns

STATUS: ACCEPTED_LIMITED_PAPER; ACCEPT_ACTUAL_MEAN_SIGNED_STEIN_ENERGY_OBSTRUCTION_ONLY.
Base: 0fb70b28063e76b87e0ac0b5e2aab0019a74d604. Isolated research only.
Original full V/RH: OPEN. No negative original-V witness.

## S0. Bounded test, existing equation, and exact non-goal

The full-source differential equation and positive convolution forcing are
already in HYPERBOLIC_SOURCE_COMPENSATION L5. They are not newly discovered
source properties. Its scalar gauged Sturm energy was already excluded by
L9; its coupled field and subsequent renewal constructions are not reopened.
This test checks a DIFFERENT, specified reading: use L5 as a stationary
diffusion-minus-jump Stein identity and its quadratic energy on the actual
conditional-mean likelihood columns. No positivity premise is inserted.

The result below is a negative energy on admissible mean columns, whereas
the corresponding original one-node V is positive. Thus neither stationarity
nor the positive convolution forcing makes THIS energy a carrier of V.
It does not exclude a corrected full conditional field, which would have
to keep the original weight, mixed term and boundary. No new request to
construct a generic reservoir or source-support operator follows.

Accepted inputs, read and pinned separately:

- REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md, L1, L5, L18--L19.
- REPORT_2026-09-16_CONVOLUTION_RECIPROCITY_RIGIDITY.md, R2--R3 for m=4.

We use their previously accepted identities/tails, not a fresh audit of
the entire old ladder or its published probabilistic source. All new
calculations below use real integrals and exact differentiation only.

## S1. Fixed full source and the signed stationary identity

Let r=r_2 be the density of T=sum_(n>=1) Gamma(2,rate pi*n^2), and
r_4=r*r the density of T+T' for an independent copy. Every rate and mode
is retained. The exact identity L5 is

    6 r_4(t)=4t^2 r''(t)+(22t-4pi)r'(t)+20r(t), t>0.       (S1)

The full r is positive on (0,infinity), flat at zero, and its derivatives
decay exponentially at infinity, with polynomial factors. For a smooth
compactly supported test phi, integration by parts gives

    E phi(T+T')
      = E[(2/3)T^2 phi''(T)+(2pi/3-T)phi'(T)+phi(T)].      (S2)

Indeed the adjoint of 4t^2 d^2/dt^2 +(22t-4pi)d/dt +20,
acting on phi under dt, is 4t^2 phi''+(4pi-6t)phi'+6phi.
There are no hidden distributions or boundary terms for these tests.

Define on this initial test class

    (Jg)(t)=int_0^infinity [g(t+s)-g(t)]r(s)ds,
    (Ag)(t)=(2/3)t^2 g''(t)+(2pi/3-t)g'(t),
    Lg=Ag-Jg.                                            (S3)

Then E Lphi(T)=0. The sign preceding J is MINUS. This is a signed
stationary identity, not an assertion of a Markov generator or of a
contractive semigroup. In particular a positive jump rate may not be
substituted for this negative one while retaining S2.

## S2. The exact energy includes a negative jump term

For complex g in the above test class, direct product differentiation and
expansion of the jump yield

    L|g|^2-2 Re(conjugate(g)Lg)
       =(4/3)t^2 |g'(t)|^2
          -int_0^infinity |g(t+s)-g(t)|^2 r(s)ds.

Using S2 for |g|^2 therefore gives the exact energy

    D[g]:=-2 Re int_0^infinity conjugate(g)Lg r dt
         =(4/3)int_0^infinity t^2 |g'|^2 r dt
             -E|g(T+T')-g(T)|^2.                        (S4)

This is the full signed expression. The two expectations are not made
independent when they share T. Stationarity alone gives the equality in
S4, not D>=0. We next test D on actual source mean columns, rather than
on an unrelated arbitrary probability law.

## S3. Actual mean likelihoods and admissibility

For 1/2<a<1 let x=(log a)/2 in I=(-log(2)/2,0), and put

    g_a(t)=a^(5/4) r(at)/r(t).                            (S5)

This is exactly Cg_x=E_(p_t)g_x in the original conditional-field source
report L18--L19. It is not a newly chosen exponential surrogate.
The measure in S4 is r(t)dt, deliberately distinguished from the physical
measure eta with its t>=1 cutoff and outer theta weight.

For the following limit restrict a to (1/2,3/4], and set

    sigma_a=pi(1-a), d_a=pi-2sigma_a=pi(2a-1)>0.

The full theta series and its derivatives give, uniformly in this a range,
as t tends to infinity,

    r(t)=4pi^2 t exp(-pi t)[1+O(1/t)],
    g_a(t)=a^(9/4) exp(sigma_a t)[1+O(1/t)],
    g_a'(t)=a^(9/4) exp(sigma_a t)[sigma_a+O(1/t)].         (S6)

For clarity the full leading formula is
r(t)=4pi^2 t exp(-pi t)[1-3/(2pi t)+O(exp(-3pi t))].
Its differentiated series gives the corresponding logarithmic derivative.
Applying it at at>=t/2 proves uniformity in S6; r is bounded below by
its positive leading expression for sufficiently large t. No finite-mode
substitution for the source is made.

At zero, exact reciprocity r(1/t)=t^(5/2)r(t) gives

    r(t)=4pi^2 t^(-7/2) exp(-pi/t)[1+O(t)],
    g_a(t)=a^(-9/4) exp[-pi(1/a-1)/t][1+O(t)].             (S7)

The differentiated estimates hold too. Since 1/a-1>=1/3 in the chosen
range, g_a and its first two derivatives are uniformly bounded near zero
by fixed powers of 1/t times exp(-pi/(3t)). On every intermediate compact,
uniform bounds follow from smoothness and the positive r denominator.
In particular g_a(t)<=C exp(sigma_a t) for all t>0, uniformly in this range.

For each fixed a>1/2 all terms in S4 are finite. For example the square
at T+T' is integrable against r_4, and all derivative terms against r,
because their exponent at infinity is -d_a t with polynomial factors.
All origin products vanish by S7. Thus S2 extends to |g_a|^2 directly
by integration by parts with its paid endpoints; Fubini for the jump is
absolute. This proves S4 for the actual g_a, not merely for compact tests.

## S4. Leading full-energy comparison at the admissible endpoint

From S6 and the elementary integral int_0^infinity t^3 exp(-d t)dt=6/d^4,

    lim_(a down to 1/2) [d_a^4/a^(9/2)]
        (4/3)int_0^infinity t^2 |g_a'|^2 r dt = 8pi^4.    (S8)

Indeed the leading integrand is (16/3)pi^2 a^(9/2) sigma_a^2
t^3 exp(-d_a t). Its integral, after scaling, is
32pi^2 sigma_a^2 ->8pi^4. The uniform O(1/t) errors in S6 contribute
O(d_a^(-3)) before scaling; a fixed initial interval is uniformly bounded.
These statements can also be checked after the substitution v=d_a t.

The accepted full convolution tail for m=4 is

    r_4(t)=(8pi^4/3)t^3 exp(-pi t)[1+O(1/t)].             (S9)

It follows from the complete convolution source, not a replacement by a
single shape-four gamma. Therefore S6 and S9 imply

    lim_(a down to 1/2) [d_a^4/a^(9/2)] E[g_a(T+T')^2]
       =16pi^4.                                         (S10)

The other two terms in the expansion of the squared jump have smaller
order. With M(theta)=E exp(theta T), the full source tail implies
M(2sigma_a)=O(d_a^(-2)), while M(sigma_a)<=M(pi/2)<infinity.
The global bound following S7 gives

    E g_a(T)^2 <= C^2 M(2sigma_a)=O(d_a^(-2)),
    E[g_a(T+T')g_a(T)]
       <=C^2 M(2sigma_a)M(sigma_a)=O(d_a^(-2)).            (S11)

Independence is used only for T and T' in this upper bound; the shared T
is counted twice in its exponential. Both S11 terms vanish after the
scaling in S10. Combining the complete S4, S8, S10 and S11 proves

    lim_(a down to 1/2) [d_a^4/a^(9/2)] D[g_a] = -8pi^4 <0.  (S12)

Consequently D[g_a]<0 for every sufficiently small positive a-1/2.
All such a remain strictly inside the original admissible interval.
No numerical node, quadrature or finite theta scan is used. The boundary
a=1/2 is used only as a limit; divergent endpoint energies are not tests.

## S5. Original V on these same one-node signals has the opposite sign

For the ORIGINAL f=Phi/||Phi||_2, evenness and the full decay give directly

    V(x,x)=2int_x^infinity u f(u)^2 du
          =2int_|x|^infinity u f(u)^2 du>0.                (S13)

This holds for every real x, including x=(log a)/2 above. Thus D[g_a]
cannot equal V(x,x), nor a positive constant multiple or positive
node-weighted version of it, on the whole required class. A stationary
identity with the exact source and its square-rate coefficient is not
by itself an original-V nonnegative energy representation.

Scope: the failure is precisely the unweighted diffusion-minus-additive-
jump energy S4 on the actual conditional MEANS S5. It is not a sign
claim for the full conditional-field energy with physical eta, for any
of its cutoff boundary corrections, or for another coupled operator.
S1 is inherited old mathematics; S2--S12 are the bounded energy test.
No new source-sign supplier, canonical admission, or counter reset.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The exact source stationarity equation yields a signed Stein energy that is negative on admissible actual mean columns while original one-node V is positive; it is not a positive-energy identification of V.

## Independent acceptance

Candidate SHA256: 7955245e345793cc6a82e4e4ef84eaf4627a3c9ea2153544631e3c4e2ae7eafd.
Complete independent review SHA256: d88e537108cb4ba61e9b435a3db946d2a115f7ad585e7d77c846f68accb6c40d.
Parent check SHA256: f57531489e1f098e654420bac1dab15cdca8fa9f1488452c149d810b19b5abcf.
Reviewer: /root/pairzero_geometry_review. The full independent review and pinned source formulas were read. No correction was required. Only the specified signed-energy obstruction is accepted. No Lean verification, canonical admission, original-V negative witness or source-sign progress is asserted.
