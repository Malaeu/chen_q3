# Post-Q08 own attempt1: positive autocorrelation and scalar envelopes

2026-10-21. Original full CCM, fixed epsilon, M=R=floor(m^epsilon),
L=log m and exact original sparse-band P=P_(m,epsilon).
Here S=P A_prime P, the original full prime-power compression; it is
not the Q08 sieve correction D_y or the earlier composite C5 operator. No Q09 sent. Full exponent unchanged.
This tests a sufficient scalar comparison before investing in its search.

For unit c in ran P, f=Fc zero-extended belongs to H1(R), because its
endpoint values vanish. With fhat(xi)=integral f(t)exp(-itxi)dt,

 a_m(xi)=2 sum_(2<=n<=m) Lambda(n)/sqrt(n) cos(xi log n),
 <c,S c>=(1/(2pi)) integral_R a_m(xi)|fhat(xi)|^2 dxi.

This is the full prime-power sum, not a diagonal approximation. Positivity
of |fhat|² permits scalar multiplier comparison, but a finite Fourier band
on [0,L] does NOT give compact support of the zero-extension's transform.
The two exponential contacts are zeros at complex frequencies; they do not
assert fhat(0)=0 or discard a real-frequency neighborhood.

## Cheap uncentered Sobolev envelope is excluded

If a_m(xi)<=A_m+B_m xi² for all real xi with B_m>=0, then
S<= (A_m+B_m Omega²)P by Plancherel and ||f'||<=Omega||f||.
At xi=0 this requires A_m>=2 sum Lambda(n)/sqrt(n).
From the ordinary PNT, psi(x)~x, partial summation gives

 sum_(n<=m) Lambda(n)/sqrt(n)
 =psi(m)/sqrt(m)+(1/2)integral_1^m psi(t)t^-3/2 dt
 =(2+o(1))sqrt(m).

Thus this sufficient certificate has unavoidable price >=(4+o(1))sqrt(m).
The same statement holds for any nonnegative extra pointwise penalty that
vanishes at xi=0, when its integrated payment is also nonnegative. This is
a limitation of that CERTIFICATE, not a spectral lower bound for original S.
A negative penalty or a constraint-aware nonlocal comparison is not covered.

PNT source verified: https://dlmf.nist.gov/27.12#E5 . Only its unconditional
PNT consequence is used; no RH-size error assumed. The two displayed
partial-summation steps are the present derivation.

## Centering repairs that objection but leaves the actual unpaid source

Let g_m(xi)=2 integral_0^L exp(s/2)cos(xi s) ds and b_m=a_m-g_m.
The accepted full-window identity gives P G P=-P H P, H kernel
exp(-|t-u|/2),0<=H<=4I. Hence exactly

 <c,S c>=(1/(2pi))integral b_m(xi)|fhat(xi)|² dxi - <f,H f>.

All continuous and arithmetic contributions and the original constraints
remain. This centered multiplier does not inherit the a_m(0) obstruction.
Its desired upper envelope is NOT supplied by autocorrelation positivity.
In particular, a_m at zero and an arbitrary-phase counterexample must not
be used to kill this centered possibility. Cheap centering was already on
the shelf (CCM_CONTINUOUS_RANK_TWO_TEST.md); this identity is not new gain.

The shelf's CCM_COMPOSITE_HEAT_RETURN.md already shows Gaussian smoothing
preserves every finite-frequency multiplier sign, with a paid original-band
return. CCM_Q03_ONE_SIDED_PRIMITIVE_CONE_TEST.md already shows the actual
projected correlation's weighted derivative changes sign. Neither provides
the needed centered scalar or quadratic-form upper estimate.

Decision: do not launch a search for uncentered A+Bxi² certificates with a
subpower price. Preserve the centered joint pairing as open; next attempt
must use more than nonnegative Fourier density alone. No source route killed.
AUTOPSY: dropped=THEOREM_SHAPE; note=Uncentered pointwise Sobolev upper certificate spends half-power at zero frequency before using the original contacts.

## Explicit centered PNT fallback (not a new supplier)

Write E(x)=psi(x)-(x-1). Partial summation with z=1/2-i xi gives
D(xi;m)=m^-z E(m)+z integral_1^m E(t)t^(-z-1)dt,
and b_m(xi)=2 Re D(xi;m). The classical unconditional PNT error yields
|E(t)|<=C t exp(-c sqrt(log t)) after enlarging C on a finite range.
Splitting the integral at sqrt(m) bounds its early part by O(m^1/4)
and its late part by O(sqrt(m)exp(-c sqrt(L/2))). Thus for some c'>0,

 |b_m(xi)|<=C(1+|xi|)sqrt(m)exp(-c' sqrt(L)).

Cauchy-Schwarz and Plancherel give integral |xi||fhat|²/(2pi)<=||f'||<=Omega
for unit f. The resulting full upper price is
C(1+Omega)sqrt(m)exp(-c' sqrt(L)), power1/2+epsilon-o(1).
It is worse in power than the elementary full norm and cannot supply eta->0.
This is a concrete failed return, not merely a change of notation.
The old CCM_LONG_MOBIUS_PRIMITIVE_TEST.md already documents why absolute
subpower control of the same prime discrepancy would be RH-strength; that
stronger absolute condition is not silently assumed here.

Root PAPER derivation and q09_autocorrelation_preflight independent bounded
PAPER review PASS: multiplier, centering sign and PNT budget checked.
Reviewer scope clarification (S and exact sparse-band P) incorporated.
No new numerical, Lean or Arb run. No global absence or novelty claim.
