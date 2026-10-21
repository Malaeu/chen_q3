# Post-Q08 own attempt2: retain the attainable density and pay its tail

2026-10-21. Original sparse-band P, fixed0<epsilon<1/32,
M=R=floor(m^epsilon), d=2M+1, L=log m,
omega_j=2pi j/L, Omega=2pi M/L. No source exponent improvement.
Full constrained f=Fc, ||c||=1, is extended by zero outside[0,L].
This is a bridge calculation, not an asserted arithmetic supplier.

## Exact joint density

Set R_c(xi)=sum_(j=-M)^M c_j/(omega_j-xi),
D_M(xi)=product_(j=-M)^M(xi-omega_j). Direct integration gives

 fhat(xi)=(exp(-i xi L)-1) R_c(xi)/(i sqrt(L)).

The apparent poles are removable in fhat. The endpoint condition sum c_j=0
reduces the degree of N_c=D_M R_c to at most d-2=2M-1. The two exponential
contacts are fhat(i/2)=fhat(-i/2)=0; the exponential prefactors and D_M are
nonzero there, so N_c=(xi²+1/4)p_c with deg p_c<=2M-3. Therefore

 rho_c(xi)=|fhat(xi)|²/(2pi)
 = [4 sin²(xi L/2)/(2pi L)] (xi²+1/4)² |p_c(xi)|²/D_M(xi)².

Conversely every complex polynomial p of degree<=2M-3 gives a unique vector
by partial fractions, c_j=-N(omega_j)/D_M'(omega_j), satisfying all three
contacts. For nonzero p, scaling to integral rho=1 equals ||c||=1. Mixed terms in |p|²
must stay; replacing them by sums of squares of coefficients changes the form.
This is the same dimension2M-2 as E, not a relaxed arbitrary density cone.

For centered b_m from CCM_Q09_AUTOCORRELATION_PREFLIGHT.md, the exact target
is its signed integral against this cone, with the paid negative H term.
A generalized moment-matrix inequality in these coordinates would be
EQUIVALENT to the existing source bound; its formulation alone supplies no
estimate and is not a new goal closure. No pointwise b_m>=0 is asserted.

## The transform is not supported on the Fourier grid or on [-Omega,Omega]

Using sum c_j=0, for |xi|>=2Omega,
R_c(xi)=sum c_j omega_j/[xi(omega_j-xi)],
|R_c(xi)|<=2sqrt(d)Omega/xi².
Consequently, for T>=2Omega,

 integral_(|xi|>T)rho_c(xi) dxi <=16d Omega²/(3pi L T³).

The elementary prime norm gives |a_m(xi)|<=12sqrt(m), and the continuous
multiplier satisfies |g_m(xi)|<=4(sqrt(m)-1). Hence |b_m|<=16sqrt(m) and

 |integral_(|xi|>T)b_m rho_c|
 <=256d Omega² sqrt(m)/(3pi L T³).

For fixed kappa>0,T=max(2Omega,m^(1/6+epsilon+kappa)), this tail price is
O(m^(-3kappa)/L³)=o(1). It pays all frequencies outside that interval.
It does not pay its interior and does not imply this T is necessary: it is
only a sufficient cutoff for the displayed absolute estimate.

The cheaper-looking choice T=O(Omega) gives this budget O(sqrt(m)) rather
than a small return. Sampling only the original mode frequencies cannot
silently remove this continuum tail. A sharper joint argument remains possible.

## Decision

Preserve this exact density class when testing a constraint-aware embedding,
sampling, or signed quadrature mechanism. Positive-measure embedding alone
is not a bound for signed b_m. Need one actual arithmetic estimate for its
joint integral, with all constants/degree dependence and tail return.
No new full exponent. No source route killed; no Q09 sent at writing.
AUTOPSY: dropped=NO_DERIVATION; note=Exact constrained density and paid continuum tail leave joint interior arithmetic integral unpaid.
Independent q09_rational_density_review bounded PAPER PASS: full converse,
normalization, partial-fraction sign and both tail constants checked.
Explicit fixed-epsilon schedule and nonzero-p qualification incorporated.
No numerical/Lean/Arb claims.
