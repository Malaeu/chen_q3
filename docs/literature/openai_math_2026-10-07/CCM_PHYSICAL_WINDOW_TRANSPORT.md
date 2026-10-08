# Full CCM window transport: exact overlap and a logarithmic edge loss

2026-10-08, own followup to Q03 section8A. Same original N=m family.
No new Pro message. All formulas below concern the whole finite Fourier space,
not an adapted choice of ground vector. They do not estimate the signed source.

Write M=m+1, L=log m, Lp=log M, a=L/Lp, h=1-a, d=2m+1.
Use centered normalized modes phi_(L,j)(x)=L^(-1/2)exp(2pi i j x/L)
on [-L/2,L/2]. The (-1)^j convention in Q03 is a diagonal unitary change;
it does not alter the norm statements below.

Let E be zero extension into [-Lp/2,Lp/2], U f(x)=sqrt(a)f(ax) the unitary
dilation, and P the orthogonal projection onto new modes |k|<=M.
U maps the old finite space into P exactly. Direct integration gives

    <phi_(Lp,k), E phi_(L,j)> = sqrt(a) sinc(pi(j-a*k)),          (1)

where sinc(v)=sin(v)/v, with its continuous value at zero.
Thus the exact projection-return matrix is O_(kj) in(1); no neighboring
mode or boundary interval is omitted. E is isometric, P E need not be.

## Full-space upper bound

For every old f, Bernstein gives ||f'||<=2pi m/L ||f||. On the old interval,
integrating x f'(t x) from t=a to1 yields

    ||f-f(a .)|| <= L(1-sqrt(a))||f'||.

Consequently its contribution to ||E f-U f|| is at most
(1-sqrt(a))(1+2pi m sqrt(a))||f||. On the two added edge intervals,
total length Lp-L, the pointwise finite-mode bound gives

    integral_edges |Uf|² <= d*h ||f||².

Since h<=1/(m L), 1-sqrt(a)<=h, and d<=3m, for m>=2,

    ||(I-P)E||² <= ||E-U||²
      <= d*h + (1-sqrt(a))²(1+2pi m sqrt(a))²
      <= 3/L + (1+2pi)²/L².                                  (2)

Also I-O*O=E*(I-P)E is PSD and its norm is the squared leakage norm.
This is an exact full-space loss account, not an assertion that it is small
in the arithmetic form norm.

## One actual edge mode rules out a polynomial L2 return rate

Take the original mode j=m and the first omitted new label k=m+2.
In(1), j-a*k=-2+epsilon, epsilon=(m+2)h.
For m>=16, 0<epsilon<=1/2, a>=1/2, and epsilon>=1/Lp:
log(1+1/m)>=1/(m+1) proves the last inequality.
Using sin(pi epsilon)>=2epsilon gives

    ||(I-P)E phi_(L,m)||
      >= sqrt(a) sin(pi epsilon)/(pi(2-epsilon))
      >= 1/(sqrt(2)*pi*Lp).                                  (3)

This is a real production-basis edge-mode obstruction, not a planted
replacement matrix. In particular a uniform carrier-wide O(m^(-b)) leakage
bound is false for every fixed b>0. It does NOT refute a better estimate on
the actual adaptive spectral density, a signed form estimate, or SP.

## Exact source-evaluation return and missing estimate

For the Laplace functional F_z(f)=integral f(x)exp(zx) dx, zero extension
retains F_z exactly. With r_f=(I-P)Ef,

    F_z(PEf)=F_z(f)-F_z(r_f).

On the new physical window Cauchy-Schwarz gives

    |F_(delta+i gamma)(r_f)|²
      <= [sinh(delta Lp)/delta] ||r_f||²,                       (4)

with the value Lp when delta=0. At the allowed fixed displacement
delta=3/8 the coefficient still has power M^(3/8). A logarithmic L2 loss
does not turn this bound into a subpolynomial source-form error.
Equation(4) is a bound for one evaluation only; summing it over infinitely
many zeros is not permitted without an additional sampling/tail estimate.

The full signed form difference retains cross terms between F_z(f) and
F_z(r_f) and the residual-residual term, for every critical pair and quartet
with the Q03 signs. Small L2 leakage supplies no favorable sign for these
terms. An operator bound on their contraction with the true T, including
new-mode couplings and the diagonal companion, remains OPEN.

Outcome: exact transport and leakage are now explicit. Uniform polynomial
L2 return is ruled out by(3); using the arithmetic form instead requires a
new source-specific estimate. No fixed-power floor improvement or RH claim.

## Return to the existing physical Fourier energy theorem

Three shelf dictionaries were queried: Fourier extension spectral leakage
moving interval; Paley Wiener sampling complex zeros form bound; frame
perturbation nonharmonic Fourier boundary transport. Each ended INCOMPLETE
on semantic-index freshness; no absence is inferred. A concrete local hit is
Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean:145–179.
Its projection-tail estimate explicitly assumes summability of the weighted
Fourier energy; its selected decay theorem also assumes bounded selected
energies and cofinal bandwidth. AmbientResidualSplit.lean:30 gives only the
exact residual-plus-leakage identity, not a leakage bound.

For this proposed zero-extension transport even the old constant mode fails
the squared-frequency summability entrance. Its coefficients are
O_(k,0)=sqrt(a)*sinc(pi*a*k), so for k!=0

    k² |O_(k,0)|² = sin²(pi*a*k)/(pi²*a).

Because 0<a<1, exp(2pi*i*a)!=1. The geometric-series bound gives
sum_(k=1)^n sin²(pi*a*k)=n/2+O_a(1), hence the weighted energy diverges.
The omitted fixed physical-frequency factor (2pi/Lp)² is positive and
does not change divergence. No numerical or asymptotic assumption about
irrationality of the logarithm ratio is needed.

Thus that existing finite-energy theorem cannot be applied to the unchanged
zero extension on the full old carrier. Smoothing the edge would change the
source evaluation and needs its own signed form return. This excludes only
this attempted theorem import; a restricted adaptive subspace with endpoint
vanishing or a weaker form estimate remains open.

Independent read-only ccm_window_transport audit PASS: exact overlap, whole-space
upper bound, omitted production-mode lower bound, single-evaluation return and
weighted-energy divergence. This bounds/rejects only the stated transport
mechanisms, not the actual signed CCM estimate.
