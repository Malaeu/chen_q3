# Gaussian height on literal even CCM carriers

DIAGNOSTIC_NEVER_A_PROOF. Base50777d478c72298ff65c7ffaa2b3783aec183dd6.
No route-state or RH export. N=m,L=log m, unchanged literal even carrier.

With d_n=1,sqrt2,… and omega_n=2pi n/L, the repository's even basis has
Fourier evaluations E_n(z)=2d_n z sin(zL/2)/(sqrtL(z²−omega_n²)). Build

    A_y = 2 sum_line exp(-y gamma²) E(gamma)E(gamma)^T
        + 4 sum_quartets Re[exp(-y(gamma+i beta)²) E(z)E(z)^T].

All supplied events enter; none is removed at the nominal T. The plant is
zeta plus the original quartet gamma=2pi/log2,beta=1/4. DH retains its complete
supplied numerical900-height census, including every listed quartet. The
zeta input has601 real ordinates through939.66. Inputs are point coordinates,
not certified root enclosures or proofs of completeness.

The multiplier fixes the convention: G_y(s)=exp(-s²/(4y))/sqrt(4pi y),
variance2y. For a zero z=gamma+i beta, exp(-yz²) has modulus
exp[-y(gamma²−beta²)] and phase−2y gamma beta. No assertion that a whole
matrix bottom eigenvalue is multiplied by that modulus is made. Fixed-vector,
isolated-quartet and reoptimized levels are distinct receipts.

## Separator convention

A nonvanishing Gaussian defines no finite exact quiet subspace. Retain the
original cutoff-indexed J(T), formed from physical Fourier constraints, only
as auxiliary test spaces. T labels those spaces; y=c/Omega(m)² is held fixed
while their nontrivial kappa>=1 sectors are scanned, Omega=2pi m/logm.
For r=dimJ, define gap=lambda_r(A_y)−||A_y Q||, using zero-based ascending
lambda_r. q=0,J=0 are never successes. Enumeration stops before q>=m+1;
no rank threshold or pseudoinverse substitutes a dimension.

A768-bit ordered twice-reorthogonalized MPFR frame followed by float QR
preserves all physical row prefixes. The input rows are computed at260 decimal
digits from the supplied coordinates; real Cauchy rows may be rescaled, while
two real rows for a quartet are kept together. The frame helper is byte-identical
to the pinned implementation. m600 repeats at1024 bits check conversion stability.

For every sector, compute delta or retain the rigorous-in-exact-arithmetic
upper estimate gap<=lambda_r. Branch pruning retains all sector receipts.
The computed best-gap bracket pads eigenvalue and residual calculations by
twice the matrix budget [1000 eps64 (m+1) max(1,||A||) plus four times
the observed full-versus850 prefix matrix difference]. A source operator
perturbation can change a gap by twice its norm; the factor2 reserves that
allowance, while subspace errors remain controlled empirically. This is a conservative observed-error convention,
NOT an outward bound for source error or unlisted zeros. Intervals touching0
are UNRESOLVED, never exact failure/closure. Matrix negatives are separately
reported using the original roundoff guard; all DH/plant levels are far larger.
annotate_scope.py performs this explicit postprocessing without changing any
eigenvalue, residual, frame or source matrix value.

## Independent source check

source_check.py convolves the original archimedean/arithmetic distribution,
without a zero-side sign assumption. For normalized autocorrelation R_ij,

    (A_y)_ij = c (G_y*R_ij)(0)
      + 2 integral_0^infinity j(s)[(G_y*R_ij)(0)−(G_y*R_ij)(s)] ds
      −2 sum_n b(n)/sqrt(n) (G_y*R_ij)(log n)
      +2 exp(y/4) F_i(i/2)F_j(i/2) [zeta only].

Finite-window R has explicit trigonometric formulas; its convolution is
computed with complex erf and Gaussian moments. Prime sums extend BEYOND m
to ceil(exp(L+12sqrt(y))); no nonzero arithmetic term inside that bound is
removed. The arch integral starts at1e-7, splits near the smoothed window edge,
and integrates to200, with an analytic-large-s simplification above30.
All five entries (0,0),(1,1),(m,m),(m−1,m),(0,m) at310/600, both worlds,
all three c are retained. This is60 spot checks, not a full operator bound.
The reported quadrature error estimates exclude the small-s omission and
finite prime/census tails; cancellation makes some estimates pessimistic.
They must not be consumed as interval certificates. Positivity of the finite
zeta zero sum is algebraic and by itself is not evidence for all-source RH.

controls.py independently integrates the physical Gaussian against complex
cosines, recomputes carrier evaluations at80 digits, and sweeps negative levels
at310/450/600 through c128. Comparisons of finite prefixes750/850, all source
pieces, frame controls and original sharp-gap values remain visible.
