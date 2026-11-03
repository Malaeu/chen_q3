# Final bounded coupling-interval review

No blocking mathematical or convention issue found for the stated
finite, epsilon-relaxed numerical problem. Reviewed solve.py, all855
factor100 primary receipts and the MP pilot documentation. Independent
dense endpoint checks at zeta16,zeta248 andDH54 are in VALIDATION.json.
No full-grid source rebuild or interval certification was performed.

Counters agree:285 zeta NONEMPTY,285 double2 EMPTY, DH16–54 NONEMPTY(39)
and55–300 EMPTY(246). Every reported finite lower endpoint has positive
arithmetic slope, every upper endpoint negative slope. The whitening is
H=L^-1 B L^-T with G=C+aB+epsilon I=L L^T. Endpoints a−1/h_extreme and
Euclidean carriers L^-T w are correctly oriented. Direct endpoint residuals
in the six checked cases are<=2.22e-15; interior minima are positive,
while the designated outside steps have negative minima. Tiny signed
endpoint closure errors at binary64 precision remain closure residuals,
not evidence of an open interval or a certified source boundary.

Global EMPTY outputs are supported by incompatible affine Rayleigh cuts
on ALL real u, rather than a search restricted to positive u or a failed
anchor at1. The positive convex weights combine one positive and one
negative cut slope to zero algebraically and a strictly negative constant.
Every EMPTY receipt has outer_lower>outer_upper and dual_constant below
−dual_guard; the smallest ratio of negative constant magnitude to guard
is4.8463e6. Printed dual slopes have roundoff up to1.23e-15. The intended
slope cancellation is exact for the algebraic cut construction; the float
residual is not itself an interval all-real certificate. The cuts and
source-error accounting remain numerical diagnostics, as labeled.

The epsilon definition is shared across worlds at each m:
100 times rho, with rho=1000*eps64*d*max(1,max_world(||C||+||B||)). Thus
comparisons do not silently use different per-world tolerances. This is a
conservative chosen experiment scale, not an established source error
bound. The metadata correctly states pencil uncertainty depends on u as
e_C+|u|e_B; rho*max(1,|u|) is a heuristic scale. No fixed-radius guarantee
at u1 should be extrapolated to arbitrary u. Anchors are checked with a
margin before Cholesky; recession/tangency/iteration outcomes are explicit.
The reported primary interval is I_epsilon, not I_0.

The quiet reference for double2 is explicitly the zeta reference carrier
kernel, not a claimed census of its own zeros. Zeta and DH use their own
kappa1 quiet frames. Primary zeta endpoint quiet masses are between
.9999999999999981 and1.0000000000000024, consistent with membership up to
float projection error; the tiny excursion above1 is not physical.
All285 zeta quiet minimum eigenvalues remain labeled float-floor
unresolved. Consequently primary endpoint overlap with an individual
numerically rotated quiet near-zero eigenvector is not a resolved mode
identification. The zero-cluster mass is the appropriate robust quantity.

The separate MP pilots at16,24,40 retain endpoint offsets as MP strings
rather than adding them to1 in float. Their epsilon sweep shows numerical
plateaus at intrinsic scales in those selected windows. This supports a
sensitivity distinction; it is not a proof that the plateau equals the
exact unrelaxed source interval. Their upper endpoints have nearly unit
overlap with the first positive quiet mode; their lower endpoints are
approximately93%/7% mixtures of the first two quiet modes, not pure quiet
mode2. Those MP mode assignments are separate from the unresolved full-
grid float quiet spectrum. Pilot source/span floors and quadrature checks
remain numerical; no full-grid MP extrapolation follows.

Doubled_atom2 must retain its documented meaning: doubling n2 only, not
all powers of2 or all arithmetic terms. The reviewed solver consumes C/B
as supplied; source split correctness is a separate provenance obligation.
No exact source PSD, continuum, RH or route-state conclusion is warranted.

DIAGNOSTIC_NEVER_A_PROOF.
