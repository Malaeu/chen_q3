# Interval fallback — before its execution

Native python-flint is unavailable while the requested shared installation
has not returned an interpreter. Do not turn this into nearest-rounded
mpmath certification. The fallback uses mpmath.iv directed interval arithmetic
and encloses every Li2 power-series remainder explicitly. The source,
nodes, pivots, acceptance criterion and finite scope remain unchanged.

For Li2(real x), use reflection to a power series on [0,1/2]. For Li2(ix),
use Li2(z)+Li2(z/(z-1))=-log(1-z)^2/2; the transformed modulus is at most
1/sqrt2. The series tail is bounded by r^(N+1)/((N+1)^2(1-r)). Add that
bound to both rectangular components. Stop when the bound is below1e-50.
Use512-bit primitive interval arithmetic so series error dominates roundoff.

Prediction probability .99: M32 finite LDL still certifies at all3windows.
Discriminator: independent source sampling containment and a higher series
accuracy replay on at least W3; no midpoint sign is allowed to certify.
Budget: at most3minutes per cell; if fallback is too slow, report the
library limitation, preserving any completed certificates. Native Arb may
be used instead if an actual installed interpreter arrives.
