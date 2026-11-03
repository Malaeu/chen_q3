# Exact coordinate invariance and bounded Hermite checks

DIAGNOSTIC_NEVER_A_PROOF. This is a row-coordinate identity, not a new
separator/source bound or an RH assertion.

For two distinct included real height events a<b with physical Fourier
rows E(a),E(b), define

    S=(E(a)+E(b))/2,   D=(E(b)-E(a))/(b-a).

The2x2 row matrix [[1/2,1/2],[-1/(b-a),1/(b-a)]] has determinant1/(b-a),
so it is invertible. Replacing exactly those two INCLUDED rows preserves
the row span, ker(E), its physical orthogonal projector, r, and lambda_r.
Consequently delta=||A|ker(E)|| is exactly unchanged for every fixed source A.
The identity requires no assumption on zero signs or a zero-free region.
It applies source-independently to all eligible same-multiplicity edges of
the frozen pair map, without numerically recomputing the full945-cell grid.

For adjacent events each carrying two real rows (complete complex quartet
constraints), apply this invertible transformation separately to real and
imaginary branches. This is an invertible4x4 block transformation and keeps
both complete orbits. If their imaginary offsets differ, the operation is
still an exact divided-difference row-coordinate change, not necessarily a
complex derivative along a constant-offset line. A one-row line event and a
two-row quartet cannot be silently paired using the two-row recipe; mixed
multiplicity edges are not numerically transformed here.

Every pilot constructs PHYSICAL rows with the factor
2t sin(tL/2)/sqrt(L) before forming S and D. Removing a height-dependent
scalar before differencing changes the coordinates being tested, even
though each raw scaled row separately spans the same one-dimensional space.
The source carrier is the original endpoint-signed cosine basis. The same
768-bit native algorithm computes raw and transformed frames; source matrices
and lambda_r are reused identically, not recomputed or optimized separately.

Pair admissibility uses the USER local mean spacing
s(t)=2pi/log(t/(2pi)), not2pi/L. theta=.5,.6,.75 activates only frozen T1
near-window edges below that ratio. No event count or complete quartet is
split or deleted. The numerical pilot q can be an explicitly labeled
additional whole-orbit sector required to INCLUDE both events; it is never
reported as the original optimizer when it differs.

Numerical checks are bounded representative pilots. Fine projector/delta
agreement is a diagnostic, not an interval source or subspace certificate.
A relative delta comparison is scored only when delta exceeds its original
heuristic guard; floor-relative comparisons remain UNRESOLVED. Inactive
identity cases do not count as executed nonidentity Hermite validations.
The exact row-span argument, rather than an unexecuted grid of numerics,
is the full-grid coordinate-invariance statement.
