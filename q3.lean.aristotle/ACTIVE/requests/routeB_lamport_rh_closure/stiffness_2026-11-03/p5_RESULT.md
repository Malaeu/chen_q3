# P5: counterterm-preserving 2cosh deformation

DIAGNOSTIC_NEVER_A_PROOF. Route B CHALLENGER / NOT_RH.

Only the owner-authorized unchanged calibration sources/frames and cached MP
pilots are consumed. No saved source/frame is replaced or reselected by p5.py; the independent a=0 gate reconstructs its formula without calling split.build. Binary calibration:
m=16,24,40,80,120,200,248,300. MP pilots:16,24,40; source400bits,
GL256/8panels, mpmath120dps; epsilon=1e-100. Binary epsilon is read verbatim
from pinned SUMMARY.csv. Source and cache SHA-256 are saved per cell.

## The source deformation

Write Q(s)=2R(s), k(s)=exp(s/2)+exp(-s/2), and b_n/sqrt(n)=w_n.
The scalar source constant is c. The physical deformation is

    arch_a = integral_0^L j(s)[4I-4cosh(as)R(s)]ds
             +4I integral_L^infinity j(s)ds,
    scalar_a=2cI,
    arithmetic_a=-4 sum_(n<=m) w_n cosh(a log n)R(log n),
    pole_a=4 integral_0^L k(s)cosh(as)R(s)ds   (zeta only).

In particular the norm/Dirac counterterm only doubles. It is NOT multiplied
by cosh. The birth atom n=m has Q(L)=0 exactly, explicitly enforced in every world.
DH uses its own odd gamma kernel, all signed integer coefficients,
its own c, and has no pole. Double2 adds only one extra n=2 atom.

For stable evaluation A_a=2A+Delta_a uses the saved source A and
cosh(t)-1=2sinh(t/2)^2. Delta is built from every unchanged source atom and
quadrature weight, including the deformed pole. There is no extra floor,
ridge, tuned constant or scalar normalization of the deformation.

An independent regularized reconstruction of A is compared against the
saved source before any dependent computation; gates pass in every executed
cell. The MP maximum entry discrepancies are approximately
4.0275e-119,5.9638e-119,9.6040e-119, versus declared allowance1e-110.
Thus A_0=2A exactly in the preserved-baseline evaluation, with a separate
non-tautological source-definition check. This is not an interval certificate.

## Curvature and known-zero decomposition

The expansion is A_a=2A+a^2 H+O(a^4), where

    H_arch=-2 integral s^2 j(s)R(s)ds,
    H_arithmetic=-2 sum w_n(log n)^2 R(log n),
    H_pole=2 integral s^2 k(s)R(s)ds,   H_scalar=0.

Each cell keeps the basis it actually consumes; the explicit same-frame
confirmation below uses the unchanged quiet/build.py saved columns.
p5_basis.csv records every consumed basis
curvature diagonal, its known-positive-zero lowpart

    -4 sum_(0<gamma<T) (E'_q(gamma))^2,

and source minus that lowpart. p5_spectra.csv records the FULL curvature
compression spectrum and spectra of both corresponding matrix pieces.
The latter difference is a SOURCE BALANCE, not an independently summed,
certified or sign-controlled infinite zero tail. At finite precision it also
retains any nonzero evaluation residual of the quiet frame. No RH positivity
or complete infinite zero census is assumed for this remainder.

**S4 (.90) FAILS for the owner-authorized regenerated quiet/build.py frame.**
The authoritative same-column MP check is p5_S4_FRAME_CONFIRMATION.csv/json.
This score concerns the unchanged-builder REGENERATED frames used in this
execution. Original archived NPZ byte hashes were not matched, so no score
on the original-byte frame artifacts is asserted.
At m24, saved Q column16 (zero-based, the17th column) has curvature
+1.7871964414710223799, far above the source floor. The exact binary64
coefficients are lifted into MP120dps unchanged, without reorthogonalizing
or replacing the frame. MP confirms all authorized-regenerated frame columns negative at16
and40; a single robust positive m24 column falsifies the all-pilots claim.
Binary calibration also sees a positive saved-frame column at120; no extra
MP pilot beyond16/24/40 is introduced.

The confirmation additionally projects EACH ORIGINAL COLUMN onto the cached
MP quiet span and normalizes it, retaining its orientation. Per-column
projection differences and projected curvatures are saved. The m24 positive
value survives this tiny leakage correction, so nonexact binary quietness
cannot explain it.

Separately, original p5_mp_m*.json quiet_basis_diagonal fields refer to the
cached audit.quiet polynomial/MGS basis, NOT the quiet/build.py frame. Those
alternative-basis diagonals are all negative at16,24,40; this basis-specific
fact does not rescue registered S4. The existing cell JSONs are preserved
unchanged for provenance. p5_summary.csv reflects the basis actually used in
each cell; use the new same-frame confirmation for the registered S4 score.

All three full MP curvature compressions nevertheless have resolved positive
eigenvalues, with maxima approximately3.3637992e-5,3.5645479,1.6609710e-8.
Thus negativity of the alternative basis diagonals never implied negative
definiteness. Tiny eigenvalue signs at the source/float floor remain unresolved.

## First sampled negative threshold and S5

A negative threshold means lambda_min(A_a)<-epsilon. The numeric search
brackets by doubling and bisects; it reports the first sampled crossing,
NOT a global no-earlier-crossing/monotonicity theorem. At MP, Cholesky of
A_a+epsilon I supplies the cheap finite threshold test; both final full-source
bracket endpoints are independently checked by minimum eigenvalues. Their
sign margins are above the empirical ~1e-114 source floor. No precision chase
or conversion of that empirical floor into an outward-rounded bound occurs.
Binary root digits are point estimates only; ±10% coarse checks are retained
because fine binary bisection signs can be at roundoff.

|m|full-source a*|full / registered sqrt(lambda_q/abs h_q)|full / corrected sqrt((2lambda_q+epsilon)/abs h_q)|
|---:|---:|---:|---:|
|16|1.228549462e-16|1.414016529|0.9998606762|
|24|8.733477978e-25|1.414106752|0.9999244737|
|40|2.716368803e-40|1.414190075|0.9999833919|

S5 (.75), within factor2 of the originally REGISTERED expression, passes
all three pilots. The corrected factor2 formula nearly predicts the fixed
quiet-minimum trial crossing; reoptimization makes the full-source crossing
slightly earlier. p5_summary.csv reports BOTH full and fixed-trial roots and
both predictions. The original prediction is not retroactively replaced.

The binary calibration full crossings are approximately
3.0880e-5,3.5447e-5,3.1218e-5,3.5255e-5,4.2339e-5,4.8526e-5,
5.3534e-5,5.9419e-5. Those finite-epsilon/float calibrations do not estimate
the extremely smaller unregularized/MP thresholds. Their baseline quiet
minimum directions can be unstable within the float near-zero cluster.

## Controls and boundaries

p5_controls.csv retains DH and double2 source reconstruction gates and
baseline negative detections, plus the existing pinned low-quartet plant
at gamma=2pi/log2,beta=.25. The plant baseline is exactly
2[A_zeta+4Re(E(z)E(z)^T)], not a substitute for a source-correct false world.
For a literal convolution-quartet kernel, its 2cosh deformation replaces its
baseline contribution by

    4Re[E(z+ia)E(z+ia)^T+E(z-ia)E(z-ia)^T].

This identity shows the beta±a split; it does not imply monotone growth of
the negative eigenvalue on every selected vector. No altered-source zero
list is invented. Controls already negative at a=0 have first-negative dial0.

All results are finite numerical diagnostics. They do not prove a cofinal
stiffness, a cone vertex, a favorable prime sign, or RH. S4 and S5 outcomes
are recorded with their original meanings and probabilities.

Replay (requires the parent's unchanged source/frame regeneration and MP
cache preparation, then no additional reconstruction by this script):

    PYTHONPATH=/workspace/stiffness/deps python p5.py float 16 24 40 80 120 200 248 300
    PYTHONPATH=/workspace/stiffness/deps python p5.py mp 16 24 40
    PYTHONPATH=/workspace/stiffness/deps python p5_summarize.py
    PYTHONPATH=/workspace/stiffness/deps python p5_s4_confirm.py
