# Conventions and numerical gates

DIAGNOSTIC_NEVER_A_PROOF. N=m,L=logm; no carrier replacement.
Use the pinned arithmetic_coupling source/run.py and source/split.py unchanged:
400-bit source,GL192/eight panels for calibration dense arrays, paired256 at
16/300; MP pilots use GL256 and120-digit algebra. quiet/build.py is unchanged:
768-bit ordered MPFR construction, fixed orbit counts, float stored frames.
MP quiet bases use the inherited audit.py constructor at120digits.

## Knobs and face

C_Gamma=C−C_pole. C_pole=p p^T in zeta/double2, zero inDH. Each B_p is the
sum of the ORIGINAL signed translation-autocorrelation matrices at p^k<m.
The n=m atom is identically zero; it is retained as a possible invisible knob.
DH has an explicit B_nonprime remainder assembled from all its other signed
atoms, never reassigned to a prime. Double2 changes the integer2 coefficient
only. P1 binary tolerance is inherited rho=epsilon_m/100; MP tolerance1e−108.

For eigenvalues lambda0<=… and d=m+1, examine j1..floor(d/2). Binary ratio is
max(lambda_j,rho)/max(lambda_(j−1),rho); MP uses
lambda_j/max(lambda_(j−1),1e−114). The MP eigenvalues here are all positive.
Choose the first maximizing gap, F=lowest j eigenvectors and P=FF^T. Arrays
M_i=F^T C_i F are coordinates ON THE FACE of PC_iP. Lambda_min in P3 is on
this face, not on the full matrix padded with a zero complement. Every ratio,
floor and chosen dimension is retained. Secondary binary numeric_radius
sensitivity at MP pilots is separately labeled, not substituted.

Admit a near-null face for dependent P2/P3 only when
||F^T A F||2/max_i||M_i||2 <=1e−8. This is a declared numerical relative
criterion, not exact nullity. Conservation sumM_i=F^TAF is also measured.

P2 vectorizes symmetric matrices with sqrt2 off-diagonals, so Euclidean image
norm equals Frobenius norm. The parameter norm weights every named knob
Euclideanly, without column normalization. Binary reports a source-error
threshold and a separate1e−8 relative-face threshold, including both kernels.
MP numerical singular/inertia threshold is1e−110 times max(1,sigma_max).
On a scalar face full map rank1 means full kernel k−1, budget kernel k−2.
Ones is tested, not forced null; a small nonzero PAP remains nonzero in data.

## Primal, dual and intervals

P3's ball contains0. Its known feasible lower bound is0; a negative solver
candidate is NOT a negative optimum. Candidates are projected to1perp and
normalized into the ball. MP scalar optimum is exactly the projected price
vector's Euclidean norm and is recomputed at120digits. Finite dual upper
envelopes come from a PSD-projected trace-one candidate Y: the norm of the
projected price vector bounds the ball optimum. A zero-trace candidate gives
NO upper bound. Equal-price residual and positivity must both be checked
before calling Y an annihilating stress. Condition ratio alone is insufficient;
parameter-kernel directions additionally preclude strict coefficient geometry.
No binary SCS result is promoted to a strict dual or a resolved exact zero.

P4 acts on the FULL source, independently of a failed face gate. At a feasible
anchor, whiten A+epsilon I and the one knob to obtain interval ends from
extreme generalized eigenvalues, preserving offsets rather than rounding to1.
Known PSD pole has upper+infinity; an exact zero knob gives all-real or empty
according to baseline feasibility. For an infeasible PSD-pole baseline, a
negative vector in the knob kernel proves emptiness numerically. General
indefinite pencils reuse the pinned affine-cut/anchor/congruence algorithm.
Binary and MP inertia floors, feasible epsilons, empty witnesses and unresolved
labels are retained. Inertia is numerical; near-zero clusters are not certified.

P5 has its own independent source-reconstruction gate and exact preserved
A(0)=2A. See p5_RESULT.md for the distributional counterterms, curvature,
known-zero balance, root sampling and finite-threshold checks.

## Precision and scope

Binary source/frame arrays and MP caches remain local; exact file and array
payload hashes are committed. Original NPZ file hashes do not match this
regeneration. Recorded dimensions/input hashes and independent constraint
residuals validate the reproduced numerical spans; no original binary equality
or certified rank is inferred. Source errors/floors and all conic residuals
are empirical. Cluster selection itself changes with precision/floor. Results
are finite price diagnostics, not an exact source-cone tangent theorem.
