# Structural audit before numerical execution

Route B CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.

## Quiet is not null

For the requested map Phi(t)=sum t_i Q^T C_i Q,
Phi(ones)=Q^T A Q identically. The pinned mp_pilots/QUIET.csv gives
max quiet eigenvalues1.3248257961,2.8663226352,.8378920490 at16,24,40.
These coexist with extremely small MINIMUM quiet levels. They are not a
numerically zero matrix. Thus imposing ones in the kernel would alter the
map and the source. Domain restriction t⊥ones is still a well-defined chosen
budget gauge, but is not a quotient by a genuine scaling null direction.

## The stated P3 optimum cannot be negative

At t=0, Phi(t)=0 and lambda_min=0. Therefore max over the stated ball is >=0,
for every input and every precision. A returned negative optimum indicates
solver/numerical failure, not a strict vertex. A zero optimum alone does not
distinguish strictness from a nonzero PSD direction. The unit-sphere variant
removes0 but is nonconvex; it cannot inherit the ball program's convex status.

## An exact invisible prime knob

At m prime, B_m contains only the atom at log m=L. Autocorrelation of the
zero-extended finite carrier vanishes at separationL. Consequently B_m=0
as a full finite matrix, and e_m is an exact kernel direction of Phi.
Keep and label this knob. Dropping it would silently change the requested
parameter space and its numerical kernel dimension.

## Controls must conserve all source terms

DH has non-prime-power atoms. Prime-power knobs alone cannot reconstruct
its B; an explicit remaining-atoms knob is needed, or its P1 gate fails.
The double2 knob B_2 must add only a second copy of integer2, not duplicate
all powers of2. DH's pole is absent, so a retained pole knob is identically0.
Double2 uses saved REFERENCE_J_zeta, not invented altered-source zeros.

## A finite SPD source is not a cone vertex

The MP pilots resolve positive finite-source eigenvalues. At such a finite
SPD baseline, all bounded symmetric source perturbations remain SPD for a
sufficiently small step. An approximate quiet compression can diagnose severe
stiffness and limiting behavior, but is not the exact tangent cone at a
singular boundary. No cofinal boundary or RH conclusion follows.

## Curvature normalization

F_a uses2cosh(a s)=2+a²s²+O(a⁴), hence
A_a=2A+a² A^(s²)+O(a⁴). On a fixed quiet direction q with curvature h<0,
the unrelaxed fixed-vector zero is approximately sqrt(2 lambda_q/abs(h)),
not sqrt(lambda_q/abs(h)). At a finite negative threshold -epsilon, replace
2lambda_q by2lambda_q+epsilon. Reoptimization, mixing and higher-order terms
can change the full-matrix first crossing. The registered factor2 comparison
and its original prediction must still be reported separately.

## Pole interval cannot have finite full width (S3)

Let P=p p^T=C_pole and G=A+epsilon I. At a strictly feasible baseline,

    G+(u−1)P = G^(1/2)[I+(u−1)vv^T]G^(1/2), v=G^(-1/2)p.

Thus, for s=p^T G^(-1)p>0, the full real interval is
[1−1/s,+infinity), not a narrow two-sided interval. If p=0 it is all real.
More generally a PSD baseline stays PSD for every u>=1 without requiring
invertibility. This analytically contradicts the pole portion of S3 unless
'width' is redefined to a one-sided decrement or an external coefficient box.
No such redefinition is silently adopted.

## A dual certificate that addresses the intended geometry

Choose an orthonormal domain basis V for1perp and N_j=Phi(V e_j).
The ball SDP remains a useful optimization but can never have negative value.
For nonzero-direction exclusion, seek

    maximize eta
    tr(Y)=1, Y>=eta I, tr(Y N_j)=0 for all j.

A strictly positive eta provides a positive-definite stress annihilating the
image. It excludes every nonzero PSD image: tr(Y Phi(t))=0 is incompatible
with Phi(t)>=0 and Phi(t)!=0. To exclude nonzero parameter directions too,
Phi restricted to the chosen domain must additionally be injective, or its
kernel must be reported and explicitly quotiented. The per-knob dual prices
tr(Y M_i) are then equal under the chosen1perp budget gauge. A global scaling
interpretation is unavailable unless Phi(ones)=0 is independently verified.

These statements have a separate bounded independent read-only algebra audit.
They do not constitute a numerical result for missing price matrices, a
source-level sign theorem, a cofinal limit, or an RH claim.

For a positive-definite dual Y with trace1, Y>=eta I, projected price
residual delta, and restricted smallest singular value sigma>0, a sufficient
uniform sphere bound is

    lambda_min(Phi(t)) <= -(eta*sigma−delta)/(1+eta*sqrt(r)).

It is useful only if the numerator is resolved positive. It combines actual
stiffness (sigma) with a full-rank stress (eta), rather than one-knob rankings.
No numerical dual is claimed in the absence of the price matrices.

At a prime-m invisible knob j, if k is the knob count and A_J>=0, the unit
budget-neutral direction t=(1−k e_j)/sqrt(k(k−1)) has
Phi(t)=A_J/sqrt(k(k−1))>=0. Thus merely changing the ball to a sphere does
not remove every structural softness; keeping zero knobs is consequential.

P5 distributional counterterm: if H=integral j(s)[2N−Q(s)] ds,
its deformation is integral j(s)[4N−2cosh(as)Q(s)] ds. The norm/Dirac
counterterm is at separation0 and only doubles; it is not multiplied by
cosh(as). The curvature arch term is −integral s²j(s)Q(s) ds, with no
s² norm/tail counterterm. The scalar cI curvature is0. Multiplying the whole
arch integrand by cosh would change the source and can create a spurious
divergence. This normalization was independently flagged in the algebra review.

## V2 addendum (owner-authorized continuation,2026-11-03)

The earlier input hold is resolved by explicit authorization to regenerate
unchanged pinned builders on calibration16,24,40,80,120,200,248,300 and
MP pilots16,24,40. The original v1 brief and its failed predictions are not
rewritten. V2 replaces J by a selected low spectral cluster only for P2–P3;
the original quiet frames remain inputs to P5 and comparisons.

V2's positive dual condition excludes nonzero PSD IMAGES when its equal-price
conditions hold. To exclude every nonzero PARAMETER direction, injectivity on
the declared quotient is also required. Kernel directions must be reported.
An approximate positive condition ratio with a nonzero equality residual is
not a strictness certificate. The actual MP selected face has dimension1,
large kernel and positive ball optimum, so no strict dual is inferred.
