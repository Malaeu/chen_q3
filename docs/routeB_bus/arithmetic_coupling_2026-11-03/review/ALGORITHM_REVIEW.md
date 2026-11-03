# Affine arithmetic-coupling interval: bounded algorithm review

Put F(u)=C+u B+epsilon I=A(1)+epsilon I+(u-1)B, with real symmetric
matrices and ALL real u allowed. The feasible set {u:F(u)>=0} is a closed
convex interval, possibly empty, singleton, half-line or all R. Do not
truncate to u>=0 or assume u=1 is feasible in a control world.

## Feasible SPD anchor

If G=F(1) is positive definite, factor G=L L^T and form
H=L^(-1) B L^(-T) with triangular solves, then symmetrize roundoff.
Congruence gives F(u)>=0 iff I+(u-1)H>=0. Thus

    u_minus = 1-1/h_max_positive, or -infinity if none;
    u_plus  = 1-1/h_min_negative, or +infinity if none.

The most positive and most negative eigenvalues give the active endpoints.
An interior SPD anchor a works identically, replacing1 by a. A singular
PSD anchor cannot be Cholesky-whitened without a separate nullspace
analysis; adding jitter changes the requested problem and must be labeled.
The recovered Euclidean unit boundary vector is proportional to L^(-T)w,
not Lw, where w is the active H eigenvector. Check F(u*)v directly and
check a small step inward/outward, retaining a residual/error guard.
Repeated active eigenvalues require a boundary subspace rather than an
arbitrary uniquely named vector.

## Controls with no known feasible anchor

A robust bounded default is Rayleigh cutting planes. For each unit vector
v, alpha=v^T(C+epsilon I)v and beta=v^T Bv give the necessary affine cut
alpha+u beta>=0. Positive beta gives a lower bound on u, negative beta an
upper bound, and beta=0 with alpha<0 rules out the entire line. Start with
extreme B eigenvectors and any known negative C/A(1) directions. If B is
indefinite, its positive/negative directions give finite outer bounds.
At a trial u, evaluate the smallest eigenpair. A negative eigenvector gives
a new globally valid Rayleigh cut. Empty guarded cut intersection proves
numerical infeasibility without assuming u=1. A separated positive minimum
eigenvalue supplies the SPD anchor for whitening.

For efficient search maximize the current piecewise-affine upper envelope
min_i(alpha_i+u beta_i), e.g. a two-variable LP maximizing t subject to
 t<=alpha_i+u beta_i and current outer u bounds. This is an upper bound on
max lambda_min(F(u)). If that upper bound is separated below zero, the
feasible set is empty. A budget stop near zero is UNRESOLVED, not empty.
The signs in these cuts must include arithmetic uncertainty. Checking a
trial with a float minimum slightly above zero is not an SPD certificate.

Generalized QZ eigenvalues solve det(C+epsilon I+u B)=0 and are useful
candidate endpoints. Enumerate real roots, sort/cluster, and test every
open component plus its endpoints; sample both unbounded components too.
Do not call all real roots interval boundaries or declare emptiness merely
because no convenient real root appears. Singular B gives infinite roots;
a singular pencil can have determinant identically zero, and repeated
real roots can acquire numerical imaginary parts. Singleton feasible sets
(e.g.diag(u,-u)) have no SPD anchor and need explicit handling. For
semidefinite B, feasibility can be unbounded or empty with supremum0
attained only at infinity; finite cutting-plane iterations need not decide
that case. Return unresolved or perform a separate kernel/recession
analysis instead of forcing a bounded interval answer.

## First-exit slopes and epsilon scale

At a simple boundary eigenpair with ||v||=1,

    d lambda/du = v^T Bv,
    du*/d epsilon = -1/(v^T Bv),

when the boundary branch is differentiable and the slope is nonzero.
Lower-boundary inward slope is positive and upper-boundary slope negative.
A small slope makes endpoints epsilon-sensitive; slopes zero/repeated
modes require subspace/tangency analysis. Eigenvector phase is arbitrary.

For a genuinely PSD reference A(1), decompose into its kernel K and a
positive block G. With t=u-1, the Schur complement near t=0 is

    epsilon I_K + t B_KK
      - t^2 B_KP (G+epsilon I+t B_PP)^(-1) B_PK.

If B_KK vanishes and the quadratic coupling is nonzero, the leading exits
can be order sqrt(epsilon). If B_KK has nonzero eigenvalues, corresponding
exits are order epsilon; if it is indefinite, both sides can be order
epsilon. Uncoupled null directions or higher degeneracies can behave
differently. Therefore square-root width is a conditional Schur mechanism,
not a universal law of this finite grid. Compare epsilon multiples with
both sqrt(epsilon) and epsilon scalings and report which boundary/mode
fits, rather than forcing one model. The toy tests demonstrate both scales.

## Source/quiet-space conventions and epsilon

Doubled_atom2 means double ONLY the n=2 atom. It does not double n=4,8,...
and does not replace all arithmetic coefficients by2b(n). For every world
write B explicitly from signed arithmetic moments, with all gamma, pole
and constant terms retained in C. For planted worlds the planted finite-
rank term belongs to the fixed C unless the task explicitly couples it.

Kappa1 quiet membership uses that world's actual zero rows and rank,
including two real rows per quartet. Report ||E v|| after row scaling,
||U^T v||, ||Q^T v|| and/or projector distance. Near-degenerate boundary
vectors may rotate, so a subspace comparison is preferable. D=Q^T A Q
near the float floor is unresolved; its tiny signed eigenvalues are not
resolved physical quiet modes. Do not infer membership from a tiny raw
Fourier value alone, since row norms vary sharply.

Epsilon=100*float_numeric_radius is a declared tolerance experiment, not a
source-positivity certificate. Source uncertainty for variable u also
changes with u: if C and B have norm-error budgets e_C,e_B, the pencil
error budget is e_C+|u|e_B. A radius valid only at u=1 does not uniformly
bound an unbounded u interval. Run separate intervals at explicit epsilon
multiples (e.g.half/base/double) and track endpoint sensitivity; do not
confuse that sweep with random error bars. Use the same epsilon for a
well-defined comparison across worlds or record why per-world values differ.
Freeze the exact epsilon choice and source split in output metadata.

`algorithm_tests.py` and ALGORITHM_TESTS.json contain bounded synthetic
checks for negative-u endpoints, sqrt/linear epsilon scaling, an empty
pencil despite two real generalized roots, and a singleton. No expensive
source pilot was run and no continuum/source spectral claim is made.

DIAGNOSTIC_NEVER_A_PROOF. No RH or route-state export.
