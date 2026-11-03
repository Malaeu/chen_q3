# Uniform extension margins, before numerical execution

DIAGNOSTIC_NEVER_A_PROOF. No route-state changes.

P1 (probability .99): for a positive old history and one new endpoint at Delta,
the margin equals the next saved innovation divided by 2Psi(Delta). It crosses
zero at the planted/DH first negative extension, but need not equal the planted
2x2 negative-capacity margin numerically. Compare direct Schur controls.

P2 (probability .8): representative finite new-node blocks at q=4,8,16,32 have
nonincreasing margins on the nested dyadic future grid; zeta stays positive
through the tested length6 histories. These are upper approximants to the
all-node margin and cannot certify its positivity. Record both past and fresh
positivity guards, no pseudoinverse truncation or indefinite whitening.

P3 (probability .5): the finite-future zeta margin stays above .1 for Delta
at representative histories a=1..6. This is a separate finite-grid check,
not Mythos's arithmetic-section claim. Kill if any supported value is below.1;
do not choose a more favorable future grid afterwards.

P4 (probability .8): zeta's sampled extensions on the fixed microgrid Delta/4
stay positive to cap1/4 after histories a=1,3,6. This measures a capped sampled
lower bound on the first failure length, never the greatest admissible step
in the full infinite-dimensional future. Conditional on RH the full-step
supremum is infinite; no finite zeta delta-star is assumed to exist.

Numerics: source entries from exact finite arithmetic hinges and full closed
arch/pole formulas, vectorized float64. Old covariance comes from saved MP100
source r arrays. Validate source values and selected margin cells independently
at80digits; any near-zero unresolved guard blocks sign interpretation.
Budget: 12 q1 saved-grid conversions; 4meshes*3worlds*6histories*q1,4,8,16,32
with extra pre-onset samples; three nested extension searches per mesh for zeta.
No dense all-prefix eigenproblems. Stop if normalization/source replay fails.

Independent validation registered before its run: compare float margins to MP80
on zeta(mesh32,a6,q32,delta=Delta), zeta(mesh32,a6,q32,delta=1/4),
DH(mesh32,a5,q8,delta=Delta), plant(mesh32,a45/32,q8,delta=Delta),
and zeta(mesh256,a1/4,q8,delta=Delta). Prior .99 that all absolute differences
are below1e-6. Repeat the last small cell at120digits. Stop sign claims if
errors are comparable to the claimed margin. Dense MP80 factors are independent
of float Cholesky, but share the exact source formula and old covariance inputs.

Before additional refinement run (owner integration request): zeta a=6,
delta=Delta at all four meshes, q64 and128, prior .9 that q32-to128 margin
change is less than.01 absolute. These dyadic grids are nested. This is a
stability diagnostic, not a rigorous bound on the uncomputed infinite tail.
