# Independent finite extension-margin conventions control

DIAGNOSTIC_NEVER_A_PROOF. No route-state change or mathematical proof claim.

Before running these new cells:

P1, probability0.99: fixed-history, fixed-delta dyadic future-node refinement
q=1,4,8,16,32 gives nonincreasing finite margins whenever C and F remain
positive. DISCRIMINATOR: direct increment Schur, direct point Schur and
whitened cross-block norm agree; no pseudoinverse clipping. Nested future
spaces, not equal count on moving nodes, underlie this check.

P2, probability0.95: the source's section16 cell remains positive across
these refinements even though its scalar beta-rho lower envelope is
negative. This illustrates that failure of the scalar lower envelope is
not failure of the sampled full-form comparison.

P3, probability0.95: for a fixed four-node past, shortening delta from
log(17/16) to1e-3 and1e-5 increases the margin toward one on all q. Fresh-only
infill does not by itself force a zero margin at the common boundary.
DISCRIMINATOR: separate q-refinement from delta shrinkage. This says
nothing about simultaneously refining the old history.

Budget: the fifteen zeta cells above at70digits, plus repeat q=32 for
section16 at100digits. Stop if a C or F eigenvalue is nonpositive or unresolved;
record that guard rather than selecting a numerical pseudoinverse. No longer
scan or fitted extrapolation if the proposed pattern fails.

Addendum before the requested coarse-budget replay: repeat the five section16
cells at80digits and retain all70/80/100 calculation digits in the margin field.
P4 (normalization replay, probability0.99): stable direct g-prime integration
will reproduce the source's negative scalar envelope while the finite margins
remain positive. The source has already supplied the sign; this is a precision
and convention check, not a new discovery prediction. Retain both pole terms
and the full arithmetic response. Budget adds one4-by4 quadrature at80digits.
