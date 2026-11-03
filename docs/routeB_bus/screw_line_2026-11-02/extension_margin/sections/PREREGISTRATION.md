# Arithmetic-section extension margins

DIAGNOSTIC_NEVER_A_PROOF. Registered before this run.

For n=2..240, a=log n and delta=log((n+1)/n), retain every old uniform
increment of mesh1/32,1/64,1/128,1/256 up to a, plus the final partial
increment ending exactly at a. Use zeta, DH and the same planted quartet.
Test q1 on every section and nested q1,4,8,16,32 on n16,32,64,120,240
and the q1-minimizing section for each world/mesh with positive old history.

Mythos prediction, probability0.4: zeta min mu_q across the requested
arithmetic sections stays at least0.1. DISCRIMINATOR: fresh-node refinement,
old-mesh refinement, direct Schur normalization and a selected80-digit
replay. Reject the finite prediction if one validated zeta margin is below0.1;
do not adjust the bound or delete that section.

Implementation control, probability0.99: nested future refinement makes mu_q
nonincreasing wherever C and F are positive. DISCRIMINATOR: validate all
future F factorizations and the partial-old Schur pivot; never apply a
PSD inverse after old negativity. Prefix signs are guarded by the existing
100-digit main scan as well as the new partial-interval pivot.

All n<16 are marked outside the source's proved delta<=1/16 coercivity
range. Their sampled F positivity is checked directly rather than imported
from that lemma. Finite positive mu does not certify the all-node margin.

Budget: twelve239-section q1 scans, the prescribed representatives and
argmin sections, plus meaningful selected80-digit replay. No installations,
new eigensystem of CCM carriers, route-state edits or mathematical proof.
