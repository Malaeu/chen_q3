# Full raw intake of the Euler conditional comparison

STATUS: ACCEPTED_PAPER_CONDITIONAL_COMPARISON_ONLY.
Date: 2026-09-16. No Lean or canonical admission; full V and RH remain open.

## Immutable input and provenance correction

Input commit: ef41d39ac265f475717437882b54ec5494115476.
Path: docs/routeB_bus/proshka/PROSHKA_EULER_CONDITIONAL_COMPARISON_2026-09-16.md.
Git blob: 853d5985c232320140ee1fa104fb6db04f00e5b1.
Actual SHA256: 88d402d04a7dcc019d5ffd7a747fff979d55ec31b3f2c47b26031fe7ea6f4607.
39331 UTF-8 bytes, 421 LF, zero CR, final LF.

Initial publication 341bbc98991e953851c57330a208fba546b6af2c instead had
SHA256 79218063594f447b27fd3ba37b4823db176045e39550424fdbc59cfd4b6783e4,
39266 bytes and 422 LF, which did not match its commit-message hash.
The producer corrected the transport in two subsequent commits; final bytes
now match the originally announced SHA256 exactly. Both readers checked the
complete initial mathematical text and the full final delta: equivalent
Young-inequality prose and reformatting of the unchanged E15. The final
source pin is the corrected Git blob above. The historical mismatch is
preserved as provenance. No independent direct sandbox download is claimed.
This is a complete-text audit, not merely the earlier pasted-summary audit.

## Accepted mathematical statements

For the actual full conditional density p_t(s)=t h(ts)h(t(1-s))/r(t),
the source's exponential-convolution construction proves log-concavity;
exchange of the two copies proves symmetry. For complex symmetric signals,

    Var_(p_t)(q) <= (1/(4*pi^2)) integral |partial_s q|^2 p_t ds.

The constant is uniform in t and optimal on the ambient symmetric class.
No optimality on the restricted source-translate span is claimed.
The map is H(s)=integral_0^s p_t(q-E_tq), u=H/sqrt(p_t) on (0,1/2).
It uses the original s coordinate, not a quantile coordinate. Symmetry gives
H(1/2)=0. The full small-s source estimates pay the other endpoint and the
potential term in E8/E9. All complex phases are preserved by polarization.

Parent independently checked the physical derivative identity E11:
sqrt(barW*p_t) contributes t^(3/4), differentiation contributes t, yielding
t^(7/4). The factors D_a and J_a retain both endpoint exponential budgets
for a in (1/2,1); integration against the probability density r* pays the
whole t>=1 domain. No t integration by parts or missing cutoff trace occurs.

For the original finite complex family the accepted consequence is

    L[c] <= (D_X[c]+sqrt(D_G[c]D_B[c]))/(2*pi^2),
    V[c] >= L_pi[c]
          =M[c]-(D_X[c]+sqrt(D_G[c]D_B[c]))/(2*pi^2).

This is an upper bound on the complete loss, including an upper bound by
the modulus of its mixed covariance. It does not prove that the lower
envelope L_pi is nonnegative. The source deformation in section 10.3
preserves the conditional estimate; it is not claimed to preserve the
entire exponential-rate construction as a new marginal source.

## Already resolved next test

REPORT_2026-09-16_POINCARE_BUDGET_OBSTRUCTION.md at commit
345dfea4365498cfdff460e78620f4d717e49147 independently proves that, for
every fixed kappa>0, some admissible finite actual-source row has
M-kappa D_X<0. Consequently all-row L_pi>=0 is false. The inequality
V>=L_pi remains valid. A negative lower bound is not a negative V witness.

The source primitive covariance identity E9 remains available for a
signed comparison. Its equality of mixed terms must be retained; the
accepted scalar constant cannot be promoted to a full-sign supplier.
The ongoing request REQ-2026-09-16-POINCARECOMP already asks for that joint.
This intake is not a duplicate dispatch and does not close that request.

## Independent review

Reviewer /root/sibling5_check accepted the conditional comparison only.
Initial complete audit SHA256:
d4aa4f36b08d113a8e25970608c1ce047c589f78028929303508d318f6390437.
The final delta review and both review texts are pinned in the accompanying
certificate. The initially required hash correction is now resolved by
reading and hashing the producer's corrected immutable Git bytes.
