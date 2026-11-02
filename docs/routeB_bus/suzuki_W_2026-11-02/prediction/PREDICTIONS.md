# Preregistered finite prediction probe

DIAGNOSTIC_NEVER_A_PROOF. Registered before numerical runs.

Pinned source: inbox ab8d123, PROSHKA_VERDICT_SCREW_LINE_INVARIANT_v1_2026-11-02.md, Git blob b56a16a0540ed3f81858c113bc48de68c909b8c8. The planted model is §6.2, formula (18), not §5.

P1: constant-mode identity g(L)=-L A00/2 agrees with literal source, including the zeta pole and all DH logarithmic-derivative coefficients.
P2: zeta finite prefixes are predicted positive, but this is a diagnostic prediction, not RH or a premise. DH and the planted source are predicted eventually indefinite; detection by t<=6 is not guaranteed.
P3: prime hinges do not imply a positive Schur increment. The complete prior kernel stays fixed when probing a new endpoint across a hinge.
P4: 80-to-120 digit replay preserves resolved signs. Failure invalidates those signs until repaired.

Kill switches: an unresolved signed LDL pivot stops that prefix sequence (no pseudoinverse truncation); range failure is reported separately. Float eigenvalues below an explicit conservative roundoff diagnostic floor have unresolved signs. No finite positive scan is promoted to global positivity. A missed negative control by t=6 is censored, not declared positive globally.

Kernel: K(s,t)=g(s-t)-g(s)-g(t), g even. t=0 is an exactly zero structural row and column; its range component is identically zero. All other pivots, including negative ones, are retained. For nonsingular prefixes Kdagger=K^-1. Singular nonstructural cases require a separate range/eigenspace calculation and are not silently processed.
