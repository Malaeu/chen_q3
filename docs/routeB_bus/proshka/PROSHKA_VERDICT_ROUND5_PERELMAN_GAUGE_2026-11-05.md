# STATUS: TRY_ROUND5_PERELMAN_GAUGE

```yaml
OPERATIVE_CLASS: TRY_ROUND5_PERELMAN_GAUGE
ARTIFACT_STATE: FROZEN_BEFORE_CONSTRUCTION
REQUEST_COMMIT: 7755fdf8bcc751c445e04508c203758032cda7ec
REQUEST_BLOB: 4c533a5b151986fbae40ebc7cbd691a925375b06
ADDENDUM_BLOB: 764ecbcdd61cbf0c80e45c3f5c1a0a1447b4ee81
ROUND4_A_COMMIT: 7a1d9a53e9972a0339369fe7b866d89e36cabe38
ROUND4_B_COMMIT: dd22692d
WRITE_BRANCH: proshka_inbox_2026-10-31
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: UNPAID_SIGNED_PRIME_FLUX
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: DUALIZE
ROUTE_SCORE: 2
```

<!-- FROZEN_R5_BEGIN -->
## Frozen S5: quotient gauge and physical flux

[ABSTRACT | CONDITIONAL] For every m>=3 set L=log m, K_m={z:z_0=0,p_m^*z=0}, G_m=I+diag((2*pi*j/L)^2). Import the literal damping A_m(delta), delta in [0,1/2], and its terminal positivity from Round 4 B §§1,4; import its exact arithmetic derivative (6.2)-(6.4) and 9/25 budget. Import Round 4 A's radial full-xi curvature only as a comparator, not an equality with the finite window.

Define the fixed G-orthogonal projection P_m onto K_m and compression B_m(delta)=P_m G_m^(-1/2)A_m(delta)G_m^(-1/2)P_m on the G-normalized admissible subspace (equivalently use an orthonormal basis of G_m^(1/2)K_m). Use only counterterms of the form C_m(delta)=C_m(delta)^* with P_m C_m(0)P_m=0; require exact endpoint invariance on K_m. For the primary candidate require the stronger identity P_m C_m(delta)P_m=0 for all delta, so that the entire compressed path is invariant. The candidate functional is W_m(delta)=U_m(delta)^*B_m(delta)U_m(delta)-a_m(delta)I, with U unitary, U(0)=I and a_m(0)=0. Seek W_m'=-R_m^*R_m and a_m(1/2) bounded by polylog(m). Do not assume this is achievable.

A second, explicitly separate candidate permits interior changes P C(delta)P !=0 while keeping P C(0)P=0 and terminal PSD. Such changes are not gauge invariances of the path: their derivatives and terminal difference must be paid in an exact telescoping identity. Do not optimize over unrestricted paths and claim an arithmetic estimate.

Register before testing:
P1: quotient-gauge terms vanishing on the admissible space cannot change the compressed velocity or its optimal eigenvalue-transport loss.
P2: allowing arbitrary interior paths collapses the action to an endpoint negative-eigenvalue budget, hence merely renames the original sign gap.
P3: a source-exact positive-square flow, if it exists, must expose a nontrivial arithmetic one-sided inequality for the joint prime error E_psi in Round 4 B (6.3); the 9/25 bound alone cannot do this.
P4: the radial xi square cannot equal the literal window generator without a new source-to-window identity and boundary control.

Falsifier: finite exact 2x2 Hermitian paths and a planted off-line quartet before any large numerical run. No numerical success can close a cofinal quantifier.
<!-- FROZEN_R5_END -->
