# STATUS: TRY_ROUND5_PERELMAN_GAUGE

```yaml
OPERATIVE_CLASS: TRY_ROUND5_PERELMAN_GAUGE
ARTIFACT_STATE: FINAL_PAPER_VERDICT
REQUEST_COMMIT: 7755fdf8bcc751c445e04508c203758032cda7ec
REQUEST_BLOB: 4c533a5b151986fbae40ebc7cbd691a925375b06
ADDENDUM_BLOB: 764ecbcdd61cbf0c80e45c3f5c1a0a1447b4ee81
ROUND4_A_COMMIT: 7a1d9a53e9972a0339369fe7b866d89e36cabe38
ROUND4_B_COMMIT: dd22692d
WRITE_BRANCH: proshka_inbox_2026-10-31
RH_PROVED: false
PROVED_STEPS: [{id: NULL_GAUGE_RIGIDITY, scope: FINITE_CELL, verifier: PAPER}, {id: UNRESTRICTED_PATH_ENDPOINT_SHORTCUT, scope: ABSTRACT, verifier: PAPER}]
RH_GAP: UNPAID_JOINT_PRIME_ERROR_EIGENBLOCK_SIGN
PROGRESS_CLASS: PROOF_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: [{id: UNRESTRICTED_PATH_AS_INDEPENDENT_SUPPLIER, KILL_SCOPE: THEOREM_SHAPE, KILL_EVIDENCE_KIND: EXACT_VARIATIONAL_IDENTITY, evidence: R5.4}]
CLOSES: [NULL_GAUGE_RIGIDITY, UNRESTRICTED_PATH_SHORTCUT]
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

## Verdict: exact gauge rigidity and the endpoint shortcut

[ABSTRACT | PAPER] **No RH proof.** The freeze survives as a registered candidate, not as a completed S5. A correction to the freeze's coordinate shorthand is necessary: the isometry from the physical constrained space is J_m: C^d -> C^m with range G_m^(1/2)K_m, J_m^*J_m=I. The actual compression is B_m(delta)=J_m^*H_m(delta)J_m. Using P onto K_m directly in H-coordinates would be a metric error. The frozen text is preserved above, not silently repaired. The endpoint equivalence is z^*A_m(0)z=y^*B_m(0)y for y=J_m^*G_m^(1/2)z.

### Theorem 1: exact gauge invariance and curvature obstruction

[FINITE_CELL | PAPER] If C(delta) is Hermitian and J^*C(delta)J=0 for every delta, then B^C(delta)=J^*(H(delta)+C(delta))J=B(delta). In particular (B^C)'=B', all Rellich eigenvalue velocities and their minimal loss are identical. Gauge terms built from e0 and p_m that vanish on K_m satisfy the same statement after correct graph conjugation. Thus a *null gauge* cannot reduce the Round-4-B action.

For any differentiable unitary U with U'=Omega U, Omega^*=-Omega, and scalar a,
W=U^*BU-aI satisfies the exact identity

    W'=U^*(B'+[B,Omega])U-a'I.                    (R5.1)

If a' I-(B'+[B,Omega])=R^*R >=0, then W'=-U^*R^*RU. At an eigenvalue lambda of B, its spectral projector P_lambda obeys

    P_lambda[B,Omega]P_lambda=0.                 (R5.2)

Hence a'(delta)>=lambda_max(P_lambda B'P_lambda) for every eigenspace, and therefore a'>=max_i lambda_i' almost everywhere along Rellich eigenbranches. If a' is required nonnegative, the optimal price is exactly

    L(B)=integral_0^(1/2) (max_i lambda_i'(delta))_+ ddelta.  (R5.3)

This is the inherited Round-4-B formula, now proved to be *invariant under all null gauges*. In particular no choice of off-diagonal commutator can change the block-diagonal signed eigenvalue velocity. Trace gives the weaker gauge-invariant necessary condition a'>=(tr B')/d.

Proof: differentiate U^*BU and use (U^*)'=-U^*Omega. Compress the commutator with P_lambda; BP_lambda=lambda P_lambda. Rellich diagonalization makes the block spectrum equal to the derivatives of analytic eigenbranches. The positive-semidefinite condition implies the block inequality. The lower envelope is attained by the Rellich unitary transport, as in Round 4 B §5. No spectral gap is assumed. □

### Theorem 2: unrestricted interior gauge is circular

[ABSTRACT / FINITE_CELL | PAPER] Suppose only B(0)=B_0 is fixed, and the terminal may be any PSD matrix. Then the best possible nonnegative scalar loss over *all* differentiable paths, transports, squares and terminal PSD matrices is

    inf action = (-lambda_min(B_0))_+.            (R5.4)

Lower bound: integrating the square identity from 0 to T gives B_0=U_T^*B_T U_T+integral (RU)^*(RU)-action I, so B_0>=-action I.

Upper bound: take T=1/2, B(delta)=(1-2delta)B_0, B_T=0, U=I, eta=2(-lambda_min B_0)_+, and R^*R=eta I+2B_0>=0. Then the action is (-lambda_min B_0)_+, attaining the bound. If lambda_min B_0>=0, eta=0 works. □

**This is an exact theorem-shape obstruction, not a claim that the original damping route is impossible.** Allowing arbitrary interior counterterms with zero endpoint and freely chosen positive terminal collapses the Perelman design problem to the unknown endpoint lower bound. The construction explicitly reads B_0, so it violates the intended independent arithmetic-supplier requirement. With the original fixed positive terminal and fixed source path, (R5.4) is only a lower bound, not an equality; the frozen prediction P2 needs precisely this qualification.

### Exact source residual and what a new W would have to pay

[FINITE_CELL | PAPER; imported Round 4 B §6] The literal derivative is

    A_m'(delta)[f]=C_delta[f]+E_delta[f],

    C_delta[f]=int_0^L u exp(-delta*u) exp(-5u/2)/
                    (1-exp(-2u)) Q_f(u) du,

    E_delta[f]=-int_0^L exp(-delta*u)D_psi(u)
             {[1-(1/2+delta)u]Q_f(u)+u Q_f'(u)}du,

    D_psi(u)=exp(-u/2)(psi(exp u)-exp u).

Here Q_f is the full physical correlation, with its endpoint term in Q_f' as Round 4 B (6.4), and psi includes **all** prime powers. The continuous-prime part cancels the growing pole term exactly; the remaining non-arithmetic integral satisfies int_0^(1/2)|C_delta[f]|d delta <=(9/25)||f||².

Let E_m(delta) be the Hermitian graph-compressed matrix of E_delta and C_m(delta) the same for C_delta. Then B'=C_m+E_m exactly. For any eigenprojector P_lambda of B, the required pointwise scalar loss must satisfy

    eta(delta)>=lambda_max(P_lambda(C_m+E_m)P_lambda). (R5.5)

The 9/25 bound alone cannot pay the positive spectral part of E_m. The *cheapest missing statement for this fixed source path* is a source-specific bound, with fixed C,r,M,

    for all integers m>=M:
    integral_0^(1/2) [max_lambda
       lambda_max(P_lambda(delta)[C_m(delta)+E_m(delta)]
                                      P_lambda(delta))]_+ ddelta
       <= C(1+log m)^r.                           (R5.GAP)

This equals the Round-4-B spectral action in substance; **it is not a new inequality**. No proof of it has been obtained, and therefore no RH-sign progress is claimed. A nontrivial future supplier must establish a strictly new bound on the joint E_psi term, not simply define a gauge or choose eta to be its positive part.

### Strongest attack and false worlds

[ABSTRACT | PAPER] An arbitrary 2x2 Hermitian path B(delta)=diag(1+M sin²(2pi delta),1) has positive endpoints and is PSD throughout, but action M; a unitary gauge cannot remove the eigenvalue rise. Thus positivity of the terminal and a formal square derivative are insufficient. Conversely the unrestricted path (R5.4) can always be built for any B_0, including false-world matrices: it is **not an arithmetic discriminator**.

For the source-specific residual (R5.GAP), Round 4 B §9 supplies the inherited conditional-to-false-world implication: DH with its own coefficients and odd Gamma fails its terminal condition; DMV with its own generalized primes and explicit Gamma/pole cannot have both terminal PSD and cofinal small action; a planted off-line quartet retains terminal PSD but violates the cofinal budget via the Gaussian negative response. The E/F3 curve has its own spectral comb and an action at most 2 log m. These are inherited PAPER source-return results, not independent new verification. The *exact missing discriminator for Q* is a one-sided estimate using the ordinary integer-lattice psi in E_delta that does not hold for generalized primes or the quartet. The null-gauge and abstract endpoint theorems do not provide it.

No pointwise radial-xi curvature identity with B' is asserted. The full xi curvature contains global zero information, whereas B' is a finite-window correlation functional with a sharp endpoint. Equating them would require a new source-exact intertwiner, including its boundary defect. Round 4 A already killed a stronger pointwise window-curvature square, so the new route must be physically paired or use a genuinely different representation.

### Prediction closeout and route map

- P1: **HIT** (Theorem 1, with the corrected graph-coordinate isometry).
- P2: **HIT WITH QUALIFICATION** (Theorem 2 only when terminal is freely replaceable; fixed terminal case not covered).
- P3: **HIT AS NECESSITY, NOT AS A NEW BOUND** (R5.5; no signed prime estimate).
- P4: **NOT RESOLVED AS A UNIVERSAL IMPOSSIBILITY**; no source-to-window intertwiner produced.
- No numerical tests, Lean, Arb, or independent audit. The pre-registered 2x2 counterexample is analytic; no precision/grid was required. Future strictly stronger finite claims must pre-register quantity, m-grid, t-grid, precision, planted quartet, and interval pass/fail criteria before computation. No such claim is made here.

| Chain | Status | Implication |
|---|---|---|
| Uniform source-specific (R5.GAP) | CONDITIONAL, RH-equivalent for Q via Round 4 B | implies finite square transport with polylog loss |
| Finite square transport with polylog loss | CONDITIONAL | implies A_m(0)>=-polylog(m)G_m |
| Gaussian receiver | inherited PAPER | implies RH |
| Gauge rigidity (R5.1)-(R5.3) | THEOREM [FINITE_CELL/PAPER] | does not imply R5.GAP |
| Unrestricted endpoint shortcut (R5.4) | THEOREM [ABSTRACT/PAPER] | does not imply RH |

**Alternative representations, not extra assumptions.** Candidate A: source-specific physical paired flow on the cone |fhat|², aiming for a direct one-sided E_psi estimate after pole and continuous-prime cancellation (kill-power high; analytic cost high). Candidate B: nonlocal full-xi radial curvature transferred by an explicit window/Hardy intertwiner with controlled boundary defect (kill-power high; construction cost very high). Neither has a proved uniform bound. A zero-consistent finite test must be discriminated by a strict interval sign or a nonzero analytic residue, not floating-point near-zero.

**K8A.** DOWNSTREAM_CONSUMER=RH via Gaussian source return. ACTUAL_CONSUMER_REQUIREMENT=any cofinal subpolynomial lower bound for the literal physical Weil form; the full Round-4 action is only one sufficient interface. ORIGINAL_REQUESTED_OBJECT=Perelman W with arithmetic-controlled square flow. ORIGINAL_OBJECT_IS=UNKNOWN as necessary for RH. KNOWN_WEAKER_INTERFACES=direct Gaussian signed-response bound or physical cone lower bound, each requiring its own source-to-RH proof. FAILURE_TYPE=NO_DERIVATION for E_psi estimate; COUNTEREXAMPLE for unrestricted-path-as-progress. EPISTEMIC_STATUS=RESEARCH_DEBT for the actual zeta route, MATHEMATICALLY_DEAD only for the claim that unrestricted path design independently proves the endpoint sign. NOVELTY_AXIS=exact gauge-rigidity and endpoint shortcut separation. REOPEN_TRIGGER=source-derived one-sided estimate of the transported E_psi block or an independently proved source-exact intertwiner.

**KILL_SCOPE: THEOREM_SHAPE** for unrestricted interior path as an independent supplier. KILL_EVIDENCE_KIND: exact variational equality (R5.4) in this file, freeze commit ca746d4fb3f76c2f5ef9a74070a57243ba57f08a. This does not kill the fixed-source damping family or RH.

```yaml
iteration:
  target: ARITHMETICALLY_CONTROLLED_PERELMAN_GAUGE
  status: PROGRESS
  cognitive_operator_used: DUALIZE
  new_gap_name: JOINT_PRIME_ERROR_EIGENBLOCK_ONE_SIDED_ESTIMATE
  invariant_learned: NULL_GAUGE_CANNOT_CHANGE_COMPRESSED_SPECTRAL_VELOCITIES
  forbidden_future_move: FREE_INTERIOR_PATH_AS_PROOF_OF_ARITHMETIC_SIGN
  next_decisive_test: DERIVE_NEW_ONE_SIDED_BOUND_FOR_E_PSI_ON_PHYSICAL_EIGENBLOCKS
  route_score: 2
```

RH_PROVED: false. The only newly closed mathematical quantifiers are the finite/abstract gauge-rigidity and unrestricted-path variational statements. No new RH inequality has been proved.
