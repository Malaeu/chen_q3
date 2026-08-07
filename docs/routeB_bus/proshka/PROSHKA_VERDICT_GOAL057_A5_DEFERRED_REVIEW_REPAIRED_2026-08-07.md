# STATUS: OPEN — SOURCE LOCK REPAIRED; CONDITIONAL CHAIN REPAIRED; ACTUAL-NUMERATOR AUDIT SELECTED

```yaml
STATUS: OPEN
OPERATIVE_CLASS: RUN_ACTUAL_NUMERATOR_SOURCE_AUDIT

SOURCE_LOCK:
  REQUEST_SHA256:
    expected: not_separately_precommitted
    observed: 8546ea7827cd668e0e81ede3455b2a9cfe4e6c60f12924752b8833c8103f5b0f

  CONTEXT_PACK_SHA256:
    expected: cf3c4d6d0438003b617c31eb82e05de8f1e5273393574e87dd60e225bfbdba28
    observed: cf3c4d6d0438003b617c31eb82e05de8f1e5273393574e87dd60e225bfbdba28
    status: PASS

  HEAD:
    expected: 21ff34778401d013b5a54a6d66b006e042ebb9da
    commit_exists: true

  LISTED_REVIEW_OBJECTS:
    total: 10
    verified: 10
    status: ALL_PASS

  PHASE3_SCRIPT:
    expected: 60ea1dab2d1d62aa386d69cb3885da4158ac727d2cfb76e2ce0c9e77bd7e1c29
    observed: 60ea1dab2d1d62aa386d69cb3885da4158ac727d2cfb76e2ce0c9e77bd7e1c29
    status: PASS

  PHASE3_RESULT:
    expected: dd60446849839256b08f8dd4cf78968987c501d7f196cdafffdd4b2f9640cb71
    observed: dd60446849839256b08f8dd4cf78968987c501d7f196cdafffdd4b2f9640cb71
    status: PASS

P057_6:
  status: FIRED

  EXECUTABLE_MUTATION:
    mutation: reverse_the_registered_sign_of_rate_slope
    original: "-(log Delta_right - log Delta_left)/(m_right-m_left)"
    mutated: "(log Delta_right - log Delta_left)/(m_right-m_left)"
    mutated_sha256: 0d4ea62a2a02210a91375bd4a62470013968dda835ac13c55ed09827cb892476
    source_gate: FAIL_EXPECTED

  RESULT_MUTATION:
    mutation: set_grid_m12_N120_retained_global_gap_lower_to_zero
    mutated_sha256: 02a1f81f1f25abf5ff8e3fe2be5841120f1de7c3174062763534a5e8317cf7b3
    source_gate: FAIL_EXPECTED

R1_AUDIT_CHAIN:
  ruling: TRY_CHAIN_REPAIRED

  exact_statement_or_first_invalid_implication: >-
    Let lambda_j -> infinity and N_j -> infinity be one joint cofinal schedule.
    Let F_j be the source-defined, zero-free-gauge-normalized entire function
    attached to the finite CCM ground object at (lambda_j,N_j). Assume:
    (1) every zero of F_j is real;
    (2) F_j converges locally uniformly on every compact substrip to the
        correspondingly normalized continuum-ground transform G_j;
    (3) G_j converges locally uniformly to the transform T_j of the same
        source trial k_lambda_j, with this step supplied by an exact
        actual-residual/true-gap theorem on the same family;
    (4) T_j converges locally uniformly to Xi.
    Then F_j converges locally uniformly to Xi, and the real-zero
    Hurwitz/Rouche consumer implies RH.

  original_chain_fate: REPAIR_REQUIRED_NOT_KILLED
  target_changes_to_cluster_now: false
  cluster_route_status: FALLBACK_ONLY_IF_TRUE_GROUND_GAP_OR_SIMPLE_SELECTOR_FAILS

  named_remaining_suppliers:
    - FINITE_QW_REAL_ZERO_SAME_FAMILY
    - DETREG_ZERO_FREE_GAUGE_NORMALIZATION_LOCK
    - JOINT_FINITE_TO_CONTINUUM_GROUND_TRANSFORM
    - ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
    - TRUE_WEIL_GAP_OR_CLUSTER_DISCRIMINATOR
    - WEIGHTED_GROUND_TO_TRIAL_COMPACT_OPEN_TRANSFER
    - CCM_TRIAL_TO_XI_PROJECT_CROSSWALK
    - SELECTED_TRIAL_NORMALIZER_BOUNDED

R4_JUDGE_INTEGRITY:
  ruling: RUN_JUDGE_INTEGRITY_ACCEPT_WITH_NAMED_NEXT_PLANT
  verdict_changer: NONE
  accepted_scope: FINITE_SECTIONAL_PROFILE_AND_RATE_UNRESOLVED_ONLY
  independent_solver_scope: EIGENSOLVER_INDEPENDENCE_NOT_INDEPENDENT_MATRIX_FORMULA
  next_required_plant: >-
    P057_7_FINITE_PLATEAU_NOT_ATTOP:
    provide a synthetic positive gap sequence whose N=90 and N=120 values
    satisfy the registered one-percent plateau test but whose later values
    collapse to zero. The judge must retain eventually_atTop_claim=false,
    continuum_gap_claim=false, and must refuse every operator-gap or
    finite-to-continuum receiver invocation.

RNUM_ACTUAL_NUMERATOR:
  ruling: RUN_NUMERATOR_SOURCE_AUDIT_FIRST

  source_object: >-
    CCM source trial k_lambda := E(h_lambda) on
    H_lambda = L2([lambda^-1,lambda], du/u), with the project-side candidate
    supplied by the exact hTrial_m / projected coefficient construction.

  target_object: >-
    The quasimode numerator
    nu_lambda := ||(W_lambda - mu_lambda) k_lambda||_Hlambda,
    mu_lambda := <W_lambda k_lambda,k_lambda>/<k_lambda,k_lambda>,
    together with its finite compression
    nu_lambda_N := ||(K_lambda_N-a_lambda_N I) q_source_lambda_N||_2.

  theorem_shape_or_audit: >-
    Audit and classify the two identities
      q_source_lambda_N
        = coefficients(P_lambda_N k_lambda) /
          ||coefficients(P_lambda_N k_lambda)||_2
    and
      K_lambda_N q_source_lambda_N
        = coefficients(P_lambda_N W_lambda P_lambda_N k_lambda)
    under the exact CCM/Q3 index, basis, normalization, parity and carrier
    crosswalk. Then determine whether nu_lambda_N is the numerator consumed by
    the existing residual/gap receiver and whether a proved finite-to-continuum
    or weighted-Mellin transfer relates nu_lambda_N to nu_lambda.
    The fixed zero-padded penalty probe, the Galerkin projection tail, and
    m^(9/2) exp(-4*pi*m) are forbidden substitutes.

  source_pointer: >-
    Embedded original unified-chain brief S3; CCM Section 7;
    q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean;
    Phase-1 portable coefficient artifact and control-cell report;
    generic projective/residual-gap receivers cited in the context pack.

P_DELTA_R_SCORE: UNSCORED_PRECONDITIONS_UNMET

FIRST_SHIFT_CHILD:
  selection: GOAL057_ACTUAL_NUMERATOR_SOURCE_TARGET_AUDIT
  stop: GOAL057_ACTUAL_NUMERATOR_SOURCE_TARGET_AUDIT_MISSING
  success: GOAL057_ACTUAL_NUMERATOR_SOURCE_TARGET_CLASSIFIED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE

iteration:
  target: Goal_057_A5_deferred_R1_R4_actual_numerator_review
  status: PROGRESS
  failed_strategy: infer_an_input_B_rate_from_unstabilized_sectional_gaps_or_the_prolate_proxy
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_OBJECT_LOCK
  invariant_learned: >-
    finite real-zero, finite-to-continuum, ground-to-trial and trial-to-Xi
    statements must concern one normalized joint family; a finite sectional
    gap, a fixed penalty probe and a prolate leakage proxy occupy different
    mathematical categories
  forbidden_future_move: >-
    substitute_the_prolate_deficit_projection_tail_or_fixed_zero_padded_probe
    for_the_true_Weil_quasimode_residual
  next_decisive_test: bounded_actual_numerator_source_target_audit
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## Source-lock repair

The two newly attached artifacts rehash exactly to the missing Phase-3 pins. The script is the complete executable that fixes the grid, (N)-ladder, precision ladder, stabilization gate, solver pair, slope orientation, and explicit proxy separation. The JSON is the retained complete result with all cells, interval endpoints, solver metadata, empty slope arrays, and explicit denial of continuum or `Eventually atTop` claims.  

Together with the eight previously rehashed snapshots inside the context pack, all ten source objects listed by the controlling request are now independently byte-locked.  

`P057_6` is substantive. Reversing the sign convention of `rate_slope` changed the script digest and failed the expected pin. Mutating one retained lower endpoint in the (m=12,N=120) global gap changed the result digest and failed its pin. The plant proves source-gate sensitivity; it does not, by itself, certify the mathematics of either artifact.

## R1 — the chain survives only in repaired same-family form

### Ruling

[
\boxed{\texttt{TRY_CHAIN_REPAIRED}}
]

The final complex-analytic implication is valid: a locally uniformly convergent sequence of nonzero entire functions with only real zeros cannot converge to a nonzero limit having a nonreal zero. The problem is not the Hurwitz/Rouché end. The problem is that S1–S4, as originally written, do not yet supply one normalized sequence to that end. `[ABSTRACT][PAPER]`

The original chain mixes three potentially different objects:

1. a finite determinant or finite ground transform carrying the real-zero theorem;
2. a continuum ground transform;
3. the prolate source trial (k_\lambda=\mathcal E(h_\lambda)), whose transform tends to (\Xi).

The context itself identifies the central type mismatch: real-zero information belongs to the finite ground family, while the paper’s trial-to-(\Xi) convergence belongs to (k_\lambda). A theorem connecting those normalized families is still required.  

### Exact repairs

**First, replace “A for every (\lambda)” by the exact demand the closure theorem consumes.** It is enough to produce one cofinal joint schedule ((\lambda_j,N_j)) whose finite normalized approximants have only real zeros. Proving simple-even for every continuum (\lambda) is one possible supplier, not the theorem’s minimal hypothesis.

**Second, use one joint schedule rather than silently exchanging limits.** Fixed-(\lambda) convergence as (N\to\infty), followed by (\lambda\to\infty), is enough existentially if it is stated with quantifiers permitting diagonal selection. For an exhaustion (K_1\Subset K_2\Subset\cdots) of the open strip, choose (N_j) so that the finite-to-continuum error at (\lambda_j) is below (1/j) on (K_j). No uniform-in-(\lambda) modulus is logically necessary for this existential diagonal theorem. The project still needs the exact local-uniform finite-to-continuum hypothesis from which that selection is made. `[COFINAL_FAMILY][CONDITIONAL]`

**Third, lock the determinant gauge.** Multiplication by (e^{a_j+i b_jz}) preserves zeros because it is zero-free, but it does not preserve convergence to (\Xi). The factor must be source-defined and removed exactly, or fixed through enough source-locked normalization data to prevent scalar and linear-exponential drift. Fitting a constant after observing convergence is forbidden.

**Fourth, formulate B directly in the topology consumed by S5.** The clean hypothesis is compact-open tracking of the normalized continuum ground transform by the trial transform. A weighted (L^1(d^*u)) estimate with the correct (u^\eta+u^{-\eta}) weights is a sufficient supplier for every closed substrip. The rate (o(\lambda^{-\eta})) is relevant when transferring from a weaker window norm that costs (\lambda^\eta); it is not a substitute for stating the final weighted or compact-open bound precisely.

**Fifth, do not switch to a cluster object merely because the Phase-3 plateau failed.** No sampled (m) stabilized, but that does not prove ground-state multiplicity, true-gap collapse, or failure of a rank-one selector. The rank-one repaired theorem remains legitimate as a conditional branch. A cluster projection/determinant route becomes mandatory only after a genuine true-gap or selector discriminator kills the simple-ground branch.

The Phase-3 result itself correctly stops at `DELTA_RATE_UNRESOLVED`: all nine finite sectional gaps are interval-positive, but none of the three (m)-values passes the precommitted (N=90\to120) stabilization test. It therefore supplies no slope, no asymptotic rate, and no operator gap.  

## R4 — current finite verdict is controlled; one eventuality plant remains mandatory

### Ruling

[
\boxed{\texttt{RUN_JUDGE_INTEGRITY_ACCEPT_WITH_NAMED_NEXT_PLANT}}
]

The current evidence is adequate for exactly this statement:

```text
The eighteen registered finite interval cells passed;
the three retained N=120 cells agree with a second Arb eigensolver;
every observed finite ground is even and the odd ground is the controlling
second competitor;
the registered stabilization gate failed at every m;
the rate remains unresolved.
```

`[FINITE_CELL][ARB_INTERVAL]`

The evidence does **not** support an asymptotic, continuum, or true-operator conclusion. The artifacts preserve that boundary explicitly: unstabilized points are excluded from every slope array, the actual numerator is null, the prolate quantity remains a separately named proxy, and both `eventually_atTop_claim` and `continuum_gap_claim` are false.  

The second solver is independent at the eigenvalue-enclosure algorithm level (`rump` versus `vdhoeven_mourrain`). It shares the matrix builder, source formulas, parity decomposition, and endpoint extraction. It must not be described as an independent reconstruction of the CCM matrix. Phase 0 supplied the separate source/formula checks.

The capability counterexamples are also correctly retained: a positive model gap without both endpoint controls proves nothing about a true gap, and endpoint errors may consume the entire budget. Arb radii for the same finite matrix are not finite-to-continuum endpoint bounds. 

### Next judge plant

```text
P057_7_FINITE_PLATEAU_NOT_ATTOP
```

Use a synthetic positive sequence with:

[
\Delta_{90}=\Delta_{120}=1,
]

so the registered pairwise drift gate passes, but with later values tending to zero. The expected outcome is:

```text
finite pairwise plateau:
  permitted as a finite diagnostic;

Eventually atTop:
  false;

continuum/operator gap:
  false;

operator-gap receiver:
  forbidden.
```

This plant protects the exact implication that current numerics are most likely to overstate.

## RNUM — audit the object before building the bridge

### Ruling

[
\boxed{\texttt{RUN_NUMERATOR_SOURCE_AUDIT_FIRST}}
]

The original chain names the mathematical numerator:

[
\nu_\lambda
===========

\left|
(W_\lambda-\mu_\lambda)k_\lambda
\right|*{H*\lambda},
\qquad
k_\lambda=\mathcal E(h_\lambda),
]

with (\mu_\lambda) its Rayleigh quotient. This is the numerator that belongs in a Kato/Temple ground-tracking estimate. 

What is not source-locked is its exact project realization.

Three existing objects must not be collapsed:

| Object                                                 | Role                               | May serve as actual numerator?                                          |
| ------------------------------------------------------ | ---------------------------------- | ----------------------------------------------------------------------- |
| Fixed zero-padded (q) from Phase 2                     | Common-core penalty-transfer probe | No, not without an exact source-trial theorem                           |
| `selectedNormalizedGalerkinResidual` / projection tail | Finite (N\to\infty) input-C defect | No; it is a projection residual, not a Weil-operator quasimode residual |
| (m^{9/2}e^{-4\pi m})                                   | Prolate concentration proxy        | No; no equality or one-sided bridge is proved                           |

The audit must first establish whether the finite vector used for an actual-numerator computation is literally the normalized coefficient vector of (P_{\lambda,N}k_\lambda), and whether multiplication by the finite CCM matrix is literally the coefficient representation of the compressed Weil operator. Only then is

[
\nu_{\lambda,N}
===============

\left|
(K_{\lambda,N}-a_{\lambda,N}I)
q^{\mathrm{src}}_{\lambda,N}
\right|_2
]

an honest finite source numerator. `[FINITE_CELL][CONDITIONAL]`

The audit then has to classify the missing upper bridge:

[
\nu_{\lambda,N}
\longrightarrow
\nu_\lambda
\quad\text{or}\quad
\nu_{\lambda,N}
\ \text{directly controls the same weighted projective defect}.
]

A finite residual and a continuum residual are different objects until a form-to-operator, projection, carrier, and limit theorem identifies them. This is a C04 category boundary. Substituting the prolate deficit would be a C10 surrogate error. Selecting the fixed Phase-2 probe because it already gave good certificates would violate the source-object precommit protected by C09.

### Bounded audit outcomes

The selected child must return exactly one:

```text
ACTUAL_NUMERATOR_BRIDGE_READY
```

The source trial, finite projection, finite CCM matrix, normalization and residual receiver match exactly.

```text
FINITE_RESIDUAL_EXACT_CONTINUUM_BRIDGE_OPEN
```

The finite numerator is valid, but the finite-to-continuum or weighted transform transfer is missing.

```text
PROBE_NOT_SOURCE_TRIAL
```

The current numerical probe is only a diagnostic approximation. Its residual may not be called the Input-B numerator; a source-defined projected trial must replace it.

```text
TARGET_OBJECT_MISMATCH
```

The located receiver consumes a projection tail, Rayleigh value, prolate deficit, or other non-residual object. The proposed bridge is killed and the exact quasimode residual receiver must be named.

No larger-(N) slope run should precede this classification. More sectional-gap data cannot resolve an undefined numerator.

## Prediction fate and first child

The registered prediction compares two rates only after:

1. the sectional gap has passed the registered (N)-stabilization gate;
2. the actual trial numerator has been identified and measured.

Neither predicate was met. The prediction therefore receives:

```text
UNSCORED_PRECONDITIONS_UNMET
```

This is not a confirmation, refutation, or retroactive weakening. The instrument behaved correctly by refusing to produce the comparison.

The first shift-sized child is:

```text
GOAL057_ACTUAL_NUMERATOR_SOURCE_TARGET_AUDIT
```

A larger (N)-ladder is deferred. It may later stabilize the finite gap, but it cannot identify the numerator or prove a continuum bridge. A separate chain-wrapper formalization is also deferred: without the source-target audit it would merely package the missing hypothesis under a new name.

## Strongest attack

The strongest objection to `TRY_CHAIN_REPAIRED` is that any false route can be rescued by assuming exactly the convergence needed for Hurwitz.

That objection is valid against an empty wrapper. It is why the selected child is not “formalize the repaired chain.” The repaired theorem only fixes the legal consumer shape. Progress now requires identifying the concrete actual numerator and the exact theorem that transports it to same-family compact-open ground-to-trial tracking.

The strongest objection to the finite probe is equally direct:

> Nine positive finite gaps and two interval eigensolvers still say nothing about the true operator gap.

Correct. The verdict accepts only the finite profile and the honest unresolved rate. The new plateau plant makes that boundary executable rather than rhetorical.

## Meta closeout

**What became smaller?**

The original three-input narrative is now one exact joint-family closure theorem with two named quantitative suppliers:

```text
actual numerator / ground-to-trial tracking;
finite-to-continuum ground transform.
```

**What was killed?**

* mixing Suzuki’s real-zero family with the CCM ground/trial family without a crosswalk;
* treating continuum simple-even as an automatic finite real-zero supplier;
* silently exchanging (N\to\infty) and (\lambda\to\infty);
* reading finite positive gaps as an operator gap;
* substituting the prolate deficit for the actual numerator;
* using the fixed zero-padded penalty probe as the moving source trial.

**What must not be tried again?**

Do not run a broader gap-rate grid before the actual numerator object is fixed. Do not formalize a wrapper whose only substantive premise is the still-unnamed source-target bridge.

**Current smallest named gap**

```text
ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_OBJECT_LOCK
```

**Next cheapest decisive test**

Compare, at one source-locked finite cell, the exact project coefficient vector of the selected source trial with the Phase-1 probe and verify whether its CCM matrix residual is definitionally or provably the compressed Weil-operator residual.
