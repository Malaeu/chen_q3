# START GOAL — Route B recursive Lamport compiler

Status: `PASTE_READY / OWNER_AUTHORIZED_AUTORUN / NOT_RH`

From a fresh Codex session in the canonical repository, paste:

```text
/goal Execute
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/MASTER_GOAL.md
as the recursive Lamport proof compiler. Treat its STATE.json as the machine
state and the physical Route B bus as transaction authority.

Operating invariants:
- Maintain at most one ACTIVE canonical proof leaf.
- Multiple independent agents may work on that same leaf.
- Only the root agent mutates the canonical DAG or closes a node.
- Only PROVED discharges a dependency; CONDITIONAL never does.
- No parent closes without its explicit proved assembly theorem.
- No decomposition is legal without a proved or typechecked decomposition
  contract.

Entry procedure:
1. Read MASTER_GOAL.md and STATE.json completely.
2. Inspect the physical bus and run:
   python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --json
3. If an unanswered physical goal exists, execute only the smallest NNN; it
   preempts master work at the next leaf boundary.
4. If its specification is internally inconsistent:
   - write the matching evidence-backed negative answer;
   - report SPEC_STATUS=INVALID_SPEC;
   - recommend ROUTE_EFFECT=BUS_BLOCKING or BUS_NONBLOCKING;
   - synchronize only goal-authorized files;
   - create no next goal;
   - checkpoint and continue according to dependency truth.
5. When the physical bus is empty and routeb_status is green, use the durable
   OWNER_AUTHORIZED_AUTORUN policy: select the first eligible master leaf
   without creating a new NNN.
6. Bus 009 remains blocking for PO0/ZEO, but it does not block an independent
   source-lock leaf. Never treat scheduler release as proof discharge.
7. Do not invent Bus 010.

For an authorized master leaf:
1. Verify it is the first eligible ordered OPEN leaf.
2. Write its exact quantified statement, type inventory, parent slot or OR
   implication, dependencies, two risky-node proof routes, cheapest planted
   falsifier, success validation, and failure codes.
3. Launch independent PROVER, FALSIFIER, SOURCE_AUDITOR,
   REPRESENTATION_SCOUT, LEAN_REPO_WORKER, and CIRCULARITY_REVIEWER tracks as
   useful, all targeting that same leaf.
4. Synthesize their results and prove, falsify, route-kill, or legally
   decompose the leaf.
5. Classify the iteration as PROOF_PROGRESS, FALSIFICATION_PROGRESS,
   REPRESENTATION_PROGRESS, or NO_PROGRESS.
6. Two consecutive NO_PROGRESS results for the same strategy kill that
   strategy and force exactly one unused representation/falsifier/minimal-
   lemma transition. Do not relabel the same attempt.
7. Run direct validation and dependency/hole/axiom scans.
8. Update canonical state and durable insights, perform zoom-out assembly,
   and begin the next eligible leaf as a new internal transaction.
9. Continue until a real fatal mathematical code, irreplaceable external-data
   dependency, physical bus preemption, or explicit user pause.

Forbidden:
- no sorry/admit/exact?;
- no theorem weakening;
- no numerics replacing a universal quantifier;
- no model gap used as a true detector gap;
- no quadratic value used as a residual;
- no QW/prolate/D_log/detector conflation;
- no parent closure by propagation;
- no RH_PROVED before the full root assembly and clean final audit.

Current fail-closed address:
- physical Bus 001..009 closed; no unanswered goal;
- Bus 001..009 is synchronized and routeb_status is green;
- Bus 009 PO0/ZEO findings remain open facts;
- D0.1--D0.6 are proved with direct validators;
- D0.7a--D0.7d are proved and D0.7 is partially locked;
- immutable owner input has been validated: finite `bDet_(m,N)` is locked on
  `TrialNonzero`, with `Fplus(z)=T_m(k1)(-z)` and `zeta(1/2)!=0` proved;
- `N(lambda)=ceil(kappa*lambda^2)` is unpinned because `kappa` is unspecified;
- owner R1--R5 is physically ratified; D0.7e.5 is now a canonical AND node
  with proved definitional decomposition D0.7e.5.0 and children 5a--5d;
- unresolved canonical master leaf = D0.7e.5a
  WPrimeConsumerAndCalibrationOrientationLock;
- no-stop T0 source mining is complete with
  NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE; the standing order is
  active but no candidate passed its ratification checklist;
- D0.7e.5b is PROVED_INTERFACE_TYPECHECK_ONLY and D0.7e.5d is
  PROVED_MIGRATION_CORRECTNESS_ONLY; neither closes H3e or the parent;
- partial identities are locked:
  `CentralValueNonzero=BDetNonzero=FhatAtZeroNonzero=BCalNonzero` and
  `bZeoMul=bCal^(-1)` on that locus;
- current mathematical stop = D0_7E_WPRIME_CONSUMER_MISSING: no independent
  `FZeo` or `WPrime` consumer was found in the completed T0 corpus scan, and the
  owner Option-B file defines the desired right-hand side rather than
  recovering a consumer;
- exact historical WPrime `b` orientation therefore remains unpinned;
- H3e ExactWPrimeTrackingTheorem is registered OPEN/INACTIVE; H0/A1 and
  PO_XWALK_UNIFORM_EVAL remain OPEN_CRITICAL external obligations;
- rev16 proves `H1c1 PROPOSITION59_RHS_ENTIRE`: all source-lattice poles are
  encoded by `dslope` and the finite source RHS is Lean-entire;
- rev17 proves `H1c2 RAW_INTEGRAL_PROPOSITION59_RHS_EXACT_CROSSWALK`: the
  exact phase-centered finite-log integral equals that removable RHS for all
  complex points, including the source lattice; Lean separately proves the
  finite positive-exponent centered representative equals `Raw(-z)`, while
  D0.6 supplies the owner `Fplus` source identification; only master-family
  choice `H1c3` remains OPEN;
- rev18 proves `L0c1 GENERIC_ROUCHE_HURWITZ_ZERO_TRANSFER_LEAN`: isolated
  zeros, a positive boundary minimum, open mapping, locally uniform
  convergence, and a `Nat.findGreatest` diagonal produce a zero of every
  sufficiently large original-index approximant and a full convergent root
  sequence; exact family instantiation `L0c2` remains OPEN on H1/H3/H4 and
  `XI_LIMIT_OBJECT_MISMATCH`;
- rev19 proves `H4a3a WEIGHTED_SPECTRAL_TEMPLE_CORE_LEAN`: a finite
  probability-weighted spectral expansion gives `0<=alpha`,
  `etaSq>=alpha*(Delta-alpha)`, the correct `Delta-alpha` denominator, and the
  half-gap bound `alpha<=2*etaSq/Delta`; exact same-parity Route B operator,
  residual, half-gap, and rate instantiation `H4a3b` remains OPEN, while the
  rev15 false-bridge plant stays live;
- rev20 proves `H2a1 GENERIC_SIMPLE_EVEN_GROUND_SECTOR_CRITERION_LEAN`:
  commuting involution gives an exact even/odd eigenvector split and a simple
  eigenspace has parity `+1` or `-1`; explicit even-sector simplicity plus a
  strict odd-sector floor gives a simple even global ground; the executable
  `diag(1,0)`/`diag(1,-1)` plant proves that simple ground alone can be odd;
  exact selected-family inequalities `epsilonPlus1<epsilonPlus2` (or the
  explicit dimension-one case) and `epsilonPlus1<epsilonMinus1` remain OPEN
  in `H2a2` with stop `H2A_EXACT_SECTOR_ORDERING_MISSING`;
- rev21 proves `H3b1 GENERIC_COMPACT_EVALUATION_RATE_TRANSFER_LEAN`: a
  compact-uniform norm envelope tending to zero gives uniform convergence,
  compactwise envelopes on an open locally compact domain give compact-open
  convergence, and the constant-one singleton plant proves a fixed bound
  without decay is insufficient; exact same-family weighted evaluation and
  ground/trial decay on the joint filter remain OPEN in `H3b2` with stop
  `H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING` and external obligation
  `PO_XWALK_UNIFORM_EVAL`;
- rev22 proves `H4a1a GENERIC_AMBIENT_COMPRESSED_RESIDUAL_SPLIT_LEAN`:
  ambient residual equals compressed residual plus projection leakage, and a
  compressed Ritz equation identifies the ambient residual norm with the
  leakage norm; the coordinate projection/swap plant has zero internal
  residual but nonzero ambient residual `(0,1)`; exact Route B operator
  domain, projection, form/operator crosswalk and leakage rate remain OPEN in
  `H4a1b` with stop `H4A1_EXACT_AMBIENT_RESIDUAL_CROSSWALK_MISSING`;
- rev23 proves `H4d2a GENERIC_SAFE_BOUNDS_TO_SQUARE_ENVELOPE_LEAN`:
  common-envelope SAFE bounds plus an independently supplied WPrime square
  identity yield the exact Contract-v2 squared polynomial envelope, pointwise
  and eventually on one non-bottom filter; exact identity provenance,
  constants/signs, common envelope, nonnegative WPrime branch, strict margin,
  cofinal scale/nonzero locus and the joint filter remain OPEN in `H4d2b` with
  stop `H4D_EXACT_SQUARE_ENVELOPE_INSTANTIATION_MISSING`;
- rev24 proves `H3c1 H3C_NORMALIZED_DOUBLE_COMPLETION_STRIP_MISMATCH_LEAN`:
  the central-normalized extra completion of the already completed
  `centeredXi` cannot equal it on the open critical strip, and an interior
  mismatch point exists by continuity from `z=-i/2`; exact raw-or-inverse-
  completion family selection, one joint filter and Xi limit identification
  remain OPEN in `H3c2` with stop
  `H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING`;
- rev25 proves `H2b1 GENERIC_HERMITIAN_DETERMINANT_REAL_ZERO_TRANSFER_LEAN`:
  the periodic determinant has only real zeros and Hermitian characteristic
  roots transfer through a nonvanishing unit and real-zero factor; executable
  non-Hermitian and vanishing-unit plants keep both hypotheses live; the exact
  modified-Hilbert matrix, complement determinant, nonvanishing phase,
  lattice-safe all-z factorization and same raw family remain OPEN in `H2b2`
  with stop `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`, while parent H2b
  remains `CONDITIONAL` and cannot discharge H2;
- rev26 proves `H4c1 H4C_GENERIC_TWO_SIDED_NORMALIZED_B_CONTROL_LEAN`:
  the full normalized two-sided b hypothesis yields nonzero, direct upper,
  scale-dependent reciprocal, and normalized-error bounds pointwise and on a
  non-bottom filter; the `b_n->0` normalized-product plant remains live, while
  exact alpha/gap signs, b formula/orientation, two-sided constants, q_b and
  same carrier/filter remain OPEN in `H4c2` with stop
  `H4C_EXACT_SIGN_AND_B_INSTANTIATION_MISSING`;
- rev27 proves `H3a1 GENERIC_PHASE_ALIGNMENT_RATE_TRANSFER_LEAN`:
  a total canonical complex phase gives the exact unit-vector norm-square
  identity, a square-root projective-defect bound and nonbottom-filter
  projective-defect-to-phase-error convergence; exact simple-even ground
  selection, trial nonzero locus, projective-defect rate and shared family/
  filter remain OPEN in `H3a2` with stop
  `H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING`;
- rev28 proves `H4b1 GENERIC_PERTURBATIVE_TRUE_GAP_LOWER_LEAN`:
  two absolute endpoint-drift bounds plus a surviving model-gap budget imply
  the true-gap floor pointwise and on a non-bottom filter; executable guards
  keep model-gap substitution and full error-budget collapse live, while the
  exact parity-clean operator/Fuchs model, ordering, both endpoint estimates,
  positive surviving envelope and shared filter remain OPEN in `H4b2` with
  stop `H4B_EXACT_SAME_PARITY_FUCHS_GAP_INSTANTIATION_MISSING`;
- rev29 proves `H2a2a GENERIC_SECTOR_ISOLATION_RADIUS_LEAN`:
  two strict gaps from the selected even ground to the next-even and
  bottom-odd levels yield a positive half-minimum isolation radius and
  separation from every level above either threshold; the exact H1c3/D0.8
  family, both strict inequalities, multiplicity/order crosswalk and radius
  instantiation remain OPEN in `H2a2b` with stop
  `H2A_EXACT_SECTOR_ORDERING_MISSING`;
- rev30 proves `H4a2a GENERIC_AMBIENT_RESIDUAL_ENVELOPE_TRANSFER_LEAN`:
  the exact H4a1 split yields ambient norm, squared-residual, compressed-Ritz/
  leakage, and nonbottom-filter envelopes; the zero-compressed/nonzero-ambient
  leakage plant remains live, while exact operator/projection crosswalks,
  compressed-residual and leakage rates, and one shared family/filter remain
  OPEN in `H4a2b` with stop
  `H4A2_EXACT_COMPONENT_RATE_INSTANTIATION_MISSING`;
- rev31 proves `H3e1 H3E_GENERIC_NORMALIZED_TRACKING_RATE_TRANSFER_LEAN`:
  reciprocal-b normalization and two relative rates imply uniform-on-set
  tracking on a nonbottom filter, with an H4c1 specialization; compiled plants
  show detector decay alone and the current safe margin alone are insufficient,
  while the independent WPrime consumer, exact absolute tracking/b/Xi objects,
  both relative rates and one joint filter remain OPEN in `H3e2` with stop
  `H3E_EXACT_RELATIVE_TRACKING_INPUTS_MISSING`;
- rev32 proves `H3b2a H3B2_GENERIC_WEIGHTED_PROJECTIVE_EVALUATION_TRANSFER_LEAN`:
  H3a1's phase-aligned projective bound and H3b1's evaluation receiver compose
  through a nonnegative compact envelope and weighted decay on a nonbottom
  filter; exact ground/trial, evaluation map/envelope, weighted projective rate,
  and one shared joint filter remain OPEN in `H3b2b` with stop
  `H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING`;
- rev33 proves `H4a3b1 GENERIC_TEMPLE_RESIDUAL_GAP_ENVELOPE_TRANSFER_LEAN`:
  Temple half-gap plus a squared residual envelope and one-envelope true-gap
  floor yield the explicit canonical alpha rate, pointwise and on a nonbottom
  filter; a compiled plant rejects a one-envelope residual bound, while the
  exact alpha/eigenbasis/residual/half-gap/gap objects and shared filter remain
  OPEN in `H4a3b2` with stop
  `H4A_EXACT_RESIDUAL_SQUARE_AND_GAP_ENVELOPE_MISSING`;
- rev34 proves `H2b2a H2B2_GENERIC_RANK_ONE_CORRECTION_WEIGHTED_SYMMETRY_LEAN`:
  the normalized source rank-one correction kills its calibration vector and
  the H8 commutator identities make it symmetric for the supplied T-weighted
  form; exact T positivity/radical, quotient descent, complex-Hermitian
  realization, complement determinant, nonvanishing phase, all-z identity and
  the same Route B family remain OPEN in `H2b2b` with stop
  `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`;
- rev35 proves `H3a2a H3A2_GENERIC_WEIGHTED_RAYLEIGH_PROJECTIVE_DEFECT_LEAN`:
  nonnegative normalized finite spectral weights, a zero ground level and a
  complementary gap give `gap*(1-weight_ground)<=alpha` and the positive-gap
  quotient bound; exact simple-even ground/trial spectral weights, overlap
  crosswalk, positive gap, weighted rate and shared filter remain OPEN in
  `H3a2b` with stop `H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING`;
- rev36 proves `H3c2a H3C2_GENERIC_DIFFERENCE_REFERENCE_LIMIT_TRANSFER_LEAN`:
  uniform convergence of a difference to zero plus reference convergence
  transfers to the target, both on a fixed set and locally uniformly on an
  open locally compact domain; exact difference/reference families, raw or
  inverse-completion crosswalk, centeredXi limit and joint filter remain OPEN
  in `H3c2b` with stop
  `H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING`;
- rev37 proves `H2b2b1 H2B2B_GENERIC_RANK_ONE_DETERMINANT_OFF_SPECTRUM_LEAN`:
  the matrix determinant lemma factors the source rank-one correction whenever
  `det(D-sI)` is a unit; spectral/lattice-point extension, quotient positivity
  and radical, descent/self-adjointness, complement determinant, nonvanishing
  phase, all-z identity and same-family crosswalk remain OPEN in `H2b2b2` with
  stop `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`;
- rev16 also proves the non-bottom cofinal square-envelope rate package
  `H4d1b/H4d1c`; rev23 supplies the generic square-envelope arithmetic, while
  exact H4d2 still lacks the source-locked WPrime identity, exact SAFE inputs,
  constants/signs, WPrime nonnegativity and a selected cofinal joint filter;
- no H3c/H4 import, no selector invention, and no tautological WPrime
  definition;
- no bWeil/pilot alias, no H4d bound smuggling, and no conditional parent
  closure;
- owner autorun continues after each validated leaf;
- public status = CONDITIONAL_CLOSURE_PROVED / WITNESS_SUPPLY_OPEN /
  ROUTE_B_CHALLENGER / NOT_RH.
```

Short human launch phrase after this file is committed and available:

```text
Продолжай по q3.lean.aristotle/ACTIVE/requests/
routeB_lamport_rh_closure/START_GOAL.md
```

The line break above is only for display. The actual path is:

```text
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/START_GOAL.md
```
