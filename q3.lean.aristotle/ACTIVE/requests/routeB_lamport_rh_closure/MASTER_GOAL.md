# MASTER GOAL — Lamport RH closure compiler for Route B

Status: `ACTIVE / CONDITIONAL_CLOSURE_PROVED / RH_OPEN`

Route rank: `CHALLENGER / NOT_RH`

Compiler semantics: `recursive v3 / one active leaf / explicit assembly`

This file is a user-authorized proof-compiler goal. It is not a numbered bus
goal, does not select a future `NNN`, and does not permit Codex to skip the
smallest physical unanswered goal in
`../routeB_twolevel_spectral_ladder/bus/`.

## 0. Objective and honesty contract

The final objective is the Riemann Hypothesis:

```text
Every non-trivial zero rho of zeta satisfies Re(rho) = 1/2.
```

The compiler separates two statements:

1. the complex-analytic export theorem `H1 ∧ H2 ∧ H3 ∧ H4 -> RH`;
2. the still-open supply of `H1` through `H4` for one exact project family.

The first statement is proved below. The second is not currently proved.
Therefore this document is not a proof of RH.

The status `RH_PROVED` is forbidden until every leaf below is proved, the
object identities are source-locked, and the final Lean export has no `sorry`,
`admit`, `exact?`, unexpected axiom, RH-conditional import, or circular bridge.

## 1. Classical definitions

### Definition 1.1 — Riemann zeta function

For `s ∈ C` with `Re(s) > 1`,

```text
zeta(s) = sum_(n >= 1) n^(-s).
```

The classical continuation theorem extends `zeta` meromorphically to `C`,
with one simple pole at `s = 1`. Its zeros at `-2,-4,-6,...` are called
trivial; all other zeros are non-trivial. The classical zero-free regions and
functional equation place every non-trivial zero in `0 < Re(s) < 1`.

These classical statements are named inputs, not Route B contributions. A
fully formal export must pin their exact Mathlib or Lean interfaces.

### Definition 1.2 — Completed zeta function

```text
xi(s) = (1/2) * s * (s-1) * pi^(-s/2) * Gamma(s/2) * zeta(s).
```

The classical completion theorem states that `xi` is entire,
`xi(s) = xi(1-s)`, is not identically zero, and its zeros with multiplicity
are exactly the non-trivial zeros of `zeta`.

### Definition 1.3 — Centered Xi function

```text
Xi(z) = xi(1/2 + i*z).
```

If `rho = 1/2 + i*z` and `z = x + i*y`, then

```text
Re(rho) = 1/2 - y.
```

Thus `Re(rho)=1/2` if and only if `z` is real. Moreover
`0 < Re(rho) < 1` if and only if `|Im(z)| < 1/2`.

### Lemma 1.4 — RH/Xi equivalence

```text
RH <-> every zero of Xi in S = {z : |Im(z)| < 1/2} is real.
```

Proof. The zeros correspond by Definition 1.2 and the affine change of
variables in Definition 1.3. The two displayed equivalences translate the
critical strip and critical line exactly. QED.

## 2. Exact top-level obligations

Let `lambda_j -> infinity` be a cofinal sequence in the eventual exact
parameter set. Let `F_j : C -> C` and `W_j >= 0` be one source-locked family.
No pilot formula may fill these symbols by reconstruction.

### H1 — EntireApproximants

For every `j`, `F_j` is entire.

### H2 — RealZeroApproximants

For every `j` and `z ∈ C`,

```text
F_j(z) = 0 -> z ∈ R.
```

This must come from the exact real-zero theorem for the same eigenvector and
normalization used to define `F_j`; a small Rayleigh value does not imply H2.

### H3 — StripUniformTracking

For every compact `K` contained in

```text
S = {z ∈ C : |Im(z)| < 1/2},
```

there are a finite constant `A_K >= 0` and errors `eps_(j,K) >= 0` with
`eps_(j,K) -> 0` such that

```text
sup_(z ∈ K) |F_j(z) - Xi(z)| <= A_K * W_j + eps_(j,K).
```

### H4 — DetectorDecay

```text
W_j -> 0.
```

If `W_j` is supplied by a residual/gap estimate, its denominator must be the
spectral distance from the residual center to the complementary spectrum.
Writing a model gap or `mu_3-mu_1` is legal only after an exact identity and
sector theorem.

## 3. Closed conditional export

### Lemma 3.1 — Local uniform convergence

Under H3 and H4, `F_j -> Xi` locally uniformly on `S`.

Proof. Fix compact `K ⊂ S`. H3 gives

```text
sup_K |F_j-Xi| <= A_K W_j + eps_(j,K).
```

Both terms on the right tend to zero by H4 and the definition of H3. QED.

### Theorem 3.2 — ZeroEscape

Under H1–H4, `Xi` has no non-real zero in `S`.

Proof.

1. Assume for contradiction that `Xi(z_0)=0` for a non-real `z_0 ∈ S`.
2. Since `Xi` is entire and not identically zero, its zeros are isolated.
3. Choose `r>0` small enough that the closed disk
   `Dbar={z:|z-z_0|<=r}` is contained in `S`, is disjoint from `R`, and its
   boundary contains no zero of `Xi`.
4. Continuity and compactness give

   ```text
   m = min_(z ∈ boundary D) |Xi(z)| > 0.
   ```

5. By Lemma 3.1, for all sufficiently large `j`,

   ```text
   sup_(boundary D) |F_j-Xi| < m <= |Xi|.
   ```

6. H1 makes `F_j` holomorphic on and inside the boundary. Rouche's theorem
   therefore says that `F_j` and `Xi` have the same number of zeros in `D`,
   counted with multiplicity.
7. The function `Xi` has at least the zero `z_0` in `D`; hence `F_j` has a
   zero in `D`.
8. But `D` is disjoint from the real axis, contradicting H2.

The contradiction proves the claim. QED.

### Corollary 3.3 — Conditional RH closure

```text
H1 ∧ H2 ∧ H3 ∧ H4 -> RH.
```

Proof. By Theorem 3.2 every zero of `Xi` in `S` is real. Apply Lemma 1.4.
QED.

This corollary is a complete proof of the implication only. It supplies none
of H1–H4.

## 4. Recursive Lamport proof-tree semantics

The compiler is a typed proof tree, not a list of promising tasks. Every
canonical node records:

```text
id
parent_id
kind: AND | OR | LEAF
role: GOAL | DECOMPOSITION_CONTRACT | ASSEMBLY
statement
type_inventory
dependencies
ordered_children
assembly_theorem_id
proof_status
activity
validation
failure_codes
```

Mathematical truth and scheduler activity are separate. The allowed proof
statuses are:

```text
OPEN
CONDITIONAL
PROVED
FALSIFIED
FATAL_CURRENT_ROUTE
BLOCKED
INVALID_SPEC
```

The only activity values are `INACTIVE` and `ACTIVE`. At most one canonical
proof leaf may be `ACTIVE`. Only `PROVED` discharges a dependency;
`CONDITIONAL` never does.

### 4.1 AND and OR closure

An AND node `G` may be marked `PROVED` only when:

1. every ordered child is `PROVED`;
2. the explicit assembly theorem

   ```text
   child_1 AND ... AND child_n -> G
   ```

   is itself `PROVED`;
3. all node and assembly validations pass.

An OR node `G` may be marked `PROVED` only when:

1. at least one child `G.i` is `PROVED`;
2. the exact bridge `G.i -> G` for that successful branch is `PROVED`;
3. all node and bridge validations pass.

A parent never closes by status propagation alone. A falsified sufficient
route usually gives `FATAL_CURRENT_ROUTE`; it makes the parent `FALSIFIED`
only if a separate necessity, equivalence, or route-completeness theorem has
also been proved.

### 4.2 Leaf closure

A leaf may be marked `PROVED` only by one of:

- a complete mathematical proof with every imported theorem pinned;
- a compiled Lean theorem with audited dependencies;
- an explicitly authorized external theorem whose hypotheses, normalization,
  domain, topology, and conclusion exactly match.

Numerics may falsify, calibrate, or certify an explicitly finite statement.
They may not discharge a universal analytic leaf.

### 4.3 Legal decomposition and zoom

Before a leaf is replaced by children, the compiler must first lock and prove
or typecheck a decomposition contract:

```text
AND decomposition: child_1 AND ... AND child_n -> parent
OR decomposition:  child_i -> parent for every admitted route i
```

No child becomes canonical merely because it appears useful. For a child of
an AND node, its `parent_contract` is its exact hypothesis slot in the parent
assembly theorem; the child alone is not falsely claimed to imply the parent.
For a child of an OR node, the parent contract is the exact branch implication.

Traversal is ordered depth-first:

1. select the first `OPEN` leaf whose dependencies are all `PROVED` and whose
   control-plane release is valid;
2. make that leaf the unique `ACTIVE` canonical mutation target;
3. prove, falsify, kill the current route, or legally decompose it;
4. validate and update only that node;
5. return to the parent and revalidate the already locked assembly theorem;
6. mark the parent `PROVED` only if its closure rule is satisfied;
7. repeat upward until the first still-open ancestor;
8. do not start a sibling in the same bus transaction.

### 4.4 One active leaf, multiple worker tracks

Several independent workers may investigate the same active leaf:

```text
PROVER
FALSIFIER
SOURCE_AUDITOR
REPRESENTATION_SCOUT
LEAN_REPO_WORKER
CIRCULARITY_REVIEWER
NUMERICAL_CALIBRATOR
```

All workers target the same `active_node_id`. They must not concurrently edit
the same canonical file. Each returns its claim, exact assumptions, method,
evidence, files and commands, dependency classification, counterexample or
proof, and recommended status. The root agent alone selects the accepted
route, mutates the canonical DAG, creates children, marks a node `PROVED`, and
performs zoom-out.

### 4.5 Progress and strategy kill rule

Every iteration is classified for the pair `(leaf_id, strategy_id)` as:

```text
PROOF_PROGRESS
FALSIFICATION_PROGRESS
REPRESENTATION_PROGRESS
NO_PROGRESS
```

`PROOF_PROGRESS` closes a dependency or strictly reduces a proved obligation.
`FALSIFICATION_PROGRESS` supplies a counterexample or a valid kill
certificate. `REPRESENTATION_PROGRESS` supplies a proved equivalence,
source-lock, or typed representation that strictly reduces unresolved
premises. Renaming, wrapper lemmas, new prose, or numerics without quantified
closure are `NO_PROGRESS`.

Two consecutive `NO_PROGRESS` results for the same strategy kill that
strategy and forbid a third identical attempt. Exactly one unused transition
must then be selected:

```text
REPRESENTATION_SHIFT
COUNTEREXAMPLE_HUNT
DUALIZE
BOUNDARY_CASE
UNIT_AUDIT
MINIMAL_LEMMA
ABANDON_ROUTE
```

Renaming a strategy does not reset the streak; its statement, object, or
representation must materially change. `ABANDON_ROUTE` yields a route-kill
recommendation and `FATAL_CURRENT_ROUTE`, not theorem falsity. Route-level
abandonment remains an owner/Mythos decision.

### 4.6 Mandatory leaf contract

Before proof work, the active leaf must have:

```text
Statement: exact quantified theorem
Type inventory: domain, codomain, operator/form, normalization, topology,
                parameter set
Parent contract: exact AND slot or OR implication
Dependencies: named PROVED inputs only
Candidate routes: at least two when the node is risky
Cheapest falsifier: planted violation and expected failure
Success condition: theorem, artifact, validation command, dependency profile
Failure codes: FALSE, OBJECT_MISMATCH, CIRCULAR, INSUFFICIENT_IMPORT,
               NO_PROGRESS
Progress record: class plus strict reduction/evidence
```

### 4.7 Bus authority and invalid specifications

Bus review uses two independent axes:

```text
SPEC_STATUS:  VALID_SPEC | INVALID_SPEC
ROUTE_EFFECT: BUS_BLOCKING | BUS_NONBLOCKING
```

An unanswered physical goal is always first. For an invalid specification
Codex writes the matching evidence-backed negative answer, synchronizes only
authorized state, and creates no next bus goal. `INVALID_SPEC` closes only the
bus transaction; it neither closes the mathematical blocker nor implies
`BUS_NONBLOCKING`.

Owner authorization on 2026-07-11 changes the scheduler to
`OWNER_AUTHORIZED_AUTORUN`. Once the current physical transaction is recorded
and no unanswered goal exists, the compiler immediately selects the first
eligible ordered master leaf. It does not need a new NNN for each internal
leaf. A newly appearing unanswered physical goal preempts autorun.

Autorun continues through proof, validation, assembly/zoom-out, and the next
eligible sibling. It pauses only for:

1. a real fatal mathematical code for the active route;
2. missing external data or authority that cannot be reconstructed safely;
3. a physical unanswered bus goal;
4. an explicit user pause.

Open Bus-009 facts such as ZEO ambiguity remain blockers for the nodes that
depend on them. They do not block an independent source-lock leaf such as
`D0.1` merely by existing.

### 4.8 Canonical tree and D0 decomposition

```text
R0 RHClosure [AND]
|-- C0 ClassicalXiInterface
|-- D0 ExactObjectFamily [AND]
|   |-- D0.1 ExactHilbertSpaceAndNorm
|   |-- D0.2 ExactWeilSesquilinearForm
|   |-- D0.3 ExactOperatorRegistry [AND]
|   |   |-- D0.3a FormRepresentationOperator
|   |   |-- D0.3b PeriodicScalingOperator
|   |   |-- D0.3c FiniteFormRieszOperator
|   |   |-- D0.3d PerturbedScalingCarrierSplit
|   |   |-- D0.3e ProlateDifferentialExpression
|   |   |-- D0.3f ProlateSelfadjointRealization
|   |   |-- D0.3g CanonicalDetectorOperator
|   |   |-- D0.3h OperatorNonconflationFirewall
|   |   `-- D0.3i D0.3Assembly
|   |-- D0.4 ExactParitySector
|   |-- D0.5 ExactGroundEigenspaceAndTrialVectorTypes
|   |-- D0.6 ExactTransformConvention
|   |-- D0.7 ExactNormalization [AND]
|   |   |-- D0.7a DirichletBoundaryVectorAndFunctional
|   |   |-- D0.7b TrialScalarAndPhase
|   |   |-- D0.7c ConditionalGroundBoundaryNormalization
|   |   |-- D0.7d BNamespaceFirewall
|   |   |-- D0.7e ExactDetectorBDefinitionAndCrosswalk [AND]
|   |   |   |-- D0.7e.1 ImmutableOwnerDefinitionProvenance
|   |   |   |-- D0.7e.2 FiniteCentralMellinCalibration
|   |   |   |-- D0.7e.3 DependentCentralNormalizationIdentity
|   |   |   |-- D0.7e.4 RealityPhaseAndNamespaceFirewall
|   |   |   |-- D0.7e.5 TypedWPrimeConsumerSlot [AND]
|   |   |   |   |-- D0.7e.5a WPrimeConsumerAndCalibrationOrientationLock
|   |   |   |   |-- D0.7e.5b ExactFiniteConsumerObjects
|   |   |   |   |-- D0.7e.5c ExactWPrimeConsumerIdentity
|   |   |   |   |-- D0.7e.5d DownstreamTrackingObligationMigration
|   |   |   |   `-- D0.7e.5e D0.7e.5Assembly
|   |   |   `-- D0.7e.6 D0.7eAssembly
|   |   `-- D0.7f D0.7Assembly
|   |-- D0.8 QWToZeroProducingOperatorCrosswalk
|   `-- D0.9 D0Assembly                  [assembly, not analytic sibling]
|-- H1 EntireApproximants [AND]
|   |-- H1a FiniteEntireCombinationCore
|   |-- H1b PhaseReflectionScalarClosure
|   |-- H1c ExactApproximantSourceCrosswalk
|   `-- H1d H1Assembly
|-- H2 RealZeroApproximants [AND]
|   |-- H2a SimpleEvenGround
|   |-- H2b SameVectorRealZeros
|   `-- H2c H2Assembly
|-- H3 StripUniformTracking [AND]
|   |-- H3a GroundTrialTracking
|   |-- H3b CompactStripEvaluation
|   |-- H3c XiLimitIdentification
|   |-- H3e ExactWPrimeTrackingTheorem
|   `-- H3d H3Assembly
|-- H4 DetectorDecay [AND]
|   |-- H4a ResidualIdentity
|   |-- H4b ResidualUpperBound
|   |-- H4c TrueSpectralDistanceLowerBound
|   |-- H4d NormalizationControl
|   `-- H4e DetectorDecayAssembly
|-- L0 LeanZeroEscape [AND]
|   |-- L0a DetectorBoundConvergenceCore
|   |-- L0b RealZeroLimitLogic
|   |-- L0c RoucheHurwitzZeroTransfer
|   `-- L0d L0Assembly
|-- L1 FinalAxiomAudit
`-- R0.A FinalRHAssembly
```

For D0, the decomposition contract is fixed definitionally as

```text
D0 <-> D0.1 AND D0.2 AND D0.3 AND D0.4
          AND D0.5 AND D0.6 AND D0.7 AND D0.8.
```

This structural equivalence is `D0.0`. Its forward assembly application is
`D0.9`; D0.9 is not a ninth independent analytic hypothesis.

Proof of D0.0. In this compiler, `D0 ExactObjectFamily` is defined to be the
displayed eight-component bundle. Unfolding that definition gives both
directions of the equivalence by conjunction introduction and elimination.
This is a complete mathematical decomposition proof; its final Lean record
constructor and projections remain to be pinned. QED.

| Node | Exact role | Dependencies |
| --- | --- | --- |
| `D0.1` | Lock the cofinal parameter/index set, `L=2 log lambda`, `H_lambda=L2([lambda^-1,lambda],du/u)`, its norm, `kappa`, `V_n`, `E_(lambda,N)`, and zero-extension support | none after control release |
| `D0.2` | Lock `QW`, `QW_lambda`, and `QW^N_lambda` on exactly D0.1, with sesquilinear convention and matrix normalization | D0.1 |
| `D0.3` | AND registry for `A_lambda`, finite-form Riesz operator, `D_log`, its raw/modified-space perturbations, prolate expression/realization, detector, and nonconflation | D0.1, D0.2 |
| `D0.4` | Define `gamma V_n=V_(-n)`, inversion, and exact parity sectors; do not claim parity cleanliness | D0.1, D0.3 |
| `D0.5` | Define the least eigenspace and prolate trial-vector types and keep their roles distinct; do not assume simple-even | D0.2, D0.4 |
| `D0.6` | Lock zero extension, multiplicative Fourier/Mellin sign and half-shift, and compact-substrip topology | D0.1 |
| `D0.7` | Lock `delta_(lambda,N)`, boundary normalization, phase/scalar convention, and `b`; uniform nonzero bounds remain H4d | D0.1, D0.5, D0.6 |
| `D0.8` | Prove the same-object crosswalk among `QW^N`, the chosen ground object, `D_log`, its transform/determinant, and all H1-H4 consumers | D0.1-D0.7 |
| `D0.9` | Apply D0.0 to proved D0.1-D0.8 and produce `EXACT_OBJECT_FAMILY_LOCKED` | D0.1-D0.8 |

After control-plane clearance, the first mathematical leaf is `D0.1`, not
`ArchFormBoundedOnFixedWindow`. D0.5 does not absorb H2a, D0.7 does not absorb
H4d, and D0.4 does not claim the parity theorem that belongs to its later
proof node.

## 5. Leaf ledger

| ID | Exact obligation | Current status | Honest exit |
| --- | --- | --- | --- |
| `C0` | Classical `zeta/xi/Xi` interface and RH equivalence | `PROVED / LEAN_PINNED` | `XI_RH_INTERFACE_LOCKED` |
| `D0` | AND parent: one exact object family; no QW/prolate/D_log conflation | `OPEN_CRITICAL` | `EXACT_OBJECT_FAMILY_LOCKED` |
| `D0.0` | Definitional decomposition contract `D0 <-> D0.1 AND ... AND D0.8` | `MATH_PROVED / LEAN_UNPINNED` | `D0_DECOMPOSITION_LOCKED` |
| `D0.1` | Exact parameter set, Hilbert space, measure, norm, support, basis, and finite subspace | `PROVED / SOURCE_LOCKED / LEAN_UNPINNED` | `EXACT_HILBERT_SPACE_AND_NORM_LOCKED` |
| `D0.2` | Exact Weil sesquilinear form and finite restriction | `PROVED / SOURCE_LOCKED / LEAN_UNPINNED` | `EXACT_WEIL_FORM_LOCKED` |
| `D0.3` | Separate exact operator representations and types | `PROVED / SOURCE_LOCKED / LEAN_UNPINNED` | `EXACT_OPERATOR_TYPES_LOCKED` |
| `D0.4` | Exact parity involution and sectors, without cleanliness claim | `PROVED / SOURCE_LOCKED / LEAN_UNPINNED` | `EXACT_PARITY_SECTORS_LOCKED` |
| `D0.5` | Exact ground eigenspace and trial-vector types, without simple-even claim | `PROVED / SOURCE_LOCKED / LEAN_UNPINNED` | `GROUND_TRIAL_TYPES_LOCKED` |
| `D0.6` | Exact Fourier/Mellin convention and topology | `PROVED / SOURCE_LOCKED / LEAN_UNPINNED` | `EXACT_TRANSFORM_CONVENTION_LOCKED` |
| `D0.7` | Exact boundary/scalar/phase normalization definitions | `BLOCKED / BDET_DEFINITION_LOCKED / WPRIME_CONSUMER_MISSING` | blocker: `D0_7E_WPRIME_CONSUMER_MISSING` |
| `D0.7e` | Owner-ratified finite central calibration plus exact WPrime/ZEO crosswalk | `BLOCKED / 4_OF_5_SUBCOMPONENTS_PROVED` | partial: `D0_7E_CENTRAL_CALIBRATION_LOCKED`; blocker: `D0_7E_WPRIME_CONSUMER_MISSING` |
| `D0.7e.5` | Owner-ratified AND parent for the typed WPrime consumer slot | `BLOCKED / DECOMPOSITION_LOCKED` | partial: `D0_7E_5_DECOMPOSITION_LOCKED`; blocker: `D0_7E_WPRIME_CONSUMER_MISSING` |
| `D0.7e.5.0` | Definitional contract `5 <-> 5a AND 5b AND 5c AND 5d` | `PROVED / OWNER_RATIFIED` | `D0_7E_5_DECOMPOSITION_LOCKED` |
| `D0.7e.5a` | Independent WPrime/ZEO consumer and exact b-orientation lock | `ACTIVE / PARTIAL_MATH_PROVED / SOURCE_BLOCKED` | partial: `D0_7E_CENTRAL_NONZERO_LOCUS_LOCKED`, `D0_7E_BCAL_INVERSE_NORMALIZER_IDENTITY_LOCKED`; blocker: `D0_7E_WPRIME_CONSUMER_MISSING` |
| `D0.7e.5b` | Type downstream alpha, true DeltaE, delta_dict and filter on independent `(m,N)` without defining them | `PROVED / INTERFACE_TYPECHECK_ONLY` | `D0_7E_5B_TYPED_INTERFACE_LOCKED` |
| `D0.7e.5c` | Derive the finite WPrime consumer identity from an independent consumer | `OPEN / BLOCKED_BY_5a` | `D0_7E_WPRIME_CONSUMER_IDENTITY_LOCKED` |
| `D0.7e.5d` | Readdress the unchanged full tracking obligation to H3e | `PROVED / MIGRATION_CORRECTNESS_ONLY / H3e_OPEN` | `D0_7E_XWALK_MIGRATION_LOCKED` |
| `D0.7e.5e` | D0.7e.5 assembly theorem | `BLOCKED_BY_5a_AND_5c` | `D0_7E_5_ASSEMBLED` |
| `D0.8` | Same-object QW-to-D_log-to-transform crosswalk | `OPEN / BLOCKED_BY_D0.7` | `ZERO_PRODUCING_CROSSWALK_LOCKED` |
| `D0.9` | D0 assembly application | `OPEN / BLOCKED_BY_D0.7_D0.8` | `EXACT_OBJECT_FAMILY_LOCKED` |
| `H1` | AND parent for entirety of the exact normalized approximants | `OPEN / GENERIC_CORE_PROVED / EXACT_FAMILY_UNPINNED` | `ENTIRE_APPROXIMANTS_PROVED` |
| `H1.0` | Definitional H1 decomposition contract | `PROVED` | `H1_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H1a` | Finite linear combinations of entire summands remain entire | `PROVED / GENERIC_LEAN` | `LEAN_DIFFERENTIABLE_FINITE_ENTIRE_COMBINATION` |
| `H1b` | Reflection, exponential phase and nonzero scalar preserve entirety/zeros | `PROVED / GENERIC_LEAN` | `LEAN_ENTIRE_PHASE_REFLECTION_SCALAR_CLOSURE` |
| `H1c` | Exact master `F_j` is the same source-locked entire transform | `OPEN / INELIGIBLE_BY_D0.8_AND_ARCHITECTURE_CHOICE` | blocker: `H1_EXACT_APPROXIMANT_SOURCE_UNPINNED` |
| `H1d` | H1 exact-family assembly | `OPEN / BLOCKED_BY_H1c` | `H1_ASSEMBLED` |
| `H2` | AND parent for same-vector real-zero supply | `OPEN / COMPLETED_TRACKER_GLOBAL_IDENTIFICATION_KILLED` | `REAL_ZERO_APPROXIMANTS_PROVED` |
| `H2a` | Simple isolated even ground eigenvector for the exact finite operator | `OPEN_CRITICAL` | `SIMPLE_EVEN_GROUND_PROVED` |
| `H2b` | Transform of that same vector has only real zeros | `CONDITIONAL_ON_H2a` | `REAL_ZERO_APPROXIMANTS_PROVED` |
| `H2c` | H2 assembly theorem | `OPEN / BLOCKED_BY_H2a_H2b` | `H2_ASSEMBLED` |
| `H3` | AND parent for same-family strip tracking | `OPEN` | `STRIP_UNIFORM_TRACKING_PROVED` |
| `H3a` | Ground/trial phase-aligned proximity | `OPEN_CRITICAL` | `GROUND_TRIAL_TRACKING_PROVED` |
| `H3b` | Bounded evaluation on every compact substrip | `OPEN` | `COMPACT_STRIP_EVALUATION_PROVED` |
| `H3c` | Normalized limit is exactly `Xi`, with cofinal quantifiers | `OPEN_CRITICAL` | `XI_LIMIT_IDENTIFICATION_PROVED` |
| `H3e` | Exact migrated WPrime tracking theorem; consumes the D0 slot, H3 inputs, true H4 quantities, H0/A1 and `PO_XWALK_UNIFORM_EVAL` | `OPEN / INACTIVE` | `EXACT_WPRIME_TRACKING_PROVED` |
| `H3d` | H3 assembly theorem `H3a AND H3b AND H3c AND H3e -> H3` | `OPEN / BLOCKED_BY_H3_CHILDREN` | `H3_ASSEMBLED` |
| `H4` | AND parent for detector decay | `OPEN` | `DETECTOR_DECAY_PROVED` |
| `H4a` | Exact non-internal Galerkin/continuum residual identity | `OPEN` | `RESIDUAL_IDENTITY_PROVED` |
| `H4b` | Uniform residual upper bound | `OPEN_CRITICAL` | `RESIDUAL_UPPER_PROVED` |
| `H4c` | True complementary spectral-distance lower bound | `OPEN_CRITICAL` | `TRUE_GAP_LOWER_PROVED` |
| `H4d` | Nonzero normalization and uniform upper control | `OPEN_CRITICAL` | `NORMALIZATION_CONTROL_PROVED` |
| `H4e` | Assembly theorem `H4a AND H4b AND H4c AND H4d -> W_j -> 0` | `OPEN / ASSEMBLY` | `DETECTOR_DECAY_PROVED` |
| `L0` | AND parent for exact Lean ZeroEscape | `OPEN / GENERIC_LOGIC_PROVED / ANALYTIC_TRANSFER_OPEN` | `LAMPORT_ZERO_ESCAPE_LEAN_PROVED` |
| `L0.0` | Definitional L0 decomposition contract | `PROVED` | `L0_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `L0a` | Detector bound plus decay gives error tending to zero | `PROVED / GENERIC_LEAN` | `LEAN_DETECTOR_BOUND_TENDS_TO_ZERO` |
| `L0b` | Approached limit zeros of real-zero approximants are real | `PROVED / GENERIC_LEAN` | `LEAN_REAL_ZERO_LIMIT_LOGIC` |
| `L0c` | Exact Rouché/Hurwitz zero transfer for the H1/H3/H4 family | `OPEN / INELIGIBLE` | blocker: `ROUCHE_HURWITZ_LEAN_ZERO_TRANSFER_MISSING` |
| `L0d` | Exact C0/H2/L0a/L0b/L0c assembly | `OPEN / BLOCKED_BY_H2_L0c` | `LAMPORT_ZERO_ESCAPE_LEAN_PROVED` |
| `L1` | Final `#print axioms` and hole audit | `BLOCKED_BY_ALL` | `ZERO_SORRY_ZERO_UNEXPECTED_AXIOMS` |
| `R0.A` | Final assembly from C0, D0, H1-H4, L0, L1 to RH | `OPEN / BLOCKED_BY_ALL` | `RH_PROVED` |

The source paper already proves a finite real-zero theorem conditionally on a
simple even smallest eigenvector of `QW^N_lambda`, and constructs the derived
zero-producing operator `D_log^(lambda,N)`. It explicitly names two missing
steps: simple-even ground state and sufficiently accurate trial/ground
tracking. Therefore those are obligations, not imported conclusions.

## 6. Transcript claims retained only as conditional interfaces

The attached July 11 transcript contains useful finite algebra:

```text
M_N = G_N^(-1/2) K_N G_N^(-1/2),
k_N = S_N G_N^(-1/2) q_1,
eta_N = ||(I-P_N) T k_N||,
Delta_N = distance from the residual center/target cluster to complement.
```

It does not unconditionally construct the continuum operator, prove Arch-form
boundedness in the chosen Hilbert norm, prove a positive true gap, prove real
zeros for the selected `F_N`, or prove convergence to `Xi`.

`ArchFormBoundedOnFixedWindow` remains a candidate leaf only after D0 fixes
the exact space, norm, canonical Arch form, prime form, and their equality to
the source `QW` object. It is not allowed to manufacture a convenient
surrogate detector.

## 7. Resume protocol — do not stop at narration

On every continuation:

1. Read `STATE.json` and this file.
2. Read the physical Route B bus from disk and run `routeb_status.py --json`.
3. If a physical unanswered bus goal exists, execute only the smallest `NNN`,
   produce its matching answer and state synchronization, and validate the
   transaction. Never skip it or create its successor.
4. If the goal is internally inconsistent, report
   `SPEC_STATUS=INVALID_SPEC`, recommend a `ROUTE_EFFECT`, preserve evidence,
   without treating the spec defect as mathematical success.
5. If no physical goal is open, immediately select the first eligible ordered
   master leaf under `OWNER_AUTHORIZED_AUTORUN` and make it the unique
   `ACTIVE` target.
6. Verify that the selected leaf's dependencies are `PROVED` and that no open
   blocker actually feeds that leaf.
7. Lock its exact statement, types, quantifiers, parent slot, sources, at least
   two risky-node routes, planted falsifier, validations, and failure codes.
8. Launch independent workers on that same leaf, synthesize their results, and
   prove, falsify, route-kill, or legally decompose the leaf.
9. After a proof patch, run direct validation and dependency/hole/axiom scans.
   Update the canonical master state and durable insights.
10. Perform zoom-out assembly checks and automatically select the next
    eligible leaf. Continue until a real pause condition from Section 4.7.

## 8. Current protocol address

Bus 009 `ZeoProvenanceHarmonizationVerify_v1` is now physically closed by a
negative answer. It found:

- its planted-absence token appears in its own scan scope;
- living ZEO overclaims remain in `docs/PROJECT_TREE.md` and
  `docs/project_tree.json`;
- its three-way classification lacks a class for valid statements belonging
  to another route;
- its required artifacts omit the full execution-state synchronization.

The physical pairs `001..009` exist and there is no unanswered bus goal. Bus
009 is staged but not committed. Its negative result still leaves
`OVERCLAIM_LIST` and `OPEN_CRITICAL_ZEO_EXPORT_AMBIGUOUS`; its control-plane
mirrors have now been synchronized, and `routeb_status.py --check` is green as
a transaction/state check only.

Bus 009 keeps the factual classification:

```text
SPEC_STATUS = INVALID_SPEC
ROUTE_EFFECT = BUS_BLOCKING_FOR_PO0
RESOLUTION = ANSWER_RECORDED
```

The owner has now authorized autonomous master execution. Codex does not
create Bus 010 and does not relabel PO0/ZEO as closed. D0.1--D0.6 are proved.
For D0.3g, Pro review ratified only the finite detector carrier
`Mfin_(m,N)=WeilOp_(m,N)`; it did not authorize a one-parameter `M_lambda` or
identify diagnostic Schur values `theta_j` with exact spectra. The exact
parity reduction gives the full spectrum `nu_j(m,N)` and sector spectra
`epsilon_plus_j(m,N)`, `epsilon_minus_j(m,N)` without a global rank crosswalk.
This closes D0.3 and its assembly as `EXACT_OPERATOR_TYPES_LOCKED`. D0.4 locks
the exact inversion/parity sectors without numerical cleanliness, and D0.5
locks the set-valued ground eigenspace plus trial-vector dependent types
without simple-even or nonzero assumptions. D0.7 was then legally decomposed:
the exact Dirichlet vector/functional, trial scalar/phase, dependent ground
boundary normalization, and `b`-namespace firewall are proved. The canonical
detector `b` used by `W'` was then supplied by immutable owner input. The audit
accepted the finite dependent definition
`bDet_(m,N)=Fhat_(m,N)(0)/Xi(0)=sqrt(L_m)c0/zeta(1/2)` on `TrialNonzero`, with
the exact reflection `Fplus(z)=T_m(k1)(-z)`, an eta-series proof that
`zeta(1/2)!=0`, and dependent normalization only on `BDetNonzero`.

It did not accept the unspecified `N(lambda)=ceil(kappa lambda^2)` selector or
the proposed WPrime/ZEO inequality as a proof. The latest Pro review then
forced a consumer-orientation audit before any finite identity. That audit
proved the exact dependent locus
`CentralValueNonzero=BDetNonzero=FhatAtZeroNonzero=BCalNonzero` and the
identity `bZeoMul=bCal^(-1)`, hence
`G=Fhat/bCal=bZeoMul*Fhat`. It also proved that `TrialNonzero` alone does not
give central nonvanishing.

No independent `FZeo` or `WPrime` consumer was found by the completed T0 corpus
mining pass. The old `W'=|b|sqrt(lambda)sqrt(alpha/DeltaE)` row is explicitly a
target/sketch or diagnostic, and the physical Option-B owner ruling defines
that desired right-hand side rather than recovering an independent consumer.
The owner has now physically ratified recommended R1--R5. This closes only the
DAG decision layer: `D0.7e.5` is a canonical AND node, its decomposition
contract `D0.7e.5.0` is proved definitionally, and the full tracking theorem is
registered only at `H3e`, with Contract-v2 direct `q_b`, independent `(m,N)`,
and alpha's definitional home at H0/A1. The owner-ratified no-stop sprint then
closed 5b only as an uninstantiated type interface and 5d only as preservation
of wording/address. H0/A1 and `PO_XWALK_UNIFORM_EVAL` remain external
`OPEN_CRITICAL` obligations; H3e itself remains OPEN.

The independent rev14 frontier closes C0 in Lean using Mathlib's entire
`completedRiemannZeta0` and an exact affine critical-strip/centered-strip
crosswalk. It also proves generic Lean cores for finite entire combinations,
phase/reflection/scalar normalization, detector-bound convergence, and the
logic that approximated limit zeros of real-zero approximants are real. These
generic cores do not select or supply the project family. The exact H1
same-object crosswalk and the exact Rouché/Hurwitz zero-transfer leaf remain
OPEN/ineligible.

The same rev14 audit gives a compiled scope falsifier for the completed trial
tracker: `gammaC(1)=0`, hence every such tracker has the fixed non-real zero
`z=-i/2`. Therefore the current global H2 contract cannot use `Fhat` or `G` as
its `F_j`. This kills only that identification. The remaining coherent choices
are a source-canonical raw transform with global H1/H2 or a separately
ratified strip-local completed-tracker contract; no choice is inferred here.

The unique active canonical leaf is now `D0.7e.5a`. Owner ratification did not
supply an independent consumer or choose the historical WPrime `b`
orientation, so the mathematical stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`. The standing order is active, but T0 produced
no candidate eligible for its C1--C6/two-review ratification path. H3e is
`OPEN / INACTIVE`; no H3c/H4 theorem
was imported into D0, D0.7 and all ancestors remain blocked, no Bus 010 was
created, and Route B remains `CHALLENGER / NOT_RH`.

## 9. Completion condition

Only a proved root assembly permits the label `RH_PROVED`:

```text
(C0 AND D0 AND H1 AND H2 AND H3 AND H4 AND L0 AND L1)
AND R0.A
AND zero holes
AND zero unexpected axioms
AND zero RH-conditional imports
AND zero circular bridges.
```

Until then the exact public label is:

```text
CONDITIONAL_CLOSURE_PROVED / WITNESS_SUPPLY_OPEN / ROUTE_B_CHALLENGER / NOT_RH
```

## 10. Restart entry point

For a fresh Codex session, use `START_GOAL.md` in this directory. It is a
paste-ready goal that loads this master file and `STATE.json`, enforces the
physical-bus transaction boundary, and resumes the unique active leaf recorded
in state (currently canonical `D0.7e.5a`) under the durable owner-authorized
scheduler. The owner-ratified B-prime subtree is canonical, but its first
mathematical child is source-blocked.
