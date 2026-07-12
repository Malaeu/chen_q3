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
|   |-- H1c ExactApproximantSourceCrosswalk [AND]
|   |   |-- H1c1 Proposition59RhsEntire
|   |   |-- H1c2 RawIntegralRhsCrosswalk
|   |   |-- H1c3 ExactMasterFamilySelection
|   |   `-- H1c4 H1cAssembly
|   `-- H1d H1Assembly
|-- H2 RealZeroApproximants [AND]
|   |-- H2a SimpleEvenGround [AND]
|   |   |-- H2a1 GenericSimpleEvenGroundSectorCriterion
|   |   |-- H2a2 ExactSelectedFamilySectorOrdering [AND]
|   |   |   |-- H2a2a GenericSectorIsolationRadius
|   |   |   |-- H2a2b ExactSectorOrderingAndRadiusInstantiation
|   |   |   `-- H2a2c H2a2Assembly
|   |   `-- H2a3 H2aAssembly
|   |-- H2b SameVectorRealZeros [AND / CONDITIONAL]
|   |   |-- H2b1 GenericHermitianDeterminantRealZeros
|   |   |-- H2b2 ExactTheorem510Factorization [AND]
|   |   |   |-- H2b2a GenericRankOneCorrectionWeightedSymmetry
|   |   |   |-- H2b2b ExactModifiedHilbertFactorization
|   |   |   `-- H2b2c H2b2Assembly
|   |   `-- H2b3 H2bAssembly
|   `-- H2c H2Assembly
|-- H3 StripUniformTracking [AND]
|   |-- H3a GroundTrialTracking [AND]
|   |   |-- H3a1 GenericComplexPhaseAlignmentCore
|   |   |-- H3a2 ExactGroundTrialProjectiveRate [AND]
|   |   |   |-- H3a2a GenericWeightedRayleighProjectiveCore
|   |   |   |-- H3a2b ExactSpectralProjectiveRateInstantiation
|   |   |   `-- H3a2c H3a2Assembly
|   |   `-- H3a3 H3aAssembly
|   |-- H3b CompactStripEvaluation [AND]
|   |   |-- H3b1 GenericCompactEvaluationRateTransfer
|   |   |-- H3b2 ExactWeightedEvaluationInstantiation [AND]
|   |   |   |-- H3b2a GenericWeightedProjectiveEvaluationCore
|   |   |   |-- H3b2b ExactWeightedProjectiveInstantiation
|   |   |   `-- H3b2c H3b2Assembly
|   |   `-- H3b3 H3bAssembly
|   |-- H3c XiLimitIdentification [AND]
|   |   |-- H3c1 NormalizedDoubleCompletionStripGuard
|   |   |-- H3c2 ExactRawOrCompensatedXiLimitAndFilter [AND]
|   |   |   |-- H3c2a GenericDifferenceReferenceLimitTransfer
|   |   |   |-- H3c2b ExactReferenceXiLimitAndCrosswalk
|   |   |   `-- H3c2c H3c2Assembly
|   |   `-- H3c3 H3cAssembly
|   |-- H3e ExactWPrimeTrackingTheorem [AND]
|   |   |-- H3e1 GenericNormalizedTrackingRateTransfer
|   |   |-- H3e2 ExactRelativeTrackingInstantiation
|   |   `-- H3e3 H3eAssembly
|   `-- H3d H3Assembly
|-- H4 DetectorDecay [AND]
|   |-- H4a SafeAlphaUpper [AND]
|   |   |-- H4a1 AmbientResidualIdentity [AND]
|   |   |   |-- H4a1a GenericAmbientCompressedResidualSplit
|   |   |   |-- H4a1b ExactRouteBAmbientResidualCrosswalk
|   |   |   `-- H4a1c H4a1Assembly
|   |   |-- H4a2 UniformResidualUpper [AND]
|   |   |   |-- H4a2a GenericAmbientResidualEnvelopeTransfer
|   |   |   |-- H4a2b ExactRouteBComponentRateInstantiation
|   |   |   `-- H4a2c H4a2Assembly
|   |   |-- H4a3 ResidualToCanonicalAlphaUpper [AND]
|   |   |   |-- H4a3a GenericWeightedSpectralTempleCore
|   |   |   |-- H4a3b ExactRouteBResidualSpectralInstantiation [AND]
|   |   |   |   |-- H4a3b1 GenericTempleResidualGapEnvelopeTransfer
|   |   |   |   |-- H4a3b2 ExactRouteBSpectralResidualRateInstantiation
|   |   |   |   `-- H4a3b3 H4a3bAssembly
|   |   |   `-- H4a3c H4a3Assembly
|   |   `-- H4a4 SafeAlphaUpperAssembly
|   |-- H4b SafeGapLower [AND]
|   |   |-- H4b1 GenericPerturbativeTrueGapLower
|   |   |-- H4b2 ExactSameParityFuchsGapInstantiation
|   |   `-- H4b3 H4bAssembly
|   |-- H4c SafeSignAndB [AND]
|   |   |-- H4c1 GenericTwoSidedNormalizedBControl
|   |   |-- H4c2 ExactSafeSignAndBInstantiation
|   |   `-- H4c3 H4cAssembly
|   |-- H4d SafeRateAssembly [AND]
|   |   |-- H4d1 GenericSafeRateCore [AND]
|   |   |   |-- H4d1a NaturalScaleExponentCore
|   |   |   |-- H4d1b CofinalSquareEnvelopeCore
|   |   |   `-- H4d1c GenericSafeRateAssembly
|   |   |-- H4d2 ExactSafeRateConstantsAndFilter [AND]
|   |   |   |-- H4d2a GenericSafeBoundsToSquareEnvelope
|   |   |   |-- H4d2b ExactSafeInputsAndJointFilter
|   |   |   `-- H4d2c H4d2Assembly
|   |   `-- H4d3 SafeRateAssembly
|   `-- H4e QuantitativeSafeWitnessAssembly
|-- L0 LeanZeroEscape [AND]
|   |-- L0a DetectorBoundConvergenceCore
|   |-- L0b RealZeroLimitLogic
|   |-- L0c RoucheHurwitzZeroTransfer [AND]
|   |   |-- L0c1 GenericLocallyUniformZeroTransfer
|   |   |-- L0c2 ExactRouteBFamilyInstantiation
|   |   `-- L0c3 L0cAssembly
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
| `D0.7` | Lock `delta_(lambda,N)`, boundary normalization, phase/scalar convention, and `b`; uniform nonzero/two-sided bounds remain H4c SafeSignAndB | D0.1, D0.5, D0.6 |
| `D0.8` | Prove the same-object crosswalk among `QW^N`, the chosen ground object, `D_log`, its transform/determinant, and all H1-H4 consumers | D0.1-D0.7 |
| `D0.9` | Apply D0.0 to proved D0.1-D0.8 and produce `EXACT_OBJECT_FAMILY_LOCKED` | D0.1-D0.8 |

After control-plane clearance, the first mathematical leaf is `D0.1`, not
`ArchFormBoundedOnFixedWindow`. D0.5 does not absorb H2a, D0.7 does not absorb
H4c SafeSignAndB, and D0.4 does not claim the parity theorem that belongs to its later
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
| `H1c` | AND parent from Proposition-5.9 source formula through exact master-family selection | `OPEN / SOURCE_RHS_AND_RAW_INTEGRAL_PROVED / MASTER_CROSSWALK_OPEN` | blocker: `H1_EXACT_APPROXIMANT_SOURCE_UNPINNED` |
| `H1c.0` | H1c source/crosswalk decomposition contract | `PROVED` | `H1C_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H1c1` | Proposition-5.9 removable RHS is entire for every finite vector | `PROVED / SOURCE_FORMULA_LEAN` | `PROPOSITION59_RHS_ENTIRE` |
| `H1c2` | Exact phase-centered raw integral equals the removable RHS, including lattice values | `PROVED / EXACT_LEAN / ALL_Z` | `RAW_INTEGRAL_PROPOSITION59_RHS_EXACT_CROSSWALK` |
| `H1c3` | Select the exact master `F_j` and prove its D0.8 same-family crosswalk | `OPEN / OWNER_ARCHITECTURE_CHOICE_REQUIRED` | blocker: `H1_MASTER_ARCHITECTURE_CHOICE_REQUIRED` |
| `H1c4` | H1c exact source-family assembly | `OPEN / BLOCKED_BY_H1c3` | `H1C_ASSEMBLED` |
| `H1d` | H1 exact-family assembly | `OPEN / BLOCKED_BY_H1c` | `H1_ASSEMBLED` |
| `H2` | AND parent for same-vector real-zero supply | `OPEN / COMPLETED_TRACKER_GLOBAL_IDENTIFICATION_KILLED` | `REAL_ZERO_APPROXIMANTS_PROVED` |
| `H2a` | AND parent: generic sector criterion plus exact same-family strict sector ordering | `OPEN / GENERIC_CORE_PROVED` | blocker: `H2A_EXACT_SECTOR_ORDERING_MISSING` |
| `H2a.0` | H2a decomposition contract | `PROVED` | `H2A_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H2a1` | A simple even-sector bottom strictly below every odd eigenvalue is the simple even global ground; simple ground alone has only a parity dichotomy | `PROVED / GENERIC_LEAN / FALSIFIER_LIVE` | `GENERIC_SIMPLE_EVEN_GROUND_SECTOR_CRITERION_LEAN` |
| `H2a2` | AND parent: generic half-minimum sector-isolation radius plus exact selected-family strict sector ordering/instantiation | `OPEN / GENERIC_CORE_PROVED` | blocker: `H2A_EXACT_SECTOR_ORDERING_MISSING` |
| `H2a2.0` | H2a2 decomposition contract | `PROVED` | `H2A2_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H2a2a` | Two strict sector gaps give a positive isolation radius below every level above the next-even or bottom-odd threshold | `PROVED / GENERIC_LEAN` | `GENERIC_SECTOR_ISOLATION_RADIUS_LEAN` |
| `H2a2b` | Select the exact H1c3/D0.8 family, prove both strict sector gaps and instantiate the radius with ordering/multiplicity crosswalks | `OPEN / INELIGIBLE` | blocker: `H2A_EXACT_SECTOR_ORDERING_MISSING` |
| `H2a2c` | Exact H2a2 assembly | `OPEN / BLOCKED_BY_H2a2b` | `H2A2_EXACT_SECTOR_ISOLATION_ASSEMBLY` |
| `H2a3` | Exact H2a assembly | `OPEN / BLOCKED_BY_H2a2` | `SIMPLE_EVEN_GROUND_PROVED` |
| `H2b` | AND parent: generic Hermitian determinant transfer plus exact same-family Theorem-5.10 factorization | `CONDITIONAL / GENERIC_CORE_PROVED / EXACT_FACTOR_OPEN` | blocker: `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING` |
| `H2b.0` | H2b decomposition contract; conditional parent never discharges H2 | `PROVED` | `H2B_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H2b1` | Periodic determinant and Hermitian charpoly/product real-zero transfers, with non-Hermitian and vanishing-unit plants | `PROVED / GENERIC_LEAN / FALSIFIERS_LIVE` | `GENERIC_HERMITIAN_DETERMINANT_REAL_ZERO_TRANSFER_LEAN` |
| `H2b2` | AND parent: generic rank-one kernel/weighted symmetry plus exact modified-Hilbert quotient and factorization | `OPEN / GENERIC_CORE_PROVED` | blocker: `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING` |
| `H2b2.0` | H2b2 decomposition contract | `PROVED` | `H2B2_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H2b2a` | Rank-one correction kills the calibration vector and is symmetric for the supplied T-weighted form | `PROVED / GENERIC_LEAN` | `H2B2_GENERIC_RANK_ONE_CORRECTION_WEIGHTED_SYMMETRY_LEAN` |
| `H2b2b` | Exact same-family T positivity/radical, quotient descent, complement, phase and all-z factorization | `OPEN / INELIGIBLE` | blocker: `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING` |
| `H2b2c` | Exact H2b2 assembly | `OPEN / BLOCKED_BY_H2b2b` | `H2B2_EXACT_FACTORIZATION_ASSEMBLY` |
| `H2b3` | Exact H2b assembly | `OPEN / BLOCKED_BY_H2b2` | `H2B_EXACT_REAL_ZERO_ASSEMBLY` |
| `H2c` | H2 assembly theorem | `OPEN / BLOCKED_BY_H2a_H2b` | `H2_ASSEMBLED` |
| `H3` | AND parent for same-family strip tracking | `OPEN` | `STRIP_UNIFORM_TRACKING_PROVED` |
| `H3a` | AND parent: generic complex phase/rate transfer plus exact same-family ground/trial projective-defect rate | `OPEN / GENERIC_CORE_PROVED` | blocker: `H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING` |
| `H3a.0` | H3a decomposition contract | `PROVED` | `H3A_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H3a1` | Total canonical phase, exact unit-vector norm identity, square-root defect bound and nonbottom-filter rate transfer | `PROVED / GENERIC_LEAN` | `GENERIC_PHASE_ALIGNMENT_RATE_TRANSFER_LEAN` |
| `H3a2` | AND parent: generic weighted Rayleigh/projective inequality plus exact same-family spectral rate | `OPEN / GENERIC_CORE_PROVED` | blocker: `H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING` |
| `H3a2.0` | H3a2 decomposition contract | `PROVED` | `H3A2_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H3a2a` | Nonnegative normalized spectral weights and a complementary gap bound projective defect by Rayleigh excess/gap | `PROVED / GENERIC_LEAN` | `H3A2_GENERIC_WEIGHTED_RAYLEIGH_PROJECTIVE_DEFECT_LEAN` |
| `H3a2b` | Exact simple-even ground/trial spectral weights, overlap crosswalk, positive gap, weighted rate and shared filter | `OPEN / INELIGIBLE` | blocker: `H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING` |
| `H3a2c` | Exact H3a2 assembly | `OPEN / BLOCKED_BY_H3a2b` | `H3A2_EXACT_PROJECTIVE_RATE_ASSEMBLY` |
| `H3a3` | Exact H3a assembly | `OPEN / BLOCKED_BY_H3a2` | `H3A_EXACT_GROUND_TRIAL_TRACKING_ASSEMBLY` |
| `H3b` | AND parent: generic compact rate transfer plus exact weighted Route B instantiation | `OPEN / GENERIC_CORE_PROVED` | blocker: `H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING` |
| `H3b.0` | H3b decomposition contract | `PROVED` | `H3B_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H3b1` | Vanishing compact-uniform envelopes imply uniform/compact-open convergence; a fixed bound alone is falsified | `PROVED / GENERIC_LEAN / FALSIFIER_LIVE` | `GENERIC_COMPACT_EVALUATION_RATE_TRANSFER_LEAN` |
| `H3b2` | AND parent: generic H3a1-to-H3b1 weighted-projective bridge plus exact same-family instantiation | `OPEN / GENERIC_CORE_PROVED` | blocker: `H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING` |
| `H3b2.0` | H3b2 decomposition contract | `PROVED` | `H3B2_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H3b2a` | A nonnegative compact envelope times the phase-aligned projective defect controls uniform evaluation error on a nonbottom filter | `PROVED / GENERIC_LEAN` | `H3B2_GENERIC_WEIGHTED_PROJECTIVE_EVALUATION_TRANSFER_LEAN` |
| `H3b2b` | Instantiate exact ground/trial, evaluation map/envelope, weighted rate and joint filter | `OPEN / INELIGIBLE` | blocker: `H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING` |
| `H3b2c` | Exact H3b2 assembly | `OPEN / BLOCKED_BY_H3b2b` | `H3B2_EXACT_WEIGHTED_EVALUATION_ASSEMBLY` |
| `H3b3` | Exact H3b assembly | `OPEN / BLOCKED_BY_H3b2` | `COMPACT_STRIP_EVALUATION_PROVED` |
| `H3c` | AND parent: double-completion strip guard plus exact raw-or-compensated same-family Xi limit | `OPEN / WRONG_OBJECT_KILLED / EXACT_LIMIT_OPEN` | blocker: `H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING` |
| `H3c.0` | H3c decomposition contract | `PROVED` | `H3C_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H3c1` | Central-normalized extra completion of already completed `centeredXi` differs somewhere inside the open critical strip | `PROVED / EXACT_LEAN / FALSIFIER_LIVE` | `H3C_NORMALIZED_DOUBLE_COMPLETION_STRIP_MISMATCH_LEAN` |
| `H3c2` | AND parent: generic difference/reference transfer plus exact raw-or-inverse family/reference Xi limit | `OPEN / GENERIC_CORE_PROVED` | blocker: `H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING` |
| `H3c2.0` | H3c2 decomposition contract | `PROVED` | `H3C2_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H3c2a` | Uniform and locally-uniform convergence of a difference to zero plus a reference to Xi transfers to the target family | `PROVED / GENERIC_LEAN` | `H3C2_GENERIC_DIFFERENCE_REFERENCE_LIMIT_TRANSFER_LEAN` |
| `H3c2b` | Exact difference family, reference Xi limit, raw/inverse completion crosswalk and joint filter | `OPEN / INELIGIBLE` | blocker: `H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING` |
| `H3c2c` | Exact H3c2 assembly | `OPEN / BLOCKED_BY_H3c2b` | `H3C2_EXACT_LIMIT_TRANSFER_ASSEMBLY` |
| `H3c3` | Exact H3c assembly | `OPEN / BLOCKED_BY_H3c2` | `H3C_EXACT_LIMIT_IDENTIFICATION_ASSEMBLY` |
| `H3e` | AND parent: generic normalized-tracking rate transfer plus exact same-family WPrime relative-rate instantiation | `OPEN / GENERIC_CORE_PROVED / PLANTS_LIVE` | blocker: `H3E_EXACT_RELATIVE_TRACKING_INPUTS_MISSING` |
| `H3e.0` | H3e decomposition contract | `PROVED` | `H3E_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H3e1` | Reciprocal-b normalization plus two relative rates imply uniform-on-set tracking; detector-decay-only and safe-margin-only shortcuts are falsified | `PROVED / GENERIC_LEAN / FALSIFIERS_LIVE` | `H3E_GENERIC_NORMALIZED_TRACKING_RATE_TRANSFER_LEAN` |
| `H3e2` | Instantiate the independent WPrime, absolute tracking, exact b/Xi objects, both relative rates and one joint filter on the same family | `OPEN / INELIGIBLE` | blocker: `H3E_EXACT_RELATIVE_TRACKING_INPUTS_MISSING` |
| `H3e3` | Exact H3e assembly | `OPEN / BLOCKED_BY_H3e2` | `H3E_EXACT_NORMALIZED_TRACKING_ASSEMBLY` |
| `H3d` | H3 assembly theorem `H3a AND H3b AND H3c AND H3e -> H3` | `OPEN / BLOCKED_BY_H3_CHILDREN` | `H3_ASSEMBLED` |
| `H4` | Contract-v2 AND parent for QuantitativeSafeWitness and detector decay | `OPEN` | `DETECTOR_DECAY_PROVED` |
| `H4.0` | Contract-v2 decomposition into four safe leaves | `PROVED` | `H4_CONTRACT_V2_DECOMPOSITION_LOCKED` |
| `H4a` | SafeAlphaUpper for the canonical alpha | `OPEN_CRITICAL` | `SAFE_ALPHA_UPPER_PROVED` |
| `H4a.0` | Residual-to-alpha decomposition contract | `PROVED` | `H4A_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4a1` | AND parent: generic ambient/compressed residual split plus exact Route B carrier crosswalk | `OPEN / GENERIC_CORE_PROVED` | blocker: `H4A1_EXACT_AMBIENT_RESIDUAL_CROSSWALK_MISSING` |
| `H4a1.0` | H4a1 decomposition contract | `PROVED` | `H4A1_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4a1a` | Ambient residual equals compressed residual plus leakage; zero internal residual need not mean zero ambient residual | `PROVED / GENERIC_LEAN / FALSIFIER_LIVE` | `GENERIC_AMBIENT_COMPRESSED_RESIDUAL_SPLIT_LEAN` |
| `H4a1b` | Pin the exact domain-safe Route B operator, projection, trial/Ritz object, residual/leakage crosswalk and later norm-rate interface | `OPEN / INELIGIBLE` | blocker: `H4A1_EXACT_AMBIENT_RESIDUAL_CROSSWALK_MISSING` |
| `H4a1c` | Exact H4a1 assembly | `OPEN / BLOCKED_BY_H4a1b` | `RESIDUAL_IDENTITY_PROVED` |
| `H4a2` | AND parent: generic ambient/compressed/leakage envelope receiver plus exact same-family component-rate instantiation | `OPEN / GENERIC_CORE_PROVED` | blocker: `H4A2_EXACT_COMPONENT_RATE_INSTANTIATION_MISSING` |
| `H4a2.0` | H4a2 decomposition contract | `PROVED` | `H4A2_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4a2a` | Component bounds imply ambient norm and squared-residual bounds, with Ritz/leakage and nonbottom-filter wrappers | `PROVED / GENERIC_LEAN / FALSIFIER_RETAINED` | `GENERIC_AMBIENT_RESIDUAL_ENVELOPE_TRANSFER_LEAN` |
| `H4a2b` | Instantiate both exact component rates on one domain-safe Route B operator/projection/family/filter | `OPEN / INELIGIBLE` | blocker: `H4A2_EXACT_COMPONENT_RATE_INSTANTIATION_MISSING` |
| `H4a2c` | Exact H4a2 assembly | `OPEN / BLOCKED_BY_H4a2b` | `H4A2_EXACT_AMBIENT_RESIDUAL_RATE_ASSEMBLY` |
| `H4a3` | AND parent for the corrected weighted-spectral Temple bridge and exact Route B instantiation | `OPEN / GENERIC_CORE_PROVED / EXACT_INSTANTIATION_OPEN` | blocker: `H4A3_EXACT_SPECTRAL_INSTANTIATION_MISSING` |
| `H4a3.0` | Definitional H4a3 decomposition contract | `PROVED` | `H4A3_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4a3a` | Weighted spectral variance gives `etaSq >= alpha*(Delta-alpha)` and the correct Temple/half-gap bounds | `PROVED / GENERIC_LEAN` | `WEIGHTED_SPECTRAL_TEMPLE_CORE_LEAN` |
| `H4a3b` | AND parent: generic Temple residual/gap envelope rate transfer plus exact same-parity spectral instantiation | `OPEN / GENERIC_CORE_PROVED / FALSIFIER_LIVE` | blocker: `H4A_EXACT_RESIDUAL_SQUARE_AND_GAP_ENVELOPE_MISSING` |
| `H4a3b.0` | H4a3b decomposition contract | `PROVED` | `H4A3B_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4a3b1` | Temple half-gap + residual-square/gap envelopes imply the explicit single-envelope SafeAlphaUpper rate | `PROVED / GENERIC_LEAN / FALSIFIER_LIVE` | `GENERIC_TEMPLE_RESIDUAL_GAP_ENVELOPE_TRANSFER_LEAN` |
| `H4a3b2` | Instantiate canonical alpha, spectral weights, residual variance, half-gap, squared residual and true-gap envelopes on one exact family/filter | `OPEN / INELIGIBLE` | blocker: `H4A_EXACT_RESIDUAL_SQUARE_AND_GAP_ENVELOPE_MISSING` |
| `H4a3b3` | Exact H4a3b assembly | `OPEN / BLOCKED_BY_H4a3b2` | `H4A3B_EXACT_SAFE_ALPHA_RATE_ASSEMBLY` |
| `H4a3c` | Assemble the generic core with the exact spectral instantiation | `OPEN / BLOCKED_BY_H4a3b` | `H4A3_EXACT_RESIDUAL_TO_ALPHA_ASSEMBLY` |
| `H4a4` | SafeAlphaUpper assembly | `OPEN / BLOCKED_BY_H4a1-a3` | `SAFE_ALPHA_UPPER_PROVED` |
| `H4b` | AND parent: generic two-endpoint perturbation budget plus exact same-parity Fuchs-gap instantiation | `OPEN / GENERIC_CORE_PROVED / GUARDS_LIVE` | blocker: `H4B_EXACT_SAME_PARITY_FUCHS_GAP_INSTANTIATION_MISSING` |
| `H4b.0` | H4b decomposition contract | `PROVED` | `H4B_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4b1` | Absolute endpoint drift bounds plus a surviving model-gap budget imply the true-gap floor, pointwise and on a nonbottom filter | `PROVED / GENERIC_LEAN / FALSIFIERS_LIVE` | `GENERIC_PERTURBATIVE_TRUE_GAP_LOWER_LEAN` |
| `H4b2` | Pin the parity-clean Route B operator/model, both endpoint perturbations, ordering/multiplicity and positive Fuchs-envelope remainder | `OPEN / INELIGIBLE` | blocker: `H4B_EXACT_SAME_PARITY_FUCHS_GAP_INSTANTIATION_MISSING` |
| `H4b3` | Exact H4b assembly | `OPEN / BLOCKED_BY_H4b2` | `H4B_EXACT_SAFE_GAP_LOWER_ASSEMBLY` |
| `H4c` | AND parent: generic normalized-b consequences plus exact alpha/gap/b/sign/filter instantiation | `OPEN / GENERIC_CORE_PROVED` | blocker: `H4C_EXACT_SIGN_AND_B_INSTANTIATION_MISSING` |
| `H4c.0` | H4c decomposition contract | `PROVED` | `H4C_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4c1` | Two-sided normalized b control gives nonzero, direct upper, scale-dependent reciprocal and normalized-error bounds | `PROVED / GENERIC_LEAN / FALSIFIER_RETAINED` | `H4C_GENERIC_TWO_SIDED_NORMALIZED_B_CONTROL_LEAN` |
| `H4c2` | Define exact alpha/b, prove alpha/gap signs, b orientation, full two-sided bound, q_b and one carrier/filter | `OPEN / INELIGIBLE` | blocker: `H4C_EXACT_SIGN_AND_B_INSTANTIATION_MISSING` |
| `H4c3` | Exact H4c assembly | `OPEN / BLOCKED_BY_H4c2` | `H4C_EXACT_SAFE_SIGN_AND_B_ASSEMBLY` |
| `H4d` | SafeRateAssembly parent | `OPEN` | `SAFE_RATE_ASSEMBLED` |
| `H4d.0` | Generic/exact rate decomposition contract | `PROVED` | `H4D_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4d1` | Generic exponent and cofinal square-envelope rate package | `PROVED / GENERIC_LEAN` | `LEAN_SAFE_RATE_GENERIC_PACKAGE` |
| `H4d1.0` | H4d1 natural/cofinal generic decomposition contract | `PROVED` | `H4D1_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4d1a` | Strict margin gives negative-power decay on the natural scale | `PROVED / GENERIC_LEAN` | `LEAN_SAFE_RATE_POLYNOMIAL_CORE` |
| `H4d1b` | A non-bottom cofinal scale plus squared envelope forces detector decay | `PROVED / GENERIC_LEAN` | `LEAN_SAFE_RATE_COFINAL_SQUARE_CORE` |
| `H4d1c` | Assemble exponent negativity and cofinal detector convergence | `PROVED / GENERIC_LEAN` | `LEAN_SAFE_RATE_GENERIC_PACKAGE` |
| `H4d2` | AND parent: generic common-envelope square bound plus exact SAFE/WPrime/filter instantiation | `OPEN / GENERIC_CORE_PROVED` | blocker: `H4D_EXACT_SQUARE_ENVELOPE_INSTANTIATION_MISSING` |
| `H4d2.0` | H4d2 decomposition contract | `PROVED` | `H4D2_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `H4d2a` | Common-envelope SAFE bounds and an independent WPrime square identity imply the exact Contract-v2 squared polynomial envelope | `PROVED / GENERIC_LEAN` | `GENERIC_SAFE_BOUNDS_TO_SQUARE_ENVELOPE_LEAN` |
| `H4d2b` | Instantiate exact WPrime identity, SAFE constants/signs, common envelope, nonnegative branch, strict margin and one cofinal joint filter | `OPEN / INELIGIBLE` | blocker: `H4D_EXACT_SQUARE_ENVELOPE_INSTANTIATION_MISSING` |
| `H4d2c` | Exact H4d2 assembly | `OPEN / BLOCKED_BY_H4d2b` | `H4D2_EXACT_SQUARE_ENVELOPE_ASSEMBLY` |
| `H4d3` | Exact SafeRateAssembly | `OPEN / BLOCKED_BY_H4d2` | `SAFE_RATE_ASSEMBLED` |
| `H4e` | Four safe leaves imply QuantitativeSafeWitness and `W_j -> 0` | `OPEN / ASSEMBLY` | `DETECTOR_DECAY_PROVED` |
| `L0` | AND parent for exact Lean ZeroEscape | `OPEN / GENERIC_ZERO_TRANSFER_PROVED / EXACT_FAMILY_OPEN` | `LAMPORT_ZERO_ESCAPE_LEAN_PROVED` |
| `L0.0` | Definitional L0 decomposition contract | `PROVED` | `L0_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `L0a` | Detector bound plus decay gives error tending to zero | `PROVED / GENERIC_LEAN` | `LEAN_DETECTOR_BOUND_TENDS_TO_ZERO` |
| `L0b` | Approached limit zeros of real-zero approximants are real | `PROVED / GENERIC_LEAN` | `LEAN_REAL_ZERO_LIMIT_LOGIC` |
| `L0c` | AND parent for generic zero transfer and exact H1/H3/H4 instantiation | `OPEN / GENERIC_CORE_PROVED / EXACT_FAMILY_OPEN` | blocker: `L0C_EXACT_FAMILY_INSTANTIATION_MISSING` |
| `L0c.0` | Definitional L0c decomposition contract | `PROVED` | `L0C_DECOMPOSITION_EQUIVALENCE_LOCKED` |
| `L0c1` | Entire locally-uniform nonzero limits satisfy full-tail `ZerosApproachOn` | `PROVED / GENERIC_LEAN` | `GENERIC_ROUCHE_HURWITZ_ZERO_TRANSFER_LEAN` |
| `L0c2` | Instantiate L0c1 with the one exact Route B family and `centeredXi` | `OPEN / INELIGIBLE / H1_H3_H4_OPEN` | blocker: `L0C_EXACT_FAMILY_INSTANTIATION_MISSING` |
| `L0c3` | Apply the generic theorem to the exact-family inputs | `OPEN / BLOCKED_BY_L0c2` | `L0C_EXACT_ZERO_TRANSFER_ASSEMBLY` |
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

Revision 15 repairs H4 to the four leaves required by final Contract v2:
SafeAlphaUpper, SafeGapLower, SafeSignAndB, and SafeRateAssembly. The former
residual identity and upper-bound obligations now live strictly below
SafeAlphaUpper. The historically registered composition
`sqrt(alpha/DeltaE) <= eta/DeltaE` is falsified by a two-level exact
counterexample and may not be used; a correct Rayleigh-center spectral-distance
bridge is now an explicit OPEN obligation. The generic strict-exponent decay
core of SafeRateAssembly is Lean-proved, but no exact safe leaf closes.

The same audit proves that I-b2's lower bound on `|b|sqrt(lambda)` does not
give a positive lower bound for `|b|`, so absolute H3e tracking cannot be
divided into normalized tracking without reciprocal error control. It also
registers `XI_LIMIT_OBJECT_MISMATCH`: H8 proves raw transform convergence to
Xi, while the owner tracker applies an additional completion factor whose
compensating crosswalk is not supplied. H3c and H3e remain OPEN.

Revision 16 closes two further unconditional Lean cores without choosing an
exact family.  H1c1 encodes every apparent pole in the H8 Proposition-5.9
finite formula by a complex `dslope`, proves the finite removable RHS entire,
and recovers the printed quotient formula off the source lattice.  Independently,
H4d1b upgrades the natural-scale exponent lemma to any non-bottom cofinal
filter: an eventual squared WPrime envelope plus the strict Contract-v2 margin
forces detector decay.  H4d2 still must supply the exact identity, constants,
SAFE bounds, and joint filter.  Thus H1c, H1, H4d, H4, and RH remain OPEN.

Revision 17 closes H1c2 constructively.  The exact phase-centered log-window
integral equals the removable Proposition-5.9 RHS for every complex `z`, both
off the source lattice and at its finite `L*cos(pi*k)` values.  The same Lean
artifact separately proves that the finite positive-exponent centered
integral equals `Raw(-z)`, without assuming coefficient evenness or silently
flipping the Fourier sign; D0.6 is the separate source lock identifying that
representative with owner `Fplus`.  H1c3 still needs D0.8 and the owner
master-family choice; therefore H1c and H1 stay OPEN and no new independent
worker leaf is currently eligible.

Revision 20 separates the universal H2a parity algebra from the exact Route B
spectral ordering.  Lean proves that a commuting involution splits every
eigenvector into even and odd eigenvectors, that a one-dimensional eigenspace
has parity `+1` or `-1`, and that an even-sector simple bottom strictly below
the odd sector is the simple even global ground.  The executable model
`A=diag(1,0)`, `J=diag(1,-1)` retains the mandatory guard: a simple ground can
be odd.  Exact H2a2 therefore still needs, on the selected H1c3/D0.8 family,
`epsilonPlus1<epsilonPlus2` (or its explicit dimension-one replacement) and
`epsilonPlus1<epsilonMinus1`.  H8 assumes rather than proves these inputs, so
H2a, H2, and RH remain OPEN.

Revision 21 separates the generic compact-open topology below H3b from the
exact weighted Route B estimate.  Lean proves that a compact-uniform envelope
`C_i||e_i|| -> 0` forces uniform convergence on that compact, and that such an
envelope on every compact subset of an open locally compact domain forces
locally uniform convergence.  A constant-one singleton family proves that a
fixed bound without decay is insufficient.  Exact H3b2 still needs the
same-family estimate and rate, schematically
`sqrt(L_i) lambda_i^a ||ground_i-trial_i|| -> 0`, or a source-locked weighted
cancellation replacement, on the selected joint filter.  D0.6 alone is only
fixed-window boundedness, so H3b, H3, and RH remain OPEN.

Revision 22 separates the universal H4a1 residual algebra from the exact
Route B operator realization.  Lean proves
`ambient = compressed + leakage`; under the compressed Ritz equation, the
ambient residual and leakage have the same norm.  The executable coordinate
model has an idempotent projection and a zero compressed residual but nonzero
ambient residual `(0,1)`, so the internal-residual tautology is killed.  Exact
H4a1b still must pin the domain-safe operator, projection, trial/Ritz object,
form-to-operator crosswalk, and leakage norm/rate.  Therefore H4a1, H4a, H4,
and RH remain OPEN.

Revision 23 separates the universal H4d2 square-envelope arithmetic from its
exact Route B instantiation.  Lean proves, pointwise and eventually on one
non-bottom filter, that same-envelope alpha/gap bounds, a b upper bound, and
an independently supplied identity
`W^2=|b|^2*scale*alpha/gap` imply the exact Contract-v2 squared polynomial
envelope.  The theorem does not define WPrime.  Exact H4d2b still needs the
non-tautological D0.7e.5c consumer identity, common-envelope SAFE bounds,
fixed constants and signs, `q_b`, a strict exponent margin, eventual WPrime
nonnegativity, cofinal scale, nonzero locus, and one selected joint filter.
Therefore H4d2, H4d, H4, and RH remain OPEN.

Revision 24 turns the H3c double-completion suspicion into an exact Lean kill
certificate.  At the closure point `z=-i/2`, the central-normalized extra
completion of already completed `centeredXi` is zero while `centeredXi=1/2`.
Continuity and uniqueness of the within-strip limit prove that the two
functions cannot agree throughout the open strip, hence an interior mismatch
point exists.  This retires only `H3C_DOUBLE_COMPLETION_NOT_EXCLUDED`.
Exact H3c2 still must select the same Route B family and one joint filter, then
prove raw convergence or an exact inverse-completion crosswalk to `centeredXi`.
Thus `XI_LIMIT_OBJECT_MISMATCH`, `XI_LIMIT_IDENTIFICATION_MISSING`, H3c, H3,
L0c2, and RH remain OPEN.

Revision 25 separates H2b's universal determinant algebra from the exact H8
Theorem-5.10 crosswalk.  Lean proves that `1-exp(-iLz)` has only real zeros for
real nonzero `L`, that right factors inherit the real-zero property from an
exact product, and that a nonvanishing unit times a Hermitian characteristic
polynomial times a real-zero factor has only real zeros.  One-dimensional
plants prove Hermitianity and unit nonvanishing are essential.  Exact H2b2
still needs the `T`-induced quotient metric, Hermitian finite matrix, complement
determinant, nonvanishing phase, lattice-safe all-`z` factorization, and same
H1c3/D0.8/H2a raw family.  H2b therefore deliberately remains CONDITIONAL;
H2 and RH remain OPEN.

Revision 26 extracts the legal consequences of Contract v2's normalized
two-sided b bound.  Lean proves pointwise and eventually on a non-bottom filter
that `0<c_b<=|b| scale^(-q_b)<=C_b` implies b is nonzero, the direct upper
bound `|b|<=C_b scale^q_b`, the scale-dependent reciprocal bound, and the
corresponding normalized-error inequality.  The existing sequence with
normalized product one but `b_n->0` remains a live guard against a uniform
lower-bound overclaim.  Exact H4c2 still must define canonical alpha and b,
prove alpha/true-gap signs, the full two-sided bound and q_b, and select the
same carrier/filter as H3e/H4d2.  H4c, H4, and RH remain OPEN.

Revision 27 separates universal complex-Hilbert phase geometry from the exact
Route B ground/trial approximation.  Lean defines a total canonical phase,
proves the exact unit-vector squared-distance identity, bounds phase-aligned
error by the square root of twice the projective defect, and transfers a
vanishing projective defect to phase-aligned norm convergence on a non-bottom
filter.  Exact H3a2 still must select the same normalized simple-even ground
and nonzero trial family and prove the projective-defect rate required by H3b.
The source identifies precisely that approximation as a main remaining
obstacle.  H3a, H3, L0c2, and RH remain OPEN.

Revision 28 separates the universal perturbation-budget arithmetic from the
missing exact SafeGapLower source.  Lean proves that absolute drift bounds for
both selected endpoints and a surviving model-gap budget imply the true-gap
floor, including strict positivity and a non-bottom-filter wrapper.  Two live
guards show that a positive model gap alone can coexist with a collapsed true
gap and that endpoint errors can consume the entire separation.  Exact H4b2
still must pin the parity-clean Route B operator/Fuchs model, order the true
same-parity endpoints, prove both drift bounds, and leave a positive
Contract-v2 Fuchs envelope.  H4b, H4, H3e, L0c2, and RH remain OPEN.

Revision 29 constructs the universal isolation receiver nested below H2a2.
Lean defines half the minimum of the next-even and bottom-odd gaps, proves it
positive from the two strict inequalities, bounds it by both gaps, and shows
that it separates every level above either sector threshold.  The primary
paper still assumes the simple-even hypothesis and explicitly lists its proof
as missing.  Exact H2a2b must therefore select the H1c3/D0.8 family, prove both
strict sector inequalities with ordering/multiplicity crosswalks, and
instantiate the radius.  H2a2, H2a, H2, and RH remain OPEN.

Revision 30 constructs the universal residual-envelope receiver nested below
H4a2.  Lean transfers the exact H4a1 ambient/compressed/leakage identity to
norm, squared, compressed-Ritz/leakage, and non-bottom-filter bounds.  The live
H4a1 plant still shows that zero compressed residual does not imply zero
ambient residual when leakage survives.  Exact H4a2b must now pin one
domain-safe Route B operator and source-locked projection and prove both the
compressed-residual and leakage rates on the same family/filter, including the
squared rate consumed by H4a3.  H4a2, H4a, H4, and RH remain OPEN.

Revision 31 constructs the universal normalized-tracking receiver nested below
H3e.  Lean proves the exact scalar normalization identity and transfers an
absolute compact-set tracking estimate to `TendstoUniformlyOn` from reciprocal
control and two explicit relative rates, with an H4c1 specialization on a
non-bottom filter.  Compiled plants show both that detector decay can be erased
by division by `b` and that the current Contract-v2 safe margin alone need not
imply the stronger normalized relative-rate margin.  Exact H3e2 must still
supply the independent WPrime consumer, exact family/Xi/b objects, absolute
tracking theorem, both relative rates, and one joint filter.  H3e, H3, L0c2,
and RH remain OPEN.

Revision 32 composes the two generic H3 frontiers below H3b2.  H3a1 bounds the
phase-aligned vector error by the square-root projective defect; after
multiplication by a nonnegative compact evaluation envelope and a squeeze,
H3b1 turns the weighted rate into `TendstoUniformlyOn` of the evaluation error
on a supplied set and non-bottom filter.  Exact H3b2b still needs the selected
simple-even ground/trial family, exact evaluation map/envelope, weighted rate,
and the shared joint filter.  H3b2, H3b, H3, and RH remain OPEN.

Revision 33 closes the universal SafeAlphaUpper rate arithmetic below H4a3b.
The local Temple half-gap theorem, a residual-square bound carrying two common
envelope factors, and a true-gap floor carrying one factor yield
`C_alpha=2*C_eta/c_Delta` and `r_alpha=r_eta-r_Delta`, pointwise and on a
non-bottom filter.  A fixed Lean counterexample proves that only one residual
envelope factor is insufficient.  Exact H4a3b2 still needs the canonical
spectral/residual/gap objects and rates on one family/filter.  H4a3b, H4a3,
H4a, H4, and RH remain OPEN.

Revision 34 isolates the universal algebraic portion of H8 Lemma 5.4 below
H2b2.  Lean proves that the normalized rank-one correction kills the source
vector and that the source commutator plus `T(D xi)=-beta` makes it symmetric
for the `T`-weighted bilinear form.  This does not establish positivity,
radical, quotient descent, complex-Hermitian self-adjointness, complement
determinants, the nonvanishing phase, or the exact all-z identity.  Those stay
OPEN in H2b2b under `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`; H2b remains
CONDITIONAL and H2/RH remain OPEN.

Revision 35 isolates the universal spectral-weight arithmetic below H3a2.
Lean proves that nonnegative weights summing to one, a zero ground level and a
complementary spectral gap imply `gap*(1-weight_ground) <= alpha`, and derives
the quotient bound when the gap is positive.  Exact H3a2b must still construct
the same Route B spectral weights, identify the ground weight with squared
overlap, prove the positive gap and weighted cofinal rate, and select the joint
filter.  H3a2, H3a, H3, L0 and RH remain OPEN.

Revision 36 closes the last independent generic H3 limit-composition core.
Lean proves, on arbitrary filters, that uniform convergence of `F-G` to zero
and of `G` to `X` implies uniform convergence of `F` to `X`, and proves the
locally-uniform open-domain version through compact subsets.  Exact H3c2b must
still select the raw or inverse-completed family, prove the exact difference
identity and reference convergence to centeredXi, establish the finite/
continuum crosswalk, and choose one joint filter.  H3c2, H3c, H3, L0 and RH
remain OPEN.

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
