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
- rev16 also proves the non-bottom cofinal square-envelope rate package
  `H4d1b/H4d1c`; exact H4d2 still lacks the WPrime square envelope, constants,
  SafeAlphaUpper, SafeGapLower, SafeSignAndB, and a selected joint filter;
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
