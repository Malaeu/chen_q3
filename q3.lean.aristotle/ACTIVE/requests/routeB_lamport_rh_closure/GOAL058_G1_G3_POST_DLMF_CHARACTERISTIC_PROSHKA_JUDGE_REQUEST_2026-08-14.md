# Goal 058 G1/G3 post-DLMF-characteristic request to Proshka

Date: 2026-08-14

```text
[->PROSHKA]
PHASE: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
REPO: https://github.com/Malaeu/chen_q3
BRANCH: rh_clean
SOURCE_BASE: 525d96dde4d08857e7c26ca2ab1953c4d65505c9
ROUTE: CHALLENGER_NOT_RH
G1: OPEN
G3: OPEN
PX_RH_CLAIM: NOT_MADE
```

This is a narrow evidence-delta adjudication in the existing living Goal 058
phase.  Do not repeat the general G1/G3 audit.  Mythos was asked twice in the
same living phase, completed reasoning twice, but emitted no final answer.
The transport incident is archived separately and supplies no mathematical
verdict.

## Read first

1. `q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenRightBranchCrosswalk.lean`
2. `q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenCharacteristicSource.lean`
3. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DLMF3035_CHARACTERISTIC_OBJECT_CLOSEOUT_2026-08-14.md`
4. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G1_G3_POST_DLMF_CHARACTERISTIC_MYTHOS_REQUEST_2026-08-14.md`
5. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G1_G3_POST_DLMF_CHARACTERISTIC_MYTHOS_TRANSPORT_INCIDENT_2026-08-14.md`
6. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G1_G3_CURRENT_PROBLEM_IO_LEDGER_2026-08-14.md`
7. `docs/Codex/TASK_2026-08-14_goal058_g3_prolate_rate_floor.md`

The two new Lean files have direct Lean, named target build, `q3_check`, full
build, and standard-only public axiom audits.  They establish, without
defining the source objects through the project residual:

- literal DLMF 30.3.7 even coefficients;
- the infinite right continued fraction and its equality to the existing
  `mode4RightTailLimit`;
- an independent finite-left recurrence;
- a pole-safe even DLMF 30.3.5 characteristic predicate;
- at split `2*(K-1)`, equivalence of that predicate with
  `mode4RootFunction = 0` in the production domain.

This is a characteristic-object adapter.  It is not the missing spectrum or
mode-selection theorem.

## Q1 — G3 route decision after the new adapter

Adjudicate the smallest noncircular next producer.  Choose exactly one:

1. `DIFFERENTIAL_SPECTRUM`: materialize an independent ordered even singular
   Sturm--Liouville carrier, prove DLMF 30.3.5 gives exactly its solution set,
   then prove the DLMF 30.16.3 same-index finite-limit theorem to the current
   internal carrier;
2. `JACOBI_INERTIA`: prove a general/source-addressed infinite Jacobi or
   continued-fraction spectral theorem which directly identifies zeros of
   the new independent characteristic predicate with the current `iInf`
   finite-limit carrier, without defining either side through the other;
3. `MISSED_SUPPLIER`: name an existing source theorem or repository
   capability which already closes the same seam.

The current target name is only a specification, not a declaration:

```lean
mode4DLMF30163_3035_evenCharacteristicSolutions
```

Return the exact first theorem head and every required carrier definition.
For each logical seam provide one anti-circularity plant.  In particular,
reject any construction that:

- defines the source spectrum as the desired project roots;
- defines the characteristic predicate through `mode4RootFunction`;
- takes endpoint counts `2/3`, a desired root, a desired coefficient row, or
  same-index convergence as arbitrary binders;
- silently upgrades finite nonsingular count stability into the classical
  source spectrum.

State whether the count-jump/inertia route actually shortens the source wall,
or merely repackages the missing spectrum identification.

## Q2 — G1 first quantitative producer

The correct odd-contamination receiver already exists:

```lean
sourceCCMComplexOddMass_le_norm_sub_sq_of_inversion_even
```

The exact inversion-even limiting comparison exists as
`E_star_explicitCCMLimitH_inv`.  Exact reflection-evenness of the finite source
row is not a sound target.  The first absent prolate producer remains actual
degree-0/4 mode existence and selection over the unchanged production
`ProlatePair`:

```lean
forall i : PairIndex, IsActualProlateModePair (S.source.pair i)
```

After that, the source-locked CCM Lemma 7.2 rate is still missing.  The
even-head complement floor and its cofinal fixed-shift connector are separate
missing arithmetic facts.

Decide the next honest G1 producer among:

1. actual degree-0/4 prolate mode existence and selection;
2. CCM Lemma 7.2 on an already source-locked actual pair;
3. an independent even-head arithmetic/coercivity theorem;
4. a missed supplier.

Return the exact theorem head, inputs, outputs, primary-source pins, and
dependency arrows.  A new receiver or an arbitrary rate/floor binder is a
rejection.

## Aristotle boundary

Say `READY` only if there is now a bounded theorem whose source meaning is
fully policed by its statement and existing imports.  If ready, provide the
exact Lean theorem statement, allowed imports, forbidden assumptions, and
success/failure codes.  Otherwise return `NOT_READY` with the typed missing
source theorem.

## Required final verdict

Write the response for archival at:

```text
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_G1_G3_POST_DLMF_CHARACTERISTIC_PROSHKA_VERDICT_2026-08-14.md
```

Return exactly:

1. `G3_ROUTE_DECISION`;
2. `G3_EXACT_NEXT_HEAD` or `NOT_READY`;
3. `G3_ANTICIRCULARITY_PLANTS`;
4. `G1_ROUTE_DECISION`;
5. `G1_EXACT_NEXT_HEAD` or `NOT_READY`;
6. `DEPENDENCY_DAG`;
7. `ARISTOTLE_BOUNDARY`;
8. `G1_STATUS`, `G3_STATUS`, and one typed `STOP_CODE` per open front.

Do not claim G1, G3, Route B promotion, or RH unless the exact missing
producers are proved in the pinned tree.
