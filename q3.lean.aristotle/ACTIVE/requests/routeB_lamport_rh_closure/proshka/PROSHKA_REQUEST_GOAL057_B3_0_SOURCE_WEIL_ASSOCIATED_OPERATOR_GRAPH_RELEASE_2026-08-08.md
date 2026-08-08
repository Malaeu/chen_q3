# PROSHKA REQUEST — GOAL 057 B3.0 SOURCE WEIL ASSOCIATED OPERATOR GRAPH RELEASE

```yaml
MODE: DELEGATED_STRATEGIC_REVIEW
TRANSACTION: GOAL057_B3_0_SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH_RELEASE
CONVERSATION_ID: 6a72e750-dc60-83eb-946b-61d2073c232b
PHASE_KEY: UNCHANGED
HEAD: 626bd62b2bc590e1d7de43fb1a25747f35e4cdea
ORIGIN_RH_CLEAN: 626bd62b2bc590e1d7de43fb1a25747f35e4cdea
PARENT_PRIMARY: TRY_GOAL057_B3_SELECTED_KTRIAL_OPERATOR_DOMAIN_FROM_PIECEWISE_SMOOTH_CORE
PARENT_VERDICT_SHA256: 5071da78f2a521f002487178547e2a005c4e44587a7521f4dca0f003033da10a
REQUESTED_CHILD: GOAL057_B3_0_SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH
OWNER_GATE: PX_RH_CLAIM_ONLY
```

## Why this release is separate

The parent review was design-only and explicitly set:

```yaml
EXECUTION_AUTHORIZED_INSIDE_THIS_REVIEW: false
NEXT_RELEASE_TRANSACTION:
  id: GOAL057_B3_0_SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH
  execution_requires_later_explicit_operational_release: true
```

No Lean file was edited after that ruling. The complete source audit and its
verdict are now committed and pushed at `626bd62b`.

Release exactly one smallest production child or return one fail-closed stop.
Do not reopen B2 and do not authorize the later compression file yet.

## Parent-selected route

The selected mathematical chain is:

```text
exact source form
  -> source-specific Fourier multiplier graph
  -> weighted L2 certificate for every finite mode
  -> selected kTrial operator-domain membership
  -> projected action = finite Riesz action
```

This request covers only the first two arrows through the generic mode theorem
`V_n_m_mem_sourceWeilOperatorDomain`.

## Current production facts

Parent B2 is closed and retained:

- `D0PstarCCMFiniteRieszOperator.lean` is hole-free;
- file SHA-256 is
  `bf72d6f84c33f6ddd0f6e0c76563c8d6cf4416124f1b8c8e8dc988dc4ad58e59`;
- it proves only `FINITE_RIESZ_CARRIER_BIND_ONLY`;
- it does not define the source form, `Dom(A_m)`, an ambient operator, or an
  operator compression identity.

Current Lean has no production declaration for `qW_m`, `BW_m`,
`SourceWeilFormDomain`, `SourceWeilAssociatedGraph`, `SourceWeilOperatorDomain`,
or an unbounded `sourceWeilAssociatedOperator`.

The literal ambient carrier is:

```lean
H_m i = Lp ℂ 2 (dStar.restrict (I_m i))
```

and the literal finite mode is `V_n_m i n : H_m i`.

## Source lock

Read these exact repository sources before releasing code:

1. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/D0_2_EXACT_WEIL_SESQUILINEAR_FORM.md`
   - source form, signs, Fourier convention, prime and pole terms;
   - proves only the form-domain statement recorded there.
2. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/D0_3_EXACT_OPERATOR_TYPE_REGISTRY.md`
   - explicitly records that form-domain membership is not operator-domain
     membership and finite form coordinates are not operator compression.
3. `literature/zotero/H8ULBMAL/fulltext.md`
   - Proposition 3.3: lower-bounded lower-semicontinuous form;
   - Proposition 3.4: modes span is a form core;
   - Section 3.2: associated unbounded self-adjoint operator;
   - Theorem 3.6: bounded prime/pole pieces plus the archimedean multiplier;
   - the piecewise-smooth passage itself states only form-domain membership.
4. `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFiniteProjection.lean`
   and its imports for exact `H_m`, `V_n_m`, `E_m_N`, and `P_m_N` types.
5. `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean`
   only as a naming and carrier precedent. Its discrete log-window coefficient
   energy is not the source archimedean Fourier multiplier graph.

The primary source supports the route only as
`DERIVED_FROM_PRIMARY_SOURCE_PLUS_STANDARD_ANALYSIS`. The production proof
must exhibit the weighted Fourier certificate; source prose is not an axiom.

## Exact child boundary

Owned file, if released:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarWeilAssociatedOperatorGraph.lean
```

Maximum public surface for this child:

```yaml
definitions:
  - SourceWeilFormDomain
  - SourceWeilAssociatedGraph
  - SourceWeilOperatorDomain
  - sourceWeilAssociatedOperator
theorems:
  - sourceWeilAssociatedOperator_graph
  - V_n_m_mem_sourceWeilOperatorDomain
total_public_declarations: 6
```

Everything else must be private: zero-extension representative, exact Fourier
formula, arch-symbol normalization/growth, weighted-L2 lemmas, bounded
prime/pole constructors, and local graph extensionality.

The associated operator must be domain-subtype valued, not
`Module.End ℂ (H_m i)`.

The decisive theorem must prove, for the literal mode and exact source
conventions:

```text
V_n_m i n ∈ SourceWeilOperatorDomain i
```

by supplying all of:

- exact zero-extended representative of `V_n_m`;
- exact source-normalized Fourier formula;
- an explicit `O(1 / (1 + |t|))` bound;
- exact source arch-symbol growth;
- `(archSymbol * Fourier(V_n_m)) ∈ L2`;
- bounded prime and pole actions;
- no inference from `SourceWeilFormDomain` alone.

## What the release must decide

Return exactly one operative primary:

```yaml
A: TRY_GOAL057_B3_0_SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH
B: KILL_GOAL057_B3_0_EXACT_FOURIER_NORMALIZATION_OR_CARRIER_MISMATCH
C: WALL_GOAL057_B3_0_SOURCE_FORM_REPRESENTATION_API_MISSING
```

If A, provide:

1. exact sole import or minimal import list;
2. exact namespace;
3. exact Lean types/signatures of all six public declarations;
4. the private-helper dependency order;
5. the exact Fourier transform and zero-extension representation used;
6. the exact theorem proving the logarithmic weighted-L2 certificate;
7. how bounded prime and pole parts enter without changing the domain;
8. the precise proof of `sourceWeilAssociatedOperator_graph`;
9. K6 object precommit;
10. all mandatory plants with mutation and required stop code;
11. validation commands and allowed axiom set;
12. STOP, SUCCESS, next gap, and ledger effect;
13. whether Aristotle is forbidden, optional, or required;
14. whether the six-field phase key changes.

If B or C, name the exact first unavailable equality/API and the smallest
replacement transaction. Do not return a vague research program.

## Mandatory plants

At minimum preserve and specialize:

```yaml
- P057_B3_1_FORM_DOMAIN_NOT_OPERATOR_DOMAIN
- P057_B3_2_ASSOCIATED_OPERATOR_BOUNDEDNESS_ERASURE
- P057_B3_5_BOUNDED_LIFT_SURROGATE_REJECTED
```

Add convention-lock plants for:

- Fourier normalization and sign;
- zero-extension/window carrier;
- `dStar.restrict (I_m i)` versus the source Fourier-side measure;
- logarithmic symbol weight versus the unrelated discrete
  `physicalFourierWeight`;
- prime/pole bounded-part signs.

The direct P057-B3-1 counterexample remains load-bearing: finite form energy
does not imply multiplier-graph energy.

## Hard boundaries

```yaml
FORBIDDEN:
  - edit Lean inside this review
  - infer operator domain from form domain or form core
  - define A_m as Module.End over H_m
  - introduce a bounded finite-rank surrogate
  - accept the desired graph/compression identity as a public premise
  - use discrete physicalFourierEnergy as the source arch multiplier graph
  - claim E_m_N invariance
  - edit the later D0PstarCCMCompressedWeilAction.lean child
  - call the finite residual the continuum numerator
  - close H4a1b
  - decrement the ten-checkpoint ledger
  - create Bus_010
  - release Goal_055
  - promote Route_B
  - make PX or RH claim
  - open a fresh chat
```

Final boundary remains:

```yaml
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
Aristotle_submission: NONE unless this review explicitly releases it
route_promotion: false
px_rh_claim: NOT_MADE
```
