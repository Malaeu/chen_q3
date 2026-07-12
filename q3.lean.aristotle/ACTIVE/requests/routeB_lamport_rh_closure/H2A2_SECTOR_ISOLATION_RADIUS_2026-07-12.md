# Route B H2a2 sector-isolation radius — revision 29

Status: `H2A2A_PROVED / EXACT_SELECTED_FAMILY_SECTOR_ORDERING_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves only the universal isolation-radius construction that
consumes two strict sector gaps.  It does not select the Route B family, prove
either strict eigenvalue inequality, prove that the global ground is even,
close H2a2/H2a/H2, create Bus 010, or prove RH.

## 1. Three ordered inputs

For one already selected finite self-adjoint parity decomposition, write

```text
epsilonPlus1   = selected even ground level,
epsilonPlus2   = next even level,
epsilonMinus1  = bottom odd level.
```

The source-level exact obligation is to prove

```text
epsilonPlus1 < epsilonPlus2,
epsilonPlus1 < epsilonMinus1.
```

Revision 29 does not prove those inequalities.  It proves what follows from
them once they are supplied on the exact same family.

## 2. Constructive isolation radius

Define

```text
sectorIsolationRadius
  = min(epsilonPlus2-epsilonPlus1,
        epsilonMinus1-epsilonPlus1) / 2.
```

Under the two strict gaps, Lean proves

```text
0 < sectorIsolationRadius.
```

It also proves that the radius is bounded by each full sector gap.  Therefore,
for any level `mu` satisfying either

```text
epsilonPlus2 <= mu
```

or

```text
epsilonMinus1 <= mu,
```

the radius obeys

```text
sectorIsolationRadius <= mu-epsilonPlus1.
```

The bundled theorem is

```text
sectorIsolationRadius_certificate.
```

Verdict:

```text
GENERIC_SECTOR_ISOLATION_RADIUS_LEAN.
```

## 3. Primary-source boundary

`Zeta Spectral Triples`, Definition 5.3 and Theorem 5.10, use an even-simple
smallest eigenvalue.  Section 8 explicitly states that proving simplicity and
evenness for the exact Weil-form family is still missing.  Hence the paper is
an authority for the obligation, not a proof of its two strict gaps.

D0.4 pins the plus/minus sector types and D0.5 pins the set-valued ground/trial
types.  Neither selects the winner or proves the internal even gap.

## 4. Exact H2a2 obligation left open

H2a2b must still provide:

1. the exact H1c3/D0.8 finite operator family and one common index/filter;
2. ordered even levels `epsilonPlus1 < epsilonPlus2`;
3. the cross-sector inequality `epsilonPlus1 < epsilonMinus1`;
4. multiplicity and enumeration crosswalks showing these are the first two
   even and first odd levels of that operator;
5. the instantiation of `sectorIsolationRadius_certificate` on those exact
   levels;
6. a Lean export from the radius to the exact isolated simple-even ground
   statement consumed by H2a1 and downstream H4 nodes.

The exact stop remains

```text
H2A_EXACT_SECTOR_ORDERING_MISSING.
```

`H2A_ISOLATION_RADIUS_MISSING` is retired only at the generic receiver level;
the exact radius instantiation stays inside H2a2b.

## 5. Honest nested DAG split

```text
H2a SimpleEvenGround                                  OPEN / AND
|-- H2a1 GenericSimpleEvenGroundSectorCriterion       PROVED
|-- H2a2 ExactSelectedFamilySectorOrdering            OPEN / AND
|   |-- H2a2.0 H2a2DecompositionContract             PROVED
|   |-- H2a2a GenericSectorIsolationRadius            PROVED / LEAN
|   |-- H2a2b ExactSectorOrderingAndRadiusInstantiation OPEN / INELIGIBLE
|   `-- H2a2c H2a2Assembly                            OPEN / INELIGIBLE
`-- H2a3 H2aAssembly                                  OPEN / INELIGIBLE
```

The generic radius cannot discharge the exact family-selection or ordering
dependencies of H2a2.

## 6. Mathlib source boundary

Official order/min API:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/MinMax.html

The API supplies the elementary minimum inequalities used after the two gaps
are assumed.  It supplies no spectral theorem for the Route B operator.

Primary paper:

- https://arxiv.org/abs/2511.22755

## 7. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/SectorIsolationRadius.lean
```

It compiles without `sorry`, `admit`, or `exact?`; every printed axiom set is
within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_ROUTE_B_FAMILY_SELECTION
NO_EVEN_INTERNAL_GAP_PROOF
NO_EVEN_ODD_BOTTOM_ORDER_PROOF
NO_EXACT_ISOLATION_RADIUS_INSTANTIATION
NO_SIMPLE_EVEN_GROUND_CLOSURE
NO_H2A2_PARENT_CLOSURE
NO_H2A_PARENT_CLOSURE
NO_H2_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
