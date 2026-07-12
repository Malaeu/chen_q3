# H3c2 uniform difference/reference limit transfer

Date: 2026-07-12
Transaction: Route B revision 36
Status: `GENERIC CORE PROVED / EXACT INSTANTIATION OPEN / NOT_RH`

## Scope

H3c2 contains a universal additive limit step and an exact Route B object
identification.  This transaction proves only the universal step:

```text
(F_i - G_i) -> 0 uniformly on K
G_i -> X uniformly on K
--------------------------------
F_i -> X uniformly on K.
```

The same result is proved locally uniformly on an open set in a locally
compact domain by reducing to every compact subset.

## Lean result

`Q3/Proofs/RouteB/UniformDifferenceReferenceTransfer.lean` proves:

- `tendstoUniformlyOn_of_difference_and_reference`;
- `tendstoLocallyUniformlyOn_of_difference_and_reference`.

Direct `lake env lean` validation is hole-free.  The printed axiom set is only
`propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

The theorem does not choose between the raw and inverse-completion Route B
families, define the finite reference tracker, prove the difference estimate,
identify its continuum limit with `centeredXi`, select a cofinal joint `(m,N)`
filter, or establish the original-index full-tail statement.  The normalized
double-completion candidate remains excluded by H3c1.  All exact inputs stay
OPEN in H3c2b under `H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING`.

## DAG transaction

```text
H3c2  ExactRawOrInverseCompletionXiLimit           OPEN
|-- H3c2.0 DecompositionContract                   PROVED
|-- H3c2a GenericDifferenceReferenceTransfer      PROVED / LEAN
|-- H3c2b ExactFamilyLimitAndJointFilter           OPEN / INELIGIBLE
`-- H3c2c ExactXiLimitAssembly                     OPEN / INELIGIBLE
```

H3c, H3 and L0 remain OPEN.  D0.7e.5a remains the unique active leaf, Bus 010
is absent, and Route B remains `CHALLENGER / NOT_RH`.

## Verdict

`H3C2_GENERIC_DIFFERENCE_REFERENCE_LIMIT_TRANSFER_LEAN`
