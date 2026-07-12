# H3a2 weighted Rayleigh/projective-defect transfer

Date: 2026-07-12
Transaction: Route B revision 35
Status: `GENERIC CORE PROVED / EXACT INSTANTIATION OPEN / NOT_RH`

## Scope

This transaction extracts the universal finite spectral-weight inequality from
H3a2.  For nonnegative weights summing to one, a distinguished ground level
zero, and every other level at least `gap`, the Rayleigh excess controls the
weight outside the ground state:

```text
gap * (1 - weight ground) <= alpha.
```

When `gap > 0`, division gives
`1 - weight ground <= alpha / gap`.

## Lean result

`Q3/Proofs/RouteB/WeightedRayleighProjectiveDefect.lean` proves:

- `weighted_projective_defect_mul_gap_le_rayleigh_excess`;
- `weighted_projective_defect_le_rayleigh_excess_div_gap`.

Direct `lake env lean` validation is hole-free.  The printed axiom set is only
`propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

The generic theorem does not supply the Route B spectral weights, identify the
selected simple-even ground, prove trial nonvanishing, establish the exact
Rayleigh expansion, produce a positive eigengap, or prove the same-family
cofinal rate and joint filter.  Those inputs remain in H3a2b under
`H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING`.

## DAG transaction

```text
H3a2  ExactGroundTrialProjectiveRate               OPEN
|-- H3a2.0 DecompositionContract                   PROVED
|-- H3a2a GenericWeightedRayleighProjectiveCore    PROVED / LEAN
|-- H3a2b ExactSameFamilyRayleighRate              OPEN / INELIGIBLE
`-- H3a2c ExactProjectiveRateAssembly              OPEN / INELIGIBLE
```

H3a, H3 and L0 remain OPEN.  D0.7e.5a remains the unique active leaf, Bus 010
is absent, and Route B remains `CHALLENGER / NOT_RH`.

## Verdict

`H3A2_GENERIC_WEIGHTED_RAYLEIGH_PROJECTIVE_DEFECT_LEAN`
