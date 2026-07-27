# 005 — centered Pstar and strip-local roof

Date: `2026-07-27`

Owner-sign:

```text
PROSHKA_VERDICT_S1_ANCHOR_2026-07-27.md
```

Verdict:

```text
CENTERED_PSTAR_STRIP_ROOF_LOCKED
```

## Centered family

`Q3.RouteB.D0Pstar.centeredPstarFamily` is the exact section-iii Lean
definition.  `canonicalApproximation.Pstar` now uses it.

The following declarations are hole-free:

```text
rawFplus_zero_ne
centeredPstarFamily_zero
differentiable_centeredPstarFamily
centeredPstarFamily_eq_zero_iff
canonicalApproximation_slotH1
canonicalApproximation_slotAnchor
```

The old `pstarFamily` is retained only as the killed uncentered no-go witness.

## Kill 7

`ClusterData` now contains:

```text
limitHolomorphicOn :
  DifferentiableOn ℂ limit centeredCriticalStrip

convergence :
  TendstoLocallyUniformlyOn selectedFamily limit atTop
    centeredCriticalStrip

limitNonzero :
  ∀ z ∈ centeredCriticalStrip, ¬ ∀ᶠ w in 𝓝 z, limit w = 0
```

The local nontriviality field is the exact hypothesis used by isolated-zero
theory; it prevents an identically-zero component without making a
whole-plane claim.

New local transfer:

```text
zerosApproachOn_of_tendstoLocallyUniformlyOn_local
```

New roof:

```text
rh_of_canonical_strip_slots
```

The compatibility theorem `rh_of_canonical_slots` is a direct wrapper around
the strip theorem and has no `Set.univ` convergence input.

## Validation

```text
lake env lean Q3/Proofs/RouteB/GenericZeroTransfer.lean: exit 0
lake env lean Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean: exit 0
lake env lean Q3/Proofs/RouteB/D0CanonicalApproximation.lean: exit 0
lake build Q3.Proofs.RouteB.D0CanonicalApproximation: exit 0
lake build Q3.Proofs.RouteB.D0CenteredCriticalMoment: exit 0
0 sorry / 0 admit / 0 new axiom in the modified Lean files
```

All printed axioms are the standard project triple:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

```text
S1 critical-moment ratio: OPEN
anchor floor: OPEN
H2a exact sector ordering: OPEN
project slot supply: OPEN
RH: NOT PROVED
Bus 010: NOT CREATED
```
