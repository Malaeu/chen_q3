# 008 — anchor ratio receiver

Date: `2026-07-27`

```text
ANCHOR_RATIO_RECEIVER_PROVED
```

Implemented theorem:

```lean
Q3.RouteB.D0Pstar.D0AnchorFloorFromUnprojectedMassNormRatio
```

The positive central mass implies `‖gTrial_m‖ > 0`.  The proof instantiates
`D0AnchorFloorFromUnprojectedCentralMass` with

```text
a = δ * ‖gTrial_m‖
C = ‖gTrial_m‖
hbound = le_rfl
hmass = hratio
```

and cancels the positive source norm:

```text
(δ * ‖gTrial_m‖) / ‖gTrial_m‖ = δ.
```

Validation:

```text
lake env lean Q3/Proofs/RouteB/D0AnchorFloor.lean: exit 0
#print axioms D0AnchorFloorFromUnprojectedMassNormRatio:
  [propext, Classical.choice, Quot.sound]
```

No numerical plateau, sign hypothesis, projection lower bound, new axiom, or
separate source constants occur in the final receiver.

Next paper front:

```text
EStarRelativeSourcePackage
```
