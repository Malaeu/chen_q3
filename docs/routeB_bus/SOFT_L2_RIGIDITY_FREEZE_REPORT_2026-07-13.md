# SOFT_L2_RigidityFreeze — goal report

Status: `CLOSED / SOFT_L2_SOURCE_INJECTIVITY_LOCKED / SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED / SOFT_L2_O2_INTERTWINER_LOCKED / EVEN_FROM_SIMPLE_GROUND / ALL_PLANTS_LIVE / NOT_RH`

## Result

1. `SOFT_L2_EvenRealFullAutocorrelationRigidity` is typed over an injective
   additive transform into a commutative no-zero-divisor domain.  Lean proves
   equality up to sign by difference of squares and proves that two positive
   anchors select equality.
2. `SOFT_L2_AutocorrelationSquareRootReconstruction` is frozen with the exact
   Round-12 fields: certified even complex multiplicities, `ord_0(H) in 4N`,
   `H>=0` on the real axis, `H|R in L1`, and `type(H)<=2R`.  Its semantic input
   type is an even autocorrelation transform; this necessary invariant is not
   inferred from the scalar conditions.  The input/output types compile in
   Lean and the global analytic proof is recorded in the theorem file; the
   analytic existence theorem is not falsely reported as kernel-formalized.
3. The centered O2 lines are source-locked as

   ```text
   kappaHat_m Gamma_m = J kappaHat_m;
   T(Jq)=(Tq)^sharp_Z,  F^sharp_Z(z)=conj(F(conj z)).
   ```

   D0.6's uncentered `kappa_D06` has the opposite direction, so its literal
   line is first `Gamma_m kappa_D06=kappa_D06 R_L`; re-centering produces the
   requested typed identity.
4. Provenance verdict is `EVEN_FROM_SIMPLE_GROUND`, not
   `EVEN_BY_CONSTRUCTION`: D0.5 leaves `GroundSpace subset Eplus` and the
   canonical selector open; D0.4 states `NO_SIMPLE_EVEN_GROUND`.  Existing
   Lean proves that a commuting simple ground can be odd, so an independent
   even-sector winner/selector remains necessary.

## Plant replay

```text
PL1_EVEN_REAL_RECONSTRUCTION_PASS
  relative error 5.353301558149146e-16

PL2_NON_EVEN_TWINS_AMBIGUITY_DETECTED
  common autocorrelation [6,35,62,35,6]

PL3_COMPLEX_EVEN_SHARP_SQUARE_MISMATCH_DETECTED
  |FFsharp-F^2|=21.42703254155939 at x=0.37

PL4_POSITIVE_ANCHOR_SELECTS_GLOBAL_SIGN
  anchors +/-2.152127051220663

P5_PROSHKA_RECONSTRUCTOR_REFUSED
  missing certificate: EVEN_ZERO_CERTIFICATE_MISSING_OR_FALSE
  forged certificate: ODD_ZERO_MULTIPLICITY_DETECTED at +/-i
```

## Lean validation

```text
lake env lean Q3/Proofs/RouteB/EvenRealAutocorrelationRigidity.lean       PASS
lake env lean Q3/Proofs/RouteB/AutocorrelationSquareRootReconstruction.lean PASS
holes: 0
```

The main rigidity theorems use only standard Lean/Mathlib axioms printed by
the kernel (`propext`, `Quot.sound`, and `Classical.choice` for the anchored
wrapper).  No project RH axiom is imported.

## Artifacts

```text
Q3/Proofs/RouteB/EvenRealAutocorrelationRigidity.lean
  af3881dd0be7df726b9bc19975f833d410aeddb2b9740e7d9c0dffd72b67b077

Q3/Proofs/RouteB/AutocorrelationSquareRootReconstruction.lean
  c1e55f9fc0e1a0a0003b8e0cc6f6026fb7f2f85504227bb3190bfe3614e4db10

SOFT_L2_RIGIDITY_FREEZE_THEOREM_2026-07-13.md
  7998c3f4a3fe1a214d66d555cd7a416ab7c62ac3ed86bc3ef43a5c4f2ce7e6fb

SOFT_L2_RIGIDITY_FREEZE_PLANTS.json
  97538967ebed6375a3c47e743db7e7413eb76fb2dbef0edd191e8df01e2cee46

soft_l2_rigidity_freeze_plants.py
  21dd317f3055ef8924556c1983ba2998a72b9e7074705b2ce0788a25806f846a

validate_soft_l2_rigidity_freeze.py
  050f17c2c8372ea42822f4725b01981934b6ef2f1e61307df93b0443f36bcd71
```

Final:

```text
SOFT_L2_SOURCE_INJECTIVITY_LOCKED
SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED
SOFT_L2_O2_INTERTWINER_LOCKED
EVEN_FROM_SIMPLE_GROUND
ALL_PLANTS_LIVE
NOT_RH
BUS_010_CREATED=false
```
