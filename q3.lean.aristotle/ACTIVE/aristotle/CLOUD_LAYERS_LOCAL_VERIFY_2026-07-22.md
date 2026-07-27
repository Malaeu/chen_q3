# Recovered Aristotle cloud layers — local verification 2026-07-22

Status: `LOCAL_LEAN_4_28_BUILD_PASS / THREE_CLOUD_LAYERS_HOLE_FREE /
PROJECT_APPROX_TYPED / MAIN_17_HOLES_PRESERVED / NOT_RH`

## Environment

- Recovered project: `16535289-f016-4f62-bfbd-be83d826b4da`.
- Toolchain: `leanprover/lean4:v4.28.0`.
- Mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- The first source build exhausted local disk space while compiling all of
  `import Mathlib`.  Only its generated dependency build directory was
  removed; `lake exe cache get` then installed the official Mathlib binary
  cache and the complete target build passed.

## Build command

```text
lake build RequestProject.Main RequestProject.H2aPenalty \
  RequestProject.H2aBridge RequestProject.AbstractCoboundaryLedger \
  RequestProject.ProjectApprox
```

Result: `Build completed successfully (8030 jobs)`.

## Hole audit

```text
RequestProject/Main.lean                       17 code sorries (expected)
RequestProject/H2aPenalty.lean                 CLEAN
RequestProject/H2aBridge.lean                  CLEAN
RequestProject/AbstractCoboundaryLedger.lean   CLEAN
RequestProject/ProjectApprox.lean              CLEAN
```

The clean files contain no `sorry`, `admit`, `exact?`, declaration-level
`axiom`, `native_decide`, or `implemented_by`.  Main contains none of the
other forbidden tokens; its 17 holes remain split by POISON_GUARD rev 3 into
seven false statements and ten honest conditionals.

## Axiom audit

The following representative theorems all print exactly
`[propext, Classical.choice, Quot.sound]`:

- `H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity`;
- `RHRoute.ground_simple_isolated_even_of_spectralData`;
- `RHRoute.hfam_even_of_spectralData`;
- `RHRoute.wrong_parity_blocks_evenness`;
- `ACL.T1_coboundary_no_locality` and `ACL.T2_residual`;
- `ACL.PL1_locality_load_bearing`, `ACL.PL2_order_swap`,
  `ACL.PL3_parity_revival`;
- `RHRoute.ProjectApprox.supply_H2a_Pstar_of_penaltyPilot`.

## Interpretation

The three recovered proof layers are locally kernel-checked.  `ProjectApprox`
now freezes one D0-derived family shape, an exact conditional penalty-pilot
receiver, `(beta_j,tau_j)` accessors, and `AnchorValueProbeRecord`.  The
remaining H1/ANCHOR/S1/S2 leaves are fields of the statements-only
`PstarSupplyContract`; the file does not repeat the false universal supply
theorems.

This verifies the recovered components only.  It does not instantiate the
exact D0 family, construct the penalty certificates, supply
`H2bTransformLayer`, discharge S1/S2, or prove RH.
