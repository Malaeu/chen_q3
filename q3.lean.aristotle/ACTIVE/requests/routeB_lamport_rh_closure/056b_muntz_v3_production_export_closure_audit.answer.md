# GOAL 056 / Phase 2 — Müntz-v3 production export closure audit — answer

```yaml
GOAL: 056
PHASE: 2
NODE: MuntzV3ProductionExportClosureAudit
STATUS: CLOSED
RESULT: G6_S2_MUNTZ_V3_PRODUCTION_EXPORT_CLOSURE_AUDITED_PORT_OPEN

SCOPE: SOURCE_AND_DEPENDENCY_AUDIT
VERIFIER: IMPORT_GRAPH_PLUS_SOURCE_DIFF_PLUS_LEAN_4_28
ARSENAL_USED:
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## Exact result

The literal transitive closure of
`RequestProject.MuntzV3ProlateCombinationReceiver` contains exactly 17 local
modules.  Three are provenance exports of production modules already present
under `Q3.Proofs.RouteB`; their theorem/definition bodies are reusable.
The production port therefore needs 14 new modules, totalling 2282 source
lines, in dependency order.

This closes the inventory uncertainty.  It does not close Lean-4.26
portability and proves no new mathematics.

## Existing production suppliers

| Request-project module | Request SHA-256 | Production module | Production SHA-256 | Normalized comparison |
|---|---|---|---|---|
| `ProlateExport.ProlateLayer` | `f910db340cab06f71e04ba5efb44b5c50075fe60f9d24cf031ba91b89419a7af` | `Q3.Proofs.RouteB.ProlateLayer` | `3c2099c97df6cd0fb45f7b367d24898d11c031ed297fe9031b25ee5b9dc0edf4` | body identical; request file adds provenance header |
| `ProlateExport.ProlateModeRegularity` | `3dc9f09b49d4cfdff37cd6a44a917412e467ada3a5f38e1372d4dec8ab3e9415` | `Q3.Proofs.RouteB.ProlateModeRegularity` | `d09f80b47386afcddec890de959060e00961c57e19ca9db73a8bdcf507a06177` | import path only |
| `ProlateExport.ProlateCombinationMuntzRegularity` | `315326bb975988eb0563fc1d852c763d392c0ac40e6eb491d1397ecab234eac5` | `Q3.Proofs.RouteB.ProlateCombinationMuntzRegularity` | `d3990c1be7288b49f6d63dec42bbfa12e7799a955d80bee24c3ca9dcea9624c0` | body identical; provenance header and import path only |

The declaration inventories agree exactly: five definitions/structures in
`ProlateLayer`, one mode-regularity theorem, and six combination-regularity
theorems.

## New production export set

| Batch | Request-project module | Lines | Source SHA-256 |
|---:|---|---:|---|
| A | `Main` | 239 | `0b2e52db207610f0e63c3dac3e61c5d14f26d0119ccd11756cdbeeab80f3b888` |
| A | `R6Export.RiemannBoundaryCellBridge` | 344 | `b0c3a16db5627f4b3fbbc785ac7dc446d84a20975aa19b6296a4c25ccef65ce6` |
| B | `MellinCompactSupportAnalyticity` | 71 | `743e7cecf175a0be8c94d844c334ab66bfa5858696e6269a743b17ce0edfe148` |
| B | `MellinConvergentSqrtTail` | 46 | `dc91214ad1b7b09a37e0c90eae8891ddf8d1d743550d70380ad77cc6e31c9b04` |
| B | `MuntzV3EStarMellinAbsolutePayload` | 216 | `1f460d77a2404cbec83b739a188092e175cc73545fd8b31f5c493f62fafa6d89` |
| B | `MuntzV3EstarBoundExactClass` | 40 | `073497faa31264e8a769ccce148a9d3f54353ee3fe340e7004877cf479db769a` |
| C | `MuntzV3GwinExactClass` | 190 | `a433b05d9e798b98a45839b7510dab7199655110cc4de9a764568e2c3e13490c` |
| C | `MuntzV3RplusExactClass` | 187 | `e97f34aae6e851dc81a619587f3925c1e05a215fba90fe4d9f469441e6ee8144` |
| C | `MuntzV3Unconditional` | 79 | `7bc8e8dbec15ff87a067462a8e7e4cf5a6804c737d067fc046a5d4db3739bef2` |
| C | `MuntzV3RminusExactClass` | 287 | `c8a7d583ce60cbe6c75135ded8338a625466c6fb05e004135ddf2da990886847` |
| D | `MuntzV3HabsExactClass` | 305 | `60fd35f3c755c2a79c0c290f71e7a7a8e1c8e0d541a025e3a508eefc7496b9b7` |
| E | `MuntzV3ExactClassClosure` | 68 | `f4ea12e1497b37a809c27db35f95035111d0d126942ea8c7557ec435b0e3ebfd` |
| F | `MuntzV3SymmetricTrialCrosswalk` | 135 | `ebede2df7ff55b811bafd1dcbbb55baea064658b406611bbec4e093fd94c6f9b` |
| G | `MuntzV3ProlateCombinationReceiver` | 75 | `ab12e82fbf3993318b9e9a1dae850f20a81f944b4a71e0c9460a7d2e78212d84` |

The batches are topological:

```text
A: Core definitions + independent R6 boundary bridge
B: Direct Core consumers and exact E* bounds
C: Gwin / Rplus / unconditional / Rminus suppliers
D: Habs assembly
E: Exact-class closure
F: Positive-half symmetric crosswalk
G: Prolate receiver using the three existing production suppliers
```

## Portability boundary

The request project is pinned to Lean 4.28; production is pinned to Lean 4.26.
The Lean project explicitly states that backwards compatibility between minor
versions is not guaranteed:
https://github.com/leanprover/lean4/blob/master/RELEASES.md.

Therefore source hashes, normalized diffs, and the successful request-project
build are provenance evidence only.  Every batch remains open until it compiles
under production Lean 4.26 with the same public statement and standard axiom
triple.

The production module path will be `Q3.Proofs.RouteB.MuntzV3.*`.  No
production file may import `RequestProject.*`,
`aristotle_output/RequestProject/Main.lean`, or the canonical roof.

## Validation

```yaml
TRANSITIVE_LOCAL_MODULES: 17
EXISTING_PRODUCTION_SUPPLIERS: 3
NEW_PRODUCTION_MODULES: 14
NEW_SOURCE_LINES: 2282
REQUEST_PROJECT_RECEIVER_LEAN_4_28: PASS
RECEIVER_PUBLIC_AXIOMS: [propext, Classical.choice, Quot.sound]
RAW_ROOF_IMPORTS_IN_CLOSURE: 0
CANON_ROOF_IMPORTS_IN_CLOSURE: 0
PRODUCTION_LEAN_CHANGED: 0
```

## Prediction score

- `P056B_1`: **HIT** — 17 local modules.
- `P056B_2`: **HIT** — three production suppliers leave exactly 14 new
  modules.
- `P056B_3`: **HIT** — Batch A is the only honest first port; copying the
  receiver leaf first would fabricate unavailable imports.

## Next executable object

`MuntzV3ProductionCoreBatchA`:

1. port request `Main.lean` as `Q3.Proofs.RouteB.MuntzV3.Core`;
2. port `R6Export.RiemannBoundaryCellBridge` as
   `Q3.Proofs.RouteB.MuntzV3.R6BoundaryCellBridge`;
3. change module paths only;
4. require direct Lean-4.26 checks, normalized proof-body comparison, taint
   zero, and public axiom inventory before Batch B.

`CHALLENGER / NOT_RH`; Bus 010 `VOID`; Goal 055 `HOLD`;
`ARISTOTLE_SUBMISSION: NONE`; `PX_RH_CLAIM: NOT_MADE`.
