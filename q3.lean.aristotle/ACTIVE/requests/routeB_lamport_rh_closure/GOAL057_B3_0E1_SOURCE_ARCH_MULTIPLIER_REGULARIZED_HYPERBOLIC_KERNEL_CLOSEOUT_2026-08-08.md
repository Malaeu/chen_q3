# Goal 057 B3.0E1 — source archimedean multiplier regularized-hyperbolic kernel closeout

## Verdict

`GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL_PROVED`

- Child transaction B3.0E1: **CLOSED**.
- Parent B3.0E: **OPEN**; the weighted mode/Fubini carrier, mode correlation,
  one-sided endpoint assembly, and final negative `ccmWREntry` crosswalk are
  not yet proved.
- Parent B3.0: **OPEN**; no source Weil-form decomposition or associated
  operator graph is built.
- Parent `Goal 057`: **OPEN**.
- Route: `CHALLENGER / NOT_RH`.
- Coarse delegated checkpoints closed: **0**.
- Coarse delegated checkpoints remaining: **10**.
- Current checkpoint: `ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE` —
  **STRICTLY ADVANCED, NOT CLOSED**.

This transaction proves the first missing scalar source theorem identified by
the B3.0E wall.  It constructs the cancellation-preserving regularized
hyperbolic kernel, proves its integrability on `Ioi 0`, and proves the exact
global identity

```text
sourceArchimedeanMultiplier(t)
  = -log(pi) - EulerGamma
      - 2 * integral_(0,infinity) sourceArchimedeanRegularizedKernel(t,x) dx.
```

The endpoint numerator remains paired before every near-zero estimate.  The
integral/series exchange uses the proved norm-sum carrier, and the final minus
sign and factor `2` come from the exact `u = 2*x` pointwise crosswalk and
Jacobian.  No desired source identity is accepted as a premise.

## Production artifact

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchHyperbolicKernel.lean`

- SHA-256: `4fb022d88ded0d0afecbab8767f0b07642c7a0a97e1108736682687198e7a25d`.
- Size: 23,328 bytes / 594 lines.
- Sole explicit import:
  `Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination`.
- Authoritative harness materialization: exact after replacing the scratch
  namespace by `Q3.RouteB.D0Pstar` and omitting only the final three
  `#print axioms` commands.
- Mathematical proof deviations from the harness: **0**.
- Project import closure: 19 files / 20 project import edges.
- Closure delta over the sole parent: exactly the new production file.
- Forbidden PSD/Step33/hbox/numeric-payload imports in the closure: **0**.
- The inherited `aristotle_output/d1524982_aristotle.lean` dependency is
  already in the exact parent closure through `Q3.DigammaSeries`; this
  transaction adds no generated backend.
- Public surface: exactly 1 definition + 2 theorems.
- Private support: exactly 7 definitions + 26 theorems = 33 declarations.
- New axioms: **0**.
- All three public objects depend on exactly
  `[propext, Classical.choice, Quot.sound]`.
- Proof DB import: 36 declarations, 36 proven.

Exact public objects:

```lean
def sourceArchimedeanRegularizedKernel (t x : ℝ) : ℝ :=
  (Real.exp (x / 2) * Real.cos (2 * Real.pi * t * x) - Real.exp (-x)) /
    (Real.exp x - Real.exp (-x))

theorem sourceArchimedeanRegularizedKernel_integrableOn (t : ℝ) :
    IntegrableOn (sourceArchimedeanRegularizedKernel t) (Set.Ioi 0)

theorem sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral
    (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Real.log Real.pi - Real.eulerMascheroniConstant -
        2 * ∫ x in Set.Ioi 0, sourceArchimedeanRegularizedKernel t x
```

## Verification

- Direct production Lean check: **PASS**.
- Target build: **PASS** (`7,761` jobs).
- Full project build: **PASS** (`7,817` jobs).
- `scripts/q3_check.sh`: **PASS**.
- Orchestrator unit tests: **80/80 PASS**.
- Exact public/private surface: **1 + 2 public; 7 + 26 private**.
- Hole and forbidden-token scan: **0 findings**.
- Exact harness-to-production mechanical diff: **PASS**.
- Transitive generated-backend audit: **PASS**.
- Plant suite: **6/6 fired**.
- Strict Spine at `goal-close`: **P9_STRICT_PASS**; semantic index **PASS**.
- Semantic collection: 2,367 indexed `q3_docs` files / 12,464 vectors.
- Proof DB: **36/36 declarations proven**.
- Canonical SQLite integrity: **ok** for
  `q3.lean.aristotle/aristotle_db/knowledge.db`,
  `q3.lean.aristotle/aristotle_db/aristotle_proofs.db`, and
  `q3.lean.aristotle/aristotle_db/observability.db`.
- Canonical observability snapshot:
  `OBS_b70b00d9a25dbbfb6ac9`, status **COMPLETE**.
- Observability: **8 sources, 0 stale**, 3,351 files, 5,595 import edges,
  0 sorry sites, 10 proof nodes, 10 axiom dependencies, 44 Proshka runs.
- Honest degradation: `numeric_checks = ZERO_COVERAGE`, not PASS.
- `git diff --check`: **PASS** for authored production/state/closeout files.
  The byte-locked request and verdict mirrors deliberately retain one source
  blank EOF line and one source trailing-space line; normalizing either would
  break the recorded SHA-256 and is therefore forbidden.
- Route checker before state update: **CHECK: OK**.

Plant results:

1. `P057_B3_0E1_1_PAIRED_ENDPOINT_CANCELLATION` — deleting the paired
   subtraction fires `SOURCE_ARCH_REGULARIZATION_CANCELLATION_DROPPED`.
2. `P057_B3_0E1_2_FINAL_MINUS_AND_TWO` — removing the final minus sign from
   `-2 * integral` fires
   `SOURCE_ARCH_SCALAR_HYPERBOLIC_SIGN_SCALE_MISMATCH`.
3. `P057_B3_0E1_3_NO_GENERATED_BACKEND` — injecting a generated
   PSD/Step33/payload import fires `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.
4. `P057_B3_0E1_4_FUBINI_CARRIER` — deleting
   `hasSum_integral_of_dominated_convergence` fires
   `SOURCE_ARCH_FUBINI_CARRIER_MISSING`.
5. `P057_B3_0E1_5_PREMISE_SURROGATE` — adding an axiom-like source-identity
   premise fires `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION`.
6. `P057_B3_0E1_6_FREQUENCY_SCALE` — replacing the public
   `cos (2*pi*t*x)` coordinate fires
   `SOURCE_ANGULAR_CYCLES_NORMALIZATION_MISMATCH`.

All mutations were in-memory `/tmp` audit data; the temporary auditor and
axiom file were removed, and no mutation artifact remains in the repository.

## Proshka transaction pins

- Request SHA-256:
  `2964606d9955cec6a24b9c81e3f4d8f341c50867e8e9b87bcd94927090f417d0`.
- Harness SHA-256:
  `49425edef5c5b972d93f4f1c9f84877b4f9c23063fe736b06856cc0bae16af47`.
- Visible verdict: 24,869 bytes, SHA-256
  `d99c5fed227dd29c719f171ada3abe39ca8b1fc63b6f634ab738f854df14d753`.
- Newline-normalized archive: 24,870 bytes / 888 lines, SHA-256
  `96452e937b56305e71491ad07908eef6b0136c59003ff8291bd4866ff6808f73`.
- Request message:
  `c3168e2d-166b-4e44-ae6f-a6905dfce616`.
- Response message:
  `6de1275f-1401-4fc5-902a-8478ccaaff92`.
- Proshka primary:
  `TRY_GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL`.
- UI send time: `2026-08-08T09:47:35.140+02:00`.
- Completion time: `2026-08-08T09:57:51.842+02:00`.
- Measured runtime: **617 seconds / 10m17s**.
- `Answer now` was displayed and was not clicked.
- Same living conversation:
  `6a72e750-dc60-83eb-946b-61d2073c232b`.
- Review runtime after recording: phase **28**, global **30**, fan-out
  violations **0**.

The archived verdict contains the complete visible transcript plus one final
newline. Byte identity to a hidden Markdown representation is not claimed.

## Exact semantic boundary and next gap

This closeout is
`SOURCE_ARCH_SCALAR_REGULARIZED_HYPERBOLIC_IDENTITY_PROVED`:

- `PAIRED_ZERO_ENDPOINT_CANCELLATION_RETAINED`;
- `EXACT_U_EQUALS_TWO_X_MINUS_AND_JACOBIAN_RETAINED`;
- B3.0E1 is **CLOSED**;
- B3.0E is **OPEN**;
- **NO** weighted mode/Fubini carrier;
- **NO** mode-correlation/`ccmQKernel` crosswalk;
- **NO** one-sided half-factor assembly;
- **NO** `ccmWREntry` crosswalk;
- **NO** source Weil-form decomposition;
- **NO** associated operator graph;
- **NO** form-domain or operator-domain membership;
- **NO** compression identity;
- **NO** continuum numerator;
- `H4a1b` remains **OPEN**;
- checkpoints closed: **0**;
- checkpoints remaining: **10**.

The exact next gap is:

`GOAL057_B3_0E2_WEIGHTED_FUBINI_MODE_CORRELATION_CARRIER`

The next discriminator is:

`B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_NO_SORRY_PREFLIGHT`

It is **NAMED_NOT_AUTHORIZED** by the completed production transaction.  No
B3.0E2 implementation has occurred.  A later same-chat delegated review must
release it after the discriminator.

`ARSENAL_USED: C04,C09,C10`

Boundaries unchanged: `BUS_010: VOID` · `GOAL_055: HOLD` ·
`G2/CCM: FROZEN` · `ARISTOTLE: NONE` ·
`PX_RH_CLAIM: NOT_MADE` · promotion and RH claim forbidden.
