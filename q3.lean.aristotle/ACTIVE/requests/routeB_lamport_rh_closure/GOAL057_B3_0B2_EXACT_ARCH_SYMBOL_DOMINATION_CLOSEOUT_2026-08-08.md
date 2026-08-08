# Goal 057 B3.0B2 — exact archimedean-symbol domination closeout

## Verdict

`GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_PROVED`

- Child transaction: **CLOSED**.
- Parent B3.0B: **OPEN** until B3.0B3 exact-symbol weighted-mode `L²` transfer.
- Parent `Goal 057`: **OPEN**.
- Route: `CHALLENGER / NOT_RH`.
- Coarse delegated checkpoints closed: **0**.
- Coarse delegated checkpoints remaining: **10**.
- Current checkpoint: `ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE` —
  **STRICTLY ADVANCED, NOT CLOSED**.

Proshka selected Candidate A after a mandatory C04 coordinate repair.  The
paper's angular frequency `s` and Mathlib's cycles-per-unit Fourier frequency
`t` obey `s = 2 * pi * t`; therefore the multiplier consumed beside the
production Fourier transform is `hPlus (2 * pi * t)`, not `hPlus t`.

The hidden foundational supplier
`Q3.re_digamma_remainder_bound_stieltjes` makes the global comparison
executable without importing the generated PSD/Step33 backend.

## Production artifact

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean`

- SHA-256: `197daeed0b975bbed63cf59d2f0cfa939ed345661935d258f7e79387815344da`.
- Size: 9,584 bytes / 235 lines.
- Exact imports:
  - `Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2`
  - `Q3.DigammaRemainder`
- Transitive internal import closure: 29 modules.
- Forbidden transitive Step33/PSD/hbox/payload suppliers: 0.
- Public surface: 1 definition + 2 theorems.
- Private proof support: 6 lemmas.
- New structures / axioms: 0 / 0.
- Public theorem axioms: exactly
  `[propext, Classical.choice, Quot.sound]` for both theorems.
- Proof DB import: 9 declarations, 9 proven.

Public definition:

1. `sourceArchimedeanMultiplier`

Public theorems:

1. `sourceArchimedeanMultiplier_eq_neg_aStar_scaled`
2. `abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope`

The exact normalization is

```text
sourceArchimedeanMultiplier t = -Q3.a_star t / (2 * Real.pi).
```

The global domination is

```text
|sourceArchimedeanMultiplier t|
  <= (|log pi| + log 4 + 7) * (1 + log (2 + |t|)).
```

It covers `t = 0`, the complete compact region, and both tails.  The constant
is proved analytically from the Stieltjes remainder; it is neither fitted nor
accepted as a premise.

## Verification

- Direct Lean check: **PASS**.
- Target build: **PASS** (`7,760` jobs).
- Full project build: **PASS** (`7,817` jobs).
- `scripts/q3_check.sh`: **PASS**.
- Orchestrator unit tests: **80/80 PASS**.
- Strict Spine: **P9_STRICT_PASS**; semantic index **PASS**.
- Semantic collection: 2,336 files / 12,329 vectors.
- Proof DB: **9/9 declarations proven**.
- SQLite integrity: **ok** for `knowledge.db`, `aristotle_proofs.db`,
  and `observability.db`.
- Observability: **8 sources, 0 stale**, 3,347 files, 5,590 import edges,
  0 sorry sites, 2 proof roots, 1 taint edge.
- Honest degradation: `numeric_checks = ZERO_COVERAGE/EMPTY_CONFIG`, not PASS.
- Forbidden-token/import scan: **0 findings**.
- Public-surface check: **1 definition + 2 theorems + 6 private lemmas**.
- Plant suite: **8/8 fired**; mutations were in memory/stdin only and no
  mutation artifact was written.
- `git diff --check`: **PASS** for the production file.
- Route checker before state update: **CHECK: OK**.

Plant results:

1. `P057_B3_0B2_1_SCALE_PI_TO_HALF` — changing the production multiplier
   from `I*(pi*t)` to `I*(t/2)` breaks the exact normalization:
   `SOURCE_ARCH_SYMBOL_SCALE_MISMATCH`.
2. `P057_B3_0B2_2_SIGN` — flipping the source sign breaks the exact
   normalization: `SOURCE_ARCH_SYMBOL_SIGN_MISMATCH`.
3. `P057_B3_0B2_3_ONE_SIDED_NOT_ABSOLUTE` — a one-sided internal bound cannot
   discharge the unchanged absolute public target:
   `ARCH_SYMBOL_ABSOLUTE_DOMINATION_MISSING`.
4. `P057_B3_0B2_4_TAIL_NOT_GLOBAL` — replacing the global log helper by a
   tail-only helper leaves the compact region unproved:
   `ARCH_SYMBOL_COMPACT_REGION_MISSING`.
5. `P057_B3_0B2_5_NUMERIC_OR_PREMISE_CONSTANT` — an injected fitted/premise
   constant is caught before compilation: `ARCH_SYMBOL_SOURCE_PROOF_MISSING`.
6. `P057_B3_0B2_6_HEAVY_BACKEND_IMPORT` — an injected
   `PSD_CenteredCoeffAnalyticABoundsBackend` import is caught before
   compilation: `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.
7. `P057_B3_0B2_7_ENVELOPE_AS_SYMBOL` — replacing the exact multiplier by the
   elementary envelope breaks normalization:
   `ARCH_SYMBOL_ENVELOPE_NOT_EXACT_SYMBOL`.
8. `P057_B3_0B2_8_RE_POS_ERASURE` — removing the real part `1/4` destroys the
   Stieltjes domain witness: `DIGAMMA_STIELTJES_DOMAIN_PREMISE_MISSING`.

## Proshka transaction pins

- Request SHA-256:
  `4b4ea792a8040b7cca92b81bed5edde9ec096c529a4c71c46b2aa7803e1d6876`.
- Visible verdict: 24,851 bytes / 1,037 lines, SHA-256
  `2992171921a59d8124f5181ae480ff4a6e36d91e8834f8a635a2f2e4c5db9cdb`.
- Newline-normalized archive: 24,852 bytes / 1,037 lines, SHA-256
  `9a4fd4b622988b738595d796b0066caeb7f3a4aa04f828080389e94a35c662df`.
- Request message:
  `845acf8e-79c7-4602-8206-99039850e0d6`.
- Response message:
  `ab4c595c-da7f-478f-ae95-1e6eeb7c7dc1`.
- Proshka primary:
  `TRY_GOAL057_B3_0B2_EXACT_ARCH_SYMBOL_DOMINATION_REPAIRED`.
- Lower-bound package-publication to verdict-archive wall: **1,059 seconds**.
- The actual send timestamp was not captured; this wall is an explicit upper
  bound on model runtime.
- `Answer now` was displayed and was not clicked.
- Same living conversation:
  `6a72e750-dc60-83eb-946b-61d2073c232b`.
- Review runtime after recording: phase **23**, global **25**, fan-out
  violations **0**.

The archived verdict contains the complete visible transcript plus one final
newline. Byte identity to a hidden Markdown representation is not claimed.

## Exact semantic boundary and next gap

This closeout is
`EXACT_SOURCE_ARCH_SYMBOL_GLOBAL_DOMINATION_ONLY`:

- the public multiplier is in the Mathlib Fourier-frequency coordinate;
- the paper angular frequency equals `2*pi` times that coordinate;
- **NO** immediate exact-symbol-times-mode `MemLp` theorem;
- **NO** Plancherel carrier for arbitrary `H_m` elements;
- **NO** source Weil form;
- **NO** associated operator graph;
- **NO** form-domain or operator-domain membership;
- **NO** compression identity;
- **NO** continuum numerator;
- `H4a1b` remains **OPEN**;
- checkpoints closed: **0**;
- checkpoints remaining: **10**.

The exact next gap is:

`GOAL057_B3_0B3_EXACT_ARCH_SYMBOL_WEIGHTED_MODE_L2_TRANSFER`

It must use the exact normalization plus a source-faithful
measurability/continuity certificate and transfer the already-proved B3.0B1
weighted-mode result.  That theorem was explicitly not authorized in B3.0B2.

`ARSENAL_USED: C04,C09,C10`

Boundaries unchanged: `BUS_010: VOID` · `GOAL_055: HOLD` ·
`G2/CCM: FROZEN` · `ARISTOTLE: NONE` ·
`PX_RH_CLAIM: NOT_MADE` · promotion and RH claim forbidden.
