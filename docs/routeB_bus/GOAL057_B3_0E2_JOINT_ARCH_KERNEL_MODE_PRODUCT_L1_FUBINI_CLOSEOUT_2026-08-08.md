# GOAL 057 B3.0E2 JOINT ARCH KERNEL-MODE PRODUCT L1/FUBINI CLOSEOUT

Date: 2026-08-08
Route: Route B (`CHALLENGER_NOT_RH`)
Goal: 057
Child: B3.0E2
Status: `CLOSED_CHILD_PARENT_B3_0E_OPEN`

## Exact result

`GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_CARRIER_PROVED`

Production now proves, for every fixed `PairIndex i` and integer modes
`n,r`, joint absolute integrability of the exact conjugate-first source
kernel-mode product on the literal measure

```lean
volume.prod (volume.restrict (Set.Ioi 0))
```

This is the exact carrier needed to apply Bochner Fubini to this integrand.
It is not a public swapped-integral identity and it does not identify the
mode correlation with `ccmQKernel` or `ccmWREntry`.

## Source lock and release

- Published pre-edit head:
  `3c3681f1a93d1115d26002ff2105fc0b6c0023d1`.
- Request: 6,711 bytes / 179 lines / SHA-256
  `737d65801a9ecbeef6aa7c4312aecef7a72be46b2a427191c88537a3a2d15c6f`.
- Compiling harness: 27,927 bytes / 696 lines / SHA-256
  `1ff1ef467028a6a62a9d2722c2b96e0ec6aff94366645e32bab91ff5f82f7bde`.
- Visible Proshka verdict: 29,062 bytes / SHA-256
  `d8e24abbd4a5dd42c5db839914d3d72c7795387f5af3631c2e161dbbd5bb84e1`.
- Newline-normalized verdict archive: 29,063 bytes / 1,162 lines /
  SHA-256
  `3761805986f3cb7435d5fa0e90a470bf0e9c529c872371c99b714cad71405dd7`.
- Same living conversation:
  `6a72e750-dc60-83eb-946b-61d2073c232b`.
- Request message:
  `5e2a6a41-a1db-4afc-8914-e9f66844206a`.
- Response message:
  `efd108f8-7c62-4910-986b-477a8f3053e3`.
- Observed review wall: 1,473 seconds / 24m33s.
- `Answer now` appeared and was never clicked.

Proshka released exactly one production child and no owner action was
required.

## Production object

Path:

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchKernelModeProductL1.lean`

- bytes: `27,814`
- lines: `694`
- SHA-256:
  `8d7b5eafd4cbeffe576c285c9792c6991f696f8c9da39a9a7bc918fe00aefc0c`
- harness-to-production diff: exactly the two final `#print axioms`
  audit commands were omitted; no proof or statement changed.

Exact public surface:

```lean
def sourceArchimedeanKernelModeIntegrand
    (i : PairIndex) (n r : ℤ) (p : ℝ × ℝ) : ℂ :=
  conj (𝓕 (logWindowZeroExtendedMode i n) p.1) *
    (sourceArchimedeanRegularizedKernel p.1 p.2 : ℂ) *
    𝓕 (logWindowZeroExtendedMode i r) p.1

theorem sourceArchimedeanKernelModeIntegrand_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (sourceArchimedeanKernelModeIntegrand i n r)
      (volume.prod (volume.restrict (Set.Ioi 0)))
```

Surface counts:

- public: one definition and one theorem;
- private: four definitions and eighteen theorems;
- total proof-DB declarations: 24;
- additional declarations: zero.

## Load-bearing semantics

- `t` is Mathlib cycles-per-unit Fourier frequency.
- `x` is the positive regularized hyperbolic variable.
- mode `n` is conjugated in the first, antilinear slot;
- mode `r` is linear in the second slot;
- the exact B3.0E1 regularized kernel is retained;
- the paired zero-endpoint cancellation is retained;
- the near carrier is `x^(-1/2)`, not `x^(-1)`;
- both fixed-mode inverse-linear decays pay the `sqrt |t|` cost;
- the result is joint `L1` on the exact product measure.

## Verification

- Direct production Lean: **PASS**.
- Target build: **PASS** (`7,762` jobs).
- Full project build: **PASS** (`7,817` jobs).
- `scripts/q3_check.sh`: **PASS**.
- Live `routeb_status.py --check` before state update: **CHECK: OK**.
- Exact public/private surface: **1 + 1 public; 4 + 18 private**.
- Hole and forbidden-token scan: **0 findings**.
- Exact harness-to-production mechanical diff: **PASS**.
- Direct-import audit: exactly four released imports.
- Proof DB: **24/24 declarations proven**.
- Public axioms: exactly
  `[propext, Classical.choice, Quot.sound]`.
- Plant suite: **7/7 fired**.
- Orchestrator unit tests: **80/80 PASS**.
- Strict Spine at `goal-close`: **P9_STRICT_PASS**.
- Semantic index: **PASS**, 2,375 files / 12,495 vectors.
- SQLite integrity: **ok** on knowledge, proof and observability DBs.
- Observability snapshot:
  `OBS_c7f9506085991dbda30d`.
- Observability: 8 sources / 0 stale, 3,352 files, 5,597 import edges,
  0 sorry sites, 10 proof nodes, 10 axiom dependencies and 45 Proshka runs.
- Honest degradation: numeric checks are `ZERO_COVERAGE`, not PASS.
- `git diff --check` on authored Lean, state, closeout and synthesis files:
  **PASS**. The byte-locked verdict mirrors deliberately retain three source
  trailing-space lines; normalizing them would break the recorded SHA-256 and
  is forbidden.

## Provenance audit

The new file adds no Step33, hbox, numeric-payload, generated-PSD or direct
Aristotle-output import. Its exact four direct imports match the release.

A recursive project-source audit nevertheless finds one inherited historical
dependency:

```text
D0PstarSourceArchKernelModeProductL1
<- D0PstarSourceArchHyperbolicKernel
<- D0PstarExactArchSymbolLogDomination
<- Q3.DigammaRemainder
<- Q3.DigammaSeries
<- aristotle_output.d1524982_aristotle
```

That file is tracked, hole-free under the required scan, and was already in
the closed B3.0E1 parent closure. B3.0E2 introduces no new generated backend.
Therefore the release gate passes under its operative `no new dependency`
wording, while the stronger preflight prose claim “no transitive Aristotle
output at all” is explicitly corrected here and is not reused.

## Plant results

1. Removing first-slot conjugation fires
   `SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH`.
2. Dropping the paired endpoint subtraction fires
   `SOURCE_ARCH_REGULARIZATION_CANCELLATION_DROPPED`.
3. Replacing the square-root endpoint carrier fires
   `SOURCE_ARCH_ENDPOINT_L1_EXPONENT_MISSING`.
4. Removing the second fixed-mode decay payment fires
   `SOURCE_ARCH_FREQUENCY_MAJORANT_NOT_L1`.
5. Changing the literal positive-`x` product measure fires
   `SOURCE_ARCH_POSITIVE_X_PRODUCT_MEASURE_MISMATCH`.
6. Injecting a generated backend fires
   `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.
7. Weakening joint integrability to fiberwise statements fires
   `SOURCE_ARCH_JOINT_FUBINI_CARRIER_MISSING`.

All mutations remained in memory; no mutation artifact was written.

## Exact boundary

- `SOURCE_ARCH_JOINT_KERNEL_MODE_PRODUCT_L1_PROVED`
- `EXACT_ANTILINEAR_FIRST_ORIENTATION_RETAINED`
- `PAIRED_ENDPOINT_CANCELLATION_RETAINED`
- `EXACT_POSITIVE_X_PRODUCT_MEASURE_RETAINED`
- `FUBINI_CARRIER_ONLY`
- `NO_PUBLIC_SWAPPED_INTEGRAL_IDENTITY`
- `B3_0E2_CLOSED`
- `B3_0E_OPEN`
- `NO_MODE_CORRELATION_CCM_QKERNEL_CROSSWALK`
- `NO_ONE_SIDED_HALF_FACTOR_ASSEMBLY`
- `NO_CCM_WR_ENTRY_CROSSWALK`
- `NO_SOURCE_WEIL_FORM_DECOMPOSITION`
- `NO_ASSOCIATED_OPERATOR_GRAPH`
- `NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP`
- `NO_COMPRESSION_IDENTITY`
- `NO_CONTINUUM_NUMERATOR`
- `NO_UNIFORM_COFINAL_MODE_BOUND`
- `H4A1B_OPEN`
- `CHECKPOINTS_CLOSED_0`
- `CHECKPOINTS_REMAINING_10`

## Next atom

`GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_EQ_CCM_QKERNEL`

Discriminator:

`B3_0E3_MODE_COSINE_CORRELATION_CCM_QKERNEL_NO_SORRY_PREFLIGHT`

B3.0E3 production is not authorized. The next action is one untracked
source-locked no-`sorry` preflight, followed by exactly one same-chat
Proshka release review if it passes.

## Final boundary

- route: `CHALLENGER_NOT_RH`
- active bus goal: `057`
- `BUS_010: VOID`
- `GOAL_055: HOLD`
- `G2_CCM: FROZEN`
- Aristotle submission: `NONE`
- route promotion: `false`
- `PX_RH_CLAIM: NOT_MADE`
