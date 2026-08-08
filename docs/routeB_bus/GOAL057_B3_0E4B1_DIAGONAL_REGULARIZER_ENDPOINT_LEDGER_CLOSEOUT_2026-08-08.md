# GOAL 057 B3.0E4B1 DIAGONAL REGULARIZER ENDPOINT-LEDGER CLOSEOUT

Date: 2026-08-08
Route: Route B (`CHALLENGER_NOT_RH`)
Goal: 057
Child: B3.0E4B1
Status: `CLOSED_CHILD_PARENT_B3_0E_OPEN`

## Exact result

`GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER_PROVED`

Production proves the exact scalar cancellation required by the diagonal
equation-(4.4) source ledger for every `L > 0`:

```lean
theorem sourceArchimedeanDiagonalRegularizer_endpointLedger
    (L : ℝ) (hL : 0 < L) :
    -Real.log Real.pi -
        (∫ x in Set.Ioc 0 L,
          2 * (1 - Real.exp (-x)) /
            (Real.exp x - Real.exp (-x))) +
        (∫ x in Set.Ioi L,
          2 * Real.exp (-x) /
            (Real.exp x - Real.exp (-x))) =
      -Real.log
        (4 * Real.pi *
          ((Real.exp L - 1) / (Real.exp L + 1)))
```

The proof preserves the cancellation-bearing paired finite regularizer,
evaluates the convergent `Ioi L` tail, and closes the exact `4π` endpoint
logarithm using proved positivity/nonzero facts only. It is not the
mode-dependent diagonal pairing crosswalk.

## Source lock and release

- pre-edit HEAD and `origin/rh_clean`:
  `2b57a33f04ee09a865fa4186064afa48645b211d`;
- mathematical parent:
  `d69de380742248aacaf0b56e4707cbfe9299c63c`;
- request: 7,435 bytes / 243 lines / SHA-256
  `01f2ce1e8b690b5870e447e30b10384b4f63a91e0bd2b2bc060924c858bb11cf`;
- harness: 6,852 bytes / 174 lines / SHA-256
  `a7bdb27c58288d64b239d877b14de291719b394c8688850d5ad493755aea0a4c`;
- visible verdict: 28,974 bytes / SHA-256
  `85258e334f94e0b47d2aeeb9364050e73a7a6624f4fcc0a56e84f2bd9497d193`;
- newline-normalized verdict archive: 28,975 bytes / 1,346 lines /
  SHA-256
  `27b4098bc998069569c38ca98fa9610e75bfb3eaa0851908e95f8e4ace42641e`;
- conversation: `6a72e750-dc60-83eb-946b-61d2073c232b`;
- request message: `136f5c1e-0af2-494a-8dc4-98e05468b3ce`;
- response message: `cb1d5bad-dd13-46a2-8abd-9fe9ae25db42`;
- review wall: 1,044 seconds / 17m24s;
- `Answer now` appeared and was never clicked.

Proshka authorized exactly one production child, accepted the statement and
proof unchanged, and strengthened the plant suite from seven to nine. No
owner action was required.

## Production object

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchDiagonalRegularizerEndpointLedger.lean`

- 6,786 bytes / 173 lines;
- SHA-256
  `40248c5779c9da3fea249602c54a5b41047bd3592bf28198a2b269242a190d8c`;
- harness-to-production diff: exactly the final `#print axioms` command
  omitted;
- zero public definitions, one public theorem;
- two private noncomputable definitions, five private theorems;
- proof DB: 8/8 declarations proven.

## Load-bearing semantics

- exact hypothesis `0 < L`;
- exact paired numerator `1 - exp (-x)`;
- finite-region minus sign and factor two;
- tail plus sign and factor two;
- common split boundary `L`;
- exact ratio `(exp L - 1) / (exp L + 1)`;
- exact endpoint scale `4 * π`;
- every logarithm argument proved positive or nonzero;
- no fitted, numerical, or interval constant.

## Verification

- direct production Lean: **PASS**;
- target build: **PASS** (`2,691` jobs);
- full build: **PASS** (`7,817` jobs);
- `scripts/q3_check.sh`: **PASS**;
- pre-state `routeb_status.py --check`: **CHECK: OK**;
- harness-minus-print byte identity: **PASS**;
- exact one-import audit: **PASS**;
- hole and forbidden-token scan: **0 findings**;
- public/private surface: **0+1 public; 2+5 private**;
- public axiom audit: exactly
  `[propext, Classical.choice, Quot.sound]`;
- strengthened plants: **9/9 fired**;
- proof DB: **8/8 proven**;
- orchestrator unit tests: **80/80 PASS**;
- strict Spine: **P9_STRICT_PASS**;
- semantic index: **PASS**, 2,395 files / 12,590 vectors;
- SQLite integrity: **3/3 ok**;
- observability: `OBS_3b6dec240ffe59002b82`, 8 sources / 0 stale,
  3,355 files, 5,602 import edges, 0 sorry sites, 10 proof nodes,
  10 axiom dependencies and 48 Proshka runs;
- numeric checks: honest `ZERO_COVERAGE`, not PASS;
- production `git diff --check`: **PASS**.

## Proof-DB parser repair

The existing parser accepted at most one Lean declaration modifier and
therefore skipped the two valid declarations beginning with
`private noncomputable def`. Its declaration regex now accepts a sequence of
the already-supported `private`, `noncomputable`, and `protected`
modifiers. A direct parser regression check returns the exact eight
declarations, and repeat import records 8/8 proven. No production Lean byte or
database schema was changed by this repair.

## Dependency audit

The direct import is exactly:

```text
Mathlib.MeasureTheory.Integral.IntegralEqImproper
```

There is no Route-B parent import, Step33, hbox, numeric-payload,
generated-PSD, Aristotle-output or ACTIVE-request dependency. The theorem is
a standalone scalar supplier. B3.0E4B2 may import it later.

## Plant results

1. Tail-sign mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_TAIL_SIGN_MISMATCH`.
2. Tail-factor-two mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_TAIL_FACTOR_MISMATCH`.
3. Paired-regularizer mutation fires
   `SOURCE_DIAGONAL_REGULARIZATION_CANCELLATION_DROPPED`.
4. Common-boundary mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_SPLIT_BOUNDARY_MISMATCH`.
5. Log-ratio reciprocal mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_LOG_RATIO_ORIENTATION_MISMATCH`.
6. Endpoint-scale `4π → 2π` mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_SCALE_MISMATCH`.
7. Positive-length mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_LOG_DOMAIN_MISSING`.
8. Finite-region sign mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_FINITE_SIGN_MISMATCH`.
9. Finite-region factor-two mutation fires
   `SOURCE_DIAGONAL_ENDPOINT_FINITE_FACTOR_TWO_MISMATCH`.

Each plant changed exactly one source line and produced a real Lean failure.
All temporary mutation artifacts were removed to Trash; production remained
unchanged.

## Exact boundary

```text
SOURCE_ARCH_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER_PROVED
EXACT_FINITE_REGION_PAIRED_CANCELLATION_RETAINED
EXACT_FINITE_REGION_MINUS_SIGN_RETAINED
EXACT_FINITE_REGION_FACTOR_TWO_RETAINED
EXACT_TAIL_PLUS_SIGN_RETAINED
EXACT_TAIL_FACTOR_TWO_RETAINED
EXACT_COMMON_SPLIT_BOUNDARY_RETAINED
EXACT_LOG_RATIO_ORIENTATION_RETAINED
EXACT_FOUR_PI_ENDPOINT_SCALE_RETAINED
B3_0E4B1_CLOSED
B3_0E_OPEN
NO_DIAGONAL_MODE_PAIRING_CROSSWALK
NO_ALL_MODE_CROSSWALK
NO_SOURCE_WEIL_FORM_DECOMPOSITION
NO_ASSOCIATED_OPERATOR_GRAPH
NO_FORM_OR_OPERATOR_DOMAIN_MEMBERSHIP
NO_COMPRESSION_IDENTITY
NO_CONTINUUM_NUMERATOR
H4A1B_OPEN
CHECKPOINTS_CLOSED_0
CHECKPOINTS_REMAINING_10
```

## Next atom

`GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY`

Discriminator:

`B3_0E4B2_DIAGONAL_NEG_CCM_WR_CROSSWALK_NO_SORRY_PREFLIGHT`

B3.0E4B2 production is not authorized. It must consume B3.0D, B3.0E1,
B3.0E2, B3.0E3, this scalar endpoint ledger, the exact diagonal
`ccmQKernel = 2`, and the pinned source-mode normalization. It must not
assemble an all-mode theorem in the same transaction.

## Final boundary

- route: `CHALLENGER_NOT_RH`;
- active bus goal: `057`;
- `BUS_010: VOID`;
- `GOAL_055: HOLD`;
- `G2_CCM: FROZEN`;
- Aristotle submission: `NONE`;
- route promotion: `false`;
- `PX_RH_CLAIM: NOT_MADE`.
