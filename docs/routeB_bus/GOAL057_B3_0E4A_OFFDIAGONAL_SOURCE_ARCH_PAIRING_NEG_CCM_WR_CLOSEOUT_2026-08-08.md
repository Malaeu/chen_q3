# GOAL 057 B3.0E4A OFF-DIAGONAL SOURCE ARCHIMEDEAN / CCM-WR CLOSEOUT

Date: 2026-08-08
Route: Route B (`CHALLENGER_NOT_RH`)
Goal: 057
Child: B3.0E4A
Status: `CLOSED_CHILD_PARENT_B3_0E_OPEN`

## Exact result

`GOAL057_B3_0E4A_OFFDIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED`

Production proves the complete negative CCM-WR crosswalk for every
off-diagonal source-mode pair:

```lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ)
```

The proof consumes the exact source multiplier representation, the joint
product-measure `L¹` carrier, and the zero-extended cosine-correlation /
CCM-kernel theorem. It is not a wrapper. It does not prove the diagonal
endpoint ledger, an all-mode crosswalk, the source Weil form, or an associated
operator graph.

## Source lock and release

- pre-edit HEAD and `origin/rh_clean`:
  `ce7f7f492cabfa48b5b3628a3842d09508114df8`;
- mathematical parent:
  `3df702ead9729e187d3fbdf461452e25bb7c8bae`;
- request: 5,772 bytes / 177 lines / SHA-256
  `3c01e6440d318d87b270f13c8388f6bfe72a16ab1507703af71391d9fe5f6b6a`;
- harness: 12,483 bytes / 310 lines / SHA-256
  `4a9910f66a31400d244b240514b69dd8eb3f414401bc3226f503fd95385ce79e`;
- visible verdict: 26,595 bytes / SHA-256
  `48ba67636955c7ef62aed715d501b533ab836c35373984c0d23c40b25febae2c`;
- newline-normalized verdict archive: 26,596 bytes / 1,074 lines /
  SHA-256
  `731bee1fcafe89195f7f70e60dc8509df37257d88b6b5f16e2b909edda7b1ef7`;
- conversation: `6a72e750-dc60-83eb-946b-61d2073c232b`;
- request message: `38affb58-c374-4d83-8070-c1de08d51743`;
- response message: `4de0d32d-821f-40c5-93c7-99a872295bcb`;
- review wall: 964 seconds / 16m04s;
- `Answer now` appeared and was never clicked.

Proshka authorized exactly one production child. No owner action was required.

## Production object

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchOffDiagonalCCMWRCrosswalk.lean`

- 12,018 bytes / 299 lines;
- SHA-256
  `ae96473ac1419ec9d243be1fe3add228a578b3a46e074b575bb1d82203842c82`;
- harness-to-production diff: exactly the two final ordered examples and the
  final `#print axioms` command omitted;
- zero public definitions, one public theorem;
- two private definitions, eleven private theorems;
- proof DB: 14/14 declarations proven.

## Load-bearing semantics

- exact off-diagonal premise `n ≠ r`;
- exact `ccmQKernel (L_m i) n r 0 = 0`;
- literal conjugate-first source-mode product;
- exact `(n,r)` source order;
- public B3.0E2 joint Fubini carrier consumed;
- exact outer `-2` and B3.0E3 half-factor cancellation;
- final negative sign retained;
- zero-extended support cut retained;
- real/complex integral coercion retained.

The ordered `(0,1)` and `(1,0)` harness instances are smoke only. Because
the final scalar kernel is symmetric, they are not an independent index-order
falsifier. The repaired load-bearing plant uses the exact
`bareModeProduct` fingerprint plus a non-real complex control.

## Verification

- direct production Lean: **PASS**;
- target build: **PASS** (`7,769` jobs);
- full build: **PASS** (`7,817` jobs);
- `scripts/q3_check.sh`: **PASS**;
- pre-state `routeb_status.py --check`: **CHECK: OK**;
- harness-minus-controls byte identity: **PASS**;
- exact four-import audit: **PASS**;
- hole and forbidden-token scan: **0 findings**;
- public/private surface: **0+1 public; 2+11 private**;
- public axiom audit: exactly
  `[propext, Classical.choice, Quot.sound]`;
- repaired plants: **9/9 fired**;
- non-real C04 orientation control: **Lean PASS**;
- proof DB: **14/14 proven**;
- orchestrator unit tests: **80/80 PASS**;
- strict Spine: **P9_STRICT_PASS**;
- semantic index: **PASS**, 2,394 files / 12,559 vectors;
- SQLite integrity: **3/3 ok**;
- observability: `OBS_7f51758d4cd8607907e4`, 8 sources / 0 stale,
  3,354 files, 5,602 import edges, 0 sorry sites, 10 proof nodes,
  10 axiom dependencies and 47 Proshka runs;
- numeric checks: honest `ZERO_COVERAGE`, not PASS;
- production `git diff --check`: **PASS**.

## Provenance audit

The direct imports are exactly:

```text
Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
Mathlib.MeasureTheory.Integral.Prod
```

There is no new Step33, hbox, numeric-payload, generated-PSD or direct
Aristotle-output dependency. The inherited tracked, hole-free historical
dependency through the already closed parent chain remains recorded.
B3.0E4A introduces no new generated backend.

## Plant results

1. Off-diagonal constant mutation fires
   `SOURCE_OFFDIAGONAL_CCM_QKERNEL_ZERO_CONSTANT_MISSING`.
2. Fubini-carrier mutation fires
   `SOURCE_ARCH_JOINT_FUBINI_CARRIER_NOT_CONSUMED`.
3. Final-sign mutation fires `SOURCE_ARCH_CCM_WR_FINAL_SIGN_MISMATCH`.
4. Factor-two mutation fires `SOURCE_ARCH_CCM_WR_FACTOR_TWO_MISMATCH`.
5. Support mutation fires `SOURCE_MODE_ZERO_EXTENSION_SUPPORT_MISMATCH`.
6. Antilinear-slot mutation fires
   `SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH`.
7. Repaired fingerprint/non-real index-order mutation fires
   `SOURCE_ARCH_OFFDIAGONAL_INDEX_ORDER_MISMATCH`.
8. Real/complex coercion mutation fires
   `SOURCE_ARCH_CCM_WR_REAL_COMPLEX_COERCION_MISMATCH`.
9. Generated-backend injection fires
   `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.

All mutations were in memory. No mutation artifact was written.

## Exact boundary

```text
SOURCE_ARCH_OFFDIAGONAL_PAIRING_EQ_NEG_CCM_WR_PROVED
EXACT_OFFDIAGONAL_ZERO_CONSTANT_RETAINED
EXACT_JOINT_FUBINI_CARRIER_CONSUMED
EXACT_FINAL_MINUS_SIGN_RETAINED
EXACT_FACTOR_TWO_LEDGER_RETAINED
EXACT_ANTILINEAR_FIRST_ORIENTATION_RETAINED
EXACT_ZERO_EXTENDED_SUPPORT_RETAINED
ORDERED_EXAMPLES_SMOKE_ONLY
B3_0E4A_CLOSED
B3_0E_OPEN
NO_DIAGONAL_ENDPOINT_LEDGER
NO_DIAGONAL_CCM_WR_CROSSWALK
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

`GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER`

Discriminator:

`B3_0E4B1_DIAGONAL_ENDPOINT_LEDGER_NO_SORRY_PREFLIGHT`

B3.0E4B1 production is not authorized. The scalar cancellation ledger must
preserve the finite-region regularizer and convergent tail as one
cancellation-bearing object; it must not split them into separately divergent
near-zero pieces.

## Final boundary

- route: `CHALLENGER_NOT_RH`;
- active bus goal: `057`;
- `BUS_010: VOID`;
- `GOAL_055: HOLD`;
- `G2_CCM: FROZEN`;
- Aristotle submission: `NONE`;
- route promotion: `false`;
- `PX_RH_CLAIM: NOT_MADE`.
