# PROSHKA REQUEST — Goal 057 B2 compressed Weil action source audit

```yaml
MODE: DELEGATED_STRATEGIC_REVIEW
ROUTE: CHALLENGER_NOT_RH
PARENT_GOAL: 057
TRANSACTION: GOAL057_SOURCE_COMPLEX_COMPRESSED_WEIL_ACTION_SOURCE_AUDIT
HEAD_AND_ORIGIN: c8641e23
GOAL_057_SHA256: fe964e12619a3ba3c0832387ec07eda8f52ab2c3a12d673e18879c6af04c1e65
B1_LEAN_SHA256: c11fe72d9df1e7a81d73cdcb1beebfc016be82cb1d0bcc8ffc371fc748cfb497
B1_CLOSEOUT_SHA256: 366f7254ee7d2033deb14fba36b7dbb7904bab8e0fe6464aac0394dac0e2d83f
PROSHKA_BATCH_BUDGET: EXACTLY_ONE
OWNER_GATE: PX_RH_CLAIM_ONLY
```

## Closed input

B1 is Lean-proved and pushed.  It gives the exact complex source row on
`CCMModeFinite i.N`, exact synthesis of that row to the normalized projected
source trial, exact unit norm, the Hermitian finite CCM action, its real
Rayleigh scalar, and the finite residual orthogonal to the same row.

Strongest honest name:

`the exact finite CCM source-matrix residual`.

It is not yet the continuum Input-B numerator.

## Exact next equality proposed by the prior verdict

```lean
hCompressedAction :
  P (A x) =
    ccmFiniteSynthesis i
      (sourceCCMFiniteOperator i
        (sourceCCMComplexRow S i))
```

where `x` is the normalized projected `kTrial_m_N` source trial.  The intended
consumer is the generic `ambientResidual = compressedResidual +
projectionLeakage` split.

## Codex source audit at `c8641e23`

Found and Lean-live:

- `H_m i`, `E_m_N i`, and `(E_m_N i).orthogonalProjection`;
- `kTrial_m_N` and the source-locked `ProlateCanonicalSourceData`;
- `ccmFiniteSynthesis` and exact finite projection reconstruction;
- the real finite source matrix `ccmWeilMatFinite` and its complex operator;
- the generic `ambientResidual` / `projectionLeakage` algebra.

Not found as a production source object:

- a domain-safe ambient Weil operator `A : Module.End ℂ (H_m i)`;
- a theorem realizing the analytic Weil quadratic form as that operator;
- a source theorem identifying its compression with `ccmWeilMatFinite`;
- a single carrier/domain/normalization package from which the displayed
  `hCompressedAction` follows.

The existing H4a1b report says the same thing explicitly: form compression is
not automatically operator compression, and the exact operator domain,
projection, form/operator realization, and leakage-rate interface remain open.
Mathlib supplies projection machinery, but it cannot supply the project-specific
ambient operator or the source identity.

## Required ruling — exactly one primary

Choose exactly one operative class:

1. `TRY_GOAL057_B2_COMPRESSED_WEIL_ACTION_DIRECT` — only if the exact existing
   `A`, `P`, domain witness, and source theorem can be named from current bytes.
2. `TRY_GOAL057_B2_AMBIENT_WEIL_OPERATOR_SOURCE_CONSTRUCTION` — if a minimal
   prerequisite object/theorem can be built honestly before the crosswalk.
3. `KILL_GOAL057_B2_DIRECT_CROSSWALK_SOURCE_UNAVAILABLE` — if the displayed
   equality is presently source-free; then select the smallest real prerequisite
   atom and state whether it remains inside the same coarse checkpoint.

Do not ratify a receiver that merely accepts `hCompressedAction` as a premise
unless you classify it as structural-only and explain what new route value it
adds beyond the already-proved generic residual split.

## Required output

Return:

1. one primary and one operative `TRY_` / `KILL_` / `RUN_` class;
2. exact source objects and their current file/line locations;
3. the smallest honest theorem statement;
4. one owned production file and exact imports;
5. K6 object precommit;
6. executable plants, especially form-compression-as-operator-compression and
   projection-codomain/carrier mismatches;
7. stop and success codes;
8. the exact next gap after success;
9. effect on the ten-checkpoint ledger: closed / advanced / unchanged;
10. the strongest attack on your own recommendation.

## Hard boundaries

No Lean edit is authorized inside this review.  No numerical ladder, no
Aristotle, no Bus 010, no Goal 055 release, no route promotion, no PX claim, and
no RH claim.  Continue in this same living phase chat; never use `Answer now`.
