# GOAL 056 / Phase 4C — logarithmic measure transport and mode orthonormality

```yaml
GOAL: 056
PHASE: 4C
NODE: D0LogWindowMeasureTransport
STATUS: OPEN
OPERATIVE_CLASS: TRY_D0_LOG_WINDOW_MEASURE_TRANSPORT_AND_ORTHONORMALITY
TRANSACTION: G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_AND_ORTHONORMALITY
STOP: G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_MISSING
SUCCESS: G6_S2_D0_LOG_WINDOW_TRANSPORT_AND_V_MODES_ORTHONORMAL_PROVED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 3
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

Proshka selected Path B under `CODEX_PLUS_PROSHKA` authority at source pin
`1553624ae27944b93ef3adce265dc8e8e5c21b33`. The exact verdict is archived
at `proshka/PROSHKA_VERDICT_GOAL056_LOG_WINDOW_MEASURE_TRANSPORT_2026-08-06.md`.
This transaction is proof progress: it proves the canonical scalar
`du/u -> dx` transport and consumes it once to prove orthonormality of the
literal production modes. It does not prove projection reconstruction, the
Phase-4B residual crosswalk, decay, or `SlotS2`.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - Q3.Proofs.RouteB.D0KTrialStage1@c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
    - Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock@ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
    - Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualContract@1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
    - Mathlib@2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
    - docs/CODEX_CONTROL.md@fc77ff8d7483c87744f07e8aea3d59b08f9b5340541d3bf414885f239dfafc4e
  terminal_consumer: Q3.RouteB.CanonicalRHRoute.SlotS2 under standing Goal 056
  relation_under_test: exact logarithmic transport of dStar on I_m and orthonormality of V_n_m
  owned_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
  sole_import: Q3.Proofs.RouteB.D0KTrialStage1
  namespace: Q3.RouteB.D0Pstar
  public_definitions: 0
  public_theorems:
    - integral_comp_logWindow_dStar
    - V_n_m_orthonormal
  source_measure: dStar = volume.withDensity (fun u => ENNReal.ofReal u^-1)
  source_window: I_m i = Icc (lambda_m i)^-1 (lambda_m i)
  target_window: Icc 0 (L_m i)
  coordinate: x = Real.log (lambda_m i * u)
  inverse_coordinate: u = Real.exp x / lambda_m i
  normalized_mode: (Real.sqrt (L_m i))^-1 * exp (2*pi*I*n*x/L_m i)
  inner_convention: conjugate_linear_first
  pointwise_inner_phase: r_minus_n
  forbidden_shortcuts:
    - replace dStar by volume or reverse the logarithmic orientation
    - alter either multiplicative-window endpoint
    - replace sqrt(L_m)^-1 by L_m^-1 or one
    - reverse r-n before integration
    - introduce an axiom, opaque proof, sorry, admit, exact?, or native_decide
    - prove projection reconstruction, raw/Gwin coordinates, residual crosswalk, decay, or SlotS2
    - edit D0KTrialStage1, Phase 4A, Phase 4B, Q3.Main, Goal 055, or create Bus 010
```

No convention may be repaired after a plant result inside this transaction.
Any genuine convention failure must close with the exact stop code and open a
new named review boundary.

## Exact production surface

1. `integral_comp_logWindow_dStar i F` states the exact equality
   ```text
   integral of F(log(lambda_m i * u)) under dStar.restrict(I_m i)
     = integral of F x over Icc 0 (L_m i).
   ```
2. `V_n_m_orthonormal i : Orthonormal C (V_n_m i)` uses the literal
   `V_n_m`, with no replacement family or named hypothesis.
3. The proof must expose the endpoint image, Jacobian, normalization, and
   conjugate-linear-first `r-n` phase before applying the finite exponential
   integral.

## Load-bearing plants

```yaml
P056L_1_DENSITY:
  mutation: replace dStar by volume
  expected: G6_S2_LOG_WINDOW_DENSITY_MISMATCH
P056L_2_LOG_ORIENTATION:
  mutation: replace log(lambda_m*u) by log(u/lambda_m)
  expected: G6_S2_LOG_WINDOW_ORIENTATION_MISMATCH
P056L_3_ENDPOINT_IMAGE:
  mutation: alter one source-window endpoint while retaining Icc 0 L_m
  expected: G6_S2_LOG_WINDOW_ENDPOINT_IMAGE_MISMATCH
P056L_4_NORMALIZATION:
  mutation: replace sqrt(L_m)^-1 by L_m^-1 or one
  expected: G6_S2_V_MODE_UNIT_NORM_MISMATCH
P056L_5_CONJUGATION:
  mutation: replace the private pointwise r-n phase by n-r
  expected: G6_S2_V_MODE_INNER_CONJUGATION_MISMATCH
```

All plants are temporary and must be removed after they fire. Validation
requires direct Lean, target/full build, `q3_check`, exact public-surface and
axiom inventories, proof-DB import, strict Spine, tests, three SQLite
integrity checks, `git diff --check`, and an exact status report.

## Boundary

This leaf may close only with
`G6_S2_D0_LOG_WINDOW_TRANSPORT_AND_V_MODES_ORTHONORMAL_PROVED`. Its sole next
consumer is the not-yet-authorized finite orthogonal-projection reconstruction
`coe_P_m_N_apply_eq_sum_inner_V_n_m_smul`. No residual crosswalk, compact-open
decay, strict `SlotS2`, route promotion, PX claim, or RH claim follows.
