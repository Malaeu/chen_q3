# Proshka request: prime_heat bucket q-sum kernel closure (checker-free)

## Read first (mandatory)

Load this context before analysis:
- `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_context_pack_2026_03_03.md`

Role reminder:
- You are Proshka, elite mathematician + Lean engineer.
- Work deterministically: no speculation, no ambiguous output.

## Goal (single)

Close this theorem without checker/native_decide route:

```lean
theorem prime_heat_bucket_pp_sum_ub_q_le_kernel_target :
    ∀ k : Fin prime_heat_bucket_count,
      Full.prime_heat_bucket_pp_sum_ub_q k ≤ prime_heat_bucket_ub_q_get k := by
  ...
```

Exact target file:
- `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/prime_heat_bucket_pp_sum_ub_q_le_kernel_target.lean`

## Current status

- There is an integrated draft proof from Aristotle that compiles but is not final kernel-safe
  for load-bearing use because it uses `native_decide + revert`.
- Draft location:
  `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/ACTIVE/aristotle/queue/manual_prime_heat_bucket_pp_sum_ub_q_le_kernel/TARGET.lean`

## Where symbols are defined

- `Full.prime_heat_bucket_pp_sum_ub_q`:
  `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketCheck.lean`
- `prime_heat_bucket_ub_q_get`:
  `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Intervals.lean`
- Precomputed bucket-sum constants:
  `Full.prime_heat_pp_term_ub_q_sum_bucket_0 ... _99` in
  `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowFull.lean`
- Existing per-bucket inequalities:
  `prime_heat_pp_term_ub_q_sum_bucket_le_0 ... _99` in
  `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PpSumBounds.lean`

## Existing non-kernel route to replace

Legacy checker lemma:

```lean
lemma prime_heat_bucket_pp_sum_ub_q_le (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_pp_sum_ub_q k ≤ prime_heat_bucket_ub_q_get k := by
  classical
  fin_cases k <;> native_decide
```

File:
- `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`

## Reproduced bottleneck

- Direct definitional unfolding (`simp`/`dsimp`) of
  `Full.prime_heat_bucket_pp_sum_ub_q` times out (`isDefEq`) even for `k=0`.
- So brute-force unfolding is not viable.

## Hard constraints

1. No `native_decide`, no `admit`, no `sorry`, no `exact?`.
2. Keep decimal constants exactly as in source files.
3. Numeric policy: certification scale up to 15 digits after decimal.
4. Keep proof checker-free in load-bearing chain.
5. Do not import the heavy checker file as a proof dependency for the final theorem.

## Requested output

Provide one of:

1) complete Lean proof for the target theorem, or
2) minimal theorem decomposition with exact Lean statements and proof sketches.

If decomposition:

- **A. Bridge lemma** from `Full.prime_heat_bucket_pp_sum_ub_q k`
  to a manageable accessor/form over `Fin 100`.
- **B. Bound-transfer lemmas** using existing
  `prime_heat_pp_term_ub_q_sum_bucket_le_i` facts.
- **C. Final `∀ k` assembly** without `native_decide`.

## Suggested strategy

- Build a lightweight accessor for bucket q-sums.
- Prove accessor ≤ `prime_heat_bucket_ub_q_get` with existing per-bucket lemmas.
- Prove bridge from `Full.prime_heat_bucket_pp_sum_ub_q` to accessor
  without giant definitional unfolding.
- Compose.

## Acceptance criteria (must pass)

1. `lake env lean /mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/prime_heat_bucket_pp_sum_ub_q_le_kernel_target.lean`
2. `rg -n "native_decide|admit|sorry|exact\\?" /mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/prime_heat_bucket_pp_sum_ub_q_le_kernel_target.lean`
   should return no proof-hole/non-kernel placeholders in final route.

## Non-goals in this request

- Do not solve arch-integral axiom removal here.
- Do not alter certificate constants.
- Do not switch to checker-backed proof route.
