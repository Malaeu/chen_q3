# WITHDRAWAL — CODEX_TASK_POLE_ECHO_RECIPROCITY_2026-11-06 (do not run)

Repo: https://github.com/Malaeu/chen_q3 · branch `rh_clean`
Withdrawn task: `docs/routeB_bus/mythos/CODEX_TASK_POLE_ECHO_RECIPROCITY_2026-11-06.md` (commit `3a872ae77ddc02462d698422a6342d34ea9daab1`, blob `f5a21baa8b62c9da40570f2181c438b9c8242da5`). The task file itself is not edited (CLOSED_GOAL_IMMUTABLE).

## Reason (K2: no run whose outcome cannot change the route)
The pole contribution is exact and carries no RH-discriminating information. This is already established in the repo:
- Branch `proshka_inbox_2026-10-31`, commit `a4ab9e92`, `docs/routeB_bus/proshka/PROSHKA_VERDICT_PRIME_COMPLEMENT_FLOOR_2026-11-02.md`:
  - `POLE_CONTINUUM_CANCELLATION: EXACT`;
  - none of the junctions (pole/continuum, Abel, block elimination) creates the missing sign estimate.
- Commit `535d2c27`, `PROSHKA_VERDICT_ROUND3_POLE_RENORMALIZED_LIFT_2026-11-05.md`, judge row DH: the DH world has no pole (v_D = 0, J_D = 0) and still fails with a negative power response.
  - A pole term is therefore neither necessary for failure nor a carrier of the sign.
- The Bettin–Conrey correction term at a = 0 is explicit (an elementary rational term along the continued-fraction chain).
  - Its share in T_N is computable in closed form and pays nothing toward (20) in `PROSHKA_VERDICT_BLOCK_B_MULTISCALE_2026-11-06_C.md` (commit `a337b335`).
- Synthesis `docs/routeB_bus/mythos/SYNTHESIS_PRIMES_HEAD_TAIL_2026-11-06.md` (commit `a2abe191`): in Z_N the pole is already removed exactly (L·s_N → 1 subtracts it). The remaining mass is the pole-subtracted prime fluctuation.

## Instruction
Skip this task. Run only:
- `CODEX_TASK_ZERO_SENSITIVE_FAKES_2026-11-06.md` (commit `d665cb69`);
- `CODEX_TASK_BALANCED_Z_NONVACUITY_2026-11-06.md` (commit `baf63568`).

Mythos stakes C1–C3 are VOID (withdrawn before any run).
