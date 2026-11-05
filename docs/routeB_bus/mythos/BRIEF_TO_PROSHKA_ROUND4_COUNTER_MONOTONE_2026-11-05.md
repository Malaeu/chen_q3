# PROSHKA REQUEST — PROVE RH, ROUND 4: THE WINDOW ZERO COUNTER MUST NOT RUN BACKWARDS (2026-11-05)

**Repository:** https://github.com/Malaeu/chen_q3

**Branches:**
- `rh_clean` — this file lives here; the commit is given in the owner's message.
- `proshka_inbox_2026-10-31` @ 535d2c272bed0a0331359a9d6a7ade1362976168 — write your verdict here as a NEW file.

**Firmware:** docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md, blob 32a5337b8b3bd431126084f250baf73f86e8f749.

Rounds 1–3 are closed and are not edited.

## GOAL

Prove the Riemann Hypothesis. The bottom line of your answer is RH.

## WHERE YOU STAND (pinned)

| Item | Commit | Path | Blob |
|---|---|---|---|
| Your Round 3 | proshka_inbox 535d2c272bed0a0331359a9d6a7ade1362976168 | docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND3_POLE_RENORMALIZED_LIFT_2026-11-05.md | 8d548cb18e312ae16a087542b1eedba6c00675ea |
| Owner addendum: September proved sign + September kill list | rh_clean 404f5710cc4186f94b41a58da173787c0b8b2270 | docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND3_ADDENDUM_SEPT_SIGN_2026-11-05.md | d70d373e37b6183903a0ae321312ddf36ce61aaf |
| Codex: Q3 NB–BD audit recovered; NB–BD L² squares lie OUTSIDE the class of 8e584bb8 Thm 1; target capture and decay not proved | rh_clean a40be756 | docs/routeB_bus/NB_BD_LIFT_2026-11-05.md | 40ddadc20cfbd6f2d8104c9a16b1222882f1a6ad |
| October entropy / NOESCAPE first pass | rh_clean | docs/routeB_bus/proshka/ENTROPY_NOESCAPE_FIRST_PASS_2026-10-30.md | a29cc023db1a1d79a5cbb774b5575661eff5d3dd |
| Your one-prime increment (remainder ≤ 10/p) | proshka_inbox 616619f2ae25a6963f173854aa49267a29ef0101 | docs/routeB_bus/proshka/PROSHKA_VERDICT_PROVE_RH_2026-11-05.md | 3d122971460f97fe6df519e953b8ee728678243b |

Round 3 result: RH ⇐ Δ_m ≤ C(1+log m)^r, where Δ_m is the maximal drawdown of F_m. Unconditionally only Δ_m ≲ √m/log m is known.

## THE OWNER'S PRACTICAL IDEAS (ideas, not orders — use, refute, or ignore)

### Idea 1. Your F_m is the window version of the zero-counting function N(t)

Compare your (3.3) with Riemann–von Mangoldt:

  F_m(t) = θ(t)/π + (C_L(t) − P_m(t))/π
  N(t) = θ(t)/π + 1 + S(t),  S(t) = (1/π) arg ζ(1/2+it)

- θ/π matches literally.
- −P_m/π is the truncated formal Euler expression for S(t).
- C_L/π is the pole regularization.

Mythos DIAG (not a proof; m ≤ 10⁵, t ≤ 60): F_m tracks N(t) − ½ within ±1, with unit steps exactly at the zero ordinates 14.13, 21.02, 25.01, … . The drawdown on t ≤ 60 is ≈ 0.57–0.58 for m = 10³, 10⁴, 10⁵ and does not grow.

So your S_B3 reads: **the window zero counter never runs backwards by more than polylog(m).** A true counter never runs backwards; an off-line zero makes a truncated counter run back by ~m^δ.

Check this identification. Then check whether the classical theory of S(t) is directly usable here: Selberg's truncated formula for S(t) and the known unconditional and conditional bounds. Classify each import as THEOREM / CONDITIONAL.

### Idea 2. Perelman: monotonicity whose derivative is a square

Perelman's monotone quantities are monotone because their derivative along the flow is an integral of a square. Look for a flow parameter and a functional W such that:
- dW/d(flow) is manifestly ≥ 0 (a square, or at least a summable error);
- W controls Δ_m.

Candidate flows, all already in the repo:
- **(a) Damping / σ-flow.** At σ = 1 the September object SCATTERING_POISSON (addendum §2) has phase P > 0, so its antiderivative is MONOTONE: a proved drawdown 0. At σ = 1/2 sits your F_m. Lagarias (Acta Arith. 1999, cited from memory — verify): RH ⇔ Re ξ′/ξ > 0 on Re s > 1/2. In counter language: monotonicity survives the de-blurring from σ = 1 down to σ = 1/2. Inside a window of length L = log m, the shift σ = 1/2 + c/log m changes weights only by a bounded factor.
- **(b) m-flow.** Add primes one by one, using your exact one-prime increment (616619f2).
- **(c) de Bruijn–Newman heat flow.** The zero dynamics used by Rodgers–Tao (a no-collapse-type argument).

The October NOESCAPE / entropy work is the earlier Perelman attempt (above). Reuse whatever survives from it.

## THE TASK

Same protocol as Rounds 1–3:
1. Freeze a new specification S. Commit it before any construction.
2. Build X.
3. Chain down: RH ⇐ N_1 ⇐ … ⇐ N_K, where N_K is a theorem.

The object and the method are your choice.

## ACCEPTANCE (fixed before you start)

1. **S lies outside every killed class**, with one paragraph per kill:
   - 3d3ba2e6 §7;
   - e7be7f41 §§3–5;
   - 8e584bb8 Thm 1;
   - 3f0d43a9;
   - d558268a;
   - the September kills in the addendum, §1.
2. **No relabelling.** A restatement of N2 from Round 3 (Δ_m ≤ polylog) under a new name, with no new independent inequality, is NO_PROGRESS.
3. **Chain table.** For each N_k give:
   - the statement;
   - the proof of the arrow;
   - the asset used;
   - THEOREM / CONDITIONAL / CONJECTURE / FALSE;
   - whether it is equivalent to RH or strictly stronger.
4. **False worlds.**
   - Every N_k (k ≥ 1) must fail for DH, DMV and the planted quartet, each with its own source.
   - It must pass for the curve over 𝔽₃.
   - Name the excluding property and the step where it is used.
5. **Falsifier.** For every N_k strictly stronger than RH, give the cheapest falsifier. If numerics decide it, write the exact Codex test — quantity, grid, precision, plant, pass/fail rule — fixed in advance. Example: Δ_m over larger t-ranges.
6. **Bottom of the chain**, one of:
   - (a) RH proved;
   - (b) the lowest N_K reached plus the exact missing arrow;
   - (c) a proof that this class of S cannot be built.

   All three are results.
