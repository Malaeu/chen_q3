# PROSHKA REQUEST — PROVE RH, ROUND 2 OF SPEC-FIRST BACKWARD (2026-11-05)

Firmware: docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md, blob 32a5337b8b3bd431126084f250baf73f86e8f749 (v3 text).

Branches:
- rh_clean: this file lives here (commit given in the owner's message).
- proshka_inbox_2026-10-31 @ 3d3ba2e60785408063c9aee70657ee0a0cf0e1dc: write your verdict here, new file.

This is a new request. It does not edit round 1 (CLOSED_GOAL_IMMUTABLE).

## GOAL

Prove the Riemann Hypothesis. The bottom line of your answer is RH.

## WHERE YOU STAND (your own results, pinned)

| Item | Commit | Path | Blob |
|---|---|---|---|
| Round-1 request | rh_clean 6f8a92293c42a96ce73b0288a767313f098b4f69 | docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_SPEC_FIRST_BACKWARD_RH_2026-11-05.md | 13e29dcb53eb35bb863b5c4b2879e68566581a63 |
| Round-1 verdict, KILL (c): any positive operator majorant of −K_m costs ≥ c·sqrt(m) (PNT only); RH-GAP stated; open representations (i) and (ii) in §9 | proshka_inbox 3d3ba2e60785408063c9aee70657ee0a0cf0e1dc | docs/routeB_bus/proshka/PROSHKA_VERDICT_SPEC_FIRST_BACKWARD_RH_2026-11-05.md | 0fdb54e77c89357dd7595636e1d81e8061bfc5cf |
| Coupled one-prime increment; J_m (18) | proshka_inbox 616619f2ae25a6963f173854aa49267a29ef0101 | docs/routeB_bus/proshka/PROSHKA_VERDICT_PROVE_RH_2026-11-05.md | 3d122971460f97fe6df519e953b8ee728678243b |
| Gaussian response, growth m^(Theta/2) | proshka_inbox 62f782316d2ba4f83d27db82d0b64e1e8361cad2 | docs/routeB_bus/proshka/PROSHKA_VERDICT_PROVE_RH_2026-11-05.md | 2b5e02a0aa816da34c204f2a56a9033e6ac6b542 |
| Normalization of (7.4)/(10) confirmed numerically: 20/20 PASS, 20/20 plants FAIL | rh_clean 39c788f2d8cb80f8b870688c5c1693e559d6b9d3 | docs/routeB_bus/prove_rh_response_audit_2026-11-05/task_a_rerun/RESULT.md | 74601eb1bd6fea0938ea6f607a16dded54c46412 |

The asset inventory is in the Round-1 request, STEP 2. It is still valid. Your Round-1 verdict adds Lemmas 1–3 and the fixed radical return (7.1)–(7.6).

## THE TASK

Same protocol as Round 1:

1. **Freeze a new specification S** of an imaginary object X such that "X with S exists ⇒ RH" is strictly proved.
   - Commit S before any construction.
   - S must be checkable without RH.
2. **Build X** from the project's own material.
3. **Chain down:** RH ⇐ N_1 = "X with S exists" ⇐ … ⇐ N_K, where N_K is a theorem.

The object, its type, and the method are your choice.

## ACCEPTANCE (fixed before you start)

1. **S lies outside every class already killed.** For each kill below, state in one paragraph why S is not in that class:
   - positive operator envelope — 3d3ba2e6 §7;
   - scalar-balanced Euler–Möbius square — 8e584bb8422073d077d80d4f88a2c8416973f49a, docs/routeB_bus/proshka/PROSHKA_VERDICT_CCM_ARITHMETIC_COMPENSATION_2026-11-04.md, Theorem 1 (4.1), on proshka_inbox;
   - SD in the DMV world — 3f0d43a921b5d76ac04b2c7012291e937dace231;
   - static Frobenius gluing — d558268a.
2. **S is not a rewording of RH-GAP** or of any sufficient signed interface you have already named. A rewording is NO_PROGRESS.
3. **Chain table as in Round 1.** For each N_k give:
   - the statement;
   - the proof of the arrow;
   - the asset used;
   - THEOREM / CONDITIONAL / CONJECTURE / FALSE;
   - whether it is equivalent to RH or strictly stronger.
4. **False-world check for every N_k (k ≥ 1):**
   - Davenport–Heilbronn, DMV and the planted quartet: N_k must fail in each.
   - The function-field curve: N_k must pass.
   - Name the excluding property and the step where it is used.
5. **Falsification test** for every N_k that is strictly stronger than RH, the cheapest one available. If numerics decide it, write the test for Codex.
6. **Bottom of the chain**, one of:
   - (a) N_K is a theorem, so RH is proved;
   - (b) the lowest N_K reached plus the exact missing arrow;
   - (c) a proof that this class of S cannot be built.

   All three are results.
