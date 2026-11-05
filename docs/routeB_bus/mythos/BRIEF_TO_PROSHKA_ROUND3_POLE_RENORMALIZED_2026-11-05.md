# PROSHKA REQUEST — PROVE RH, ROUND 3: FROM YOUR POLE-RENORMALIZED IDENTITY (2026-11-05)

Firmware: docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md, blob 32a5337b8b3bd431126084f250baf73f86e8f749 (v3 text).

Branches:
- rh_clean: this file lives here; the commit is given in the owner's message.
- proshka_inbox_2026-10-31 @ e7be7f4121cdc1a9e1efd9aca74c3e3c4108d48f: write your verdict here as a NEW file.

This is a new request. Rounds 1 and 2 are closed and are not edited.

## GOAL

Prove the Riemann Hypothesis. The bottom line of your answer is RH.

## WHERE YOU STAND (your own results, pinned)

| Item | Commit | Path | Blob |
|---|---|---|---|
| Round-2 verdict. Fixed-order signed-current cost ≍_d sqrt(m)/(log m)^d for the UNRENORMALIZED phase. §8: exact pole renormalization (8.1)–(8.3), A_m[z] = (1/2π)∫[α_m+v_L]\|f̂\|² dt + J_−[f], J_− ≥ 0. Your next_decisive_test: SOURCE_EXACT_POLE_RENORMALIZED_OR_PHYSICAL_CONE_CERTIFICATE | proshka_inbox e7be7f4121cdc1a9e1efd9aca74c3e3c4108d48f (spec freeze 2c01918f5fb90189ed70fd96e9b87e76962d315c) | docs/routeB_bus/proshka/PROSHKA_VERDICT_SPEC_FIRST_BACKWARD_RH_V2_SIGNED_CURRENT_2026-11-05.md | 48d8010e4aa64c8bf28d58c1e523b06502a071b7 |
| Round-1 verdict. Positive operator envelope costs ≥ c·sqrt(m); RH-GAP; open representations (i), (ii) | proshka_inbox 3d3ba2e60785408063c9aee70657ee0a0cf0e1dc | docs/routeB_bus/proshka/PROSHKA_VERDICT_SPEC_FIRST_BACKWARD_RH_2026-11-05.md | 0fdb54e77c89357dd7595636e1d81e8061bfc5cf |
| Round-2 request (protocol and asset pointers) | rh_clean 198c68e645f9b14591ee658712325f2410d49af1 | docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_SPEC_FIRST_BACKWARD_RH_v2_2026-11-05.md | 55c072888bcf768439e3625d774be9d97a579e13 |
| Round-1 request (asset inventory, STEP 2) | rh_clean 6f8a92293c42a96ce73b0288a767313f098b4f69 | docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_SPEC_FIRST_BACKWARD_RH_2026-11-05.md | 13e29dcb53eb35bb863b5c4b2879e68566581a63 |

## THE TASK

Start from your exact identity (8.3). Same protocol as Rounds 1 and 2:

1. **Freeze a new specification S** for an object X such that "X with S exists ⇒ RH" is strictly proved. Commit S before any construction.
2. **Build X.**
3. **Chain down:** RH ⇐ N_1 ⇐ … ⇐ N_K, where N_K is a theorem.

The object and the method are your choice. Both of your named addresses are open to you:
- the pole-renormalized phase;
- the physical-cone / autocorrelation-weight certificate.

## ACCEPTANCE (fixed before you start)

1. **S lies outside every class already killed.** Give one paragraph per kill:
   - positive operator envelope — 3d3ba2e6 §7;
   - fixed-order bounded current on the unrenormalized phase — e7be7f41 §§3–5;
   - scalar-balanced Euler–Möbius square — 8e584bb8422073d077d80d4f88a2c8416973f49a, Theorem 1 (4.1);
   - SD in the DMV world — 3f0d43a921b5d76ac04b2c7012291e937dace231;
   - static Frobenius gluing — d558268a.
2. **No rewording.** If S rewords RH-GAP or any sufficient signed interface you have already named, that is NO_PROGRESS.
3. **Chain table.** For each N_k give:
   - the statement;
   - the proof of the arrow;
   - the asset used;
   - THEOREM / CONDITIONAL / CONJECTURE / FALSE;
   - whether it is equivalent to RH or strictly stronger.
4. **False-world check for every N_k (k ≥ 1).**
   - It must fail for Davenport–Heilbronn, DMV, and the planted quartet, each with its own source.
   - It must pass for the curve over 𝔽₃.
   - Name the excluding property and the step where it is used.
5. **Falsification test** for every N_k that is strictly stronger than RH: give the cheapest one. If numerics decide it, write the exact test for Codex, with the quantity, grid, precision, plant and pass/fail rule fixed in advance.
6. **Bottom of the chain**, one of:
   - (a) N_K is a theorem, so RH is proved;
   - (b) the lowest N_K reached, plus the exact missing arrow;
   - (c) a proof that this class of S cannot be built.

   All three are results.
