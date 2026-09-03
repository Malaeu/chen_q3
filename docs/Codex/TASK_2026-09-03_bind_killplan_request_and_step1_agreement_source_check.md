# [→CODEX] TASK 2026-09-03 — Bind REQ-2026-09-03-KILLPLAN and run the Step 1.3 source check

```yaml
TASK_ID: MYTHOS_2026-09-03_KILLPLAN_BIND_AND_STEP1_3
AUTHOR: Mythos (Claude) via owner relay
REPO: Malaeu/chen_q3
BRANCH: rh_clean
SOURCE_BASE_COMMIT: 2bb8db37baf532b41a502269a2e2d420cb41ca6c
OWNER_AUTHORIZATION: per-action, this task only (R0.1); push authorized for these three files + queue entry only
CALL_CLASS_FOR_PROSHKA: DELEGATED_STRATEGIC_REVIEW
NO_LEAN_SOURCE: true
NO_NUMERICS: true
```

## Part A — bind the request (transport only, no math)

1. Place the two Mythos files exactly at:
   - `docs/routeB_bus/proshka/PROSHKA_REQUEST_MYTHOS_THREE_STAGE_FASTEST_KILL_PLAN_2026-09-03.txt`
   - `docs/routeB_bus/MYTHOS_STEP1_IDENTIFICATION_PAPER_NOTE_2026-09-03.md`
   Do not paraphrase. If the owner holds the ORIGINAL chat paste bytes that were
   sent to Proshka on 2026-09-03, prefer those bytes for the payload block and
   note the substitution in the commit body. Otherwise the Mythos reproduction
   is the registered text.
2. Fill `PHASE_ID:` with the live phase key ONLY if it differs from the one
   written; do not touch any other line. Ensure final LF.
3. Append to `docs/routeB_bus/PROSHKA_QUEUE.md`:
   ```
   ## REQ-2026-09-03-KILLPLAN · Mythos three-stage fastest-kill plan, paper adjudication · OPEN

   - `STATUS: OPEN`
   - Request: `docs/routeB_bus/proshka/PROSHKA_REQUEST_MYTHOS_THREE_STAGE_FASTEST_KILL_PLAN_2026-09-03.txt`
   - Boundary: `MYTHOS_THREE_STAGE_FASTEST_KILL_PLAN_PAPER_ADJUDICATION`
   - Call class: `DELEGATED_STRATEGIC_REVIEW`
   - Registered prediction: `P_STEP1_NO_UNIQUENESS p=0.75 (2026-09-02, PENDING)`
   - Request commit / bytes / lines / SHA-256 / Git blob / Final LF: <fill after commit>
   ```
4. Commit `[Linux-Codex][rh_clean][Proshka-bind] Bind REQ-2026-09-03-KILLPLAN`
   (canon + mirror in one commit if the bus mirror rule applies), then run
   `python3 orchestrator/workflow_runtime.py review-plan --attachment docs/routeB_bus/proshka/PROSHKA_REQUEST_MYTHOS_THREE_STAGE_FASTEST_KILL_PLAN_2026-09-03.txt --request-commit <commit> --request-id REQ-2026-09-03-KILLPLAN --boundary-id MYTHOS_THREE_STAGE_FASTEST_KILL_PLAN_PAPER_ADJUDICATION --expected-sha256 <sha256>`
   and paste the full result into the answer. Mythos indicative SHA-256 of the
   draft as delivered: `d662317312585319e3c4989a7096e1f1949eeb39dbf8ced755499368fe46e04d`
   (105 lines, 8445 bytes) — recompute after any header fill.
5. Deliver to Proshka in the living chat as the byte-exact .txt attachment with
   canonical short instruction:
   `Adjudicate REQ-2026-09-03-KILLPLAN (attached .txt is authoritative).`

## Part B — Step 1.3 source check (read-only, one hour)

Question: does `proposition59CCMTransform (ccmL m) N ξ_ℝ` carry any exact
agreement with `centeredXi` on a set with a limit point in `centeredCriticalStrip`?

Do:
1. `git grep -n "proposition59CCMTransform" FETCH_HEAD -- q3.lean.aristotle/Q3` and
   list the definition file, its inputs, and every theorem relating it to
   `centeredXi`, `xi`, `Xi`, `sourceLagrangePolynomial`, or interpolation nodes.
2. In arXiv:2511.22755 §Prop. 59 (and the ground-vector construction around it),
   record whether the transform is (a) an interpolant of ξ at nodes, (b) a
   moment-matched object, (c) an operator-defined object with no explicit
   equality to ξ. Cite page and equation numbers.
3. `git grep -n -i "eqOn_of_preconnected_of_frequently_eq\|AnalyticOn.*eqOn" FETCH_HEAD -- q3.lean.aristotle/Q3` and the Mathlib toolchain pinned in
   `q3.lean.aristotle/lake-manifest.json`; report the exact identity-theorem
   identifier available.

Answer file: `docs/routeB_bus/CODEX_ANSWER_2026-09-03_STEP1_3_P59_AGREEMENT_SET_SOURCE_CHECK.md`
with one of `AGREEMENT_SET_EXISTS: <set, lemma>` / `NO_AGREEMENT_SET: <reason>` /
`UNDETERMINED_FROM_SOURCE: <what is missing>`. Score
P_STEP1_3_NO_STRUCTURAL_AGREEMENT (p=0.65) honestly; no retroactive edit.

DO NOT: write Lean, run numerics, edit the roof, edit the request payload,
change phase key, promote the route, claim RH.
