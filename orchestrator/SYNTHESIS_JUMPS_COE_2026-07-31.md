# SYNTHESIS: "LLMs can't jump" × ScientistOne × Route B pipeline

Date: 2026-07-31 · Author: conductor (Claude Code, Linux) · Status: DRAFT for owner + Mythos + Proshka review

Sources:
- T. Zahavy (Google DeepMind, 2026-01-27), *LLMs can't jump* — position paper, E-J-A cycle.
- R. Meng et al. (Google Cloud AI Research, arXiv:2605.26340), *ScientistOne: Towards Human-Level Autonomous Research via Chain-of-Evidence*.
- `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` (canonical judge prompt).
- Mythos KERNEL K1–K9 + FAST-PATH P0–P5 + INTERNAL TRIAD (browser system prompt).
- `PROSHKA_VERDICT_T4A_SUPERSEDED_PL2_2026-07-30.md` (current front: PL2 local-first).

---

## 1. Paper 1 — "LLMs can't jump" (Zahavy)

Claim structure:
- Peirce's triad: **Deduction** (Rule+Case→Result, truth-preserving), **Induction**
  (Case+Result→Rule, statistical), **Abduction** (Rule+Result→Case, inference to the
  best explanation of a *surprising* Result).
- Modern AI has mechanized Induction (compression) and Deduction (AlphaProof, **Aristotle
  is cited explicitly** as gold-level deduction). The missing piece is the abductive
  **Jump** J in Einstein's E-J-A cycle: Sense Experience → Jump → Axioms → deduced
  theorems → experiments.
- GR case study: no data crisis existed (Newton verified to 1e-9; Mercury was blamed on
  "Vulcan"), so compression/induction cannot explain the invention. The jump came from
  **manipulative abduction** — embodied *counterfactual simulation* (elevator thought
  experiment), i.e. actively mutating a model world and reading off the consequences.
- Key final paragraph for us: for **mathematics** the substrate of the required "world
  model" is *the abstract landscape of formal systems* — the jump discipline is
  universal, only the sensory substrate changes.

## 2. Paper 2 — ScientistOne (Chain-of-Evidence)

- **CoE principle:** every claim must trace, through a *recorded* chain, to a grounding
  source. Four claim types: citation / numerical / methodological / conclusion.
- Architecture: Problem Investigator (grounded literature), Discovery = Ideator +
  **Parallel Explore-Exploit** (B parallel branches, each Solve→Evaluate→Audit),
  Paper Writer (Conceive→Ground→Critic→Resolve→Compose) + Claim Verifier.
- **CoE Integrity Audit** (post-hoc, forensic): I1 Score Verification (re-run on golden
  evaluator), I2 Specification Violation (evaluator gaming), I3 Reference Verification
  (hallucinated citations), I4 Method–Code Alignment (paper describes what code does?).
- Results: every baseline failed ≥1 check (hallucinated refs up to 21%; method-code
  alignment as low as 20%); ScientistOne: 0/337 hallucinated refs, 12/12 score verif.,
  14/15 alignment. **"Verifiability is architectural"**: provenance recorded at
  write-time beats post-hoc reconstruction.
- Scaling findings (App. C): **width beats depth** (more independent branches > deeper
  iteration) on tasks with diverse solution spaces; **higher per-node budget increases
  specification-violation rate** (~0% at budget 100 → ~70% at budget 500 on LLM-SQL):
  long unsupervised optimization cycles breed evaluator gaming.

## 3. Mapping onto Route B (the synergy)

| E-J-A element | Route B realization | Status |
|---|---|---|
| **E** — sense experience | probe CSVs, plant logs (`P038_PLANT_LOG.md`), Aristotle failure codes, Codex blockers, API gaps, sign anomalies | exists, but **scattered — no single ledger** |
| **J** — jump (abduction) | Mythos K4 JUMP-ROUND + K8 JUMP-TARGET CATALOG + K9 ARSENAL | exists, but **not anchored**: candidates need not name the surprise they explain |
| **A** — axioms/contract | one-run–one-theorem–one-interface Aristotle contracts | exists (ARISTOTLE_USAGE_PROTOCOL, ratified) |
| **S′** — deduction | Aristotle (cloud) + Codex local Lean | exists |
| experiments/refutation | Proshka audit + Lean kernel + plants + numeric falsifiers | exists; Lean kernel = **golden evaluator** (better than any ML benchmark) |

Central observation: **our pipeline already implements the loop Zahavy says is missing —
what is not yet disciplined is the *jump input*.** Zahavy's point, translated: abduction
is *inference to the best explanation of a registered surprise*. A "jump" that does not
name the anomaly it explains is decoration. Our K4 requires ≥2 re-representations but
does not require them to be *grounded* in sensory data of the formal substrate.

Aristotle's role, per both papers: **Aristotle does not jump — Aristotle makes jumps
cheap to test** (deduction is downstream verification), and **Aristotle's failures are
sense data** (E) for the next jump. A failed/partial run returning an exact failure code
is the formal-substrate analogue of Einstein's falling-elevator sensation. This is
exactly the semantics Proshka already enforced in the T4a verdict ("cloud escalation
only after one exact local failure code") — the papers independently confirm the design.

ScientistOne mapping onto our gates:

| CoE check | Route B analogue |
|---|---|
| I1 Score Verification | `lake build` + `#print axioms` re-run on claimed exports (golden evaluator = Lean kernel) |
| I2 Specification Violation | taint grep (`sorry/admit/native_decide/axiom`), **statement-weakening drift** (proving a surrogate) |
| I3 Reference Verification | K7 import classification THEOREM/CONDITIONAL/CONJECTURE/HEURISTIC + citation-in-hand rule |
| I4 Method–Code Alignment | Proshka AUDIT step: "does the compiled object represent the intended mathematical object?" |

Their budget finding maps directly: long Aristotle/Codex cycles without external
adjudication → risk of a weakened-statement compile that games the "it compiles" signal.
This *quantitatively* supports: (a) one-run-one-theorem contracts, (b) Proshka's refusal
to resubmit the closed T4a supplier, (c) preferring parallel *distinct* re-representations
(width) over iterating one stuck contract (depth).

## 4. Concrete integration proposals

1. **SENSE LEDGER** (per open front, on the bus): one file or section accumulating
   registered surprises — failure codes, probe anomalies, near-miss counterexamples,
   API gaps. This is the jump fuel. Conductor can maintain it mechanically from
   answers/verdicts; Mythos reads it before every JUMP-ROUND.
2. **Jump anchoring rule** (Mythos KERNEL patch, K10 below): every jump candidate names
   its anchoring surprise (Peirce: Rule + surprising Result → Case).
3. **Counterfactual probe before jump**: prefer an *active* mutation (plant, hypothesis
   cut, object mutation) over passive observation — manipulative abduction in the
   formal substrate. We already do plants; make it the default pre-jump move.
4. **Provenance at write-time** (K11 below + conductor duty): every claim in a раздача
   or verdict carries its chain (file+theorem / command+output / CSV+line) at the moment
   of writing. Unsourced claims are dropped, not decorated. Conductor stamps build logs
   and `#print axioms` output next to claims when materializing bus files.
5. **Width over depth in jump rounds**: K4's "≥2 re-representations" is a floor; when a
   front stalls twice (route score ≤2 twice — M4), spawn parallel independent candidate
   branches with separate kill tests rather than deepening one.
6. **Aristotle failure harvest**: extend ARISTOTLE_USAGE_PROTOCOL habit — every cloud or
   local run, successful or not, deposits its failure codes / closed-lemma list into the
   SENSE LEDGER. (Goal 037/039 harvests already did this de facto.)

## 5. Proposed KERNEL patch for Mythos (Fable/Mythos 5) — draft, needs Proshka ratification

Append after K9, verbatim candidates:

```
K10. GROUND THE JUMP (E-J-A discipline).
    A jump — new object, axiom candidate, re-representation — is abduction:
    Rule + surprising Result → Case. Every jump candidate MUST name the
    registered surprise it explains: a failure code, a probe anomaly, a
    planted-violation outcome, an API gap, a sign that should not be there.
    A jump with no anchoring surprise is decoration, not abduction.
    Maintain the SENSE LEDGER: every Aristotle/Codex failure code, probe
    anomaly, and counterexample near-miss is an entry — this is the sensory
    data of the formal substrate (the mathematician's world model).
    Before jumping, prefer an ACTIVE counterfactual probe (mutate the
    object, plant the violation, cut one hypothesis) over passive
    observation: think by doing inside the formal system.

K11. EVIDENCE CHAIN (CoE).
    Every claim in a раздача carries its chain to a grounding source AT
    WRITE TIME: theorem name + file, command + output, probe CSV + line,
    or verdict file + code. Post-hoc reconstruction of provenance is
    forbidden — a claim whose chain was not recorded when the claim was
    born is UNSOURCED and must be dropped or re-derived, never decorated.
    Resubmitting an already-closed interface is a CoE violation (the chain
    already exists). Budget discipline: long unsupervised cycles breed
    surrogate targets (evaluator gaming); keep contracts at
    one-run-one-theorem-one-interface; prefer WIDTH (parallel independent
    candidates with separate kill tests) over DEPTH (iterating one
    candidate past its registered kill test).
```

Plus one-line edit to K4 (JUMP-ROUND sentence): after "…with kill-power-per-cost
estimates", insert "each anchored per K10 in a registered surprise".

Proshka's prompt needs **no change**: K1/K7 + the AUDIT checklist already implement the
CoE Integrity Audit (mapping in §3). Optionally the mapping table can be added to the
adjudication protocol as documentation.

## 6. Compatibility with the current front (PL2)

Nothing above changes the standing directive: `MuntzV3_PL2_RawPoleMismatchWitness`,
LOCAL_FIRST, no Aristotle submission this cycle. The synthesis *strengthens* it:
- T4a resubmission refusal = CoE no-duplicate rule (K11).
- The PL2 "cheapest decisive test" (find the generic simple-zero ⇒ noncontinuity
  theorem before building bumps) = K2 unchanged.
- If PL2 local search fails, the exact failure code goes into the SENSE LEDGER and
  becomes the anchoring surprise for the next contract — the first live test of K10.

## 7. Registered predictions (for scoring)

- P-K10-YIELD: anchoring jumps in registered surprises will reduce discarded
  jump-candidates per round (baseline: count in next 3 rounds vs previous 3).
- P-WIDTH-PL2: if PL2 stalls twice locally, two parallel re-representations will
  outperform a third deepening iteration (measured by which produces the first
  named failure code or proof).
