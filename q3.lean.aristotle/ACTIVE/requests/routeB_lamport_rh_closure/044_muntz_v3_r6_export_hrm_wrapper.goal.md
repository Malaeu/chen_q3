# Goal 044 — R6 certificate export under unique module name + hRm consumer wrapper

ISSUED: 2026-07-31 · Contour: Codex's named next move in 043.answer (fail-closed
  LEAN_BUILD_FAIL / DOMAIN_BRIDGE_NEEDED); transcribed by conductor-CLI on owner's
  order. Mythos ratification: post-hoc via packet 4 (this goal follows the exact
  failure-code escalation path registered in Goal 043; no new mathematics is chosen
  here, only the infrastructure repair the code names).
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen files untouched
PARENT: Goal 043 (immutable, closed fail-closed; its PHASE 0 findings are inputs here).

## Inherited PHASE 0 facts (from 043.answer, not re-derived)

- Estar and Rminus definitions are byte-identical between v3 and R6.
- Half-planes are propositionally equal; a small domain bridge is needed.
- DifferentiableOn → AnalyticOnNhd passes via `.analyticOnNhd` (open set).
- R6 hypotheses to be carried EXACTLY: global `LipschitzWith K h` and support in
  `Icc a b` with `0 < a` (support away from zero). The v3 witness class does NOT
  supply these — that mismatch is REPORTED, not repaired here (see Honesty clause).

## Task

PHASE A — EXPORT: copy the R6 certificate into muntz_v3/RequestProject/ under a
unique module namespace (e.g. `RequestProject.R6Export.TailAnalyticity`; naming free
but must not collide with any existing module in either project):
- dependency closure included (TailAnalyticity imports RequestProject.WindowAnalyticity;
  enumerate and export the full transitive closure needed);
- import lines renamed to the new namespace; proof bodies byte-preserved;
- each exported file carries a provenance header: source path + source SHA-256 +
  "exported verbatim, imports renamed only" + date;
- no statement changes, no proof changes, no reproving.

PHASE B — WRAPPER: in a NEW file, prove the consumer-shaped theorem

```lean
theorem rminus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane
```

via: exported R6 theorem → domain bridge (propositional equality of the half-planes)
→ `.analyticOnNhd`. Hypothesis list = exactly the R6 list, no weakening, no silent
strengthening of the consumer.

## Honesty clause (binding for the answer)

Discharging hRm UNDER R6 HYPOTHESES does not yet connect to the PL1/PL2 witness
class (their supports touch zero; Lipschitz is OnWith). The answer MUST state this
remaining obligation explicitly as a named open interface
(WITNESS_CLASS_VS_R6_HYPOTHESES_GAP) — deciding what to do with it belongs to the
Mythos/Proshka cycle, not to this goal.

## Forbidden

- modifying frozen files; modifying anything inside muntz_r6/;
- statement or proof changes in exported content (imports-line renames only);
- reproving R6 content from scratch;
- taint (sorry | admit | axiom | native_decide | exact?);
- any promotion; no Aristotle.

## Validation

```text
lake build            (v3 project, must include the export and the wrapper)
grep taint terms on all new files
#print axioms rminus_analyticOnNhd_shiftedHalfPlane
axioms exactly [propext, Classical.choice, Quot.sound]
diff each exported file against its R6 source modulo the import/namespace lines
  (report the exact diff in the answer — it must touch ONLY import/namespace lines)
```

## Success code

HRM_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES

## Failure codes (exactly one, fail-closed)

R6_DEP_CLOSURE_TOO_LARGE(enumerated)
MODULE_RENAME_BREAKS_PROOF(file, line)
DOMAIN_BRIDGE_FAIL
LEAN_BUILD_FAIL

## Registered predictions

P044-C1 (conductor): dependency closure ≤ 3 files; wrapper ≤ 40 lines; the whole
  goal closes in one Codex session with no new mathematics.
P044-C2 (conductor): the export diff is import-lines-only for every file (no proof
  body edits forced by the rename).

## Answer requirements

044_muntz_v3_r6_export_hrm_wrapper.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS
LOG; PHASE A file list with source/export SHA-256 pairs; the exact export diffs;
WITNESS_CLASS_VS_R6_HYPOTHESES_GAP stated; scoring P044-C1..C2; goal consumed by
SHA-256; one non-promoting state row; ROUTE_B_STATE last; canon+mirror one
transaction; report — do not repair — divergences.
