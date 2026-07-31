# Goal 045 — MuntzV3 Supplier hRp via R6Export (registered path 043→044 continued)

ISSUED: 2026-07-31, Mythos (contour in dispatch answer; transcribed by conductor-CLI
  on owner's order; source-lock added from R6Export)
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched
PARENT: Goal 044 (export closure already contains the supplier theorem).

## Consumer (exact T5 input type, Main.lean:159)

```lean
hRp : AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane
```

## Supplier (source-locked, ALREADY EXPORTED in 044)

RequestProject.R6Export.TailAnalyticity (bus copy:
docs/routeB_bus/muntz_v3/RequestProject/R6Export/TailAnalyticity.lean:16):

```lean
theorem Rplus_differentiable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (Rplus h Λ)
```

NOTE: conclusion is GLOBAL differentiability (entire) — no mass hypothesis, no
half-plane restriction. P045-2 (no domain bridge needed) is already supported by
the signature; the wrapper passage is Differentiable → AnalyticOnNhd on any set
(name the exact Mathlib lemma, e.g. Differentiable.analyticOnNhd-class API).

## PHASE 0-lite

Confirm the exported signature above compiles as read (it is in the 044 closure);
record the exact Mathlib passage lemma. No inventory diff needed — same objects
as 044 by construction.

## PHASE 1

Wrapper in a NEW file (pattern of MuntzV3R6HrmWrapper.lean):

```lean
theorem rplus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane
```

Hypothesis list = exactly the R6 list (note: NO hmass — do not add it).

## Honesty clause

Same as 044: discharge is UNDER R6 HYPOTHESES; WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
remains OPEN and is restated in the answer (do not repair here).

## Forbidden

frozen files; muntz_r6/; edits inside R6Export/ (it is a sealed certificate);
reproving R6 content; taint; bundling hG/habs; promotion; Aristotle.

## Validation

```text
lake build (v3, includes wrapper)
grep taint on new file
#print axioms rplus_analyticOnNhd_shiftedHalfPlane
axioms exactly [propext, Classical.choice, Quot.sound]
```

## Success code

HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES

## Failure codes (exactly one, fail-closed)

R6_RPLUS_DOMAIN_MISMATCH
LEAN_BUILD_FAIL

## Registered predictions

P045-1 (Mythos): wrapper ≤ 40 lines, zero new analysis.
P045-2 (Mythos): no domain bridge needed (Rplus wider than the half-plane) —
  pre-supported by the entire-conclusion signature.

## Answer requirements

045_muntz_v3_supplier_hrp.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG;
scoring P045-1..2; goal consumed by SHA-256; WITNESS_CLASS gap restated; one
non-promoting state row; ROUTE_B_STATE last; canon+mirror one transaction.
