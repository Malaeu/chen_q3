# Goal 043 — MuntzV3 Supplier hRm: Rminus analyticity on shiftedHalfPlane

ISSUED: 2026-07-31, Mythos (dispatch answer to packet 2; transcribed by conductor-CLI
  on owner's order, source-lock verified against Main.lean and muntz_r6)
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen files untouched
ORIGIN: Mythos K2 ranking — of the four retained inputs (hG/hRm/hRp/habs), hRm is the
  only one whose proof already exists in the repo (RULE_INVENTORY_FIRST applied to
  dispatch itself). Parallel non-Lean track (Mythos cycle, not this goal): promotion
  card — which mainline node an unconditional T5 would close.

## Consumer (exact T5 input type, source-locked)

docs/routeB_bus/muntz_v3/RequestProject/Main.lean:157
(continued_window_identity_of_analytic hypothesis):

```lean
hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane
```

Target theorem (new file, name binding):

```lean
theorem rminus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (Λ : ℝ) (…hypotheses per PHASE 0 inventory…) :
    AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane
```

Hypothesis set is NOT prescribed here: it is the OUTPUT of PHASE 0 (whatever the R6
supplier needs, translated to the v3 objects; no silent strengthening beyond what R6
actually uses; every hypothesis named in the answer).

## Supplier candidate (inventory anchor)

docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean:

```lean
theorem Rminus_differentiableOn_halfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    DifferentiableOn ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re}
```

## PHASE 0 (mandatory, before any promise)

Inventory diff between supplier and consumer. Answer MUST resolve, each with a
one-line verdict:

1. Same `Rminus` object? (v3 Main.lean def vs muntz_r6 def — byte-compare the
   definitions and their `Estar` dependencies.)
2. Same half-plane? (`shiftedHalfPlane` vs `{s : ℂ | -(1:ℝ)/2 < s.re}` — definitional
   or bridge needed.)
3. `DifferentiableOn` → `AnalyticOnNhd` passage (openness of the half-plane +
   Mathlib `DifferentiableOn.analyticOnNhd`-class API — name the exact lemma).
4. Hypothesis set on h / Estar / Λ: R6 uses GLOBAL `LipschitzWith` — record whether
   the consumer context can supply it or a bridge from the v3 hypothesis class is
   required (report, do not silently strengthen).

PHASE 0 output is exactly one of:

```text
CONSUMPTION_WRAPPER          (all four resolve; proceed to PHASE 1)
DOMAIN_BRIDGE_NEEDED         (name the exact bridge lemma to prove)
R6_OBJECT_MISMATCH           (exact diff of the two Rminus/Estar definitions)
```

## PHASE 1

Wrapper (or the minimal named bridge) in a NEW file inside muntz_v3/RequestProject/.
Reuse R6 — do NOT reprove its content.

## Forbidden

- modifying frozen files (Main.lean, MellinCompactSupportAnalyticity.lean);
- reproving R6 content;
- numerical integration;
- taint (sorry | admit | axiom | native_decide | exact?);
- three-input bundle (hG/hRp/habs are SEPARATE future contracts);
- any Route B / RH status promotion.

## Validation

```text
lake env lean <touched-file>
lake build
grep taint terms
#print axioms rminus_analyticOnNhd_shiftedHalfPlane
axioms must be exactly [propext, Classical.choice, Quot.sound]
```

## Success code

HRM_SUPPLIER_DISCHARGED

## Failure codes (exactly one, fail-closed)

R6_DOMAIN_MISMATCH
R6_HYPOTHESIS_GAP(named)
ESTAR_BOUND_GAP(named edge)
LEAN_BUILD_FAIL

## Registered predictions (before execution)

P043-M1 (Mythos): wrapper ≤ 80 lines, no new analysis.
P043-M2 (Mythos): friction = domain shift / Λ-parameter bookkeeping only.
P043-M3 (Mythos): on mismatch the gap names itself in one line (a concrete Estar
  bound at one edge).

## Answer requirements

043_muntz_v3_supplier_hrm.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG (else
REJECTED); scope/verifier tags on every claim; PHASE 0 verdicts explicit; scoring of
P043-M1..M3; goal consumed by SHA-256 stated; one non-promoting Route B state-history
row; ROUTE_B_STATE update last; canon + mirror in one transaction; report — do not
repair — any divergence.
