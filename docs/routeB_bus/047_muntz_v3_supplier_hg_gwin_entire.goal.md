# Goal 047 — MuntzV3 Supplier hG: gwin_entire on the exact v3 class

ISSUED: 2026-07-31, Mythos (contour verbatim from dispatch after packet 7;
  transcribed by conductor-CLI on owner's order).
MODE: LOCAL_FIRST · NO_ARISTOTLE · SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched
NUMBERING NOTE: Mythos's renumbering proposal ("048 = EstarBound") collided with
the already-issued read-only Goal 048 (habs inventory) — bus numbers are physical
and issued goals are immutable. Resolution: 047 = hG (this goal), 048 = habs
inventory (as issued, runs parallel), 049 = EstarBoundedBySqrtOfZeroMass_
IccZero_IcoLipschitz (her load-bearing lemma, next contour). Execution order is
independent of numbers.

## Rationale (Mythos, verbatim in substance)

On the window (Λ⁻¹, Λ) the arguments mu ≥ Λ⁻¹ > 0, so touching zero does not
participate; boundedness of h on [0,b] comes from Ico-Lipschitz + null endpoint
{b} (the technique that just HIT in 046); the sum has ≤ bΛ nonzero terms; hence
E* is bounded and measurable on the compact window, and Gwin is ENTIRE (simpler
than T4a — no zero-edge). The R6 column follows as a corollary (global Lipschitz
⇒ Ico-Lipschitz, Icc a b ⊂ Icc 0 b) — one goal, both columns.

## PRIMARY THEOREM

```lean
theorem gwin_entire
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (Gwin h Λ)
```

COROLLARY (consumer shape, Main.lean:156):

```lean
theorem gwin_analyticOnNhd_shiftedHalfPlane_v3Class
    (…same hypotheses…) :
    AnalyticOnNhd ℂ (Gwin h Λ) shiftedHalfPlane
```

FILE: new file under muntz_v3/RequestProject/.

## ROUTE (Mythos, verbatim)

1. h-bound on Icc 0 b (Ico-Lipschitz + null endpoint, as in 046).
2. ‖Estar u‖ ≤ √Λ·(bΛ+1)·C on the window.
3. Measurability.
4. Compact Mellin integral ⇒ entire ⇒ analyticOnNhd restriction.

## MANDATORY PLANTS (Proshka template)

PLANT-1: PL1 witness 1_Ioc(0,1]·u accepted by the theorem.
PLANT-2: dependency audit — no hmass / no 0<a / no global Lipschitz / no R6
  import anywhere in the proof.

## Forbidden

frozen files; muntz_r6/; edits in sealed R6Export/; taint (sorry | admit |
axiom | native_decide | exact?); bundling with hRm/habs; promotion; Aristotle.

## Validation

```text
lake env lean <new-file>
lake build
taint scan
#print axioms gwin_entire
#print axioms gwin_analyticOnNhd_shiftedHalfPlane_v3Class
axioms exactly [propext, Classical.choice, Quot.sound]
```

## Success code

HG_SUPPLIER_DISCHARGED_FOR_V3_CLASS (R6 column follows as corollary)

## Failure codes (exactly one, fail-closed)

HG_ESTAR_WINDOW_BOUND_GAP
HG_MEASURABILITY_GAP
PLANT_NOT_DETECTED
LEAN_BUILD_FAIL

## Registered predictions (Mythos, before execution)

P047-1: ≤ 120 lines, the T4a template transfers.
P047-2: both plants pass on the first substantive run.
P047-3: the R6 column follows as a corollary, no separate lemma.

## Answer requirements

047_muntz_v3_supplier_hg_gwin_entire.answer.md with MYTHOS_PROSHKA_HANDOFF +
ACTIONS LOG; plant results explicit; dependency audit listed; scoring
P047-1..3; goal consumed by SHA-256; canonical ledger restated (this closes hG
for BOTH columns → canonical 2/4 if 046 stands); one non-promoting state row;
ROUTE_B_STATE last; canon+mirror one transaction.
