# Goal 050 — EstarBound v3-class REPAIRED (0 ≤ b guard) — owner-authorized live repair

ISSUED: 2026-07-31, conductor-CLI on owner's direct live order ("да сделай плиз")
  following the fail-closed Goal 049 (ESTAR_BOUND_BLE0_BRANCH_GAP). This goal is a
  PROVENANCE/CONTRACT record: the repaired theorem was authored by Codex on the same
  owner instruction and is ALREADY DELIVERED and Lean-verified (see below). It is
  documented here so the artifact traces to a bus contract.
MODE: LOCAL_FIRST · NO_ARISTOTLE · SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched

## What Goal 049 found (do not lose)

Goal 049's statement was DEFECTIVE (conductor authoring bug). With the explicit
packed constant C = K*b + (‖h 0‖ + K*b) + ‖h b‖, the case b < 0 makes C negative, so
the claimed bound ‖Estar h u‖ ≤ C·√u becomes e.g. 0 ≤ -1 (h ≡ 0, b = -1, K = 1,
u = 1/4). Lean counterexample confirmed. Goal 049 correctly returned fail-closed
ESTAR_BOUND_BLE0_BRANCH_GAP rather than fabricating or strengthening without a new
goal.

## MY_MISS (conductor, registered)

The Goal-049 text asserted "the RHS is ≥ 0" for b ≤ 0 — FALSE, because the explicit
constant contains K·b terms that go negative for b < 0. Law: an explicit packed
bound constant containing a K·b term is NOT sign-safe without 0 < b (or the b = 0
base handled separately). Never DECLARE a bound nonnegative — VERIFY it.

## Delivered theorem (Lean-verified, standard triple)

File: muntz_v3/RequestProject/MuntzV3EstarBoundExactClass.lean

```lean
theorem EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ‖Estar h u‖ ≤ (K * b + (‖h 0‖ + K * b) + ‖h b‖) * Real.sqrt u
```

Repair: hypothesis `hb : 0 ≤ b`. Base case b = 0: support Icc 0 0 = {0}, hsupp forces
every dilate h(n·u) = 0 (n·u > 0), so Estar h u = 0 and RHS ≥ 0 by positivity.
Case 0 < b: direct call to sealed R6Export.riemannBoundaryCellBridge_Estar with the
v3 hypotheses passed through unchanged. `#print axioms` = [propext, Classical.choice,
Quot.sound]; taint 0; no 0<a, no global LipschitzWith, no R6-wrapper call.

## Consequence

EstarBound is now PROVED on the exact v3 class (with the 0 ≤ b guard). Per the graph
factorization this UNBLOCKS both remaining canonical cells:
- hRm-canon: left-tail pointwise estimate feeder (right tail free by T1);
- habs-canon: the MellinConvergent-near-zero technical hypothesis (per Goal 048).
EstarBound is itself a FEEDER lemma, not one of the four supplier slots — canonical
supplier count stays 2/4 (hG, hRp) until hRm-canon and habs are discharged.

## Numbering (updated, supersedes 048 reconciliation)

```text
049 = EstarBound v3-class          CLOSED fail-closed (defective statement)
050 = EstarBound REPAIRED (0 ≤ b)  DELIVERED (this record)
051 = hRm-canon (consumes 050)     next
052 = habs export (branch A)       after
```

## Registered predictions status

P049-C1: HIT in spirit — the positive branch is a direct sealed-bridge call; the only
  extra work was the b = 0 base case, not the near-zero estimate.
P049-HONEST: CONFIRMED — the "only real mathematics of the layer" was already sealed
  in R6Export (Goal 044). Proshka's P047-HRM is a REFUTE candidate: no endpoint
  Riemann-sum work remained; the wall was a mislabeled door (K2).

## Answer

If Codex produces a formal 050 answer it carries MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG
+ the delivered-file SHA. Otherwise this contract record + the committed Lean artifact
+ commit message stand as the transaction provenance (owner-authorized live repair).
