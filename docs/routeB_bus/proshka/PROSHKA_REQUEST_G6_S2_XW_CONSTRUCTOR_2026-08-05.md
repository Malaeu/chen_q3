# PROSHKA REQUEST — G6·S2-XW: is the PSWF constructor actually required?

```yaml
REQUEST_ID: G6_S2_XW_CONSTRUCTOR_NECESSITY_2026_08_05
PHASE_KEY_CLAIM:
  route_id: RouteB_TwoLevelSpectralLadder
  front_id: G6_S2_D0_SELECTED_FAMILY_MUNTZ_SAME_FAMILY_CROSSWALK
  source_object_family_id: D0_PSTAR_PROLATE_TRIAL
  terminal_consumer_id: SlotS2_of_CanonicalRHRouteSkeleton
  honesty_state: CHALLENGER_NOT_RH
  convention_lock_id: C09_PRECOMMIT_THIS_REQUEST
BATCHED: true    # one request for the whole phase, per your budget law
ROUTE: CHALLENGER_NOT_RH · BUS_010: VOID · GOAL_055: HOLD
G2_CCM_LINE: UNTOUCHED · ARISTOTLE_SUBMISSION: NONE
ASK: adjudication on necessity + order. No authorization to build is requested.
```

## 0. What happened since your verdict

Your kill of the fixed-window substitution was accepted without contest. Mythos decomposed the
new gap `G6_S2_D0_SELECTED_FAMILY_MUNTZ_SAME_FAMILY_CROSSWALK` into a paper contract
(v1.2, addresses `G6·S2-XW.0a … XW.Σ`), carrying your nine conditions one-to-one.

Two owner-side pre-flight checks against the repository then corrected that contract twice:

1. **XW.0 was not a new gate.** `MuntzV3ProlateCombinationReceiver.lean:49` already proves
   `continued_window_identity_prolateCombination_v3Class_of_modeLipschitz` — the Müntz identity
   on `prolateCombination P` over the v3 class, sorry-free, measurability derived internally
   from evenness and symmetric support. `ProlateCombinationMuntzRegularity.lean` already proves
   `integral_Ioi_prolateCombination_eq_zero` (zero mass on the positive half — your v3 condition)
   and `LipschitzOnWith K (prolateCombination P)`. Neither file appears in your MANDATORY_INPUTS
   list, nor in Mythos's v1 skeleton.
2. **`Λ = P.pw.lambda` is not a fact, it is a free field.** `ProlateOperatorData` holds
   `lambda : ℝ` unconstrained, and `ProlatePair` states in its own docstring: "All analytic facts
   are fields (hypotheses), not existence theorems." A full-tree search finds **no** instantiation
   linking `P.pw.lambda` to `λ_m = √m` anywhere. Mythos had read the type-level freedom as a
   mathematical link — his AUTOPSY records this as the same interface-polymorphism error you
   killed in the PL2 substitution.

## 1. The question this request exists for

After those corrections, the front's step −1 became **XW.0a — construct the source PSWF modes
`h0_m`, `h4_m` as functions with `λ_m = √m` entering by construction, discharging the
hypothesis-fields of `ProlatePair`.**

The owner then measured what that costs. Facts, verified 2026-08-05:

- **Mathlib contains no PSWF theory at all**: zero occurrences of `prolate` / `spheroidal`.
- **Mathlib contains no Sturm–Liouville theory**: zero files.
- What exists is the generic Hilbert-space frame only (`HasEigenvector`, spectrum, Rayleigh,
  compact operators).
- Our `prolateWaveExpression` is the singular Sturm–Liouville expression
  `−d/dx[(λ²−x²)f′(x)] + (2πλx)²f(x)`, and `ProlateOperatorData` explicitly asserts no domain,
  no symmetry, no self-adjointness, no eigenfunction.

So `XW.0a` is not "construct an object inside an existing theory". It is "formalize the spectral
theory of a singular ODE from zero": domain, self-adjointness, compactness of the resolvent,
existence of eigenfunctions, and their regularity with explicit λ-dependence.

**Q1 — NECESSITY.** Is the constructor required for source-faithfulness, or can the source modes
enter as **source-locked data with certified numerical bounds** (the same discipline you demand
for the G2 WR integrals: exact representative, rational bounds, directed rounding, hashes),
discharging `XW.0b`'s explicit `K0_m, K4_m` without formalizing spectral theory?
If the certified-data route is admissible, state the exact conditions; if it is not, say so and
we treat the front as a multi-month formalization program and plan accordingly.

**Q2 — ORDER.** Mythos's kill-order puts `XW.0a` at step −1. The owner proposes running your
strongest gate first instead: `XW.8` (same-family / H2b provenance) is an audit of **existing**
objects, needs no constructor, and by your own ordering is the fastest fatal check. Same for
`XW.6` (coordinate/phase dictionary against `rawFplus … (−z)`) and the CTRL cell.
Do you confirm: **XW.8 before XW.0a**, so that a provenance kill spares the entire PSWF program?

**Q3 — CONTRACT VALIDITY.** Does contract v1.2 (nine conditions carried one-to-one, plus
`XW.0a`/`XW.0b` split, `XW.5` re-upgraded to a missing instantiation) faithfully decompose your
verdict, or does any address misstate what you ruled?

**Q4 — SCOPE OF THE ALREADY-PROVED RECEIVER.** Given that the v3-class Müntz identity for
`prolateCombination` is already proved conditional only on mode Lipschitz regularity: does that
theorem, as stated, remain usable at the D0 instantiation, or does it need re-derivation once
the modes are concrete? We would rather learn now that it is unusable than build on it.

## 2. What is NOT being asked

No authorization to construct, to write Lean, to create a bus goal, or to submit to Aristotle.
`NO_FILE_CREATION_NOW` is respected: this request file is an adjudication request, the same
class as `PROSHKA_REQUEST_G6_S2_IDENTIFICATION_2026-08-05.md`, and the contract itself is not
materialized pending your answer.

## 3. Boundaries

Nothing promoted. RH not claimed. Bus 010 VOID, Goal 055 held, G2/CCM frozen files untouched,
no Aristotle submission. Any construction that follows goes through owner per-action OK.
