# Goal 042 — MuntzV3 PL1 MassBlowupWitness (contrast plant to PL2)

ISSUED: 2026-07-31, Mythos (contour from Mythos dispatch message, "PL1 первым, голом 042";
  transcribed to the bus by conductor-CLI on owner's order)
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT (single explicit witness) · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no status promotion from this goal
ORIGIN: Mythos K2 fork recommendation after PL2 byte-audit (PL1 cheapest: reuses the
  PL2 quadratic template); post-close guards of Goal 040 apply as reviewer guards
  (041_goal040_postclose_requirements_audit.md, non-normative there, normative HERE
  as explicit fields of this new contract).

## Semantic role (why PL1 matters)

PL2 showed: with mass 0 the raw value ζ(1)·Mellin h 1 is finite junk while the true
limit is d ≠ 0 — finite-vs-finite mismatch. PL1 is the CONTRAST plant: with mass ≠ 0
the pole of ζ is load-bearing — the raw product ‖ζ(w)·Mellin h w‖ BLOWS UP along
𝓝[≠] 1. Together they demonstrate both failure modes of the raw (non-pole-subtracted)
value and certify that zero mass is exactly the removability mechanism. No Route B or
RH consequence; falsifier-obligation layer of the Müntz v3 shell only.

## Standing constraints

- Frozen: muntz_v3/RequestProject/Main.lean and MellinCompactSupportAnalyticity.lean.
  Do not modify either; new work goes in a NEW file inside muntz_v3/RequestProject/.
- Frozen formulations: allowed — T4A_CLOSED_LOCALLY, MUNTZ_V3_T5_MELLIN_HYPOTHESIS_DISCHARGED,
  MUNTZ_V3_CONDITIONAL_SHELL_CONSUMED; forbidden — MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE
  (PL1+PL2 do NOT unlock it: hG/hRm/hRp/habs supplier front remains open).
- RULE_INVENTORY_FIRST binding (A1 canonical, see proshka/RULE_NAMING_DISAMBIGUATION_2026-07-31.md):
  inventory own repo + pinned Mathlib BEFORE any cloud thought.
- CLOSED_GOAL_IMMUTABLE: this goal file is immutable once its answer exists.

## Inputs

- Goal 040 answer + PL2 Lean file (witness template: quadratic class on (0,1] via
  hasMellin_cpow_Ioc; generic-lemma assembly pattern residue × slope × uniqueness).
- muntz_v3/RequestProject/Main.lean (project Mellin; riemannZeta_residue_one usage at
  line 85; convention bridge from Goal 017).
- muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean (T4a: Measurable +
  supp ⊆ Icc 0 b + LipschitzOnWith K on Ico 0 b ⇒ AnalyticOnNhd ⇒ ContinuousAt at 1).
- Pinned Mathlib v4.28.0: riemannZeta_residue_one, Tendsto.mul, tendsto_nhds_unique,
  NormedField norm/atTop filter API (tendsto_atTop of ‖·‖ via nonvanishing limit over
  vanishing denominator), NeBot instances for 𝓝[≠] on ℂ.

## Primary theorem shape

```lean
theorem exists_rawZetaMellin_norm_blowup_at_one :
  ∃ (h : ℝ → ℂ) (b : ℝ) (K : NNReal),
    Measurable h ∧
    (∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0) ∧
    LipschitzOnWith K h (Set.Ico (0 : ℝ) b) ∧
    (∫ u in Set.Ioi (0 : ℝ), h u ≠ 0) ∧
    Filter.Tendsto (fun w : ℂ => ‖riemannZeta w * Mellin h w‖)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) Filter.atTop
```

Mellin convention: same project convention as Goal 040 (Goal 017 bridge); at s = 1 the
identification Mellin h 1 = ∫_{Ioi 0} h must be PROVED (integrability from the T4a
hypothesis package), not assumed definitionally.

## Explicit strictness fields (post-close-guard analogue of A1.1; deleting either must
## break the proof)

```text
bump_mass ≠ 0            (exact closed form required, no numerical integration)
mellin_value_at_one ≠ 0  (via the PROVED identification Mellin h 1 = ∫ h)
```

## Proof route

1. Reuse search FIRST (cheapest decisive test): locate or assemble the generic lemma

```lean
lemma rawZetaMul_norm_tendsto_atTop
    (M : ℂ → ℂ) (m : ℂ)
    (hM : ContinuousAt M 1) (hM1 : M 1 = m) (hm : m ≠ 0) :
    Filter.Tendsto (fun w : ℂ => ‖riemannZeta w * M w‖)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) Filter.atTop
```

Registered assembly sketch: on 𝓝[≠] 1, (w−1)·ζ(w) → 1 (riemannZeta_residue_one) and
M w → m (continuity), so (w−1)·ζ(w)·M(w) → m ≠ 0; eventually
‖ζ(w)·M(w)‖ = ‖(w−1)ζ(w)M(w)‖ / ‖w−1‖ ≥ (‖m‖/2) / ‖w−1‖ with ‖w−1‖ → 0⁺ on the
punctured filter; conclude Tendsto atTop by comparison.

2. Witness from the PL2 template with the coefficient DETUNED from 3/2: simplest
   admissible choice h(u) = 1_(0,1](u) · u (b = 1, K = 1): Mellin h s = 1/(s+1) via
   hasMellin_cpow_Ioc; mass = Mellin h 1 = 1/2 ≠ 0 by exact rational arithmetic.
   Any coefficient c ≠ 3/2 in u − c·u² is acceptable if friction appears; do NOT
   spend budget optimizing the witness (K2).

3. ContinuousAt (Mellin h) 1 from T4a (AnalyticOnNhd ⇒ ContinuousAt) exactly as in
   the PL2 chain — no new analyticity work.

4. Instantiate the generic lemma with M := Mellin h, m := Mellin h 1.

## Forbidden

- no modification of Goal 040 files, its answer, or the PL2 Lean artifact;
- no rerun of T4a; no rebuild of the v3 shell;
- no numerical integration; mass and Mellin values by exact closed form only;
- no new axiom, sorry, admit, native_decide;
- no bundling with PL3 or the supplier front (one goal — one plant);
- no Route B or RH status promotion;
- no Aristotle submission in this cycle (cloud escalation only per protocol below).

## Validation

```text
lake env lean <touched-file>
lake build
grep taint terms (sorry | admit | axiom | native_decide | exact?)
#print axioms exists_rawZetaMellin_norm_blowup_at_one
axioms must be exactly [propext, Classical.choice, Quot.sound]
```

## Success code

PL1_MASS_BLOWUP_WITNESS_PROVED

## Failure codes (exactly one, fail-closed)

PL1_GENERIC_BLOWUP_API_GAP
PL1_NONZERO_MASS_INTEGRAL_GAP
PL1_MELLIN_VALUE_AT_ONE_GAP
PL1_WITNESS_LIPSCHITZ_GAP
LEAN_BUILD_FAIL

## Cloud escalation

Only after exactly one failure code above is produced; the Aristotle contract targets
only that missing theorem; RULE_INVENTORY_FIRST (A1) audit mandatory before submission;
English-only prompt; SHA-256 on the prompt text.

## Registered predictions (before execution)

P042-M1 (Mythos): PL1 is nearly free after the PL2 template — same quadratic class,
  detuned coefficient; generic blow-up lemma assembles locally (≤ 30 Lean lines);
  no cloud run needed.
P042-C1 (conductor): dominant friction = atTop/filter bookkeeping for the norm
  blow-up (comparison on the punctured filter), not Mellin machinery and not the
  witness.

## Answer requirements

042_muntz_v3_pl1_mass_blowup_witness.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS
LOG (else REJECTED); scope/verifier tags on every claim; explicit scoring of P042-M1
and P042-C1; one Route B state-history row (status not promoted); ROUTE_B_STATE update
as the last step; canon + mirror in one transaction; report — do not repair — any
divergence found on the way.
