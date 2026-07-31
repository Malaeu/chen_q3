# Goal 040 — MuntzV3 PL2 RawPoleMismatchWitness

ISSUED: 2026-07-30, Mythos
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT (single explicit witness) · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no status promotion from this goal
ORIGIN: Proshka CODEX DIRECTIVE, materialized at
  proshka/PROSHKA_VERDICT_T4A_SUPERSEDED_PL2_2026-07-30.md
AMENDED BY: Mythos — repairs R1–R3, one extra failure code, witness-Lipschitz note.

## Standing constraints

- Frozen: muntz_v3/RequestProject/Main.lean and MellinCompactSupportAnalyticity.lean.
  Do not modify either; new work goes in a new file inside muntz_v3/RequestProject/.
- Frozen formulations (Proshka verdict): allowed — T4A_CLOSED_LOCALLY,
  MUNTZ_V3_T5_MELLIN_HYPOTHESIS_DISCHARGED, MUNTZ_V3_CONDITIONAL_SHELL_CONSUMED;
  forbidden — MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE.
- ARISTOTLE_USAGE_PROTOCOL.md binding, incl. Rule 0 (repo + Mathlib inventory precedes
  any cloud submission; see proshka/ARISTOTLE_PROTOCOL_MYTHOS_RATIFICATION.md).
- Prepared T4a supplier contract: SUPERSEDED_BY_039_LOCAL_PROOF / DO_NOT_SUBMIT.

## Inputs

- muntz_v3/RequestProject/Main.lean (project Mellin; Rminus/Rplus defs at lines 20/27;
  ZetaResidueFactor via Function.update at line 36; riemannZeta_residue_one already used
  at line 85; pole values deriv (Mellin h) 1 at lines 49/125/235).
- muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean (T4a bridge; hypothesis
  template Measurable + supp ⊆ Icc 0 b + LipschitzOnWith K on Ico 0 b; a.e.-endpoint and
  eventual-zero technique directly reusable).
- Goal 017 Mellin convention bridge (project Mellin ↔ Mathlib mellin, smul_eq_mul + mul_comm).
- Pinned Mathlib v4.28.0: mellin_hasDerivAt-class API (derivative of the Mellin transform
  as the log-weighted Mellin integral), residue/removable-singularity API, slope
  characterization of HasDerivAt, tendsto_nhds_unique, NeBot instances for 𝓝[≠] on ℂ.
- Reusable generic pieces from muntz_r6/RequestProject/*.

## Primary theorem shape (Proshka, verbatim)

```lean
theorem exists_rawZetaMellin_not_continuousAt_one :
  ∃ (h : ℝ → ℂ) (b : ℝ) (K : NNReal),
    Measurable h ∧
    (∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0) ∧
    LipschitzOnWith K h (Set.Ico (0 : ℝ) b) ∧
    (∫ u in Set.Ioi (0 : ℝ), h u = 0) ∧
    deriv (Mellin h) 1 ≠ 0 ∧
    ¬ ContinuousAt (fun w : ℂ => riemannZeta w * Mellin h w) 1
```

Semantic role: with zero mass, Mellin h 1 = ∫ h = 0, hence the raw value
ζ(1) · Mellin h 1 = 0 for ANY (junk) value of riemannZeta 1, while the limit along
𝓝[≠] 1 equals d = deriv (Mellin h) 1 ≠ 0. Bounded product, finite-vs-finite mismatch
0 ≠ d — exactly the regression PL2 guards. Statement hypotheses stay as written; the
historical ban on strengthening LipschitzOnWith to global Lipschitz constrains the
THEOREM SHAPE, not the witness: the chosen tent witness may happen to be globally
Lipschitz — that is a property of the witness, not an added hypothesis.

## Proof route (Proshka steps 1–6 with Mythos repairs R1–R3)

1. Reuse search FIRST (cheapest decisive test): locate or assemble the generic lemma

```lean
lemma rawZetaMul_not_continuousAt_one
    (M : ℂ → ℂ) (d : ℂ)
    (hM1 : M 1 = 0) (hMd : HasDerivAt M d 1) (hd : d ≠ 0) :
    ¬ ContinuousAt (fun w : ℂ => riemannZeta w * M w) 1
```

Registered assembly sketch: value at 1 is riemannZeta 1 * 0 = 0; on 𝓝[≠] 1,
(w − 1) * riemannZeta w → 1 (riemannZeta_residue_one) and M w / (w − 1) → d
(hasDerivAt_iff_tendsto_slope with M 1 = 0); Tendsto.mul plus the eventual algebraic
identity ((w−1)ζ(w)) · (M(w)/(w−1)) = ζ(w)·M(w) for w ≠ 1 gives the limit d;
ContinuousAt would force Tendsto to 𝓝 0 on the same NeBot filter; tendsto_nhds_unique
yields d = 0, contradiction.

2. Reuse without modifying the v3 shell.

3. Witness: difference of two IDENTICAL triangular tents,
   tent(u) = A · max 0 (1 − |u − c|/r), at centers c₁ < c₂, half-width r,
   supports [c₁−r, c₁+r] and [c₂−r, c₂+r] ⊂ (0, b), STRICT separation c₁ + r < c₂ − r.
   h := tent_{c₁} − tent_{c₂} (real-valued, coerced to ℂ).

4. Zero mass via translation invariance (R2): ∫ tent(· − c₁) = ∫ tent(· − c₂) over ℝ;
   supports lie inside Ioi 0, so ∫_{Ioi 0} = ∫_ℝ for each tent. No area computation.

5. d ≠ 0 via derivative identification (R1) + constant bounds (R3):
   R1: deriv (Mellin h) 1 = ∫_{Ioi 0} h u · Real.log u du by the mellin_hasDerivAt-class
   API applied through the Goal-017 convention bridge (isBigO hypotheses supplied exactly
   as in the T4a bridge file).
   R3: strictness WITHOUT a strict integral-monotonicity lemma:
   ∫ tent_{c₁} · log ≤ log(c₁+r) · m < log(c₂−r) · m ≤ ∫ tent_{c₂} · log,
   where m = ∫ tent > 0 (nonneg, continuous, positive at the center); hence the
   log-moment of h is strictly negative; coercion ℝ → ℂ preserves ≠ 0.

6. Instantiate the generic lemma with M := Mellin h, using T4a for HasDerivAt
   (analyticity ⇒ differentiability at 1) if the derivative-identification lemma does
   not itself supply HasDerivAt.

## Forbidden (Proshka, verbatim)

- no rerun of T4a;
- no rebuild of the full v3 shell;
- no raw product value used as the removable value;
- no numerical integration;
- no new axiom, sorry, admit, native_decide;
- no three-plant bundle;
- no Route B or RH status promotion.

## Validation

```text
lake env lean <touched-file>
lake build
grep taint terms (sorry | admit | axiom | native_decide | exact?)
#print axioms exists_rawZetaMellin_not_continuousAt_one
axioms must be exactly [propext, Classical.choice, Quot.sound]
```

## Success code

PL2_RAW_POLE_MISMATCH_WITNESS_PROVED

## Failure codes (exactly one, fail-closed)

PL2_GENERIC_NONCONTINUITY_API_GAP
PL2_EXPLICIT_BUMP_LIPSCHITZ_GAP
PL2_ZERO_MASS_INTEGRAL_GAP
PL2_LOG_MOMENT_NONZERO_GAP
PL2_DERIV_IDENTIFICATION_API_GAP   (Mythos addition: deriv (Mellin h) 1 = log-moment)
LEAN_BUILD_FAIL

## Cloud escalation

Only after exactly one failure code above is produced; the Aristotle contract targets
only that missing theorem; full Supplier card with WHY_STRICTLY_WEAKER_THAN_TARGET is
mandatory; English-only prompt; SHA-256 on the prompt text.

## Registered predictions (before execution)

P-PL2-LOCAL (Proshka): generic noncontinuity argument almost contained in
  R6/pole-subtracted material; main work = explicit zero-mass bump witness + nonzero
  log moment.
P040-M1 (Mythos): the generic lemma assembles in ≤ 35 Lean lines from
  residue × slope × tendsto_nhds_unique; no cloud run needed for it.
P040-M2 (Mythos): dominant friction = LipschitzOnWith for the explicit tents and/or the
  derivative identification (R1) — not complex analysis.
P040-M3 (Mythos): log-moment strictness closes by the constant-bound route (R3), without
  any strict integral-monotonicity lemma.

## Answer requirements

040_muntz_v3_pl2_raw_pole_mismatch.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG
(else REJECTED); scope/verifier tags on every claim; explicit scoring of P-PL2-LOCAL and
P040-M1..M3; one Route B state-history row (status not promoted); ROUTE_B_STATE update as
the last step; canon + mirror in one transaction; report — do not repair — any divergence,
including the currently pending remote materialization of ARISTOTLE_USAGE_PROTOCOL.md.

## AMENDMENT A1 (2026-07-31, Mythos; per Proshka verdict GOAL_040_CORRECTIONS_RATIFIED_PENDING_PIN)

Original text above unchanged; this section adds binding requirements.

A1.1 STRICTNESS PRECONDITIONS (explicit named fields; deleting either must break the
strict sign of the log-moment):
  bump_mass > 0                              (m = ∫ tent)
  right_support_lower > left_support_upper   (c2 - r > c1 + r; touching supports yield only <=0)

A1.2 NO-SKIP CLAUSE: no arrow of the chain
  translated equal-mass bumps => ∫h = 0 => ∫ h·log u du < 0
  => deriv (Mellin h) 1 ≠ 0 => ¬ContinuousAt (fun w => riemannZeta w * Mellin h w) 1
may be replaced by numerical integration or by an unproven "differentiation under the
integral sign". ∫ h·log u du < 0 alone is NOT PL2: without the proved identification
deriv (Mellin h) 1 = ∫_{Ioi 0} h u * Real.log u du the run returns
PL2_DERIV_IDENTIFICATION_API_GAP, not success.

A1.3 Additional registered prediction:
P040-PL2 (Proshka): the generic simple-zero => raw-product discontinuity closes by
reuse of the existing residue/slope theorem; the dominant Lean friction is the exact
derivative identification, not the final discontinuity proof.

A1.4 The answer states which goal version it consumed (pre-A1 / post-A1) by SHA-256.

NOTE (branching rule applied): the 040 answer was produced PRE-A1 (goal closed
2026-07-30, Mac session); per the Mythos branching rule the answer is NOT
retro-edited — A1 executes as a FOLLOW-UP GATE on any future PL2-consuming step.
