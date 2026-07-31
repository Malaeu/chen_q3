PL1_MASS_BLOWUP_WITNESS_PROVED

```yaml
PRIMARY: PL1_MASS_BLOWUP_WITNESS_PROVED
PRIMARY_COUNT: 1
SCOPE: ABSTRACT_SINGLE_EXPLICIT_WITNESS
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0

GOAL_VERSION_CONSUMED:
  FILE: 042_muntz_v3_pl1_mass_blowup_witness.goal.md
  SHA256: 9a2375c271f24c4b6cb94d87998811724570f2c8bfb0468b347d0bc0b6d078c9

THEOREM:
  NAME: exists_rawZetaMellin_norm_blowup_at_one
  FILE: muntz_v3/RequestProject/MuntzV3PL1MassBlowupWitness.lean
  FILE_SHA256: 1d1e8689a083867f68c3e5ec56f06bd5a271f4af68b632cc084b450f10bbb943
  LINES: 99
  BYTES: 3974
  ISOLATED_LEAN: PASS
  LAKE_BUILD: PASS_8031_JOBS
  TAINT_MATCHES: 0
  AXIOMS: [propext, Classical.choice, Quot.sound]

WITNESS:
  FORMULA: "h(u) = 1_Ioc(0,1)(u) * u"
  B: 1
  K: 1
  SUPPORT: Ioc_0_1_SUBSET_Icc_0_1
  MELLIN_FORMULA_ON_RE_GT_NEG_ONE: "1/(s+1)"
  MASS: "1/2"
  MELLIN_AT_ONE: "1/2"
  RAW_ZETA_MELLIN_NORM_LIMIT: atTop
```

All theorem and witness claims in the YAML block are
`[ABSTRACT][LEAN]`; source hashes are `[CONTROL][SHA256]`, and route,
submission, frozen-file, and bus fields are `[CONTROL][LOCAL]`.

## Exact Lean result

The exported theorem has exactly the requested existential shape:
`Measurable h`, support in `Icc 0 b`, `LipschitzOnWith K h (Ico 0 b)`,
nonzero mass, and
`Tendsto (fun w => ‖riemannZeta w * Mellin h w‖) (𝓝[≠] 1) atTop`.
`[ABSTRACT][LEAN]`

The witness is

```text
h(u) = 1_Ioc(0,1)(u) * u,   b = 1,   K = 1.
```

On `Ico 0 1`, the witness is the real-to-complex isometric embedding, so
the Lipschitz constant is exactly `1`. It is measurable and vanishes
outside `Icc 0 1`. `[ABSTRACT][LEAN]`

Pinned Mathlib's `hasMellin_cpow_Ioc`, together with the proved
project/Mathlib Mellin convention bridge, gives

```text
Mellin h s = 1/(s+1)    when -1 < re s.
```

At `s = 1`, exact normalization proves `Mellin h 1 = 1/2`; unfolding the
project Mellin definition at that checked identity proves
`∫ u in Ioi 0, h u = 1/2`. Thus both strictness fields
`bump_mass ≠ 0` and `mellin_value_at_one ≠ 0` are discharged by exact
rational arithmetic, with no numerical integration. `[ABSTRACT][LEAN]`

The Goal 039 compact-support theorem gives
`AnalyticOnNhd ℂ (Mellin h) {s | 0 < s.re}`, hence
`ContinuousAt (Mellin h) 1`. `[ABSTRACT][LEAN]`

The generic lemma `rawZetaMul_norm_tendsto_atTop` multiplies
`riemannZeta_residue_one` by the continuous Mellin limit. The numerator
norm tends to `‖m‖ > 0`, while
`‖w - 1‖⁻¹ → atTop` on `𝓝[≠] 1`; exact field cancellation identifies
their product with `‖riemannZeta w * M w‖`. `[ABSTRACT][LEAN]`

This is the required PL1 contrast to Goal 040: PL2's zero mass cancels the
pole and leaves a finite raw-value mismatch, whereas this PL1 witness has
nonzero mass, so the zeta pole is load-bearing and the raw norm diverges.
No Route B or RH consequence follows. `[ABSTRACT][LEAN]`

## Frozen boundary

`Main.lean`, `MellinCompactSupportAnalyticity.lean`, the Goal 040 answer,
and `MuntzV3PL2RawPoleMismatch.lean` have zero source diff. All new Lean
work is confined to `MuntzV3PL1MassBlowupWitness.lean`.
`[CONTROL][GIT]`

No Aristotle command or theorem-proving cloud submission was made.
`[CONTROL][LOCAL]`

## Validation

```text
[ABSTRACT][LEAN] lake env lean RequestProject/MuntzV3PL1MassBlowupWitness.lean  PASS
[ABSTRACT][LEAN] lake build                                                        PASS (8031 jobs)
[ABSTRACT][LEAN] taint scan                                                        0 matches
[ABSTRACT][LEAN] #print axioms exists_rawZetaMellin_norm_blowup_at_one             [propext, Classical.choice, Quot.sound]
[CONTROL][GIT]   frozen source diff                                                 0
[CONTROL][LOCAL] Aristotle submissions                                              0
```

## Prediction score

- `P042-M1`: **CONFIRMED**. The PL2 witness pattern and
  `hasMellin_cpow_Ioc` made the explicit witness cheap; the generic
  residue-times-mass blow-up lemma assembled locally and no cloud run was
  needed. `[ABSTRACT][LEAN]`
- `P042-C1`: **DISCONFIRMED**. The atTop/filter proof compiled on its first
  Lean attempt using `pos_mul_atTop` and
  `inv_tendsto_nhdsGT_zero`; the only proof-level iteration was the
  real-to-complex measurability/Lipschitz coercion for the witness.
  `[ABSTRACT][LEAN]`

## ACTIONS LOG

```text
1. [CONTROL][GIT]   Checked rh_clean and ran git pull --ff-only first.          PASS
2. [CONTROL][SHA256] Locked both Goal 042 copies at 9a2375c2...d078c9.          PASS
3. [CONTROL][LOCAL] Read Route B state/control and ran routeb_status --check.   PASS
4. [CONTROL][LOCAL] Confirmed CHALLENGER / NOT_RH and Bus 010 void.             PASS
5. [ABSTRACT][SOURCE_AUDIT] Inventoried PL2, T4a, and pinned Mathlib APIs.       DONE
6. [CONTROL][LOCAL] Attempted four q3_docs queries; local index stalled.         RECORDED
7. [ABSTRACT][LEAN] Added one new PL1 Lean file; frozen files untouched.         DONE
8. [ABSTRACT][LEAN] Proved witness measurability, support, and K=1 Lipschitz.    PASS
9. [ABSTRACT][LEAN] Proved Mellin formula, mass=1/2, and Mellin(1)=1/2.          PASS
10. [ABSTRACT][LEAN] Proved generic nonzero-mass norm blow-up and instantiated. PASS
11. [ABSTRACT][LEAN] Ran isolated Lean, full build, taint, and axiom checks.     PASS
12. [CONTROL][LOCAL] Emitted no Aristotle submission.                           PASS
13. [CONTROL][MIRROR] Wrote canonical answer and code mirror together.           DONE
14. [CONTROL][STATE] Added one non-promoting Route B history row last.           DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: PL1_MASS_BLOWUP_WITNESS_PROVED
GOAL_SHA256: 9a2375c271f24c4b6cb94d87998811724570f2c8bfb0468b347d0bc0b6d078c9
SCOPE: ABSTRACT / one explicit witness
VERIFIER: Lean 4.28.0 + Mathlib v4.28.0
WITNESS: h(u)=1_Ioc(0,1)(u)*u; b=1; K=1
MELLIN_FORMULA: 1/(s+1) on re(s)>-1
MASS: exactly 1/2, nonzero
MELLIN_AT_ONE: exactly 1/2, nonzero
RAW_NORM: tends to atTop along the punctured neighborhood of 1
PL2_CONTRAST: zero mass -> finite mismatch; nonzero mass -> load-bearing pole
TAINT: zero
AXIOMS: exactly [propext, Classical.choice, Quot.sound]
ARISTOTLE: no submission in this cycle
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
NEXT: return to the existing supplier front; do not infer any status promotion
```
