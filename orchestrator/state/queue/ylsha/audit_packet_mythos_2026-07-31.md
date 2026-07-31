AUDIT PACKET FOR MYTHOS — byte-audit backlog closure + transport smoke (P-PKT-1)
Repo: Malaeu/chen_q3 · branch rh_clean · HEAD de9f056028c12cc6757627329cfda26971dd370c
Built: 2026-07-31 by conductor-CLI (Linux). Encoding: UTF-8, LF line endings.

VERIFICATION CONTRACT: each payload lies strictly BETWEEN its BEGIN and END
marker lines (marker lines themselves are NOT part of the payload). Every file
ends with a trailing newline, which IS part of the payload. Recompute SHA-256
over exactly those bytes. Any mismatch = the paste leg broke (P-PKT-1); report
which file diverged.

MANIFEST (path · bytes · sha256):
  docs/routeB_bus/040_muntz_v3_pl2_raw_pole_mismatch.answer.md · 8317 · e91dbdfe460513ced5133f9b7c7b1fe611e943175b1e69d4efea23d51686b86a
  docs/routeB_bus/041_conductor_handover_and_mirror_sync.answer.md · 5773 · 80976e272f0b3a510e57d6549d5590ec8569b620d7f62c7ac4a6f2ea096cd543
  docs/routeB_bus/041_goal040_postclose_requirements_audit.md · 3205 · 7ca84c88c6528a872613d97e57e6160c0e448d59cabce1982e92ea8d20a223f7
  docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL040_RATIFIED_PENDING_PIN_2026-07-31.md · 11683 · cd08c7ba22622f9846b2355c87f05ddf75c9bf8b22734c51019fa39c8b6c2542
  docs/routeB_bus/proshka/PROSHKA_VERDICT_DRAFT041_HOLD_VERSIONED_REPAIR_2026-07-31.md · 9056 · 220071ec09623cd210dbb553b3a54feff5ee6507067b968e2a3e00e05769b96f

═══ FILE BEGIN: docs/routeB_bus/040_muntz_v3_pl2_raw_pole_mismatch.answer.md ═══
PL2_RAW_POLE_MISMATCH_WITNESS_PROVED

```yaml
PRIMARY: PL2_RAW_POLE_MISMATCH_WITNESS_PROVED
PRIMARY_COUNT: 1
SCOPE: ABSTRACT_SINGLE_EXPLICIT_WITNESS
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0

THEOREM:
  NAME: exists_rawZetaMellin_not_continuousAt_one
  FILE: muntz_v3/RequestProject/MuntzV3PL2RawPoleMismatch.lean
  FILE_SHA256: 82ddccccefdc2b8bcd547d9bfbed4ff23d4dd6a0756f553ff6d01b40c7def339
  LINES: 140
  LAKE_BUILD: PASS
  TAINT_MATCHES: 0
  AXIOMS: [propext, Classical.choice, Quot.sound]

WITNESS:
  B: 1
  K: 2
  SUPPORT: Ioc_0_1_SUBSET_Icc_0_1
  MASS: 0
  MELLIN_FORMULA_ON_RE_GT_NEG_ONE: "1/(s+1) - (3/2)/(s+2)"
  DERIV_MELLIN_AT_ONE: "-1/12"
  RAW_ZETA_MELLIN_CONTINUOUS_AT_ONE: false
```

All claims in the YAML block are `[ABSTRACT][LEAN]`, except the route and
submission counters, which are `[CONTROL][LOCAL]`.

## Exact Lean result

The exported declaration has exactly the requested hypothesis/conclusion
shape: an existential `h, b, K` with `Measurable h`, support in `Icc 0 b`,
`LipschitzOnWith K h (Ico 0 b)`, zero mass, nonzero Mellin derivative at
`1`, and failure of continuity for the raw zeta–Mellin product at `1`.
`[ABSTRACT][LEAN]`

The concrete witness is the compact quadratic combination

```text
h(u) = 1_Ioc(0,1)(u) * u - (3/2) * 1_Ioc(0,1)(u) * u^2.
```

It is measurable, supported in `Icc 0 1`, and is `2`-Lipschitz on `Ico 0 1`.
The Lipschitz proof factors the difference as
`(x-y) * (1-(3/2)(x+y))` and uses
`|1-(3/2)(x+y)| ≤ 2` for `x,y ∈ Ico 0 1`. `[ABSTRACT][LEAN]`

Pinned Mathlib's `hasMellin_cpow_Ioc` gives, for `-1 < re s`,

```text
Mellin h s = 1/(s+1) - (3/2)/(s+2).
```

Hence `Mellin h 1 = 0` and
`HasDerivAt (Mellin h) (-1/12) 1`; the latter yields
`deriv (Mellin h) 1 = -1/12 ≠ 0`. No numerical integration or strict
integral-monotonicity lemma is used. `[ABSTRACT][LEAN]`

The generic lemma is the R6 residue-times-slope argument:
`riemannZeta_residue_one` supplies the punctured residue limit,
`hasDerivAt_iff_tendsto_slope` supplies the simple-zero slope limit, their
product tends to the nonzero derivative, while literal continuity at `1`
would force the same punctured function to tend to `0`.
`tendsto_nhds_unique` gives the contradiction. `[ABSTRACT][LEAN]`

## Frozen boundary

`muntz_v3/RequestProject/Main.lean` and
`muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean` have zero diff
against `HEAD`; all Goal 040 Lean work is confined to the new file
`MuntzV3PL2RawPoleMismatch.lean`. `[CONTROL][GIT]`

The prepared T4a contract remains present and begins with
`SUPERSEDED_BY_039_LOCAL_PROOF / DO_NOT_SUBMIT`; it was not deleted or
submitted. `[CONTROL][LOCAL]`

The already-materialized 038A audit checks seven sign sites
`[161, 163, 165, 211, 214, 234, 235]`, all with the `-Rplus` convention; it
does not use the stale phrase “five occurrences.” `[ABSTRACT][SOURCE_AUDIT]`

## Source-lock ledger

| Artifact | Bytes | SHA-256 | Scope/verifier |
|---|---:|---|---|
| `proshka/PROSHKA_VERDICT_ARISTOTLE_MICROSCOPE_2026-07-30.md` | 19569 | `4f31efe4f0ccdd7933851496848fb2701bc2588e94dd60c9dd2348aaded1de30` | `[CONTROL][SHA256]` |
| `proshka/PROSHKA_VERDICT_T4A_SUPERSEDED_PL2_2026-07-30.md` | 13605 | `053f872aab3504837d01758d7ea30ce6545e82d7122b21e5308d46bc97f3b8a9` | `[CONTROL][SHA256]` |
| `proshka/ARISTOTLE_PROTOCOL_MYTHOS_RATIFICATION.md` | 3051 | `1a969add070390407d0edfc37f42efc9ca9f6473802133f73576cd54a8577ec2` | `[CONTROL][SHA256]` |
| `040_muntz_v3_pl2_raw_pole_mismatch.goal.md` | 7437 | `48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300` | `[CONTROL][SHA256]` |
| `038A_muntz_v3_semantic_audit.answer.md` | — | `9ed7b3e0c296d35a2690fc7885c7ca3ba007c56b45303158ed0c75e1179b1d5f` | `[CONTROL][SHA256]` |
| `ARISTOTLE_USAGE_PROTOCOL.md` | — | `c5e47a7ca9af8e1b8d0db175bfbaefc4d95043635fe29cee4f390cc5c40f80a2` | `[CONTROL][SHA256]` |
| prepared T4a contract | — | `ae782b36312f3c81c08a479658abc8c6d8318ddbc26d5339f01552b028b55e25` | `[CONTROL][SHA256]` |
| Goal 040 Lean file | 6046 | `82ddccccefdc2b8bcd547d9bfbed4ff23d4dd6a0756f553ff6d01b40c7def339` | `[ABSTRACT][LEAN+SHA256]` |

The protocol's former remote 404 is repaired at commit `8e1603a1`; the
commit-pinned GitHub URL is:

```text
https://github.com/Malaeu/chen_q3/blob/8e1603a16212b70407d5164cd6f13931e0dadfd2/docs/routeB_bus/ARISTOTLE_USAGE_PROTOCOL.md
```

The URL was fetched successfully after the mirror repair. `[CONTROL][WEB]`

## Validation

```text
lake env lean RequestProject/MuntzV3PL2RawPoleMismatch.lean  PASS
lake build                                                   PASS (8030 jobs)
taint scan                                                   0 matches
#check exact exported theorem shape                          PASS
#print axioms rawZetaMul_not_continuousAt_one                standard triple
#print axioms exists_rawZetaMellin_not_continuousAt_one      standard triple
frozen Main.lean diff                                        0
frozen MellinCompactSupportAnalyticity.lean diff             0
Aristotle submit/formalize calls                             0
```

“Standard triple” means exactly
`[propext, Classical.choice, Quot.sound]`. `[ABSTRACT][LEAN]`

## Prediction score

- `P-PL2-LOCAL`: **CONFIRMED**. The generic argument was already present in
  R6, and the only new mathematical work was an explicit zero-mass witness
  with nonzero Mellin derivative. `[ABSTRACT][LEAN]`
- `P040-M1`: **CONFIRMED**. The generic lemma is 20 proof lines and uses the
  predicted residue, slope, and uniqueness APIs; no cloud run was needed.
  `[ABSTRACT][LEAN]`
- `P040-M2`: **PARTIAL / CHEAPER_ROUTE_FOUND**. Lipschitz assembly was local
  algebra, but derivative identification ceased to be dominant because
  `hasMellin_cpow_Ioc` produced an exact rational Mellin formula.
  `[ABSTRACT][LEAN]`
- `P040-M3`: **SUPERSEDED_BY_CHEAPER_EXACT_WITNESS**. The registered
  constant-bound strict-log-moment route was sound but unnecessary: exact
  differentiation gives `-1/12` directly. `[ABSTRACT][LEAN]`

## ACTIONS LOG

```text
1. Read Goal 040 and all three owner-relayed Proshka/Mythos files.        DONE
2. Verified all four dispatcher SHA/byte claims from disk.               PASS
3. Read Route B control/state and ran routeb_status.py --check.           PASS
4. Confirmed Bus 010 void and CHALLENGER / NOT_RH unchanged.              PASS
5. Audited commit 8e1603a1 instead of duplicating its operations.         DONE
6. Verified 038A has seven sign sites and the T4a contract is retired.    PASS
7. Ran four q3_docs semantic searches.                                    0 HITS
8. Searched pinned Mathlib and official Mathlib documentation.            DONE
9. Reused the R6 generic residue-times-slope lemma.                        DONE
10. Recorded the in-progress synthesis in docs/INSIGHTS.md.               DONE
11. Added only MuntzV3PL2RawPoleMismatch.lean to the frozen v3 project.   DONE
12. Built the explicit compact quadratic witness with b=1 and K=2.       PASS
13. Proved exact Mellin formula, zero mass, and derivative -1/12.         PASS
14. Proved raw zeta-Mellin discontinuity at one.                          PASS
15. Ran isolated Lean, full lake build, taint, and axiom checks.          PASS
16. Emitted no Aristotle task, project, status query, or download.        PASS
17. Wrote this answer with one primary result and prediction scoring.     DONE
18. Added one non-promoting Route B history row as the final state edit.  DONE
19. Rebuilt canon/mirror and MANIFEST in one final transaction.           DONE
20. Committed and pushed branch rh_clean without route promotion.         DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: PL2_RAW_POLE_MISMATCH_WITNESS_PROVED
SCOPE: ABSTRACT / one explicit witness
VERIFIER: Lean 4.28.0 + Mathlib v4.28.0
WITNESS: compact quadratic on Ioc 0 1; b=1; K=2
MASS: exactly zero
DERIV_MELLIN_AT_ONE: exactly -1/12
RAW_PRODUCT_AT_ONE: discontinuous
TAINT: zero
AXIOMS: exactly [propext, Classical.choice, Quot.sound]
T4A: frozen, already closed by Goal 039
ARISTOTLE: no submission in this cycle
038A: seven sign sites, all minus
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
NEXT: PL1 or PL3 only as a separate explicit plant contract; do not reopen T4a
```
═══ FILE END: docs/routeB_bus/040_muntz_v3_pl2_raw_pole_mismatch.answer.md ═══

═══ FILE BEGIN: docs/routeB_bus/041_conductor_handover_and_mirror_sync.answer.md ═══
CONDUCTOR_HANDOVER_COMPLETE

```yaml
PRIMARY: CONDUCTOR_HANDOVER_COMPLETE
PRIMARY_COUNT: 1
SCOPE: OPERATIONAL_SOURCE_AUDIT_AND_TRANSPORT
VERIFIER: LOCAL_COMMANDS_SHA256_LEAN_GIT_WEB
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID

HANDOVER:
  CONDUCTOR_ROLE: RETIRED
  CODEX_ABSORBS_GIT_MIRROR_MARKING_DUTIES: true
  HISTORY_REWRITTEN: false

T4A_CONTRACT:
  STATUS: SUPERSEDED_BY_039_LOCAL_PROOF
  DO_NOT_SUBMIT: true
  RETAINED_FOR_PROVENANCE: true

SEMANTIC_RECHECK:
  RPLUS_MINUS_SIGN_SITES: 7
  RPLUS_PLUS_SIGN_SITES: 0
  RIEMANN_ZETA_SITES: [36, 80, 85, 90, 92, 104, 106, 118, 160, 213]
  RAW_ZETA_ONE_MELLIN_ONE_SITE: false
  DERIV_MELLIN_ONE_SITES: [49, 125, 235]
  TAINT_MATCHES: 0
  DECLARATIONS_AXIOM_CHECKED: 18
  AXIOMS: [propext, Classical.choice, Quot.sound]

REMOTE_PROTOCOL:
  RESOLVES: true
  PIN_COMMIT: 8e1603a16212b70407d5164cd6f13931e0dadfd2
  PIN_URL: https://github.com/Malaeu/chen_q3/blob/8e1603a16212b70407d5164cd6f13931e0dadfd2/docs/routeB_bus/ARISTOTLE_USAGE_PROTOCOL.md
```

All claims above are `[CONTROL][LOCAL]`, except the semantic and axiom fields,
which are `[ABSTRACT][LEAN+SOURCE_AUDIT]`, and the remote-resolution field,
which is `[CONTROL][WEB]`.

## Local semantic recheck

The fresh line scan of
`muntz_v3/RequestProject/Main.lean` confirms seven continued-identity
`-Rplus` sign sites: `[161, 163, 165, 211, 214, 234, 235]`.
There is no `+ Rplus` site. Wrapped identities count as one semantic sign
site each; the ground truth is seven sites, not “five occurrences.”
`[ABSTRACT][SOURCE_AUDIT]`

The exact `riemannZeta` line inventory is
`[36, 80, 85, 90, 92, 104, 106, 118, 160, 213]`. These sites belong to the
residue-removed factor, differentiability away from the pole, and punctured
identities. No literal raw `riemannZeta 1 * Mellin h 1` occurs.
`[ABSTRACT][SOURCE_AUDIT]`

The three pole-value sites are exactly lines `[49, 125, 235]`, and every one
uses `deriv (Mellin h) 1`. `[ABSTRACT][SOURCE_AUDIT]`

The taint scan over `Main.lean` has zero matches. A fresh `#print axioms`
run over all 18 theorem/lemma declarations reports exactly
`[propext, Classical.choice, Quot.sound]` for each declaration.
`[ABSTRACT][LEAN]`

## Per-file SHA-256 ledger

| Required mirror artifact | Bytes | SHA-256 |
|---|---:|---|
| `ARISTOTLE_USAGE_PROTOCOL.md` | 7570 | `c5e47a7ca9af8e1b8d0db175bfbaefc4d95043635fe29cee4f390cc5c40f80a2` |
| `038A_muntz_v3_semantic_audit.answer.md` | 5297 | `9ed7b3e0c296d35a2690fc7885c7ca3ba007c56b45303158ed0c75e1179b1d5f` |
| `040_muntz_v3_pl2_raw_pole_mismatch.goal.md` | 7437 | `48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300` |
| `041_conductor_handover_and_mirror_sync.goal.md` | 3846 | `1ee885c50c92e4cad5f108bd51c855ea0df893caf147f2c12bb2a3d6588c8083` |
| `proshka/PROSHKA_VERDICT_ARISTOTLE_MICROSCOPE_2026-07-30.md` | 19569 | `4f31efe4f0ccdd7933851496848fb2701bc2588e94dd60c9dd2348aaded1de30` |
| `proshka/PROSHKA_VERDICT_T4A_SUPERSEDED_PL2_2026-07-30.md` | 13605 | `053f872aab3504837d01758d7ea30ce6545e82d7122b21e5308d46bc97f3b8a9` |
| `proshka/ARISTOTLE_PROTOCOL_MYTHOS_RATIFICATION.md` | 3051 | `1a969add070390407d0edfc37f42efc9ca9f6473802133f73576cd54a8577ec2` |
| `proshka/ORG_UPDATE_CONDUCTOR_RETIRED_2026-07-30.md` | 2538 | `3daf3bc4d672d1fe23c174365c73d8050899f318bd89c4740da39b886964ef8d` |

All sizes and hashes were computed from current disk bytes and then checked
against the mirrored copies. `[CONTROL][SHA256]`

The exact final `HEAD` after push is reported in the owner-facing handoff
outside this committed tree: embedding a commit's own future hash inside its
tree would be self-referential. `[CONTROL][GIT]`

## Prediction score

- `P041-1`: **CONFIRMED** — seven minus-sign sites, zero plus-sign sites,
  the expected zeta/pole-value inventories, zero taint, and the standard
  axiom triple all match. `[ABSTRACT][LEAN+SOURCE_AUDIT]`
- `P041-2`: **CONFIRMED** — the pinned protocol URL resolves on the first
  fetch; the former 404 was mirror lag. `[CONTROL][WEB]`

## ACTIONS LOG

```text
1. Read Goal 041 and the owner organizational update.                    DONE
2. Located the prepared T4a contract by content and verified its header. PASS
3. Retained the contract for provenance; submitted nothing.             PASS
4. Re-ran the Main.lean Rplus sign scan.                                 7 MINUS / 0 PLUS
5. Re-ran the exact riemannZeta line inventory.                          10 SITES
6. Re-ran the deriv(Mellin h) 1 line inventory.                          3 SITES
7. Re-ran Main.lean taint scan.                                         0 MATCHES
8. Printed axioms for all 18 theorem/lemma declarations.                STANDARD TRIPLE
9. Verified the remote protocol pin resolves.                            PASS
10. Recomputed the eight required file sizes and SHA-256 values.         PASS
11. Materialized this answer with handoff and prediction scoring.        DONE
12. Added the retirement/handover Route B history row last.              DONE
13. Rebuilt mirror and MANIFEST from canon.                               DONE
14. Verified canon/mirror byte equality and manifest entries.             PASS
15. Committed canon plus mirror in one transaction and pushed rh_clean.  DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: CONDUCTOR_HANDOVER_COMPLETE
CONDUCTOR: retired
CODEX: owns git, mirror, MANIFEST, status marking, operational audits
T4A_CONTRACT: SUPERSEDED_BY_039_LOCAL_PROOF / DO_NOT_SUBMIT / retained
038A: seven minus-sign sites; zero plus-sign sites; semantic recheck matches
MAIN_TAINT: zero
MAIN_AXIOMS: exactly [propext, Classical.choice, Quot.sound]
PROTOCOL_REMOTE: resolves at the pinned URL
GOAL_040: unchanged and completed in its separate answer
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
```
═══ FILE END: docs/routeB_bus/041_conductor_handover_and_mirror_sync.answer.md ═══

═══ FILE BEGIN: docs/routeB_bus/041_goal040_postclose_requirements_audit.md ═══
# GOAL 040 POST-CLOSE REQUIREMENTS AUDIT

```text
status: POSTCLOSE_REVIEWER_REQUIREMENTS
normative_for_goal_040_execution: false
modifies_goal_040_contract: false
```

Date: 2026-07-31 · Materialized by: conductor-CLI (Claude Code, Linux) on owner's
order, per Proshka verdict DRAFT_041_HOLD_FOR_VERSIONED_REPAIR.

Goal 040 is CLOSED (`PL2_RAW_POLE_MISMATCH_WITNESS_PROVED`, theorem
`exists_rawZetaMellin_not_continuousAt_one`, green build, zero taint, standard
axiom triple). This artifact records the reviewer requirements that arrived
AFTER closure. They are post-close reviewer guards for any future PL2-consuming
step; they are NOT conditions retroactively claimed as executed by the 040 proof.

## Reviewer guards (verbatim from ratified corrections)

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

## Route classification (per Proshka DRAFT_041 verdict)

The tent/translation/log-bound route above is classified SOUND BUT SUPERSEDED,
not as the factually used proof route. The actual 040 proof used a cheaper exact
witness: the compact quadratic function

  h(u) = 1_{(0,1]}(u) * u - (3/2) * 1_{(0,1]}(u) * u^2

with exactly computed Mellin transform, zero mass, and
deriv (Mellin h) (1) = -1/12.

## Provenance history (honest, includes the reverted misstep)

1. 2026-07-31, commit 19a4dcbf: AMENDMENT A1 was appended to the CLOSED goal-040
   file (both copies) on Mythos instruction and owner's same-day order
   (goal SHA changed 48172cdb… -> 2aac67d5…).
2. Proshka verdict DRAFT_041_HOLD_FOR_VERSIONED_REPAIR ruled this retroactive
   contract mutation FORBIDDEN (a closed goal is immutable; later reviewer
   requirements need a separate artifact).
3. This commit: goal 040 restored byte-identical to its pinned pre-A1 state
   (SHA-256 48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300,
   both copies verified), and the requirements moved HERE as post-close guards.

The interim mutation remains visible in git history (19a4dcbf); it is not hidden.

## Registered invariant (from the verdict, binding for the future)

A closed goal is immutable; later reviewer requirements need a separate
versioned artifact. Forbidden future move: rewrite a proved contract to match
later feedback.
═══ FILE END: docs/routeB_bus/041_goal040_postclose_requirements_audit.md ═══

═══ FILE BEGIN: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL040_RATIFIED_PENDING_PIN_2026-07-31.md ═══
# PROSHKA VERDICT — GOAL_040_CORRECTIONS_RATIFIED_PENDING_PIN
Date received: 2026-07-31
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
(Mythos had delegated to Codex; Filesystem bridge down in Mythos session)
Consumed by: docs/routeB_bus/041_goal040_postclose_requirements_audit.md;
proshka/RULE_NAMING_DISAMBIGUATION_2026-07-31.md
Transport artifacts note: payload is verbatim as pasted by the owner from the
Proshka browser chat; copy-paste escaping artifacts are preserved unmodified
(backslash-escaped underscores in headings, "## STATUS" heading level, fences
rendered as ```markdown). Semantic content untouched; no editing performed.

--- VERBATIM PAYLOAD BEGINS ---

## STATUS: CONDITIONAL — GOAL\_040\_CORRECTIONS\_RATIFIED\_PENDING\_PIN

```markdown
primary_verdict: GOAL_040_CORRECTIONS_RATIFIED
goal_040_source_status: USER_REPORTED_NOT_YET_PIN_VERIFIED
rule_0_status: PENDING_EXACT_TWO_TEXTS_COMPARISON

route_state: CHALLENGER_NOT_RH
bus_010: VOID
state_promotion: false
rh_claimed: false

t4a_supplier:
  status: SUPERSEDED_BY_039_LOCAL_PROOF
  submit: false
  duplicate_aristotle_run: forbidden

pl2_corrections:
  derivative_identification:
    verdict: RATIFIED
    failure_code: PL2_DERIV_IDENTIFICATION_API_GAP
  zero_mass_by_translation_invariance:
    verdict: RATIFIED
  strict_log_moment_by_separated_constant_bounds:
    verdict: RATIFIED

next_action:
  owner_conductor: mirror_sync_and_supply_pinned_goal_040_and_rule_0_texts
  judge: exact_text_ratification_only
  codex_or_aristotle: no_new_dispatch_from_this_verdict
```

## ROUTE MAP

Три поправки Mythos математически правильные.

### 1\. Деривативная идентификация — обязательна

PL2 должен получить не просто отрицательный логарифмический момент, а

$$
\operatorname{deriv}(\operatorname{Mellin}h)(1)\neq0.
$$

Между ними нужен отдельный exact bridge:

$$
\boxed{
\operatorname{deriv}(\operatorname{Mellin}h)(1)
=
\int_{0}^{\infty} h(u)\log u\,du.
}
$$

Это не definitional simplification: необходимы локальная интегрируемость, допустимость дифференцирования по комплексному параметру и точная Mellin-конвенция. Поэтому новый код

```markdown
PL2_DERIV_IDENTIFICATION_API_GAP
```

закрывает реальный source–target type gap, а не добавляет бюрократию. `[ABSTRACT][CONDITIONAL]`

### 2\. Нулевая масса через трансляционную инвариантность — лучший маршрут

Если

$$
h=\varphi-\tau_c\varphi,
\qquad
(\tau_c\varphi)(u)=\varphi(u-c),
$$

то при допустимой измеримой интегрируемой $\varphi$

$$
\int_{\mathbb R}\tau_c\varphi
=
\int_{\mathbb R}\varphi
$$

по трансляционной инвариантности меры Лебега, а значит

$$
\int h=0.
$$

Это сильнее и чище ручного вычисления двух треугольных интегралов: форма bump может впоследствии меняться, а доказательство массы останется тем же. Нужно только source-lock’нуть extension-by-zero и убедиться, что обе поддержки лежат в положительной полуоси, используемой Mellin transform. `[ABSTRACT][PAPER]`

### 3\. Строгость log-момента через константные границы — ратифицирована

Пусть две неотрицательные равномассные bump-функции имеют массу $m>0$, причём

$$
\operatorname{supp}\varphi\subset[a,b],
\qquad
\operatorname{supp}\psi\subset[c,d],
\qquad
0<a\le b<c\le d.
$$

Тогда

$$
\int\varphi(u)\log u\,du
\le
m\log b,
$$

а

$$
\int\psi(u)\log u\,du
\ge
m\log c.
$$

Следовательно,

$$
\int(\varphi-\psi)\log u\,du
\le
m(\log b-\log c)<0.
$$

Это даёт строгий знак без вычисления точного логарифмического интеграла. В Lean это также лучше: используются монотонность `Real.log`, неотрицательность, монотонность интеграла и точное равенство масс. `[ABSTRACT][PAPER]`

T4a действительно уже закрыт локально: Goal 039 фиксирует theorem `mellin_compactSupport_analyticOnNhd`, снятие `H_mellin` из T5 и отсутствие необходимости нового Aristotle iteration. Контракт v3 уже помечен `SUPERSEDED_BY_039_LOCAL_PROOF / DO_NOT_SUBMIT`; повторный запуск запрещён как дублирующий.

## FINAL PROPOSAL

Goal 040 принимать в repaired форме, где доказательная цепочка PL2 выглядит ровно так:

$$
\boxed{
\text{translated equal-mass bumps}
}
$$
 
$$
\Downarrow
$$
 
$$
\boxed{
\int h=0
}
$$
 
$$
\Downarrow
$$
 
$$
\boxed{
\int h(u)\log u\,du<0
}
$$
 
$$
\Downarrow\quad
\texttt{PL2\_DERIV\_IDENTIFICATION}
$$
 
$$
\boxed{
\operatorname{deriv}(\operatorname{Mellin}h)(1)\neq0
}
$$
 
$$
\Downarrow
$$
 
$$
\boxed{
\neg\operatorname{ContinuousAt}
\bigl(w\mapsto\zeta(w)\operatorname{Mellin}h(w)\bigr)\,1.
}
$$

`[ABSTRACT][CONDITIONAL]`

Ни одна стрелка не должна заменяться численным интегралом или утверждением «очевидно по дифференцированию под знаком интеграла».

### Registered prediction P040-PL2

```markdown
Generic simple-zero ⇒ raw-product discontinuity
закроется переиспользованием уже существующего residue/slope theorem.

Основное Lean-трение будет в exact derivative identification
deriv(Mellin h) 1 = ∫ h log,
а не в финальном доказательстве разрыва.
```

`[ABSTRACT][CONDITIONAL]`

## STRONGEST ATTACK

Сильнейшее возражение к repaired Goal 040:

> Отрицательный log-момент ещё не является отрицательной производной Mellin transform, пока не доказана законность дифференцирования и не сверена нормировка комплексной степени.

Именно поэтому новый failure code нужен. Без этого Codex мог бы доказать:

```markdown
∫ h(u) log u du < 0
```

и затем перескочить к

```markdown
deriv (Mellin h) 1 ≠ 0
```

через неподтверждённое тождество. Это было бы доказательством соседнего факта, а не PL2.

Второе возражение:

> Константные границы дают строгий знак только при положительной массе и строгом разделении поддержек.

Поэтому Goal 040 обязан иметь явные поля:

```markdown
bump_mass > 0
right_support_lower > left_support_upper
```

Удаление любого из них должно ломать strictness. Если поддержки только касаются, получается максимум $\le0$, не `<0`.

## CODEX DIRECTIVE

```markdown
NO_NEW_DIRECTIVE.

Goal 040 уже сформулирован диспетчером.
Не создавать конкурирующий PL2 goal.
Не отправлять T4a supplier в Aristotle.
Не пересобирать pole-subtracted shell.

После mirror-sync судья проверяет только:
  1. точный текст Goal 040;
  2. наличие трёх repaired slots;
  3. точные primary/failure codes;
  4. обе формулировки Rule 0.
```

## RULE 0 — КРИТЕРИЙ РАТИФИКАЦИИ

Одна live-формулировка уже видна:

> по умолчанию сообщение агенту показывается владельцу, а не отправляется; прямое отправление разрешено только после явного «отправь»; адресат и канал указываются однозначно.

Для ратификации двух формулировок они должны быть семантически эквивалентны следующим трём условиям:

```markdown
R0.1 DEFAULT_SHOW:
  подготовка текста не является разрешением на отправку.

R0.2 EXPLICIT_SEND_AUTHORITY:
  отправка разрешена только явной текущей командой владельца;
  старое общее "go" или факт готовности goal не считается разрешением.

R0.3 RECIPIENT_AND_CHANNEL_LOCK:
  перед действием однозначно названы адресат и канал:
  "Aristotle, CLI", "Codex, CLI", "Прошке, браузер", и т. п.
```

Если одна версия говорит «не отправлять без явного разрешения», а другая допускает автоматическую отправку по state-machine phase, это не редакционная разница, а конфликт. Точная ратификация удерживается до pin-URL обеих версий.

## META CLOSEOUT

**Что стало меньше?**  
PL2 разложен на три независимых и проверяемых кирпича: mass, log-moment, derivative identification.

**Что убито?**

- повторный T4a-run;
- ручное вычисление массы как обязательный путь;
- точное вычисление log-интеграла там, где достаточно разделения поддержек;
- неявный переход от log-момента к производной Mellin transform.

**Что нельзя повторять?**

Нельзя считать theorem

$$
\int h\log<0
$$

готовым PL2 без theorem

$$
\operatorname{deriv}(\operatorname{Mellin}h)(1)=\int h\log.
$$

**Current smallest named gap:**

```markdown
PL2_DERIV_IDENTIFICATION_API_GAP
```

**Следующий решающий тест:**

```markdown
lake-check exact derivative-identification lemma
under the actual Mellin definition and bump hypotheses.
```

**Rule 0:** математически не связан с PL2; его exact-text ratification остаётся отдельным control-plane актом после mirror-sync.

```markdown
iteration:
  target: Goal_040_PL2_repair
  status: OPEN
  failed_strategy: implicit_derivative_identification_and_duplicate_T4a_cloud_run
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: PL2_DERIV_IDENTIFICATION_API_GAP
  invariant_learned: strict log moment and Mellin derivative are distinct typed objects
  forbidden_future_move: send prepared text or duplicate theorem without explicit owner authorization
  next_decisive_test: pinned_goal_040_and_rule0_exact_text_audit
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

--- VERBATIM PAYLOAD ENDS ---
═══ FILE END: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL040_RATIFIED_PENDING_PIN_2026-07-31.md ═══

═══ FILE BEGIN: docs/routeB_bus/proshka/PROSHKA_VERDICT_DRAFT041_HOLD_VERSIONED_REPAIR_2026-07-31.md ═══
# PROSHKA VERDICT — DRAFT_041_HOLD_FOR_VERSIONED_REPAIR
Date received: 2026-07-31 (chat timestamp "Today 7:12 AM" preceded this message)
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
Consumed by: revert of goal-040 AMENDMENT A1 (goal restored to pinned SHA
48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300);
docs/routeB_bus/041_goal040_postclose_requirements_audit.md
Transport artifacts note: payload is verbatim as pasted by the owner from the
Proshka browser chat; copy-paste escaping artifacts preserved unmodified
(backslash-escaped underscores, "## STATUS" heading level, fences rendered as
```markdown). Semantic content untouched; no editing performed.

--- VERBATIM PAYLOAD BEGINS ---

## STATUS: OPEN — DRAFT\_041\_HOLD\_FOR\_VERSIONED\_REPAIR

```markdown
primary_verdict: DRAFT_NOT_SENDABLE_AS_WRITTEN
draft_is_send_authority: false
direct_send_authorized: false

rule_disambiguation:
  conceptual_split_A_vs_B: RATIFIABLE
  exact_text_equivalence_A: PENDING
  exact_text_equivalence_B: PENDING
  proposed_file_in_current_rh_clean: ABSENT

goal_040:
  current_status: PL2_RAW_POLE_MISMATCH_WITNESS_PROVED
  current_goal_mutation_after_answer: FORBIDDEN
  postclose_amendment_required_location: SEPARATE_VERSIONED_ARTIFACT
  proof_used_tent_log_moment_route: false
  proof_used_cheaper_exact_mellin_witness: true

goal_041:
  current_status: CONDUCTOR_HANDOVER_COMPLETE
  currently_states_goal_040_unchanged: true

route_state: CHALLENGER_NOT_RH
bus_010: VOID
state_promotion: false
```

## ROUTE MAP

Черновик **не отправлять пока**. Разделение двух разных «Rule 0» на:

```markdown
Rule A = RULE_INVENTORY_FIRST
Rule B = RULE_SEND_DISCIPLINE
```

концептуально правильное. Ратификация должна быть раздельной:

```markdown
A: A1 ≡ A2
B: live formulation ≡ R0.1–R0.3
```

`[ABSTRACT][PAPER]`

Но в текущем `rh_clean` файл

```markdown
docs/routeB_bus/proshka/RULE_NAMING_DISAMBIGUATION_2026-07-31.md
```

ещё отсутствует. Поэтому draft сейчас описывает будущий объект как уже материализованный. `[ABSTRACT][CONDITIONAL]`

Есть более серьёзная проблема. Текущий ответ 041 уже закрыт как `CONDUCTOR_HANDOVER_COMPLETE` и прямо фиксирует, что Goal 040 был **не изменён** и завершён отдельным ответом.

Сам Goal 040 уже закрыт:

```markdown
PL2_RAW_POLE_MISMATCH_WITNESS_PROVED
```

с Lean-проверенным theorem `exists_rawZetaMellin_not_continuousAt_one`, зелёной сборкой, нулевым taint и стандартной тройкой аксиом.

## FINAL PROPOSAL

### Rule A / Rule B

Оставить предложенное именование. После sync предоставить один commit-pinned файл, содержащий:

```markdown
Rule A:
  обе точные формулировки A1 и A2;
  явное утверждение эквивалентности только внутри этой пары.

Rule B:
  live formulation;
  R0.1 DEFAULT_SHOW;
  R0.2 EXPLICIT_SEND_AUTHORITY;
  R0.3 RECIPIENT_AND_CHANNEL_LOCK;
  mapping между ними.
```

Тогда A и B можно ратифицировать независимо. `[ABSTRACT][PAPER]`

### Goal 040

**Не вставлять `AMENDMENT A1` задним числом в уже закрытый goal-файл.**

Исходный Goal 040 и его ответ образуют source-locked транзакцию. Ответ 040 пинит конкретный SHA goal-файла и сообщает, что theorem уже доказан. Изменение goal после результата превратит контракт в ретроактивно отредактированный.

Правильный объект:

```markdown
docs/routeB_bus/041_goal040_postclose_requirements_audit.md
```

или следующий нумерованный audit-goal. Его header:

```markdown
status: POSTCLOSE_REVIEWER_REQUIREMENTS
normative_for_goal_040_execution: false
modifies_goal_040_contract: false
```

В нём можно дословно сохранить:

```markdown
A1.1:
  bump_mass > 0
  right_support_lower > left_support_upper

A1.2:
  log-moment without derivative-identification theorem
  ⇒ PL2_DERIV_IDENTIFICATION_API_GAP

A1.3:
  P040-PL2 registered prediction
```

Но это будут **post-close reviewer guards**, а не условия, которые будто бы были исполнены доказательством 040.

### Исправление пункта (2) в черновике

Заменить его на:

> «Оба STRONGEST-ATTACK требования сохранены в отдельном post-close audit; исходный Goal 040 и его source hash не изменялись. Goal 040 уже закрыт более дешёвым точным свидетелем: компактной квадратичной функцией с явной Mellin-формулой и $\operatorname{deriv}(\operatorname{Mellin}h)(1)=-1/12$. Поэтому tent/translation/log-bound маршрут классифицирован как sound but superseded, а не как фактически использованный proof route.»

Это соответствует реальному ответу 040: вместо двух translated tents была использована функция

$$
h(u)=1_{(0,1]}(u)\,u-\frac32\,1_{(0,1]}(u)\,u^2,
$$

для которой Mellin transform вычислен точно, масса равна нулю, а производная в единице равна $-1/12$.

## STRONGEST ATTACK

Главное возражение к текущему draft:

> После закрытия theorem вы изменили текст goal так, чтобы выполненная работа выглядела как исполнение новых требований.

Это ретроактивный ремонт контракта. Он ломает:

```markdown
registration-before-test;
source-hash provenance;
prediction scoring;
answer-to-goal correspondence.
```

`[ABSTRACT][PAPER]`

Второе возражение:

> Draft утверждает, что требования про translated tents, translation invariance и constant log bounds были внесены и исполнены, хотя фактическое доказательство выбрало другой witness.

Фактический маршрут был дешевле и сильнее: exact Mellin formula. Прогноз `P040-M3` в ответе 040 честно оценён как `SUPERSEDED_BY_CHEAPER_EXACT_WITNESS`, а не как подтверждённый использованный путь.

## CODEX DIRECTIVE

```markdown
NO EXECUTION DIRECTIVE.

Do not send the browser message.
Do not mutate the closed Goal 040.
Do not replace placeholders yet.

After mirror-sync, provide:
  1. exact HEAD;
  2. SHA-256 of the materialized Proshka verdict;
  3. pinned Rule A/B disambiguation file;
  4. separate post-close requirements audit;
  5. confirmation that original Goal 040 SHA remains unchanged.
```

## META CLOSEOUT

**Что стало меньше?**

Запрос распался на две независимые проверки:

```markdown
Rule naming/equivalence audit;
version-safe Goal 040 post-close audit.
```

**Что убито?**

```markdown
единый неоднозначный ярлык "Rule 0";
ретроактивное изменение закрытого Goal 040;
утверждение, что tent/log-moment route был фактическим proof route.
```

**Что нельзя повторять?**

Нельзя менять зарегистрированный goal после появления matching answer. Новые требования оформляются отдельным versioned audit или новым goal.

**Current smallest named gap:**

```markdown
RULE_A_B_EXACT_TEXT_AND_VERSION_SAFE_POSTCLOSE_PIN
```

**Следующий решающий тест:**

```markdown
original Goal 040 SHA before/after 041 sync must be identical.
```
```markdown
iteration:
  target: draft_reply_after_goal_041
  status: OPEN
  failed_strategy: retroactive_goal_amendment
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: RULE_A_B_EXACT_TEXT_AND_VERSION_SAFE_POSTCLOSE_PIN
  invariant_learned: a closed goal is immutable; later reviewer requirements need a separate artifact
  forbidden_future_move: rewrite a proved contract to match later feedback
  next_decisive_test: compare original_goal_040_sha_across_sync
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```

--- VERBATIM PAYLOAD ENDS ---
═══ FILE END: docs/routeB_bus/proshka/PROSHKA_VERDICT_DRAFT041_HOLD_VERSIONED_REPAIR_2026-07-31.md ═══

