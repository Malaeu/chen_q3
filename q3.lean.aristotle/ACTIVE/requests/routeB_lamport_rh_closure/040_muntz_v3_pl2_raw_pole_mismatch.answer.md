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
