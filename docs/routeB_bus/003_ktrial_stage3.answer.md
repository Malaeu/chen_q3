# kTrial → Lean — stage 3 answer

Date: `2026-07-26`

Verdict: `KTRIAL_STAGE3_COEFFICIENT_BIND_LOCKED`

## Artifacts

- File: `Q3/Proofs/RouteB/D0KTrialStage3.lean`
- Lines: `114`
- Binding file: `Q3/Proofs/RouteB/D0CanonicalApproximation.lean`
- Binding-file lines: `162`
- Hole scan over stages 1–3: `0 sorry / 0 admit / 0 exact?`

## Source locks

| declaration | D0 source |
| --- | --- |
| `TrialNonzero` | `D0_5_GROUND_AND_TRIAL_TYPES.md:94-103`; `D0_7_EXACT_NORMALIZATION_REGISTRY.md:96-107` |
| `sTrial_m_N` | `D0_7_EXACT_NORMALIZATION_REGISTRY.md:96-107`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:195-215` |
| `kTrial_m_N` | `D0_5_GROUND_AND_TRIAL_TYPES.md:94-105`; `D0_7_EXACT_NORMALIZATION_REGISTRY.md:96-107`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:195-215` |
| `c_n` | `D0_7E_OWNER_INPUT.md:32-38`; `D0_7E_CENTRAL_MELLIN_CALIBRATION.md:129-143`; `D0_6_EXACT_TRANSFORM_CONVENTION.md:105-117` |
| `CoefficientFamily.kTrial` bind | exact anonymous record constructor with row `c_n=<V_n,kTrial>`; no new D0 object name |

`norm_kTrial_m_N` proves the D0 unit normalization.  The former free field
`CoefficientFamily.coeff` was replaced by `CoefficientFamily.kTrial`, and
an `rfl` example locks that field definitionally to the constructed normalized
projected vector without introducing an extra global object name.

The constructor takes `TrialNonzero` certificates explicitly; it does not
assert universal projected nonvanishing, ground equality, or a cofinal
central-nonzero schedule.

## Build

```text
lake build Q3.Proofs.RouteB.D0KTrialStage3
Build completed successfully (7755 jobs).
exit code: 0
```

## Axioms

```text
'Q3.RouteB.D0Pstar.TrialNonzero' depends on axioms:
[propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.sTrial_m_N' depends on axioms:
[propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.kTrial_m_N' depends on axioms:
[propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.norm_kTrial_m_N' depends on axioms:
[propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.c_n' depends on axioms:
[propext, Classical.choice, Quot.sound]
```
