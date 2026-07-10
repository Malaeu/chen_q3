# Operator Static Schur Stability Gate

Status: diagnostic only. Not a proof of RH. Not a Route B kill. Phase 2 was not run. QW formulas and packet definitions were not changed.

## Headline

1. Is parity-zero structural judge clean? [NO; `PARITY_CONTAMINATION` at `(lambda_sq,N)=(13,120)`]
2. Is aligned S0 operator stable in N? [UNKNOWN; stopped before drift interpretation]
3. Is broad-tail self-energy stable? [UNKNOWN; previous broad-tail evidence exists, but this gate stops on parity instrumentation]
4. Is S0 ground direction aligned with k1? [UNKNOWN; stopped before handoff interpretation]
5. Is remaining instability only scalar scale drift? [UNKNOWN; stopped before drift interpretation]
6. Verdict code: `PARITY_CONTAMINATION`

## O0 Inventory

| lambda_sq | N | phase1 scalar JSON | static Schur operator matrix | note |
|---:|---:|---|---|---|
| 12 | 60 | True | NO | `eigenvalues_only_no_S0_matrix` |
| 12 | 90 | True | NO | `eigenvalues_only_no_S0_matrix` |
| 12 | 120 | True | NO | `scalar only / no static operator cache` |
| 13 | 60 | True | NO | `scalar only / no static operator cache` |
| 13 | 90 | True | NO | `scalar only / no static operator cache` |
| 13 | 120 | True | YES | `full_operator_anchor_from_nconv` |
| 14 | 60 | True | NO | `scalar only / no static operator cache` |
| 14 | 90 | True | NO | `scalar only / no static operator cache` |
| 14 | 120 | True | NO | `feshbach_static_eigenvalues_plus_G_no_S0_matrix` |

`(12,120)` is a missing hard static-Schur operator anchor, but it was not bought because the mandatory parity-zero judge failed first on the available full anchor.

## O2+ Parity-Zero Structural Judge

Anchor checked first: `(lambda_sq,N)=(13,120)`, source `out/nconv_anchor_lambda_sq_13_N_120.json`. Matrix order is `[k1, k2_odd, k2_even]`, so the checked odd/even entries are `(k1,k2_odd)` and `(k2_even,k2_odd)`.

| matrix | abs(k1,odd)/norm | abs(even2,odd)/norm | threshold | pass |
|---|---:|---:|---:|---|
| `G` | `0.0991838872602823218294076923485` | `0.178498637030342854892239756737` | `1e-25` | `False` |
| `K_schur` | `0.0991838872602823218294076923485` | `0.178498637030342854892239756737` | `1e-25` | `False` |
| `S0` | `4.10023431891746556275076849818e-19` | `1.13380497620053358462321431327e-15` | `1e-25` | `False` |

The required threshold is `<= 1e-25`. `S0` fails with ratios approximately `4.10e-19` and `1.13e-15`; therefore this is an instrumentation/parity contamination stop. Per goal, drift and stability interpretation are not allowed after this failure.

## Raw Block Split (Not Interpreted)

These values are recorded only for debugging the contamination; they are not promoted to operator-stability evidence.

```text
S0_oo = (3.0559134563989372500529767361349022218785049287059669709510014183634932257280172e-55 + 3.8407788224652712412272288196597754899615475817897888197715808658922209072044127e-93j)
eig(even 2x2) = ['3.4839881993313211961662855573281512815804405774566057431390124475579670783137338e-59', '1.3118543347202132108870878947367988798274794795109816081232281113233331856897737e-51']
Delta_eff = (3.0555650575790040654917810671080714191242947411280989866975761841450172491130507e-55 + 3.8407788224652712412272288196597754899615475817897888197715808658922209072044127e-93j)
```

## Decision

Stop code: `PARITY_CONTAMINATION`.

The next repair question is not N-drift, not Phase 2, and not boundary/prolate work. It is whether the request-local packet/S0 instrumentation must enforce parity exactly, for example by explicit even/odd block construction or parity symmetrization, before rerunning `OperatorStaticSchurStabilityGate`.

## Proshka Review

Status: `OPTION_3_THEN_OPTION_1`.

Proshka accepted `PARITY_CONTAMINATION` as an instrumentation stop until proven otherwise:

- do not interpret N-drift;
- do not buy a new `(12,120)` anchor now;
- do not go to boundary/prolate work;
- do not relax the registered `1e-25` parity threshold.

Recorded next gate:

```text
ParityLeakSourceAudit_then_ParityProjectedSchurRebuildGate
```

Recommended state labels:

```text
FAILURE_CODE = PARITY_CONTAMINATION
PRIMARY_DIAGNOSIS = SCHUR_PARITY_BLOCK_LEAK
SECONDARY_DIAGNOSIS = STATIC_SCHUR_OPERATOR_BUILD_NOT_CERTIFIED
ROUTE_STATUS = NOT_KILLED
NEXT_GATE = ParityLeakSourceAudit_then_ParityProjectedSchurRebuildGate
```

The next goal should first localize the parity leak at `(lambda_sq,N)=(13,120)` across packet parity, actual T parity, direct G parity, `K_schur` parity, and serialization/order. Only after that should it rebuild the Schur model in explicit even/odd parity blocks and compare the block-diagonal `S0_parity` against the previous mixed-basis S0 and actual `mu_i`.
