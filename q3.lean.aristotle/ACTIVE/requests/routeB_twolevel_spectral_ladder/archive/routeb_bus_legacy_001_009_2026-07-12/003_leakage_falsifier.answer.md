# MYTHOS_PROSHKA_HANDOFF: LeakageFalsifier_v1

STATUS: STOP.
SCOPE: NOT_RH; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.

## Verdict

Code: `H2_HOLDS + SIN_VANISHING_REFUTED + LEFT_EDGE_MISMATCH`.

The good news is real: the concrete `g04` satisfies the H2 fork very strongly.

The bad news is also real: the registered integer-sampling `lambda/k^2` law does not hold for the current prolate basis samples, and the direct/Poisson left-edge cross-check misses the strict `1e-3` agreement target.

## Scoreboard

| Test | Measured | Verdict |
| --- | ---: | --- |
| F0 `|g04(0)| <= 1e-8 * ||E(g04)||` | `|g04(0)|/||E|| = 3.26204312015e-60` | `H2_HOLDS` |
| F1 ratios for k=2..4 in `[0.5,1.5]`, all n | all fail | `SIN_VANISHING_REFUTED` |
| F1 constant sign in k | fails for n=0,2,4 | FAIL |
| F2 direct/Poisson rel agreement <= `1e-3` | `0.0117387719214` | FAIL |
| F2 magnitude band `[1.7e-29,4.2e-28]` | `3.48978688614e-29` | PASS |
| K1 phase plant `i^n -> +1` must break | inert for current `g04=h0/h4` | JUDGE NOT INFORMATIVE |

## F1 integer samples

Ratios are `|psi_n(k)| * k^2 / (lambda * |psi_n(1)|)`.

| n | `i^n` | k=2 | k=3 | k=4 | sign pattern k=1..4 | power fit p, k=2..8 |
| ---: | ---: | ---: | ---: | ---: | --- | ---: |
| 0 | `+1` | `0.0187613873388` | `0.0724894546147` | `0.0731214618359` | `+ - - +` | `0.817956485129` |
| 2 | `-1` | `0.0520851812150` | `0.0431448391378` | `0.0317239721784` | `+ + + -` | `1.23935109663` |
| 4 | `+1` | `0.0345426098392` | `0.00456420905570` | `0.0169377350350` | `+ - + -` | `0.237820289542` |

The mpmath period-split quadrature was cross-checked against the analytic Legendre/Bessel integral formula for k=1..4. Relative discrepancies were about `1e-38..1e-42`, so this is not a quadrature artifact.

## F2 left-edge cross-check

| Quantity | Value |
| --- | ---: |
| direct `E(g04)(1/lambda)` | `-1.63792282855e-29` |
| Poisson k=1..8 | `-1.65715003106e-29` |
| relative mismatch | `0.0117387719214` |
| `|direct| / ||E(g04)||` | `3.48978688614e-29` |
| H2 correction subtracted | `0` |

The planted phase-book violation did not break agreement because the current project packet is exactly `g04 = h0/h4`; both branches have `i^0=i^4=+1`. For this packet, forcing all phases to `+1` leaves the Poisson side unchanged (`delta_vs_normal_poisson = 0`). That means the K1 plant is structurally inert here, not that the phase-book judge passed.

## ACTIONS LOG

Commands:

- `/Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python leakage_falsifier_v1.py`
- Extra read-only validation: rebuilt the same prolate model and compared period-split quadrature to the Legendre/Bessel closed integral for F1 k=1..4.

Artifacts:

- `bus/003_leakage_falsifier.goal.md`
  sha256 `4e3fbf0e7eee96e6bcf9a5c07ae29e566dcb7dc49120607f3042ddc354b4ec78`
- `leakage_falsifier_v1.py`
  sha256 `de943fb3c25a9064e9e82a6b47d39da85f2923404a83cfbb7578014d49c30506`
- `out/leakage_falsifier_v1.json`
  sha256 `69fe0bf62bfab2172dd47cdffd6572acdd8fbd4a792a0237b5d1871097e4719e`
- `ROUTE_B_STATE.md`
  sha256 after history update `9b13b0b011db4d5f04ae7e321ad9f0622e102947047997e846a5c21631231a1e`

Read-only inputs:

- `docs/PEN_3_1_4_SMOOTH_REMAINDER_v1.md`
  sha256 `a913cbdc5e08ca9103760b14a89cd3f97e2fd0980e40a5c9fc391fa3049f8c45`
- `out/portable_k_coeffs_lambda_sq_13_N_120.json`
  sha256 `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88`

State:

- One history line added to `ROUTE_B_STATE.md`.
- `bus/004_split_identity_check.goal.md` remains unexecuted.
- No next gate selected by LeakageFalsifier_v1. STOP.
