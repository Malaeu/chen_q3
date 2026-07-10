# ZeroSumProfile_v2_Addendum

## Headlines

1. Phase-origin artifact confirmed? NO
2. Detrended comb mechanism supported? NO
3. Edge value closure passes? YES
4. S_2000/a1 and tail status: `None` / `NOT_RUN_PHASE_NOT_LINEAR`
5. Verdict code: `PHASE_NOT_LINEAR`, `COMB_MECHANISM_STILL_REFUTED`, `EDGE_CLOSURE_PASS`, `BK_EDGE_IMPORT_INCOMPLETE`

Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.

## A1 Phase Audit

- registered primary slope `-log(sqrt(13))=-1.282474678730768`.
- registered secondary slopes `+/-2log(sqrt(13)) = 2.564949357461537`, `-2.564949357461537`.
- best registered slope: `primary_minus_log_lambda` = `-1.282474678730768`.
- best registered circular MAD: `0.653804431635` rad; threshold `0.05`.
- corrected median `|Im|/|Re|` at best registered slope: `0.633661603928`.
- unrestricted diagnostic grid best slope: `0.0`, MAD `0.035980699028`.
- code: `PHASE_NOT_LINEAR`.

| candidate | slope | circular MAD | median corrected |Im|/|Re| |
| --- | ---: | ---: | ---: |
| `primary_minus_log_lambda` | `-1.282474678730768` | `0.653804431635` | `0.633661603928` |
| `secondary_plus_2log_lambda` | `2.564949357461537` | `0.723460536765` | `0.836440113211` |
| `secondary_minus_2log_lambda` | `-2.564949357461537` | `0.75504938187` | `0.761525140416` |

## A2 Detrended Comb

- post-peak count: `438` after j `62`.
- Spearman `|K|*gamma` vs `T(gamma)`: `0.0401690480494`.
- Spearman `|K|*gamma` vs `L(gamma)`: `0.093628144418`.
- registered repaired T corr pass: `False`.
- low-range gamma limit `2*pi*13=81.6814089933`; count `21`.
- low-range `|K|` vs `T/gamma`: `-0.314285714286`.
- low-range `|K|` vs `L/gamma`: `-0.574025974026`.
- code: `COMB_MECHANISM_STILL_REFUTED`.

## A3 Edge Value Check

- `g04(1)=-8.944672990089223e-30`.
- `k_edge=-3.618726628677109e-29`; `|k_edge|=3.618726628677109e-29`.
- registered `|k_edge|` window pass: `True`.
- median j in [300,500] of `|K|*gamma`: `4.334196465014907e-29`.
- closure ratio: `0.671363872636`; pass `True`.
- edge code: `EDGE_CLOSURE_PASS`.
- BK endpoint identity: `BK_EDGE_IMPORT_INCOMPLETE`.

## A4 Extension

- status: `NOT_RUN`.
- reason: A1 phase audit failed; objective says STOP before A4 extension.
- S_2000/a1: `None`.
- tail status: `NOT_RUN_PHASE_NOT_LINEAR`.

## A5 State

- `PHASE_ORIGIN_ARTIFACT` not recorded because A1 did not pass.
- `DISPLACED_PROFILE` not promoted because A4 was not run.
