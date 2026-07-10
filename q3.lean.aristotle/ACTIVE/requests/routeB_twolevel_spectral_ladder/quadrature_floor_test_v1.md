# QuadratureFloorTest_v1

Route B TwoLevelSpectralLadder diagnostic only. Not RH. No Phase 2. One point `(lambda_sq,N)=(13,120)`.

## Verdict

- status: `complete_with_registered_failure`
- fork_verdict: `FLOOR_AMBIGUOUS`
- failure_codes: `['FLOOR_AMBIGUOUS', 'Y_CACHE_MISSING']`
- reason: lambda1(G_even) moved outside x3 but did not satisfy the >=1e4 drop rule.
- instrument floor: Current make_packets path is double/numpy based; dust did not scale to requested 1e-15/1e-18 targets.

## Q1 Packet Rebuild Dust

| run | requested tol | quad_order | max delta_off | k1 | k2_odd | k2_even |
|---|---:|---:|---:|---:|---:|---:|
| `baseline_tol_1e-9` | `1e-9` | 900 | `1.0042009e-14` | `7.9977121e-15` | `1.0042009e-14` | `8.8380937e-15` |
| `requested_tol_1e-15` | `1e-15` | 1800 | `6.0892525e-15` | `6.0892525e-15` | `5.5438922e-15` | `5.7750985e-15` |
| `requested_tol_1e-18` | `1e-18` | 3600 | `5.4386754e-15` | `4.8399003e-15` | `5.4386754e-15` | `4.9619286e-15` |

Dust ratios:
- tol=1e-15 over baseline: `0.60637792`
- tol=1e-18 over baseline: `0.54159237`
- registered proportional drop pass: `False`

## Q2 Recomputed Metrics

| run | a1 raw | a1 even-projected | lambda1(G_even) | lambda2(G_even) | 1-|<xi1,k1_even>| | ||y|| |
|---|---:|---:|---:|---:|---:|---:|
| `baseline_tol_1e-9` | `5.9933907e-28` | `3.780565e-28` | `3.6653785e-28` | `5.1438549e-28` | `2.3459413e-9` | `2.5791514e-9` |
| `requested_tol_1e-15` | `3.9675753e-28` | `2.6745026e-28` | `2.2914021e-28` | `2.8120725e-28` | `2.3459413e-9` | `2.5791513e-9` |
| `requested_tol_1e-18` | `1.7834212e-28` | `1.047344e-28` | `9.4821691e-29` | `2.0321283e-28` | `2.3459413e-9` | `2.5791511e-9` |

Lambda1 movement:
- tol=1e-15 / baseline: `0.62514748`; drop factor `1.5996225`
- tol=1e-18 / baseline: `0.2586955`; drop factor `3.8655485`
- within x3 at both tightened labels: `False`
- M selector by latest ||y||: `M-alt`

## Q3 Free Pulls

| lambda_sq | N | status | ||y|| | source |
|---:|---:|---|---:|---|
| 12 | 120 | `MISSING` | `MISSING` | `out/nconv_anchor_lambda_sq_12_N_120.json,out/full_low_eig_lambda_sq_12_N_120.json,out/feshbach_lambda_sq_12_N_120.json` |
| 13 | 120 | `OK` | `2.57915135844e-9` | `out/nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache[0].y_norm` |
| 14 | 120 | `OK` | `2.79748987449e-9` | `out/feshbach_lambda_sq_14_N_120.json` |

## Stop

Stop after this report + handoff. Carry the fork verdict and any failure code into `OperatorStaticSchurStabilityGate` on `S0_parity`.
