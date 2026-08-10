# MYTHOS_PROSHKA_HANDOFF: LeakageCloseout_v1

STATUS: STOP.
SCOPE: NOT_RH; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.

## Verdict

Code: `H2_NUMERIC_ONLY + SECOND_EDGE_CHANNEL + STAIL_DIVERGENT_SUSPECT + PLANT_REDESIGNED_FIRES`.

The registered truncation hypothesis is refuted. Extending the exact Poisson
sum from `k<=8` to `k<=40` does not close the 1.17% mismatch: the mismatch
briefly falls to 0.71% at `k=20`, then rises to 6.51% at `k=40`. This is the
registered `SECOND_EDGE_CHANNEL` fork.

## G1 — H2 constraint row

Code: `H2_NUMERIC_ONLY`.

The true-precision constructor contains one S0 condition on `(c_0,c_4)`, not
two. Verbatim source at `true_precision_packet_gate_v1.py:187-194`:

```py
integrals[which] = v[0] * mp.sqrt(2 * lam)
g04_c = normalize_real_combo([integrals[4], -integrals[0]])
"g04": {0: g04_c[0], 4: g04_c[1]},
```

Thus the imposed linear condition is exactly

`c_0 * integral(h_0) + c_4 * integral(h_4) = 0`.

The call to `normalize_real_combo` imposes coefficient normalization
`c_0^2+c_4^2=1`; it is not a second S0 condition. No `f(0)=0` row is present.

Numeric cross-check:

- `c_0 = 0.51858801151965464918`;
- `c_4 = -0.85502425363734012436`;
- integral residual: exactly `0` at working precision;
- `g04(0)/||E(g04)|| = -3.26204312015448e-60`.

Therefore the old near-zero is emergent-numeric and is not proof of H2-ZERO.
The exact dictionary branch remains `H2-POLE/CORRECTION`, with
`h_lambda(0) != 0`.

## G2 — Poisson tail truncation

Code: `SECOND_EDGE_CHANNEL`.

The Poisson integrals were evaluated using the exact Legendre/Bessel transform.
Independent period-split quadrature at deterministic random
`k = 18, 28, 33` agrees mode-by-mode to relative errors between approximately
`2.0e-40` and `1.1e-44`.

| k max | Poisson partial sum | relative mismatch vs direct |
| ---: | ---: | ---: |
| 8 | `-1.65715003106e-29` | `0.0117387719` |
| 12 | `-1.67884571758e-29` | `0.0249846258` |
| 16 | `-1.65586695376e-29` | `0.0109554155` |
| 20 | `-1.62625689979e-29` | `0.00712239219` |
| 24 | `-1.59964902838e-29` | `0.0233672793` |
| 28 | `-1.57741899046e-29` | `0.0369393704` |
| 32 | `-1.55909790387e-29` | `0.0481249320` |
| 36 | `-1.54394083228e-29` | `0.0573787694` |
| 40 | `-1.53128418464e-29` | `0.0651060246` |

Direct value: `-1.63792282855e-29`.

The partial sums localize the turn: agreement improves through `k=20`, then
worsens steadily from `k=24` through `k=40`. The residual is not explained by
simple `k<=8` truncation.

## G3 — S_tail certificate

Code: `STAIL_DIVERGENT_SUSPECT` under the registered two-part rubric.

| K | `S_tail(K)` |
| ---: | ---: |
| 8 | `1.30806394197e-30` |
| 20 | `2.07644390213e-30` |
| 50 | `3.26478470842e-30` |
| 100 | `3.77584522891e-30` |
| 200 | `4.04332191115e-30` |

Per-mode absolute sums at `K=200`:

- mode 0: `3.39833208910e-35`;
- mode 4: `4.04334230961e-30`.

Size judge passes:

- leading `k=1` combo: `1.69844037725e-29`;
- `S_tail(200)/leading = 0.238060868390 <= 0.5`.

Convergence judge narrowly misses:

- `(S_tail(200)-S_tail(100))/S_tail(200) = 0.0661527052`;
- registered requirement: `< 0.05`.

Therefore the requested finite size budget is supportive, but the registered
convergence certificate is not yet green.

## G4 — plant redesign

Code: `PLANT_REDESIGNED_FIRES`.

- Conjugate-convention shadow: relative change exactly `0`; both active Fourier
  multipliers are real. Registered `<1e-6` judge passes.
- `c_4 -> -c_4` Poisson shadow: relative mismatch vs the original direct value
  is `1.93490784289`.
- Relative to the `k<=40` baseline mismatch, amplification is `29.7193364x`,
  exceeding the registered `10x` requirement.

## ACTIONS LOG

Commands:

- `/Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python -m py_compile leakage_closeout_v1.py`
- `/Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python leakage_closeout_v1.py`
- First full run computed all six independent period-split cross-check rows;
  the deterministic rerun reused those pinned rows and regenerated the analytic
  payload and expanded partial-sum ledger.

Artifacts:

- `bus/006_leakage_closeout.goal.md`
  sha256 `bbb92c8d31c0611ea0c9243143980864d966eac2038995b995f260ca8d2c488e`
- `leakage_closeout_v1.py`
  sha256 `8b502b2f6ede6635fc1cb061f103a1d1f2ebd04e647c9aa774359fbd90fb95d9`
- `out/leakage_closeout_v1.json`
  sha256 `a44f9b152618d3189da0e115604ef979b431e3b5be54d0eadb007ec444914a38`
- `ROUTE_B_STATE.md`
  sha256 `c22a1d7186dbca1cf8edcf9f9cf5f75e490d4fb4ddad9c1bccf657b68cea8d27`

Read-only inputs:

- `true_precision_packet_gate_v1.py`
  sha256 `ebcd3befb0f93365b3fb3979c858464cba0fdd80ccec72f734f025581af38981`
- `out/leakage_falsifier_v1.json`
  sha256 `69fe0bf62bfab2172dd47cdffd6572acdd8fbd4a792a0237b5d1871097e4719e`
- `docs/PEN_3_1_4a_LEFT_EDGE_v3.md`
  sha256 `06683fd9f52f0c01e59f6a7ff8fe32c4a9d5cb72d614f2d40eec9b3a5e73b378`

State/git:

- Appended one `LeakageCloseout_v1` history line to `ROUTE_B_STATE.md`.
- `git diff --check` passed for the script, answer, and state files.
- JSON assertions for all four verdict codes and registered numeric thresholds
  passed.
- Scoped staged status after `git add`:
  - `A  ROUTE_B_STATE.md`
  - `A  bus/006_leakage_closeout.goal.md`
  - `A  bus/006_leakage_closeout.answer.md`
  - `A  leakage_closeout_v1.py`
  - `A  out/leakage_closeout_v1.json`
- Existing unrelated staged, modified, and untracked user/project files were
  preserved.
- No next gate selected. STOP.
