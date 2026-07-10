# AnchorLocked_Extraction_v1

Status: NOT RH. Diagnostic Route B / Route Z E5 extraction only. No Phase 2, no new run, no matrix build, no zeros computed.

## Verdict

- Overall: `REJECTED_E2_MASS_P_OUT_OF_RANGE`
- J0: `JSON_SHA_MATCH`; input sha256 `65fa8e57978bb610d96c36e3ace877f0a910fc2ecad4fcda11524c26e3f182f9`.
- K1 self-test: fired `True` at `lambda_sq_14_N_120/J=100/C band judge`.
- E1: `LEDGER_LAMBDA_CLASS_PASS`.
- E2: `MASS_P_OUT_OF_RANGE`.
- E3: `UNIVERSAL_COLLAPSE_CONFIRMED`.
- E4: `RELABEL_REJECTED_E2_MASS_P_OUT_OF_RANGE`.

## Protocol Guardrails

- `not_RH` from JSON: `True`
- `phase2_run` from JSON: `False`
- `qW_formula_changed` from JSON: `False`
- `packet_definition_changed` from JSON: `False`
- `q3_main_touched` from JSON: `False`

## E1 Ledger C(lambda)

| point | C(J=100) | C(J=150) | C(J=200) | median C | band | pass |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| `lambda_sq_12_N_120` | `3.098551e-26` | `3.184515e-26` | `3.194178e-26` | `3.184515e-26` | `1.7E-26..6.8E-26` | `True` |
| `lambda_sq_14_N_120` | `1.668191e-31` | `1.713232e-31` | `1.658594e-31` | `1.668191e-31` | `9E-32..3.6E-31` | `True` |
| `lambda_sq_13_N_90` | `8.197454e-29` | `8.017769e-29` | `7.945851e-29` | `8.017769e-29` | `4E-29..1.6E-28` | `True` |

- C(13,120) anchor column quoted from A5: `7.9190e-29` (`7.918973462925e-29`).
- Slope log(C^2/E) vs log(lambda): `10.6081165937` +/- `2.24959615971`; registered `11 +/- 1.5`; packet-side quote `11.27`; `FIT_NOT_LAW`.

## E2 Mass-P

| window | gamma range | right-end C | C band pass | DeltaS/a1 |
| --- | --- | ---: | --- | ---: |
| `W1` | `811.184..1123.1` | `7.296642e-29` | `True` | `1.121400e-01` |
| `W2` | `1123.1..1419.42` | `7.175621e-29` | `True` | `3.575787e-02` |
| `W3` | `1419.42..1980.91` | `8.085985e-29` | `True` | `5.913649e-03` |
| `W4` | `1980.91..2515.29` | `8.864154e-29` | `True` | `2.655122e-03` |

- Registered C band: `6E-29..1.2E-28`.
- Mythos hand values quoted: W3 `9.3e-29`, W4 `8.7e-29`.

| adjacent pair | DeltaS ratio | p_mass | registered | pass |
| --- | ---: | ---: | --- | --- |
| `W1/W2` | `3.13609175755` | `2.02180339103` | `0.8..1.4` | `False` |
| `W2/W3` | `6.04666797186` | `4.63439244204` | `0.8..1.4` | `False` |
| `W3/W4` | `2.22726112709` | `1.39442397632` | `0.8..1.4` | `True` |

- E2 note: C-band passes on checkpoint C values; strict DeltaS adjacent-pair p_mass does not pass all registered bands.

## E3 Universality Line

| point | S200/a1 | source |
| --- | ---: | --- |
| `lambda_sq_13_N_120` | `0.506` | goal-supplied certified scalar |
| `lambda_sq_12_N_120` | `0.532378861797` | JSON A4 |
| `lambda_sq_14_N_120` | `0.523285585406` | JSON A4 |
| `lambda_sq_13_N_90` | `0.564719291914` | JSON A4 |

- Mean `0.531595934779` vs registered `0.53`; spread `0.0331233571347` by `max absolute deviation from mean`; full range `0.0587192919139`.

## E4 Relabel

- Requested relabel: `TAIL_FLATTENING_REFUTED -> TAIL_MASS_CONFIRMED + P_ESTIMATOR_ARTIFACT`.
- Extraction status: `RELABEL_REJECTED_E2_MASS_P_OUT_OF_RANGE`.
- Grounds: S2000/a1 `0.87059768426044775376272264634320593360472377175817945734893165465299634801616243693750656`; C_refit relative miss `0.00240170416777235807135863169895080726085018263076526179861967353813370907540083849703503189`; E2 code `MASS_P_OUT_OF_RANGE`.
- Future gate note: `raise tau denominator dps 80 -> 100`.

## Final State Action

- ROUTE_B_STATE.md update mode: `append_rejection_history_no_tail_relabel`.
- handoff_to_proshka.md rewritten for this extraction.
- No next gate selected.

## Output JSON

- `out/anchor_locked_extraction_v1.json`.

## Actions Log

- `anchor_locked_extraction_v1_actions_log.md`.
