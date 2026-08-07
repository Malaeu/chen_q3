# Goal 057 · CCM penalty Phase 2 fixed-q beta_N profile

```yaml
STATUS: CLOSED_PASS
VERDICT: CCM_FIXED_Q_BETA_N_INTERVAL_PROFILE_PASS
FINITE_PROFILE_CLASS: FIXED_Q_PROFILE_FINITE_POSITIVE_NOT_STABILIZED
ROUTE: CHALLENGER_NOT_RH
PROMOTION: FORBIDDEN
BUS_010: VOID
GOAL_055: HOLD
PX_RH_CLAIM: NOT_MADE
```

## Precommit исполнен буквально

```yaml
lambda: sqrt(13)
m: 13
N0: 120
N_ladder: [120, 160, 200, 240]
q: exact Phase-1 rational J-even projection in E_120
embedding: zero-padding only
precision_dps: [180, 360]
beta_initial_bracket: [0, 1e-48]
beta_search_tolerance: max(1e-100, 2^-40 * current_upper_bracket)
```

Ни один `q_N` не переоптимизировался после просмотра спектра. Moving-probe channel не
запускался и помечен `MOVING_PROBE_DIAGNOSTIC_NOT_TRANSFER_EVIDENCE`.

## Реализация и trust class

| Артефакт | SHA-256 |
|---|---|
| `phase2_scripts/ccm_beta_n_profile.py` | `851db5963b4ad012cc3746b2827931b1beedad0b931676d2b40f4cb9ca774f72` |
| `phase2_results/ccm_fixed_q_beta_n_profile.json` | `204e441ee807938335a3826257e1b77cb186fb9aa5416eec66b46cd54b69ff4b` |
| pinned Phase-1 builder | `1be57db69683652ed4f6d56dba6fc3b70c186f429fbb7f5bef978cd84f08ed0d` |
| pinned q source | `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` |

Первые две строки — финальные production pins после добавления явных cross-precision
gates.

Для каждого `N` exact Householder transform строит базис `[q,q-perp]`. Максимальный
certifiable floor равен

```text
beta*_N = min(lambda_min(K_odd), lambda_min(K_even restricted to q-perp)).
```

На безопасном нижнем endpoint вычисляется строгий Schur complement

```text
tau_required = beta - a + b* (C-beta I)^(-1) b,
```

после чего полная even+odd matrix повторно проходит interval `LDL^T`.

Production eigensolver: Arb `vdhoeven_mourrain`. Независимый полный повтор всех восьми
`N × precision` cells: Arb `rump`. Оба — интервальные алгоритмы; float64 verdict отсутствует.

## Retained 360-dps profile

| N | controlling sector | a | beta*_N | beta*_N - a | tau_required |
|---:|---|---:|---:|---:|---:|
| 120 | odd | `4.7199799795094300e-59` | `3.0559133975151657e-55` | `3.0554413995172147e-55` | `3.0555650130321454e-55` |
| 160 | odd | `4.7199799795094300e-59` | `2.7228638920503397e-55` | `2.7223918940523888e-55` | `2.7225515561212604e-55` |
| 200 | odd | `4.7199799795094300e-59` | `2.6230059967905176e-55` | `2.6225339987925666e-55` | `2.6227205969690432e-55` |
| 240 | odd | `4.7199799795094300e-59` | `2.4778868595077980e-55` | `2.4774148615098471e-55` | `2.4776049869106300e-55` |

На каждой строке:

- `a < safe beta < beta*_N` интервально;
- `tau_required < 1` интервально;
- full even LDL и odd LDL проходят;
- интервалы 180 и 360 dps для `a`, `beta*_N`, `beta*_N-a`, `tau_required` и контрольных
  элементов матрицы пересекаются.

## Что это говорит и чего не говорит

Положительность конечного fixed-q профиля настоящая. Bottleneck на всех четырёх точках —
не even `q-perp`, а первый odd-sector competitor. Значение `a` неизменно по `N`, что является
сильной проверкой буквального zero-padding и неизменности low-mode matrix entries.

Но `beta*_240 / beta*_120 = 0.8108498302087439...`: падение около `18.915%`. Поэтому
профиль **не** ратифицирует стабилизацию и не доказывает
`inf_N (beta*_N-a) > 0`. Это остаётся сильнейшей неоднозначностью Phase 2.

Итог ограничен конечной CCM family diagnostics: не `SlotH2a`, не continuum transfer,
не all-lambda input A, не uniform operator gap и не RH.

## Capability receiver audit before Phase 3

`CAPABILITY_RECEIVER_AUDIT_BEFORE_PHASE3_2026-08-07.md` подтвердил два ранее не
подключённых sorry-free receivers. `SectorIsolationRadius` применим к Phase-2 тройке после
явного relabel (`a`, `q-perp` floor, odd floor); binding clause — odd. Receiver
`PerturbativeTrueGapLower` готов, но его finite endpoint-import и `atTop` premises остаются
открытыми. Arb balls не переименовываются в finite-to-continuum error bounds.
