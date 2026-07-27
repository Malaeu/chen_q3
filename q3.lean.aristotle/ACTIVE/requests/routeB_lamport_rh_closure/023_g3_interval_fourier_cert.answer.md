# ОТВЕТ 023 — G3 INTERVAL FOURIER CERT

`G3_MODE_INPUT_NOT_INTERVAL_CERTIFIED`

Статус: `CHALLENGER / NOT_RH`. Fail-closed source audit выполнен до любой
квадратуры. `STATE` не изменён; `BUS_010_VOID` соблюдён.

## 0. Порог зарегистрирован до результата

```text
tau_G3   = 2^-256
tau_dual = 2^-192
allowed future weighted amplification = 2^64
2^-256 * 2^64 = 2^-192
```

Это абсолютные пороги; относительная ошибка около нуля не использовалась.

## 1. Обязательный input gate

Для шага 1 директивы требуется interval-safe enclosure точной канонической
моды:

```text
N_j, J_j, c_j, mu_j=lambda*J_j/c_j, phi_j(t).
```

Инвентаризация дала:

- `python-flint`/Arb установлен и годен для ball-арифметики;
- `dual_prolate_residual_probe.py`,
  `estar_full_window_sign_probe.py`,
  `prolate_coordinate_lock_probe.py` и
  `estar_full_window_canonical_probe.py` строят моду через float64
  `eigh_tridiagonal`/`solve_ivp`;
- high-precision backend 022 даёт refinement и оценку хвоста, но не
  proof-grade interval enclosure бесконечной пролатной моды;
- декларации/реализации `G3ExactModeIntervalEnclosure` в дереве нет;
- нет ни interval-eigenpair + строгого infinite-tail bridge, ни validated
  interval ODE с сертифицированными eigenvalue/initial data.

Arb умеет сертифицировать eigenpair **конечной** ball-матрицы, но это само по
себе не отождествляет её eigenvector с точной бесконечной пролатной модой.
Именно этот переход остаётся отсутствующим. Формулы Legendre/Ferrers-разложения
пролатных функций зафиксированы в [DLMF §30.8](https://dlmf.nist.gov/30.8);
rigorous finite-matrix enclosure описан в
[Arb documentation, matrix eigenvalue section](https://arblib.org/arb-2.21.0.pdf).

По STRONGEST ATTACK Прошки float-ODE не оборачивалась в нулевые интервалы.
Шаги 2–6 остановлены на input gate.

## 2. Запрошенные 18 строк

Все комбинации зарегистрированы в CSV; `IA`, `IB`, `IDelta` имеют значение
`NOT_FORMED`, а не фиктивный нулевой интервал.

| m | y | phase zeros | primary cells | modes | ladder |
|---:|:---:|---:|---:|:---:|:---:|
| 13 | `lambda*(1+1e-8)` | 26 | 27 | h0,h4 | 114/214/314 |
| 13 | `2*lambda` | 52 | 53 | h0,h4 | 114/214/314 |
| 13 | `5*lambda` | 130 | 131 | h0,h4 | 114/214/314 |
| 53 | `lambda*(1+1e-8)` | 106 | 107 | h0,h4 | 223/323/423 |
| 53 | `2*lambda` | 212 | 213 | h0,h4 | 223/323/423 |
| 53 | `5*lambda` | 530 | 531 | h0,h4 | 223/323/423 |
| 257 | `lambda*(1+1e-8)` | 514 | 515 | h0,h4 | 780/880/980 |
| 257 | `2*lambda` | 1028 | 1029 | h0,h4 | 780/880/980 |
| 257 | `5*lambda` | 2570 | 2571 | h0,h4 | 780/880/980 |

Полный 18-row леджер:
`G3_INTERVAL_FOURIER_CERT_AUDIT.csv`.

## 3. Планты

| plant | результат |
|:---|:---|
| zero-extension backend | `FIRES`: не является зарегистрированным global-continuation backend |
| `mu4` sign flip | `FIRES_STATIC_GUARD`: `[0.9,1] -> [-1,-0.9]` нарушает `0<mu<=1` |
| wrong dual half-weight | `FIRES_STATIC_GUARD`: planted `1/2` не равно обязательному dual-весу `1` |
| omitted origin counterterm | `RESERVED_NOT_EVALUATED`: только будущий residual stage |

Первые три проверки не заменяют отсутствующий interval-mode input.

## 4. Граница результата

- Обычные float-квадратуры не запускались.
- `mp.quad(error=True)` не использовался как строгая оценка.
- Float ODE не помещалась в zero-width interval.
- `mu` не подменялась единицей.
- Fejer/residual не формировались.
- Green-коды G3 не заявляются.

Минимальный именованный разрыв:

```text
G3ExactModeIntervalEnclosure
```

Допустимый ремонт: interval Legendre eigenpair с доказанной оценкой
бесконечного хвоста либо validated interval ODE с сертифицированными
eigenvalue и начальными данными.

## MYTHOS_PROSHKA_HANDOFF

```text
goal: 023_g3_interval_fourier_cert
verdict: G3_MODE_INPUT_NOT_INTERVAL_CERTIFIED
tau_G3: 2^-256
tau_dual: 2^-192
requested_rows_registered: 18
IA_IB_IDelta_formed: no
Fejer_or_residual_formed: no
smallest_gap: G3ExactModeIntervalEnclosure
STATE_mutated: no
BUS_010_created: no
```

## ACTIONS LOG

Команда:

```text
.venv/bin/python \
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/g3_interval_fourier_cert_audit.py
```

Файлы и SHA-256:

```text
8ecb7e24c98a62f30cda02f3fcbac6f83f3091f70e313567ef51a6cac8092a6c  023_g3_interval_fourier_cert.goal.md
7a69b1bf71446096237a5b1a988a3e7c8bef4c683aed6d896976ea3c71b2f2c8  g3_interval_fourier_cert_audit.py
7df1d25eb275ebe2443574a39fedebf09c1c6303aafff8af636facd83b969703  G3_INTERVAL_FOURIER_CERT_AUDIT.json
4e426665ffd87fb94c3bd9be6012988ea21f111baef7cee13caaef1ab69f66e6  G3_INTERVAL_FOURIER_CERT_AUDIT.csv
```

Git scope: только перечисленные артефакты 023 и этот answer; существующие
пользовательские изменения вне scope не изменялись и не откатывались.
