# ОТВЕТ 022 — CANDIDATE ADJUDICATION

`CANDIDATES_STILL_FLOOR`

Статус: `CHALLENGER / NOT_RH`. Это high-precision grid-диагностика, не
теорема о знаке между точками. `STATE` не изменён; `BUS_010_VOID` соблюдён.

## 1. Поправка Прошки применена

Использована лестница

```text
p0 = max(100, ceil(-log10(scale_L2_local)) + 80)
p0, p0+100, p0+200
```

| m | scale, определяющий p0 | лестница dps |
|---:|---:|:---:|
| 13 | `10^-33.894706...` | `114 / 214 / 314` |
| 53 | `10^-142.738253...` | `223 / 323 / 423` |
| 257 | `10^-699.060619...` | `780 / 880 / 980` |

Вся численная цепочка после seed выполнена в `mpmath`: трёхдиагональный
inverse iteration, коэффициенты мод, Taylor-рекурсия ODE, пакет и сумма
`E_star`. Float64 `eigh_tridiagonal` использован только как начальный seed;
после refinement residual каждой конечной eigenpair меньше целевого
`10^(-dps+20)`.

Пакет:

```text
htrial(lambda*t)
  = (J4*phi0(t) - J0*phi4(t))
    / (sqrt(lambda)*sqrt(J0^2 + J4^2)),
N0 = N4 = 1.
```

Для каждой моды реально вычислено

```text
mu_j = lambda*J_j/c_j.
```

`mu` нигде не заменялась единицей. На последней ступени:

| m | mode | `mu-1` |
|---:|:---:|---:|
| 13 | h0 | `-3.5954e-70` |
| 13 | h4 | `-2.4855e-60` |
| 53 | h0 | `-3.6515e-288` |
| 53 | h4 | `-7.4920e-276` |
| 257 | h0 | `0` на 980-digit floor |
| 257 | h4 | `+1.9305e-980` |

Последняя строка означает вычисленное округление на данном precision, а не
присваивание `mu := 1`.

## 2. Сетка и независимый crosscheck

Проверены все `68` candidate runs и обе float64-zero из 021. Для каждого
кандидата:

- 17 точек внутри исходного candidate-интервала;
- по три guard-точки к каждому соседнему зубу;
- оба соседних star-зуба, endpoint-вес `1/2`.

Для float64-zero взято 17-точечное локальное окно ширины четыре старых
band-шага плюс те же guards и зубья. Всего: `5250` point-level строк.

Taylor-представление сверено с независимым нормированным Legendre-рядом.
На разрешимых fingerprint-точках `t=0.25,0.5,0.75` drift против P3 из 021:

| m | max `|Δ log10|` |
|---:|---:|
| 13 | `1.84e-14` |
| 53 | `9.02e-13` |
| 257 | `3.98e-12` |

Центр `t=0` в 021 сам был cancellation-floor: `+5.25e-14`, `0`,
`-2.82e-13`. High-precision значения там соответственно имеют масштаб
`10^-60`, `10^-276`, а для `m=257` остаются на 980-digit floor. Поэтому
расхождение центрального знака не является сменой пакета; разрешимая часть
fingerprint совпала.

## 3. Результат по кандидатам

Классификация засчитывалась только если:

1. знак совпал на всех трёх ступенях;
2. минимальный margin превышает Taylor-tail, mode-representation и
   межступенчатую оценки ошибки.

| m | NEGATIVE_CONFIRMED | POSITIVE_CONFIRMED | STILL_FLOOR |
|---:|---:|---:|---:|
| 13 | 1 | 0 | 0 |
| 53 | 17 | 0 | 7 |
| 257 | 1 | 0 | 44 |
| **всего** | **19** | **0** | **51** |

Отрицательно подтверждённые полосы:

- `m=13`: `r=12`;
- `m=53`: `r=25,26,28,32,33,35,36,37,39,41,42,44,45,47,48,49,50`;
- `m=257`: `r=69`.

Диапазоны финального минимального margin у подтверждённых:

| m | `log10(min margin)` range |
|---:|:---:|
| 13 | `[-26.253,-26.253]` |
| 53 | `[-93.669,-14.053]` |
| 257 | `[-21.983,-21.983]` |

На самой высокой ступени все `1190` core-точек отрицательны, и все `140`
соседних star-зубов отрицательны. Однако это не повышает остальные записи:

- `m=53`: на `223 dps` ещё `34/408` core-точки положительны;
- `m=257`: на `780 dps` ещё `323/765` core-точки положительны;
- на следующих двух ступенях все они становятся отрицательными;
- у 51 записи хотя бы одна обязательная ступень не даёт contracting
  Taylor-tail/error budget.

Следовательно, устойчивого открытого положительного интервала нет, но
зарегистрированное требование стабильности на **всех трёх** ступенях не
позволяет вернуть `CANONICAL_CANDIDATES_ALL_NEGATIVE`.

Полная классификация и margins:
`E_STAR_CANDIDATE_ADJUDICATION.csv`.

Все значения по точкам и уровням:
`E_STAR_CANDIDATE_ADJUDICATION_POINTS.csv`.

## 4. Граница результата

- `POSITIVE_CONFIRMED = 0`.
- 021-плюсы на уровне `10^-13` не переживают адаптивную precision ladder.
- 19 локальных интервалов уже отрицательно подтверждены.
- 51 запись остаётся на error floor; малость ошибки или глобальный знак не
  утверждаются.
- Fejer, residual и G3 не вычислялись.

## MYTHOS_PROSHKA_HANDOFF

```text
goal: 022_candidate_adjudication
verdict: CANDIDATES_STILL_FLOOR
positive_confirmed: 0
negative_confirmed: 19
still_floor: 51
smallest_gap: candidate-local contracting mode/Taylor enclosure on every
              p0,p0+100,p0+200 level
STATE_mutated: no
BUS_010_created: no
```

## ACTIONS LOG

Команда:

```text
.venv/bin/python \
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/candidate_adjudication_probe.py
```

Файлы и SHA-256:

```text
b7a260388c02fd163fa5f56bbc1c1d5ea6d054c4d112ea8dd7f9496d71cb2561  022_candidate_adjudication.goal.md
f1ac9934b669ba3d67ffe6023e6a4cd1ba8fb11134f1674aadbce2c23a2ef180  candidate_adjudication_probe.py
9ec9c2f44bf66cd267c9744a8510b2f6c0978fd80e6f26a6a400aedb2497c56d  E_STAR_CANDIDATE_ADJUDICATION.json
d3b4fea7850f7fd3aaeea815073668ea2cd5e443fef0cf3a4caad4f8aec9599b  E_STAR_CANDIDATE_ADJUDICATION.csv
91f253eafd3c1ed49c86d7545f3b2f211ef0f4857c6702cef4ee4cfa3abe1d52  E_STAR_CANDIDATE_ADJUDICATION_POINTS.csv
be538715ce8b7225ce08145c4116676df6ba949fec217bc65f53ae3ebdc00189  E_STAR_CANDIDATE_ADJUDICATION_FINGERPRINT.csv
```

Git scope: только перечисленные артефакты 022 и этот answer; существующие
пользовательские изменения вне scope не изменялись и не откатывались.
