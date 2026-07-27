# ОТВЕТ 024 — LADDER SHIFT ADJUDICATION

`CANDIDATES_STILL_FLOOR_2`

Статус: `CHALLENGER / NOT_RH`. Это high-precision grid-диагностика, не
теорема о знаке между точками. `STATE` не изменён; `BUS_010_VOID` соблюдён.

## 1. Протокол

Критерий 022 сохранён дословно:

```text
одинаковый знак на всех трёх ступенях
AND
final margin > max(final Taylor+mode error, interlevel drift).
```

Для каждой из 51 исходных `STILL_FLOOR`-записей `p_fail` восстановлен как
первая локально не прошедшая error-budget ступень либо нижняя ступень первого
межступенчатого drift, не лежащего ниже верхнего margin.

| m | `p_fail` | записей | первичная лестница | doubling-лестница |
|---:|---:|---:|:---:|:---:|
| 53 | 223 | 6 | `423/523/623` | `623/823/1023` |
| 53 | 323 | 1 | `523/623/723` | `723/923/1123` |
| 257 | 780 | 44 | `980/1080/1180` | `1180/1380/1580` |

Все 51 записи потребовали заранее разрешённого doubling. Вся цепочка после
float64 seed выполнена в `mpmath`: refinement трёхдиагональной eigenpair,
коэффициенты, Taylor-рекурсия и сумма `E_star`. Использовано
`mu_j=lambda*J_j/c_j`; `mu` не подменялась единицей.

Пять контролей выбраны воспроизводимо через `random.Random(6)` из 19
`NEGATIVE_CONFIRMED`.

## 2. Итоговая классификация

| роль | записей | negative | positive | floor |
|:---|---:|---:|---:|---:|
| 51 доадъюдицируемая запись | 51 | 0 | 0 | 51 |
| regression-контроли | 5 | 5 | 0 | 0 |

Для 49 target-записей единственный оставшийся blocker:

```text
NONCONTRACTING_TAYLOR_OR_MODE_ERROR
```

Для `C067 (m=257,r=255)` и `C068 (m=257,r=256)` дополнительно:

```text
SIGN_NOT_STABLE_ALL_THREE_LEVELS
INTERLEVEL_DRIFT_NOT_BELOW_MARGIN
```

У этих двух записей core-знак на `1180 dps` положителен, а на
`1380/1580 dps` отрицателен; error budget при этом не сокращается, поэтому
положительный сертификат не заявляется.

## 3. Каждая оставшаяся floor-запись

| id | m | r | достигнутый dps | blocker |
|:---|---:|---:|---:|:---|
| C005 | 53 | 30 | 1023 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C008 | 53 | 34 | 1123 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C012 | 53 | 38 | 1023 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C014 | 53 | 40 | 1023 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C017 | 53 | 43 | 1023 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C024 | 53 | 51 | 1023 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C025 | 53 | 52 | 1023 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C026 | 257 | 62 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C027 | 257 | 64 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C029 | 257 | 77 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C030 | 257 | 86 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C031 | 257 | 87 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C032 | 257 | 95 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C033 | 257 | 96 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C034 | 257 | 116 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C035 | 257 | 123 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C036 | 257 | 124 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C037 | 257 | 126 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C038 | 257 | 128 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C039 | 257 | 139 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C040 | 257 | 140 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C041 | 257 | 141 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C042 | 257 | 144 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C043 | 257 | 145 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C044 | 257 | 150 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C045 | 257 | 151 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C046 | 257 | 152 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C047 | 257 | 153 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C048 | 257 | 155 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C049 | 257 | 156 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C050 | 257 | 157 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C051 | 257 | 172 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C052 | 257 | 185 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C053 | 257 | 186 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C054 | 257 | 187 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C055 | 257 | 188 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C056 | 257 | 189 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C057 | 257 | 192 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C058 | 257 | 193 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C059 | 257 | 194 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C060 | 257 | 209 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C061 | 257 | 210 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C062 | 257 | 211 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C063 | 257 | 246 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C064 | 257 | 247 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C065 | 257 | 248 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C066 | 257 | 249 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| C067 | 257 | 255 | 1580 | SIGN_NOT_STABLE + NONCONTRACTING_ERROR + DRIFT |
| C068 | 257 | 256 | 1580 | SIGN_NOT_STABLE + NONCONTRACTING_ERROR + DRIFT |
| Z001 | 257 | 92 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |
| Z002 | 257 | 126 | 1580 | NONCONTRACTING_TAYLOR_OR_MODE_ERROR |

Полные margins и error estimates находятся в
`E_STAR_LADDER_SHIFT_ADJUDICATION.csv`.

## 4. Кластеры по r

| m | r-кластеры (`min-max`, число записей) |
|---:|:---|
| 53 | `30 (1), 34 (1), 38 (1), 40 (1), 43 (1), 51-52 (2)` |
| 257 | `62 (1), 64 (1), 77 (1), 86-87 (2), 92 (1), 95-96 (2), 116 (1), 123-124 (2), 126 (2), 128 (1), 139-141 (3), 144-145 (2), 150-153 (4), 155-157 (3), 172 (1), 185-189 (5), 192-194 (3), 209-211 (3), 246-249 (4), 255-256 (2)` |

## 5. Пять regression-контролей

| id | m | r | ladder | `log10(min margin)` | запас, порядков | результат |
|:---|---:|---:|:---:|---:|---:|:---|
| C001 | 13 | 12 | `314/414/514` | -26.253 | 94.168 | negative |
| C003 | 53 | 26 | `423/523/623` | -15.424 | 293.507 | negative |
| C011 | 53 | 37 | `423/523/623` | -38.046 | 270.099 | negative |
| C021 | 53 | 48 | `423/523/623` | -80.078 | 218.168 | negative |
| C028 | 257 | 69 | `980/1080/1180` | -21.983 | 365.607 | negative |

## 6. Fingerprint и граница результата

- Девять ненулевых fingerprint-координат
  `m in {13,53,257}`, `t in {0.25,0.5,0.75}` совпали с 022 по знаку и
  сохранённым 80 значащим цифрам.
- `POSITIVE_CONFIRMED = 0`.
- Все 51 записи дошли до разрешённого `p_fail+800`; дальнейшая лестница не
  запускалась.
- Fejer, residual и G3 не вычислялись.
- Малость оставшегося error budget и глобальный знак не утверждаются.

## MYTHOS_PROSHKA_HANDOFF

```text
goal: 024_ladder_shift_adjudication
verdict: CANDIDATES_STILL_FLOOR_2
floor_targets: 51
negative_controls: 5/5
positive_confirmed: 0
remaining_floor: 51
max_dps_m53: 1123
max_dps_m257: 1580
smallest_gap: noncontracting Taylor/mode error at the authorized p_fail+800 cap
STATE_mutated: no
BUS_010_created: no
```

## ACTIONS LOG

Команда:

```text
.venv/bin/python \
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/ladder_shift_adjudication_probe.py
```

Артефакты и SHA-256:

```text
3372f00dd5e5559b92c9d79471928f326f79ace038e5ff4e32e4ebfc92802c4f  024_ladder_shift_adjudication.goal.md
9e206361e5745187f9f764132c286e8f9edc5b20124b972f27466bb1287fd5b2  ladder_shift_adjudication_probe.py
b779b3b6330ac75ae678afc81c7f2e258d713171584061a22ae6d3e8e48094ad  E_STAR_LADDER_SHIFT_ADJUDICATION.json
5b1b9352088d204c34081b16a563c14ed20e6aa848f5a907ff5d6325a6338cf9  E_STAR_LADDER_SHIFT_ADJUDICATION.csv
46d1f46357ae484eb2a51368483c18cf18b43b8d15e4df1a2ef332f81b7f5c4e  E_STAR_LADDER_SHIFT_ADJUDICATION_POINTS.csv
3f7ab5ed71d3d4435ec97af254f8988f17411d561166b7e87f6b116021ec8a1f  E_STAR_LADDER_SHIFT_ADJUDICATION_FINGERPRINT.csv
```

Git scope: только артефакты 024, этот answer и запись в `docs/INSIGHTS.md`;
существующие пользовательские изменения вне scope не изменялись и не
откатывались.
