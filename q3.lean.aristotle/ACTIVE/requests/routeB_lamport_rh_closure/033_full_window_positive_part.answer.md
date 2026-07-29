# ОТВЕТ 033 — FULL WINDOW COUPLED POSITIVE-PART BUDGET

Primary verdict:

`FULL_WINDOW_POSITIVE_PART_BUDGET_PROVED`

Secondary tooth flag:

`TOOTH_SIGN_INCONCLUSIVE`

Статус: `CHALLENGER / NOT_RH`. Scope: единственная конечная клетка
`m=257`, `lambda=sqrt(257)`. Кофинального вывода, вывода RH и поточечного
знакового вывода из интегрального бюджета нет.

## Полное окно и frozen backend

Сертификат покрывает ровно 241 band portion:

- partial `r=16`, истинный интегральный участок
  `[1/17,1/sqrt(257)]`;
- full `r=17..256`, участки `[1/(r+1),1/r]`;
- priority `r=255,256` пересчитаны и побайтово воспроизводят exact envelopes
  030/031.

Замки 030 сохранены:

```text
core_q = 440
tail_q = 700
tau_response = 2^-512
terminal cone = [0,1/2]
canonical phase = '+'
delta_0 = 0 exactly
```

На каждой полосе построен один exact-rational whole-response polynomial
степени 1400 со всеми центрами до `q=700`. Наружу добавлены только
coefficient-box response uncertainty и infinite response remainder. Старый
независимый хвост `r*(epsilon0/J0+epsilon4/J4)` в verdict не входит.

## Guard partial band

Для `r=16` использован rational outer endpoint

```text
z16+ = 0.062378286155180534493662858979332615595710...
```

Сертификат хранит сокращённые целые `n,d` и независимо проверяет

```text
257*n^2 >= d^2
16*n < d
```

Envelope построен на `[1/17,z16+]`, но формула интегрирует только до
алгебраического endpoint `1/sqrt(257)`.

## Band profile и all-sigma theorem

Для каждой полосы записаны exact-rational `L_r,U_r` и
`epsilon_r=max(0,-L_r)`. Ненулевой профиль:

```text
epsilon_r > 0  exactly for r=195..256  (62 bands)
max epsilon_r at r=225:
2.241863561007243437e-237
```

Для каждого вещественного `0 <= sigma < 1/2` сертификат доказывает

```text
Delta_full_over_C_lambda(sigma)
<= lambda^(-sigma-1/2)/(1/2-sigma) *
   [ epsilon_16*(lambda^(sigma-1/2)-17^(sigma-1/2))
     + sum_(r=17)^256 epsilon_r*
       (r^(sigma-1/2)-(r+1)^(sigma-1/2)) ].
```

Затем

```text
Delta_full(sigma)
<= C_lambda * Delta_full_over_C_lambda(sigma).
```

`C_lambda=I0*I4/sqrt(I0^2+I4^2)` получен не из сохранённого decimal:
checker заново читает outward Arb-боллы `J0,J4` из 027, использует точный
scaling crosswalk и rational square/fourth-root guards. Итоговый outward
интервал:

```text
C_lambda =
[0.6207968644022361575694926412624710482454413103505137019351957...,
 0.6207968644022361575694926412624710482454413103505137019351957...]
width = 1.34e-78.
```

Контрольные outward upper bounds:

| sigma | Delta_full / C_lambda | Delta_full |
|---:|---:|---:|
| 0 | `1.03384082065404675e-239` | `6.41805139753066808e-240` |
| 0.10 | `1.34533991195246508e-239` | `8.35182798895270793e-240` |
| 0.25 | `1.99733646956422921e-239` | `1.23994021746170589e-239` |
| 0.40 | `2.96573588822254861e-239` | `1.84111954005373892e-239` |
| 0.45 | `3.38355578307862301e-239` | `2.10050082066526190e-239` |
| 0.49 | `3.75985416016804053e-239` | `2.33410567324202257e-239` |

## Отдельный tooth ledger

Проверены ровно 241 зуб `r=17..257`:

```text
lower envelope >= 0: 179
upper envelope < 0:    0
zero-compatible:      62
```

Зубья не входят в Lebesgue budget. Изменение tooth record меняет только
отдельный tooth payload hash.

## Планты и predictions

Независимый stdlib-only checker воспроизводит coverage, exact priority
regression, endpoint guard, all-sigma formula, outward `C_lambda`, отдельный
tooth ledger и все P1–P11. Все одиннадцать плантов стреляют.

Все registered predictions P033-1..P033-4 подтвердились: backend закрыл
полное окно; interior bands участвуют в бюджете; среди оставшихся зубьев есть
zero-compatible; кофинальная теорема не заявлена.

## Независимый checker

Checker не импортирует generator 033, generator 030, Arb или flint. Он
проверяет source SHA-256, proof-carrying exact-envelope records, CSV,
рациональную арифметику, coverage/junction ledger, C-lambda construction,
secondary rule и mutation replay P1–P11.

```text
python3 check_full_window_positive_part_certificate.py
PASS
P1 PASS ... P11 PASS
```

## ACTIONS LOG

Команды:

```text
uv run python full_window_positive_part_certificate.py
python3 check_full_window_positive_part_certificate.py
```

Артефакты и SHA-256:

```text
FULL_WINDOW_POSITIVE_PART_CERT.json
126927197ee170ca289dd30ad6fdd7cfb6937d2c67d128a111c073e0c8487f7f

full_window_positive_part_certificate.py
53da243d64242ebe49390be8a3d66536ebd827cdc98d4587d64326cbabc9c627

check_full_window_positive_part_certificate.py
d76d9702144a412ccdd81fae52071dac24498d9d95db55b60c1230b5a1233362

FULL_WINDOW_BAND_PROFILE.csv
8606e7ce9d64ec1fe0e84478c729afa47f97ecd36cf0df39035442b036777253

FULL_WINDOW_TOOTH_LEDGER.csv
d9dbfd72a838ab7367508c60c8d510719d38ea2588441e5e3a71dd83d2241601

sync_proshka_github_channel.py
d91b8518e712c0a46a35e20a5f59b9baf5c2487b0a6413dbd694a8666fc393a3
```

Source locks:

```text
PROSHKA_033_DIRECTIVE_2026-07-29.md
e1a799bc07579952c47a7f8eb499f8e0d67d8b673741cd0ea6301b919cacacc5

COUPLED_FULL_SUM_RESPONSE_CERT.json
2e31e67ba9cc9aed78bfed9ed20d052c1917b508958ddff077124e2cf95989da

PRIORITY_BAND_POSITIVE_PART_CERT.json
86191e9eb8772dd013dbeb7347c1484b910109dbe5a4a2b24562e43211b937c9
```

Datasets:

```text
FULL_WINDOW_BAND_PROFILE.csv: 241 data rows
FULL_WINDOW_TOOTH_LEDGER.csv: 241 data rows
```

Git status/diff audit before commit:

```text
canonical scope: 8 new 033 files plus the rule-014 sync allowlist update
mirror scope: docs/routeB_bus only, committed separately
git diff --check: PASS
STATE / execution-state diff: empty
```

Guards:

```text
STATE untouched
Bus 010 not created
new depth not used
new precision ladder not used
teeth kept outside the Lebesgue budget
```
