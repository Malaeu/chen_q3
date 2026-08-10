# REPORT — GLOWER_NESTED_SCHUR_RESOLVENT_LOSS_AUDIT_480_960

```yaml
TARGET: GLOWER_NESTED_SCHUR_RESOLVENT_LOSS_AUDIT_480_960
DIRECTIVE: PROSHKA_VERDICT_PHASE4_CODE_AUDIT_2026-08-10
MODE: READ_ONLY_NUMERICAL_PREFLIGHT
PIN_REQUESTED: b076f97bc63a1558cf65eed7d24c7fa45c68073f
HEAD_AT_RUN: 3d3a513c0f8a5e15cbbdc9f914e5046a82cd8f9e
RESULT: CONSTANT_FLOOR_SURROGATE_KILLED_RESOLVENT_ROUTE_ALIVE
LEAN_EDITS: NONE
REPO_WRITES: SCRIPTS_LOGS_JOURNAL_ONLY
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PX_RH_CLAIM: NOT_MADE
BIRMAN_SCHWINGER: NOT_ACTIVATED
```

Директива исполнена целиком, задачи 1–14, на обеих требуемых точностях.

## REQUIRED_OUTPUT

| требование | файл |
|---|---|
| one JSON file | `phase4_results/nested_schur_audit.json` |
| raw log | `phase4_results/nested_schur_audit_dps200.log`, `…dps400.log` |
| markdown report | этот файл |
| all source hashes | ниже и в JSON |
| full precision ledger | ниже и в JSON |

## Source hashes

```
docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py
  1be57db69683652ed4f6d56dba6fc3b70c186f429fbb7f5bef978cd84f08ed0d

docs/routeB_bus/phase4_scripts/glower_nested_schur_resolvent_audit.py
  17de92e466d4089142c72f8f644852666c91245c762a18fc337c40913d2a0771
```

Хеши печатаются самим скриптом в шапке каждого прогона и пересчитываются с диска при
сборке JSON. Несовпадений нет, `SOURCE_HASH_MISMATCH` не сработал.

## Frozen input и метки мод

```
m = 13,  сектор ODD,  c₀ = 1e-58,  d = 1 − c₀
head = моды 1..70     → индексы [0, 70)
mid  = моды 71..480   → индексы [70, 480)
out  = моды 481..960  → индексы [480, 960)
```

## Построенные объекты

```
C_out   = C     − F·D_mid⁻¹·F^T                 480×480
R_out   = E_out − F·D_mid⁻¹·E_mid               480×70
X       : решение C_out·X = R_out
H_exact = R_out^T·X                             точная внешняя поправка
H_floor = d⁻¹·R_out^T·R_out                     суррогат, убитый вердиктом
B_480   = A − E_mid^T·D_mid⁻¹·E_mid
B_960   = A − E_tail^T·D_tail⁻¹·E_tail          построена независимо
```

## Precision ledger

| | `dps = 200` | `dps = 400` |
|---|---|---|
| тождество: интервалы накрывают ноль | да, все клетки | да, все клетки |
| наибольшая \|разность\| (середина) | `6.532101e-201` | `0.000000e+00` |
| масштаб диагонали `B_960` | `4.735337` | `4.735337` |
| задача 10, `H_floor − H_exact ⪰ 0` | `INSUFFICIENT_PRECISION` | `INTERVAL_POSITIVE_DEFINITE` |
| `rho_exact` | `0.2111402742` | `0.2111402742` |
| `rho_floor` | `1.049387747` | `1.049387747` |
| код | `..._ROUTE_ALIVE` | `..._ROUTE_ALIVE` |

`rho` совпадают на обеих точностях до всех печатаемых цифр; `PRECISION_NOT_STABLE` не
сработал. Задаче 10 потребовались 400 знаков — при 200 знак разности не отделяется.

## Зарегистрированные предсказания директивы

| предсказание | измерено | исход |
|---|---|---|
| `rho_exact ∈ [0.12, 0.30]` | `0.2111402742` | внутри полосы |
| `rho_floor ≈ 1.049387747` | `1.049387747` | совпадение до последней цифры |
| вложенное тождество проходит | разность `0.0` при `dps = 400` | проходит |

`rho_floor` совпал с величиной, независимо полученной 10 августа другим скриптом
(`glower_relative_form_check.py`) — перекрёстная проверка обоих расчётов.

## Задача 12 — проецированные обобщённые нормы `H_exact`

`dps = 400`, собственный базис `B_480`, норма блока (не максимум элемента):

```
dim   λ[dim-1]        ‖P·H_exact·P‖    отношение
  1   2.30600e-55     3.65047e-56      0.158303
  2   3.15697e-48     7.30614e-50      0.023143
  3   1.54268e-41     2.34522e-43      0.015202
  4   1.17400e-35     1.06935e-37      0.009109
  5   7.62410e-30     5.37449e-32      0.007049
  6   7.37177e-25     5.73478e-27      0.007779
  7   6.38982e-20     7.89075e-22      0.012349
  8   1.56335e-15     2.76419e-17      0.017681
  9   2.21238e-11     5.67156e-13      0.025636
 10   8.17091e-8      2.64295e-9       0.032346
 11   2.65383e-4      1.08408e-5       0.040850
 12   9.07306e-2      3.60068e-3       0.039685
```

## Что сертифицировано интервально

- вложенное тождество `B_480 − H_exact = B_960` (задача 8);
- знак `H_floor − H_exact ⪰ 0` при `dps = 400` (задача 10).

## Что является диагностикой по серединам

`rho_exact`, `rho_floor`, проецированные нормы задачи 12. Интервальных границ обобщённых
собственных значений в этом прогоне нет.

## Что не установлено

`infinite_constant_floor` остаётся `OPEN`: всё построено на конечном срезе `N = 960`, моды
выше в расчёт не входят.

## Соблюдение запретов директивы

Не выполнялось и в коде отсутствует: `N = 1920`; вычисление `B₀`; подгонка показателя
затухания; трактовка минимального пивота `LDL^T` как собственного значения; максимум
элемента матрицы как операторная норма; активация Birman–Schwinger; промоушен маршрута;
заявление RH; абсолютные пути репозитория.

## Воспроизведение

```bash
.venv/bin/python docs/routeB_bus/phase4_scripts/glower_nested_schur_resolvent_audit.py \
    --N 960 --S 480 --dps 200
.venv/bin/python docs/routeB_bus/phase4_scripts/glower_nested_schur_resolvent_audit.py \
    --N 960 --S 480 --dps 400
```

Сборка матриц — около трёх минут, задача 11 — около `200` с на каждый прогон.
Журнал: `PHASE4_RESULTS_2026-08-10.md`, раздел R11.
