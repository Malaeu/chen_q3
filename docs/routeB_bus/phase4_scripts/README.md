# Phase 4 scripts — GLOWER preflight

Транзакция: вердикт `PROSHKA_GLOWER_EXACT_CLOSURE_2026-08-09`, Вход 1 (хвостовой пол).
Журнал результатов: `../PHASE4_RESULTS_2026-08-10.md`.

Скрипт read-only, репозиторий не меняет. Нужен `python-flint` из корневой `.venv`.

## `glower_tail_floor_probe.py`

Меряет `R(μ)` — минимальный номер моды, с которого odd-хвост держит пол `μ`:
проверяет `K_odd[n₀:, n₀:] ⪰ μ·I` интервальным `LDL^T`.

```bash
.venv/bin/python docs/routeB_bus/phase4_scripts/glower_tail_floor_probe.py \
    --dps 40 --step 1 --N 120
```

Матрица берётся импортом `CCMArbBuilder` из `phase1_scripts/ccm_control_cell_penalty.py`,
не копией формул.

Результат: `R(μ=1) = 70`, устойчиво при `N = 90 … 480`.
Вилка Мифоса была `[2·10², 10⁵]`.

**Не сертификат хвоста:** измеряется компрессия `T_R` на конечный срез.

## `glower_corrected_head.py`

Вход 2 вердикта: сертификат `B_c − d⁻¹R_c*R_c ⪰ 0` на конечном срезе, через
Re-representation 1 (точное `Y`, при котором `R_c` = 0).

```bash
.venv/bin/python docs/routeB_bus/phase4_scripts/glower_corrected_head.py --N 240 --dps 300
```

Результат: PASS при `N = 120, 240, 480`, минимальный пивот `~2.7e-10` против `c₀ = 1e-58`
— запас 48 порядков.

**Грабли, на которые уже наступили:** `c₀` обязана считаться ПОСЛЕ установки `ctx.dps`.
Посчитанная раньше, она несёт радиус дефолтных 15 знаков, и `LDL^T` без пивотирования
раздувает его до `1e-3`, роняя сертификат в ложный `INSUFFICIENT_PRECISION`.
Признак именно этой болезни: интервал НЕ сужается при росте точности.
