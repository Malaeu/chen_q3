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
