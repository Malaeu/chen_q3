# Phase 0 scripts — CLOSED 2026-08-07

Транзакция `CCM_PENALTY_SOURCE_LOCK_AND_RATE_PROFILE`, Phase 0.
Журнал результатов: `../PHASE0_RESULTS_2026-08-07.md`.
Вердикт: `../proshka/PROSHKA_VERDICT_CCM_PENALTY_CROSSWALK_2026-08-07.md`.

Оба скрипта read-only и не меняют репозиторий. Для запуска нужен `mpmath`
из корневой `.venv`.

## `phase0_ccm_crosswalk.py` — PASS

Закрывает структурные замки: `λ² = m`, `L = log m`, простые `q = p^a ≤ c`,
полюсный блок двумя независимыми замкнутыми формами, симметрию `K` и `JK = KJ`.

```bash
.venv/bin/python -u docs/routeB_bus/phase0_scripts/phase0_ccm_crosswalk.py
```

## `arch_block.py` — PASS

Воспроизводит cutoff-free архимедов блок для `c = 13`, `N = 4` прямым source-side
путём `v → K_v → g_v`. Матричный путь проверяется точным pointwise-мостом
`Σ u_m u_n q_mn(r)/π = g_v(r)` и аналитической диагональю, включая `x = 0`.
Осциллирующий хвост дважды интегрируется по частям, а не берётся осциллирующей квадратурой.

```bash
.venv/bin/python -u docs/routeB_bus/phase0_scripts/arch_block.py
```

Результат 30/40 dps:

```text
precision_delta=1.342314243e-31
computed=0.04769748265232800635528299496674133
reference=0.047697482652328006439872417749
target_delta=8.458942278e-20
published_tail_bound=2.94838e-12
PHASE0_ARCH_BLOCK=PASS
```

Source lock лежит в `threeroute_c13N4_reference.json`; полный ZIP в репозиторий не копируется.
`arch_partial_output.txt` сохранён только как исторический след незавершённого R5-пути.

## Внешний эталон

Первичный record: `https://zenodo.org/records/21146461`.
Пакет: `guinand_weil_dictionary_tail_order_package.zip`, 508 861 байт,
md5 `71e7890a609c6db38f1324ce8225b840`.
