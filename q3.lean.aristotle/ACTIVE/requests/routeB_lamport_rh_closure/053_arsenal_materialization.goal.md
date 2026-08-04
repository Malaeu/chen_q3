# GOAL 053 — ARSENAL: материализация колоды карт + копии KERNEL v3

Ф2 плана интеграции арсенала (чат Fable/Mythos 2026-08-04). Чистая инфраструктура, никакой
математики. CLOSED_GOAL_IMMUTABLE не затрагивается. Пути Fable (macOS `/Users/emalam/GitHub/
rh_lean_01_2026/…`) адаптированы под Linux repo-relative.

## Задачи
1. NNN: у Fable провизорный 047; на нашей шине 047 занят (hG), habs=052 → фактический свободный = **053**.
2. СОЗДАТЬ `q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md` — 12 карт (байт-в-байт из блока Fable).
3. СОЗДАТЬ `q3.lean.aristotle/docs/PROJECT_INSTRUCTIONS_v3_arsenal.md` — полный KERNEL v3
   (маркер `[KERNEL v3 — arsenal edition, 2026-08-04; …]` первой строкой).
4. SHA-256 обоих → в answer.
5. `git add` обоих. **КОММИТ НЕ ДЕЛАТЬ** — коммит пакетом в Ф7 (canon+mirror один коммит + ROUTE_B_STATE).
6. `ROUTE_B_STATE.md` НЕ трогать в этом голе (обновится в Ф7, Codex последним). Глоссарий заморожен —
   новых терминов не вводить; «ARSENAL», «card-ID» — файловые алиасы.

## Критерий закрытия
053.answer.md: фактический NNN, оба пути, оба SHA-256, вывод `git status` по файлам,
строка «COMMIT DEFERRED TO PHASE 7».

## Связь с UI (правка Ылши, вне этого гола)
Три патча (K4 card-scan, K6 OBJECT PRE-COMMIT, K8 FAILURE AUTOPSY) Ылша вставляет в project
settings (UI) как KERNEL v3. Дисковая копия `PROJECT_INSTRUCTIONS_v3_arsenal.md` = зеркало того,
что в UI. `PROJECT_INSTRUCTIONS_v2` на Linux-диске отсутствует (жил только в UI/macOS) — не блокер.
