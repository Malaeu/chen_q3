# ГОЛ 039 — MUNTZ V3 CONSUMPTION + T4A CLOSURE ATTEMPT

От: Mythos (диспетчер), продолжение авторизованного цикла «го».
Статус: `CHALLENGER / NOT_RH`. `BUS_010_VOID`.
Колея: Müntz (параллельная, ζ-хвост пакета; критический путь остаётся 038).
ПРИОРИТЕТ: НИЖЕ 038 — исполнять в окнах простоя generic-m реплея или после
его сдачи; 038 не тормозить ни на минуту.

Целевой путь этого файла:
`/Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/039_muntz_v3_consumption.goal.md`

## Контекст

Проект `987ff124-3032-42e5-aa9f-24ceef69f62a`, задача
`472e126c-759f-4c69-8816-fa013ff740b2`: `COMPLETE_WITH_ERRORS 100%` =
недостигнутая цель при ЧИСТОМ коде (вердикт вынесен по Lean-исходникам).
Условно доказан весь pole-subtracted слой: dslope-тождества и аналитичность,
расширение residue-фактора (`riemannZeta_residue_one`,
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`),
аналитичность произведения, off-pole равенство, значение в полюсе, склейка
identity-теоремой (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`),
punctured/pole-value следствия. НЕ доказаны: T4a и, как следствие,
безусловные T5 и пакет плантов PL1–PL3.

Gap обмерен дословно (код `MELLIN_DSLOPE_ANALYTICITY_GAP`, теперь с адресом):

```lean
AnalyticOnNhd ℂ (fun s ↦ ∫ u in Set.Ioi (0:ℝ), h u * (u:ℂ)^(s-1)) {s | 0 < s.re}
```

из гипотез `Measurable h`, носитель `⊂ Set.Icc 0 b`,
`LipschitzOnWith K h (Set.Ico 0 b)`.

## Задача A — материализация харвеста

`muntz_v3/` по образцу `muntz_r6/` (гол 037): все файлы архива as-is
(включая RESULT.md — приложить как есть, вердиктом НЕ считать),
SHA-256-таблица на каждый файл, `_COVER.md` с провенансом (ID проекта и
задачи, вердикт по исходникам, дата). Если архив уже лежит в рабочем дереве
от кондуктора — принять на месте и зафиксировать SHA.

## Задача B — переверификация чистоты (на слово не верить никому)

`lake build`; `#print axioms` по всем главным декларациям — ожидание: ровно
`[propext, Classical.choice, Quot.sound]`, новых аксиом нет;
`grep -R "sorry\|admit\|axiom\|native_decide\|exact?"` по Lean = 0
(ожидание: Main.lean 239 строк). Расхождение → стоп-код
`V3_TAINT_OR_AXIOM_MISMATCH`, дальнейшие задачи не блокируются, но код
обязан попасть в primary-строку.

## Задача C — леджер потребления (K7)

Таблица: каждая главная теорема v3 → класс
`THEOREM_CONDITIONAL(on H_mellin)` с точной формой гипотезы; итоговая
строка статуса колеи: единственная открытая гипотеза Müntz-слоя = T4a
(дословная формулировка выше). Обновить статус-заметку колеи в шине.

## Задача D — попытка ЛОКАЛЬНОГО закрытия T4a (K2: локальный поиск до облака)

1. Поиск API в локальном Mathlib (grep + `#check`); кандидаты — список для
   ПРОВЕРКИ, не утверждения:
   - `Mathlib.Analysis.MellinTransform`: `mellin`, `MellinConvergent`,
     `mellin_differentiableAt_of_isBigO_rpow` (или ближайший аналог
     дифференцируемости Меллина по big-O при 0 и ∞);
   - `DifferentiableOn.analyticOnNhd` / `analyticOnNhd_iff_differentiableOn`
     на открытом множестве `{s | 0 < s.re}`;
   - ограниченность из Липшица на отрезке: `|h u| ≤ ‖h 0‖ + K·b`;
     `HasCompactSupport`-леммы для хвоста.
2. Bridge-лемма `MellinCompactSupportAnalyticity.lean`, таймбокс ~2 часа
   чистого кодинга. План: ограниченность на `[0,b]` ⇒ `h = O(u^0)` при
   `u→0+` и (носитель) `= O(u^{−a}) ∀a` при `u→∞` ⇒ дифференцируемость
   интеграла Меллина при `Re s > 0` ⇒ `DifferentiableOn` на открытой
   полуплоскости ⇒ `AnalyticOnNhd`. Выравнивание конвенций (`smul` vs `mul`,
   порядок множителей, ℂ-значность h) — отдельными crosswalk-леммами, НЕ
   переопределением объекта.
3a. Успех → вторичный код `T4A_CLOSED_LOCALLY`; затем механически
   инстанцировать безусловные T5 и PL1–PL3 из условного слоя v3 (слой
   параметризован гипотезой by design). При полном успехе — флаг
   `MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE`.
3b. Трение → вторичный код `T4A_LOCAL_BRIDGE_FRICTION` с ТОЧНЫМ списком
   недостающих API / побочных условий (например, `LocallyIntegrable` на
   `Ioi 0`, интегрируемостные side-conditions) И эмиссия standalone-задачи
   `ARISTOTLE_TASK_MellinCompactSupportAnalyticity.md`: дословная цель T4a,
   гипотезы, найденные entry-points, запреты (никаких новых аксиом;
   конвенции — crosswalk-леммами; standalone, Mathlib-only, English).
   Кондуктор АВТОРИЗОВАН сабмитить её в облако без ожидания диспетчера.

## Замки

- 038 не тормозить, его файлов не касаться; EdgeSliver-ран `b14fe0a5-…`
  не трогать;
- канон + зеркало одним коммитом (правило канала от 2026-07-30);
- одна строка истории в `ROUTE_B_STATE.md` по закрытии;
- статус не повышать; Müntz остаётся параллельной колеёй; RH не выводить;
- байты харвеста не менять; вся новая работа — в новых файлах.

## Прогнозы диспетчера (K6; скорить в ответе)

```text
P039-M1: чистота подтвердится на диске: taint = 0, аксиомы ровно тройка,
         сборка зелёная.
P039-M2: T4a закроется ЛОКАЛЬНО из существующего Mathlib API в ≤ ~60 строк
         моста; вилка: блокером окажется интегрируемостное/измеримостное
         побочное условие, названное точно — тогда срабатывает 3b, и это
         не провал, а сжатие контракта.
P039-M3: при закрытом T4a безусловные T5 + PL1–PL3 инстанцируются
         механически, без единой правки условного слоя v3.
```

## Ответ

`039_muntz_v3_consumption.answer.md` — handoff + полный ACTIONS LOG (иначе
REJECTED), primary первой строкой.
Primary: `MUNTZ_V3_CONSUMED`.
Вторичные: `T4A_CLOSED_LOCALLY` | `T4A_LOCAL_BRIDGE_FRICTION`;
`MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE` (если достигнут).
Стоп-коды: `V3_ARCHIVE_MISSING`, `V3_TAINT_OR_AXIOM_MISMATCH`.
Артефакты: SHA-таблица харвеста, `_COVER.md`, леджер потребления,
`MellinCompactSupportAnalyticity.lean` (при 3a) или
`ARISTOTLE_TASK_MellinCompactSupportAnalyticity.md` (при 3b),
обновлённый MANIFEST.
