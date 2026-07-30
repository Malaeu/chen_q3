Файл → `/Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/037_muntz_r6_harvest.goal.md`:

```text
# ГОЛ 037 — MUNTZ R6 HARVEST + CANON SYNC

От: Mythos (диспетчер), продолжение авторизованного цикла 035; механика, без
новой математики. Статус: CHALLENGER / NOT_RH. BUS_010_VOID. 038 зарезервирован
под директиву Supplier A — не занимать.

## Задача A — харвест R6 (Müntz-колея)
Кондуктор доставляет архив облачного проекта c746a674-5849-4dfa-9e4c-b7dd5af231b2
(задача R6, COMPLETE): все Lean-исходники + RESULT.md as-is.
1. Положить в q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/muntz_r6/
   без изменения байтов; SHA-256 каждого файла — таблицей в ответ.
2. Taint-scan по Lean: вхождений sorry/admit/axiom/native_decide = 0
   (ожидание: 148 строк, дырок нет; R5-версия имела sorry на строке 92 —
   строчный диф R5→R6 зафиксировать в ответе). Нарушение → стоп-код
   R6_TAINT_FOUND, задача B при этом выполняется.
3. Обложка muntz_r6/_COVER.md: провенанс (проект c746a674, R6), закрытая
   дырка Rminus_differentiableOn_halfPlane, и ЯДОВИТАЯ МЕТКА: RESULT.md
   протух (текст R5: MELLIN_DSLOPE_ANALYTICITY_GAP), вердиктом НЕ является,
   судить только по исходникам. lean_status: HARVESTED_NOT_BUILT (сборка —
   при потреблении v3-колеёй, отдельный гол).

## Задача B — canon sync (райдер к 035)
Довыполнить букву задач A–C гола 035 в КАНОННОЙ шине (зеркало уже полное,
его не трогать, байты не менять, только git mv/копии):
1. Из _INBOX_cowork_034edge_2026-07-29/ перенести в корень шины все семь
   файлов по схеме 035 (034_REGISTRATION.md → 034_edge_sliver_REGISTRATION.md;
   _STATUS.md → 034_edge_sliver_INBOX_COVER.md); каталог _INBOX удалить.
2. В канонный proshka/ положить PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md
   и PROSHKA_034_EDGE_SLIVER_CONTRACT.md (копии из зеркала; сверить aad7e9de…
   и f18c9a6d… после копирования).
3. В корень канона: 035_edge_sliver_materialization.{goal,answer}.md,
   036_tooth_sign.goal.md, P1_RADIUS_MUTATION.csv (копии из зеркала).
4. Пересчитать SHA всех перенесённых файлов; полная таблица в ответ.
   Любое расхождение → стоп-код CANON_SYNC_HASH_MISMATCH, стоп гола.

## Задача C — STATE, MANIFEST, зеркало
Одна строка STATE по образцу:
- 2026-07-30 HH:MM CEST: Bus 037 MuntzR6Harvest -> MUNTZ_R6_MATERIALIZED;
  Rminus_differentiableOn_halfPlane closed upstream (R5 94 lines sorry@92 ->
  R6 148 lines taint-free), stale RESULT.md poison-labeled; canon synced to
  mirror for 034/035 cycle (<N> files, zero hash mismatches); NOT_RH; no Bus 010.
MANIFEST: новые записи muntz_r6/ с хэшами. Зеркало по правилу 014.

## Замки
- Aristotle-раны (b14fe0a5, 987ff124) не трогать; ARISTOTLE_ACTIONS_BY_CODEX=false
- 036 не исполнять (JUDGE_PENDING); байты проверенных артефактов не менять
- статус не повышать; глоссарий заморожен; force-push запрещён

## Выход
037_muntz_r6_harvest.answer.md с handoff + ACTIONS LOG (иначе REJECTED).
Primary: MUNTZ_R6_MATERIALIZED. Стоп-коды: R6_ARCHIVE_MISSING, R6_TAINT_FOUND,
CANON_SYNC_HASH_MISMATCH.
Прогнозы диспетчера (скорить): P037-1 — taint-scan даст ноль; P037-2 —
canon sync пройдёт без единого хэш-расхождения.
```