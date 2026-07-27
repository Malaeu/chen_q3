# ГОЛ 015 — MUNTZ_CLOUD_HARVEST (вытянуть и оценить проект Мюнца из облака)

От: Mythos. Статус: CHALLENGER / NOT_RH. BUS_010_VOID соблюдать.
Облачный проект: c746a674-5849-4dfa-9e4c-b7dd5af231b2
(EStarMuntzZeroMassContinuation_Standalone; финальный код рана:
RIEMANN_SUM_LIPSCHITZ_GAP — частичный зелёный + одна именованная дыра).

## Задача

1. КЛОН по рецепту Монтеля: взять remote-URL из существующего клона
   aristotle_output/1803227e-…, подставить UUID c746a674-…, клонировать в
   q3.lean.aristotle/aristotle_output/c746a674-5849-4dfa-9e4c-b7dd5af231b2/.
   Если паттерн URL не подходит — код CLONE_FAIL + точная ошибка.

2. НОТАРИАТ: локальный lake build клона; #print axioms всех доказанных
   деклараций (ожидаю тройку); грепы sorry/admit/axiom/native_decide.
   Прочитать RESULT.md — приложить его содержимое в отчёт целиком.

3. ИНВЕНТАРЬ (главное — «пересобирается ли в нашей линии»):
   — точный список доказанных деклараций с сигнатурами
     (ожидаю: Estar_eq_zero_of_gt; def ZetaMellinReg; общая теорема
     разрывности сырого ζ·M-произведения в w=1 при простом нуле M-фактора;
     её сдвинутая форма в s=1/2; возможно T3/T4-куски);
   — совместимость с нашим деревом: конфликтуют ли имена/конвенции с
     Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean (Mellin-конвенция,
     Estar-определение); вердикт одной строкой: PORTABLE / NEEDS_RENAME(что);
   — НЕ переносить в дерево в этом голе — только оценка; перенос отдельным
     голом после скоринга.

4. ДЫРА: выписать ДОСЛОВНО из RESULT.md формулировку недостающей леммы-моста
   (Riemann-sum vs integral через eVariationOn) + список Mathlib-API, которые
   он назвал ближайшими (eVariationOn.sum_le и др.).

5. ХРОНОЛОГИЯ: git log --oneline -10 клона с датами; отметить, есть ли
   коммиты ПОСЛЕ финального «Aristotle finished» (~12:0x) — признак того,
   что мой follow-up-instruct ожил. Ответ: FOLLOWUP_ALIVE / FOLLOWUP_SILENT.

## Отчёт
015_muntz_cloud_harvest.answer.md: пункты 1–5, build exit, аксиомы.
Коды: MUNTZ_HARVEST_OK / CLONE_FAIL / BUILD_FAIL_LOCAL.
STATE не трогать до скоринга. Зеркало chen_q3 (гол 014) обновить включая
этот отчёт, если 014 уже исполнен.
