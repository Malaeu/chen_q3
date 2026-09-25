# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~80 строк.
При закрытии ворот, фазы или вилки — сразу обновить «Дорожную карту» в том же коммите.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-09-25 · by: Codex · HEAD at update: bfb9f0af

## Цель
Дойти до `PX_RH_CLAIM` — заявления «RH доказана». Всё направлено на него.
Цель в Lean: `RiemannHypothesis.riemannHypothesis : RiemannHypothesis`
(`q3.lean.aristotle/comparator/Challenge.lean`, Mathlib `RiemannHypothesis`).

Claim делается, только когда он действительный — все условия сразу:
1. Lean-доказательство цели собирается на чистом клоне, Comparator проходит.
2. Ни одного `sorry`; `#print axioms` показывает только propext, Classical.choice, Quot.sound.
3. Независимые проверки (разные модели и люди) раз за разом не находят ни одной ошибки.
4. Владелец объявляет claim.
До этого статус честный: RH ещё не доказана. Это состояние, а не цель.

## Стратегия (владелец, 2026-09-25): сначала бумага, потом Lean
1. Сначала закрываем МАТЕМАТИЧЕСКИ, на бумаге, все недостающие звенья цепи до RH — вместе с Прошкой.
   На это тратим время и токены.
2. Lean сейчас — только если без него дальше никакая математика не идёт
   (например, шаг держится на конечной проверке, которой верим только после kernel-check).
   То, что уже можно формализовать, но не блокирует бумагу, — откладываем.
3. Когда вся цепь закрыта на бумаге — формализация в Lean, Comparator, проверки, claim.
4. Проверки делаем, когда без них нельзя двигаться (ошибка на бумаге дороже, чем проверка).

## Дорожная карта
Маршрут: Route B → Goal058 (одна семья: вещественные нули + сходимость к Ξ).
  Фаза: `PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923`.
Всего маршрутов: 3 — Route B (активен); (i) PSD fallback (спит с 25.06); (ii) мост Судзуки/Йосиды (в Lean не начат).
  Источник: `docs/GENEALOGY.md` §0, §2. 40 «route»-киллов в базе — строки леджера, не маршруты.

Цепочка до цели — 8 ворот Goal058 (`docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md`, «Восемь ворот»):
  G0 объект/нормировка ............ частично
  G1 кофинальный ground-пакет ..... ОТКРЫТО (floors: hfloorEv, hoddEv, hratioEv)
  G2 вещественные нули ............ готово
  G2b перенос нулей на P5.9 ....... доказано
  G3 та же семья трекает trial .... ОТКРЫТО — главная стена  ← МЫ ЗДЕСЬ (Fokas, компактный decay)
  G3c projected → continuum trial . ОТКРЫТО
  G4 CCM Lemma 7.3: trial → Ξ ..... ОТКРЫТО (в статье доказано, Lean-порт открыт)
  G5 Гурвиц → Q3.RH ............... готово
  затем `riemannHypothesis_of_rh` (доказано) → Comparator → claim.

Lean-потребитель: `rh_of_real_zero_family_tendsto_centeredXi`
  (`q3.lean.aristotle/Q3/Proofs/RouteB/Goal058DirectGroundZeroEscape.lean:27`), посылки hzeros, hentire, hconv.
  В RouteB 0 `sorry`, 0 `axiom`.
Осталось: 5 из 8 ворот. В Lean 7 открытых посылок:
  1. hmode — sup-норма близости Ferrers mode0/mode4 к D0/D4 (есть только L2-оценки);
  2. hχ/hθ — сведены к hmode в собранных модулях 22.09; hmode остаётся открытым;
  3. hfloorEv; 4. hoddEv (источника нет — нужна новая математика); 5. hratioEv
     (`G6N1SelectedFerrersTrackedGroundTailReindex.lean`);
  6. компактный decay: нормировка × kernelL2 × √ratio → 0 (Lean-формулировки ещё нет);
  7. сборочная теорема → hconv → потребитель (отсутствует).
  Соответствие ворот и посылок — оценка: G1 = 3–5, G3 = 6, G3c/G4 = 1–2, 7 — сборка.
Открытые вилки:
  - 6 кандидатов-поставщиков для G1, 6 для G3;
  - Fokas: механизм 1 (Mellin/Abel–Plana) или 2 (граничный член Штурма–Лиувилля), BRIEF:44–51;
  - «ground = trial» — долг, не опровергнуто;
  (крыша решена 25.09: каноническая — `rh_of_real_zero_family_tendsto_centeredXi`;
   7-портовая `rh_of_canonical_slots` — история; `comparator/Solution.lean` и README приведены в соответствие.
   `orchestrator/roof_port_ledger.py` переведён на новую крышу: 3 порта hzeros/hentire/hconv, HEAD_LOCKED.)

## Последний доказанный результат
- 2026-09-25: Fokas step 1 в Lean: положительность двух выбранных θ, общее
  Mellin–Green тождество с нижним краем и точный перенос выбранной строки
  через sTrial к Mellin/Gwin с фазой `(-1)^n` при существующем условном порте
  `CCMLemma73PreAnchorPort`. Конечная paired-window формула также выведена
  при явной `MellinConvergent` для каждого слагаемого; эту посылку для выбранного
  источника ещё нужно закрыть. `q3_check.sh` — ok; полный `lake build` — 8219 jobs,
  exit 0. Rank-2 residual identity, decay и sector floors открыты.
- 2026-09-25: четыре Lean-кандидата 22.09 побайтно перенесены в `Q3/Proofs/RouteB/Q3*Candidate20260922.lean`;
  `scripts/q3_check.sh` — ok, полный `lake build` — 8215 jobs, exit 0. Только аксиомы
  propext/Classical.choice/Quot.sound. Теоремы остаются условными; `hmode` и RH не закрыты.
- Paired-window Mellin identity, Rminus crosswalk, Euler identity: PAPER-level
  (`docs/Codex/BRIEF_2026-09-22_FOKAS_PAIRED_WINDOW.md`, `docs/Codex/REPORT_2026-09-22_FOKAS_RMINUS_CROSSWALK.md`).

## Следующий шаг (бумага)
1. Собрать бумажную цепь до RH в одном файле `docs/Codex/PAPER_CHAIN.md`: каждое звено
   (G0…G5, посылки hzeros/hentire/hconv и их подпосылки) — точная формулировка, статус
   PAPER_PROVED (со ссылкой) / OPEN / Lean-only, и что ровно не хватает. Источники: Goal058,
   BRIEF_2026-09-22_FOKAS_PAIRED_WINDOW, вердикты Прошки, CCM Lemma 7.3.
2. Открытые на бумаге звенья — в порядке «что блокирует больше всего»: hoddEv (источника нет),
   равномерный decay joint defect / компактный decay (G3), hmode в sup-норме (G3c/G4), hfloorEv, hratioEv.
   По каждому: своя попытка → при застревании alias-hunt → запрос Прошке с точной формулировкой.
3. Lean Fokas rank-2 joint green (Mellin-сходимость, paired-window сумма, Green на выбранном U,
   решёточное сворачивание краёв) — ОТЛОЖЕНО до закрытия бумаги, кроме шагов, без которых
   бумажный аргумент не проверить. PAPER-контроль t−V = 3√2/4 остаётся в силе.

## Прошка
- Активная фаза: `PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923`, чат `6aafb38a-a7a4-83eb-9940-84a574eae168`.
- Последний запрос: `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_FOKAS_MATRIX_DEFECT_20260923.txt`.
  В `PROSHKA_QUEUE.md` статус OPEN, файла ответа в репо нет. Codex видел ответ в UI
  («убывание остатка не доказано / floors не доказаны») — сохранить ответ в bus и закрыть запрос.
  Новый запрос — только по реальному глобальному блокеру.

## Не повторять
- Owner recovery, старые launch/ingest/publication (RESUME `Do not repeat`) — не переигрывать.
- Не подменять оценки selected Ferrers packet явными гауссовыми пределами; не дифференцировать C0-сходимость.
- Не отправлять повторно уже отправленные запросы Прошке.

## Конец фазы
конец фазы = scripts/phase_end.sh
Одна команда: `scripts/phase_end.sh "что сделано"` (журнал → Lean-проверка → полка → литература → статистика → commit → push → readback).
Перед ней дописать в `docs/Progress_Log.md` запись `## <дата> — <что нашли>` с полями:
Развилка · Выбрали · Почему · Что отвергли · Инсайты · Блокеры · Иглы Зингера · Следующий ход · Адреса · Чей вердикт.
Без записи скрипт останавливается; обход владельца: `--no-log`.
Литература: скрипт сам ищет arXiv/Crossref и X (посты, новости) по строкам `- lit:`.
Агент (Claude Code) в конце фазы дополнительно прогоняет те же запросы через scite `search_literature`
и Consensus `search` и сохраняет находки в `docs/literature/scan_<дата>_agent.md` (заголовок, DOI, цитата, зачем нам).
Запросы для поиска литературы (правьте по текущему фронту):
- lit: prolate spheroidal wave functions Riemann xi zeros
- lit: Ferrers functions Sturm-Liouville eigenvalue asymptotics uniform
- lit: Fokas unified transform Riemann zeta
- lit: Hurwitz theorem zeros real entire functions locally uniform limit

## Жёсткие линии (не обсуждаются)
Без `sorry`; без собственных `axiom`; только три стандартные аксиомы Lean (см. Цель п.2);
недоказанное не называть доказанным; claim — только по условиям из «Цели»;
одновременно работает одна машина (какая — решает владелец).
