# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~80 строк.
При закрытии ворот, фазы или вилки — сразу обновить «Дорожную карту» в том же коммите.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-09-25 · by: Codex · HEAD at update: 80602f6e

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
- 2026-09-25: четыре Lean-кандидата 22.09 побайтно перенесены в `Q3/Proofs/RouteB/Q3*Candidate20260922.lean`;
  `scripts/q3_check.sh` — ok, полный `lake build` — 8215 jobs, exit 0. Только аксиомы
  propext/Classical.choice/Quot.sound. Теоремы остаются условными; `hmode` и RH не закрыты.
- Paired-window Mellin identity, Rminus crosswalk, Euler identity: PAPER-level
  (`docs/Codex/BRIEF_2026-09-22_FOKAS_PAIRED_WINDOW.md`, `docs/Codex/REPORT_2026-09-22_FOKAS_RMINUS_CROSSWALK.md`).

## Следующий шаг
1. Fokas rank-2 joint green (TRY_GOAL058_FOKAS_JOINT_GREEN_RANK2): тождество даёт точную формулу остатка;
   НЕ доказаны равномерная оценка убывания дефекта и sector floors. Граничный контроль t−V = 3√2/4 воспроизведён.

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

## Жёсткие линии (не обсуждаются)
Без `sorry`; без собственных `axiom`; только три стандартные аксиомы Lean (см. Цель п.2);
недоказанное не называть доказанным; claim — только по условиям из «Цели»;
одновременно работает одна машина (какая — решает владелец).
