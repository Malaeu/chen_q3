# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~80 строк.
При закрытии ворот, фазы или вилки — сразу обновить «Дорожную карту» в том же коммите.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-09-25 · by: Codex · baseline HEAD: 6e2a7cd7

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
  G1 кофинальный ground-пакет ..... ОТКРЫТО (constant hfloorEv опровергнут для выбранной семьи; cellwise вариант не доказан)
  G2 вещественные нули ............ готово
  G2b перенос нулей на P5.9 ....... доказано
  G3 та же семья трекает trial .... ОТКРЫТО — вместе с G1 главный математический фронт
  G3c projected → continuum trial . ОТКРЫТО
  G4 CCM Lemma 7.3: trial → Ξ ..... ОТКРЫТО (в статье доказано, Lean-порт открыт)
  G5 Гурвиц → Q3.RH ............... готово
  затем `riemannHypothesis_of_rh` (доказано) → Comparator → claim.

Lean-потребитель: `rh_of_real_zero_family_tendsto_centeredXi`
  (`q3.lean.aristotle/Q3/Proofs/RouteB/Goal058DirectGroundZeroEscape.lean:27`), посылки hzeros, hentire, hconv.
  В RouteB 0 `sorry`, 0 `axiom`.
Осталось: 5 из 8 ворот. В Lean 7 открытых посылок:
  1. hmode — sup-норма близости Ferrers mode0/mode4 к D0/D4 (бумага проверена, Lean-вход открыт);
  2. hχ/hθ — следствия hmode на бумаге; формализация не завершена;
  3. hfloorEv (constant-β форма опровергнута для выбранной семьи; нужен иной интерфейс);
  4. hoddEv (условный мост из constant hfloorEv здесь не поставщик);
  5. hratioEv (текущий constant-β wrapper неприменим)
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
Полная бумажная цепь со статусами и источниками: `docs/Codex/PAPER_CHAIN.md`. Порядок оттуда:
1. `hmode` закрыт на бумаге. Постоянный `hfloorEv` для буквальной выбранной CCM-семьи
   опровергнут кофинальным свидетелем; независимая сверка в
   `docs/routeB_bus/proshka/PROSHKA_GOAL058_FLOOR_KILL_INDEPENDENT_AUDIT_2026-09-25.md`.
2. Основное время: доказать или точно локализовать пробел для cellwise `δ_j>0` на том же
   trial-complement и оценить полный `‖r_j‖/δ_j`; отдельно проверить, какой cellwise
   consumer переносит это в tracking без подстановки в constant-β wrapper. Затем G3.
3. Параллельно: G4 crosswalk (h_λ ↔ hTrial_m, скаляр/фаза, C = 2πλ²) и projection tail (G3c).
4. После оплаченных входов — сборка → hconv. Lean Fokas joint green отложено.

## Прошка
- Активная фаза: `PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923`.
- Активный чат: [6ab6827b…](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab6827b-387c-83eb-a71d-865f68d835d5); подтверждённых математических отправок в нём: **7/10**.
  [`REQ-2026-09-25-CELLWISE-COMPLEMENT-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_FIRST_SIGN`; полный текст сохранён и независимо сверен. Отправка подтверждена 2026-09-25 16:17 Europe/Berlin, не дублировать.
  [`REQ-2026-09-25-NULLPLANE-LEAKAGE-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_SIGNED_LEAKAGE`; полный Markdown сохранён, ключевое сокращение и ledger независимо проверены. Не дублировать. Поправка `1/m` остаётся в нулевой плоскости, а точная совместная энергия ошибок даёт `τ_j=−𝔏_m/ρ_m²`; знак `𝔏_m` и следующий Schur-блок открыты.
  [`REQ-2026-09-25-COUPLED-DEFECT-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_COUPLED_DEFECT_SIGN`. Полное вложение сохранено и побайтно сверено с SHA-256 из ответа; независимая PAPER-сверка подтвердила равномерный Ferrers-tail budget и алгебру `𝔏_m=T(m)+𝓡(m)`, `|𝓡|≤B`, но не знак. Его тест одностороннего сравнения полной source-формы (17) с бюджетом (18) теперь уточнён ответом на запрос № 4 ниже. Не дублировать запрос.
  [`REQ-2026-09-25-ADJOINT-GREEN-MIX`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_ADJOINT_GREEN_MIX`; полное вложение сохранено, два независимых PAPER review-прохода не нашли замечаний. Для source-matched Robin-блоков исключён резонанс и получен точный перенос всей квартетной формы, но знак граничного отклика (28±), `τ_j` и Schur-floor открыты. Не дублировать. Следующий тест — `TEST_SOURCE_MATCHED_ROBIN_COUPLED_BOUNDARY_MARGIN` из §9 вердикта.
  [`REQ-2026-09-25-SIGNED-ROBIN-KERNEL`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен в этот чат как № **5/10**; ответ `OPEN_SIGNED_ROBIN_KERNEL` получен и побайтно сохранён (SHA-256 `289c91921139f565f939867547582d8b606fc195f53c3c0f235d7b7771c735d6`). Два независимых PAPER-прохода проверили один переход знака весов `W_k` при принятом hmode; знак полного `κ_mΣW_kh♯_k` и `τ_j` открыт. Не дублировать.
  [`REQ-2026-09-25-FULL-SCALAR-SIGN-CHAIN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен в этот чат как № **6/10** 2026-09-25 19:26 Europe/Berlin; ответ **OPEN_FULL_SCALAR_SIGN_CHAIN** получен. [Точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_FULL_SCALAR_SIGN_CHAIN_20260925.txt), SHA-256 `587f83d66de9d159f041cb8f8af6badd9057dc7775ce514a20784049b4dfc5a9`; [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FULL_SCALAR_SIGN_CHAIN_2026-09-25.md), SHA-256 `dce93c5088cd3ebf3a3d67abb0706a486fcb31d9d59c2975672699c7b6a6f42d`. [Два независимых PAPER-прохода](../routeB_bus/proshka/PROSHKA_GOAL058_FULL_SCALAR_SIGN_INDEPENDENT_AUDIT_2026-09-25.md) не нашли ошибки в (D1)–(D6), (R1)–(R8) и условном (TEST). Но знак полной суммы `Q_m=κ_mΣW_kh♯_k` и `τ_j` открыт: `y_->0` и один семейный `D_±>0` не установлены. Не дублировать запрос.
  [`REQ-2026-09-25-TWO-ENERGY-FULL-QUARTIC-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен в этот активный чат как № **7/10** by 2026-09-25 20:01:55 Europe/Berlin; ответ **PENDING**, не дублировать. [Точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_TWO_ENERGY_FULL_QUARTIC_SIGN_20260925.txt), SHA-256 `5187bfde3c014f73a537cef40876e0c8742fc732e54d9f5c485ac1029cefe98e`; отправленный текст побайтно совпал без финального LF. После первоначального LOW (неявный `θ`) исправлен и прошёл два последовательных on-target native review-прохода без замечаний. Проверять ответ по адресу строки очереди.
- Прежний чат [6aafb38a…](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6aafb38a-a7a4-83eb-9940-84a574eae168) исчерпан для **новых** запросов: точное общее число подтверждённых отправок в нём не восстановлено. Незакрытые ответы проверять по адресам соответствующих строк очереди.
- Подтверждённый запрос `REQ-2026-09-25-INDEPENDENT-COMPLEMENT-FLOOR` отвечен и
  независимо проверен; его строка и адрес сохранены в `docs/routeB_bus/PROSHKA_QUEUE.md`
  (секция `2026-09-25 · selected complement floor`). Незакрытые строки других запросов
  остаются по своим прежним адресам; ответ нельзя переносить между чатами.
- Fokas-запрос `PROSHKA_REQUEST_GOAL058_FOKAS_MATRIX_DEFECT_20260923.txt`:
  ответ виден в UI, но точный текст ещё не сохранён в bus; не повторять отправку.

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
