# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~80 строк.
При закрытии ворот, фазы или вилки — сразу обновить «Дорожную карту» в том же коммите.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-09-27 · by: Codex Mac · baseline HEAD: c2a211e3

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
- 2026-09-26 Mac: [source transfer](../routeB_bus/fokas_k_sign_2026-09-25/SOURCE_TRANSFER.md) проверен на PAPER: ошибка точной строки <=(Z*alpha+E)/(Z-E), без деления source-ошибки на gap. При принятых hmode/hchi и хвостовых оценках вклад E исчезает; семейная скорость центральной alpha открыта. Диагностика m4/m8/m13: 0.03089/0.05534/0.06052, не доказательство хвоста.
- 2026-09-25 Mac: [независимый энергетический порог](../routeB_bus/fokas_k_sign_2026-09-25/INDEPENDENT_ENERGY_SHIFT.md): для рациональной reference-строки m8 Arb строго подтвердил отрицательный Rayleigh-complement, но при mu=10^-18 — ground ниже mu, всё q-perp выше mu с запасом 3*10^-17 и проекционную ошибку <0.05536. Также сертифицирован кластер четырёх нижних уровней. PAPER-лемма и код независимо проверены; это НЕ выбранный кофинальный source-пакет.
- 2026-09-25 Mac: [полный K/sign-пакет](../routeB_bus/fokas_k_sign_2026-09-25/REPORT.md):
  [Аудит исходного Fokas-goal](../routeB_bus/fokas_k_sign_2026-09-25/GOAL_AUDIT.md): проверка завершена точным препятствием fixed-beta consumer; Goal058 и cellwise tracking открыты.
  PAPER Robin-width усилен до `G/8*(16m-3)/(24m-3)*4^(-2m)` без смены склейки;
  строгий Arb m2 finite-algebra margin с уточнённым Frobenius budget положителен.
  Source applicability m2 и cofinal sign не закрыты; диагностики m4/8/13 — не доказательство хвоста.
  Дополнительно: [signed density test](../routeB_bus/fokas_k_sign_2026-09-25/NORMALIZED_CORRELATION.md) строго исключил pointwise positivity на reference m2; m4 cancellation factor ~759 — только диагностика.
  Ответ №7 даёт более сильную скобку при m>=10000 и убивает только RAW_R6 value-anchor; наш центр+производная не подпадает под этот kill.
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
2. Основное время: независимые пороги mu_j и reference ground-tracking rate; source-перенос
   оплачивать по SOURCE_TRANSFER, не делением на gap. Открыта скорость
   m_j^(H/2)*sqrt(log m_j)*alpha_j → 0 (достаточно для G3); finite m8 не даёт её.
3. Параллельно: G4 crosswalk (h_λ ↔ hTrial_m, скаляр/фаза, C = 2πλ²) и projection tail (G3c).
4. После оплаченных входов — сборка → hconv. Lean Fokas joint green отложено.

Поиск литературы 2026-09-27: [signed-form/effective-resistance map](../literature/signed_form_effective_resistance_2026-09-27.md) даёт строгий графовый механизм `w R_eff<1` / совместный Schur-тест, но только `PARTIAL ANALOGUE` к selected Q3. Источниковая факторизация, coercivity положительной части и cofinal joint loss OPEN; текущий finite-coefficient-panel запрос Прошке не заменять.

Геометрический контроль глобальной формы: [PAPER-разбор длинных связей](REPORT_2026-09-27_LONG_LAG_CRITICAL_RATIO.md) доказал, что `N_s≤(1−ε)P_s` с фиксированным `ε>0` для всех компактных профилей невозможно: атом `n=2` дал бы запрещённый положительный finite-stencil minorant. Точное разбиение длинной связи на короткие сохраняет endpoint-веса, но их pointwise отношение неограниченно. Это **не** опровергает острое `N_s≤P_s` и **не** решает selected Goal058 floor; нужен нелокальный совместный перенос с константой `1` либо другой source-механизм.
Новый [PAPER-тест prime bridge](REPORT_2026-09-27_PRIME_BRIDGE_ENDPOINT_KILL.md): прямой перенос атома `log p` на левую окрестность `t<log p` неограничен на пространстве независимых рёбер из-за точного отношения `f₀(x+t)/f₀(x+log p)` при `x→+∞`. Это отвергает только данный ambient contraction, не знак на согласованных градиентах и не отдельный selected C128.
Его [смешанный член проверен на самих градиентах](REPORT_2026-09-27_PRIME_BRIDGE_MIXED_SIGN.md): для компактных гладких отсечённых волн на одной узкой полосе `t<log p` он бывает строго положительным и строго отрицательным. Полное суммирование по полосам даёт `Q=P−N_out−ΣS_j+ΣM_j`; требование `ΣM_j≥N_out+ΣS_j−P` ровно эквивалентно исходному DOM, а не доказывает его. Нужна независимая source-оценка полной signed суммы с исходными весами и prime-power атомами; selected C128/floor и RH OPEN.

## Прошка
- Активный чат проекта и история всех запросов: `docs/routeB_bus/PROSHKA_QUEUE.md`; ответы — `docs/routeB_bus/proshka/`.
- Открытые вопросы, убитое и текущий фронт — только в `PAPER_CHAIN.md` (здесь не дублировать).

## Правила работы (владелец, 2026-09-28)
Для этого репо сильнее глобальных правил Codex (`~/.codex/AGENTS.md` §§3, 5, 6, 9) и старого control.
1. Вопрос Прошке — рабочее сообщение, не outbound artifact: без review-цикла, без записей
   intent / dispatch / confirm / receipt. Один коммит на вопрос — после ответа: запрос + ответ + вывод вместе.
2. Сито перед вопросом: своя попытка уже сделана; вопрос называет звено `PAPER_CHAIN` и какой ответ
   изменит план; не повторяет убитое. Пока ответ не отработан — следующего вопроса по тому же звену нет.
3. Одна линия атаки — механизм из «Текущий фронт» в `PAPER_CHAIN`. Смена механизма — только после
   записанного убийства или тупика (одной строкой в «Убито»).
4. Независимая проверка (один проход) — только для вывода, который меняет статус звена (закрыто/убито).
5. Размеры: `PAPER_CHAIN.md` ≤ 200 строк, `NEXT.md` ≤ 120, запись в `PROSHKA_QUEUE.md` ≤ 5 строк.
   SHA, ID ходов, пути ревьюеров — только в файле ответа в bus. `AGENTS_LEDGER` и состояния
   prepared/attempted/observed/… не вести.
6. Бухгалтерия, которая не меняет математику, — не делать. Сомневаешься — спроси владельца одной строкой.

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
