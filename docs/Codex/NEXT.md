# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~80 строк.
При закрытии ворот, фазы или вилки — сразу обновить «Дорожную карту» в том же коммите.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-09-26 · by: Codex Linux · baseline HEAD: 2a3c207d

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

## Прошка
- 2026-09-26 Mac отправил `REQ-2026-09-26-ABEL-CUMULATIVE-FORCING` как № **1** в [новый чат того же проекта](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab7b2af-b820-83eb-8290-1684c77ac443). Ответ `OPEN_ABEL_FORCING_SIGN` получен; [точный текст](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ABEL_CUMULATIVE_FORCING_2026-09-26.md) сохранён. [Независимая PAPER-сверка](PAPER_CHAIN.md) и два read-only review-прохода приняли (A), (W), центрированную формулу и Cauchy enclosure только в этом объёме. Source-uniform запас, первый знак `τ_j` и Schur-floor OPEN. Подтверждение и хеш — в [строке запроса](../routeB_bus/PROSHKA_QUEUE.md#req-2026-09-26-abel-cumulative-forcing--full-selected-forcing-after-finite-abel-summation--open). Последующий тест `TEST_SOURCE_GROUND_CENTERED_ABEL_DISCRIMINANT` выполнен ответом № 2 ниже; № 1 не дублировать.
- [`REQ-2026-09-26-GROUND-CENTERED-ABEL-DISCRIMINANT`](../routeB_bus/PROSHKA_QUEUE.md#req-2026-09-26-ground-centered-abel-discriminant--source-ground-centered-abel-discriminant--answered) подтверждённо отправлен в тот же чат как **№ 2/10** к 2026-09-26 12:35:23 UTC; [точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_GROUND_CENTERED_ABEL_DISCRIMINANT_20260926.txt), SHA-256 `161f56855c1df5647b5ec36a760168e18335025d9e145254913b77102b05c4ef`. Ответ `OPEN_SOURCE_DISCRIMINANT` получен: [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_GROUND_CENTERED_ABEL_DISCRIMINANT_2026-09-26.md), SHA-256 `1b4dff27d3bff6808a541db78ae1f205b2e8714f62c5123ff70f46cf8a2d56cb`; [inline-ответ](../routeB_bus/proshka/PROSHKA_INLINE_GOAL058_GROUND_CENTERED_ABEL_DISCRIMINANT_2026-09-26.md), SHA-256 `94d4e08a929b5fa5ea3790295e171e4a9538afbf87a9a2dd399e373aa6fa5be3`. [Независимая PAPER-сверка](PAPER_CHAIN.md) и два read-only review-прохода приняли только нормировку и условный cone-тест. Source-оценки (20) и `δ(m)>0` нет; не дублировать запрос.
- [`REQ-2026-09-26-CONE-AXIS-GROUND-ANGLE`](../routeB_bus/PROSHKA_QUEUE.md#req-2026-09-26-cone-axis-ground-angle--source-cone-axis-ground-angle--answered) отправлен как **№ 3/10** в активный чат к 2026-09-26 14:42:56 UTC с точным [TXT](../session_protocols/PROSHKA_REQUEST_GOAL058_CONE_AXIS_GROUND_ANGLE_20260926.txt), SHA-256 `85db1f1a51f9094c4ad3138a11cd937dc68b18d38a927837470e3cd6168499ac`. Ответ **OPEN_CONE_AXIS_ANGLE** получен: [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CONE_AXIS_GROUND_ANGLE_2026-09-26.md), SHA-256 `51312b0e7c883a74609e9ab074083b2b01644680624f5e01ffdd21ef34772445`; [точный inline-текст](../routeB_bus/proshka/PROSHKA_INLINE_GOAL058_CONE_AXIS_GROUND_ANGLE_2026-09-26.md), SHA-256 `82d1b7898c1f64fadf59ffeddf81132205bc46f4db1753ae620053515cfe4dc9`. [Независимая PAPER-сверка](PAPER_CHAIN.md) и два последовательных read-only review-прохода приняли чётное plane-axis тождество и полное displacement-разложение с диагональю/Q6, но осевой зазор, obstruction, знак `τ_j` и Schur-floor OPEN; не дублировать.
- [`REQ-2026-09-26-PLANE-PROJECTIVE-DISPLACEMENT`](../routeB_bus/PROSHKA_QUEUE.md#req-2026-09-26-plane-projective-displacement--source-plane-projective-displacement--answered) подтверждённо отправлен как **№ 4/10** в активный чат к 2026-09-26 15:11:31 UTC; [точный TXT](../session_protocols/PROSHKA_REQUEST_GOAL058_PLANE_PROJECTIVE_DISPLACEMENT_20260926.txt), SHA-256 `2d47a7afc44920ab5e67012fe28441dac8c31fe7c89180171d0dc154e0574e7a`. Ответ **OPEN_PLANE_DIRECTION** получен: [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_PLANE_PROJECTIVE_DISPLACEMENT_2026-09-26.md), SHA-256 `78750ef46a881243dc68a15d61417cb480286cf50a886e13451f052531792737`; [точный inline-текст](../routeB_bus/proshka/PROSHKA_INLINE_GOAL058_PLANE_PROJECTIVE_DISPLACEMENT_2026-09-26.md), SHA-256 `7a949095757f2ae8a53100f6e5774d26aceee0fcdfd4c66a6878fb7a8c3d0b04`. [Независимая PAPER-сверка](PAPER_CHAIN.md) и два последовательных read-only review-прохода приняли тождества для фактических координат и вращение первой пропущенной пары; относительная source-оценка, сектор, осевой зазор и obstruction OPEN. Не дублировать.
- Активная фаза: `PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923`.
- Активный чат: [6ab7b2af…](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab7b2af-b820-83eb-8290-1684c77ac443); подтверждённых математических отправок в нём: **5/10**. Незакрытых строк очереди сейчас нет. Предыдущий [6ab6827b…](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab6827b-387c-83eb-a71d-865f68d835d5) исчерпан **10/10**; все его подтверждённые запросы отвечены. Следующий PAPER-ход — `TEST_SOURCE_COMPRESSION_TWO_SINGULAR_VALUE_OBSTRUCTION`: проверить знак фактического `𝔍_m` на неограниченном множестве выбранных индексов; это лишь необходимый тест rank-one сертификата.
- Подготовлен, **не отправлен** `REQ-2026-09-26-COMPRESSION-SPECTRAL-SPREAD`: [точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_COMPRESSION_SPECTRAL_SPREAD_20260926.txt), SHA-256 `6375cf87c0175f15f913fdd1343f39489f95e53065f32d4e3957e18e8d800ad9`; адрес — [активный чат 6ab7b2af…](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab7b2af-b820-83eb-8290-1684c77ac443), где подтверждено **5/10** отправок. Два последовательных on-target read-only pre-send review-прохода на этих байтах — CLEAN. Строку очереди добавить только после подтверждённой отправки.
- [`REQ-2026-09-26-FIRST-OMITTED-COMPRESSION`](../routeB_bus/PROSHKA_QUEUE.md#req-2026-09-26-first-omitted-compression--source-first-omitted-compression--answered) подтверждённо отправлен как **№ 5/10** к 2026-09-26 15:44:39 UTC; ответ **OPEN_FIRST_OMITTED_COMPRESSION** получен: [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FIRST_OMITTED_COMPRESSION_2026-09-26.md), SHA-256 `2e4c9122664351489d288bfe6eed3df630566a0e1474f3de6451562874e5912e`; [точный inline-текст](../routeB_bus/proshka/PROSHKA_INLINE_GOAL058_FIRST_OMITTED_COMPRESSION_2026-09-26.md), SHA-256 `d93e0db03cddd7fbea0b36c5dab3c3c343df056b1241c6ee76b88c7824543c51`. [Независимая PAPER-сверка](PAPER_CHAIN.md) и два последовательных on-target read-only review-прохода приняли сходимость полной формы для этих ошибок и необходимое условие на две сингулярные величины; знак фактического `𝔍_m`, доминирование и осевой зазор OPEN. Не дублировать.
  [`REQ-2026-09-25-CELLWISE-COMPLEMENT-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_FIRST_SIGN`; полный текст сохранён и независимо сверен. Отправка подтверждена 2026-09-25 16:17 Europe/Berlin, не дублировать.
  [`REQ-2026-09-25-NULLPLANE-LEAKAGE-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_SIGNED_LEAKAGE`; полный Markdown сохранён, ключевое сокращение и ledger независимо проверены. Не дублировать. Поправка `1/m` остаётся в нулевой плоскости, а точная совместная энергия ошибок даёт `τ_j=−𝔏_m/ρ_m²`; знак `𝔏_m` и следующий Schur-блок открыты.
  [`REQ-2026-09-25-COUPLED-DEFECT-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_COUPLED_DEFECT_SIGN`. Полное вложение сохранено и побайтно сверено с SHA-256 из ответа; независимая PAPER-сверка подтвердила равномерный Ferrers-tail budget и алгебру `𝔏_m=T(m)+𝓡(m)`, `|𝓡|≤B`, но не знак. Его тест одностороннего сравнения полной source-формы (17) с бюджетом (18) теперь уточнён ответом на запрос № 4 ниже. Не дублировать запрос.
  [`REQ-2026-09-25-ADJOINT-GREEN-MIX`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отвечен `OPEN_ADJOINT_GREEN_MIX`; полное вложение сохранено, два независимых PAPER review-прохода не нашли замечаний. Для source-matched Robin-блоков исключён резонанс и получен точный перенос всей квартетной формы, но знак граничного отклика (28±), `τ_j` и Schur-floor открыты. Не дублировать. Следующий тест — `TEST_SOURCE_MATCHED_ROBIN_COUPLED_BOUNDARY_MARGIN` из §9 вердикта.
  [`REQ-2026-09-25-SIGNED-ROBIN-KERNEL`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен в этот чат как № **5/10**; ответ `OPEN_SIGNED_ROBIN_KERNEL` получен и побайтно сохранён (SHA-256 `289c91921139f565f939867547582d8b606fc195f53c3c0f235d7b7771c735d6`). Два независимых PAPER-прохода проверили один переход знака весов `W_k` при принятом hmode; знак полного `κ_mΣW_kh♯_k` и `τ_j` открыт. Не дублировать.
  [`REQ-2026-09-25-FULL-SCALAR-SIGN-CHAIN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен в этот чат как № **6/10** 2026-09-25 19:26 Europe/Berlin; ответ **OPEN_FULL_SCALAR_SIGN_CHAIN** получен. [Точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_FULL_SCALAR_SIGN_CHAIN_20260925.txt), SHA-256 `587f83d66de9d159f041cb8f8af6badd9057dc7775ce514a20784049b4dfc5a9`; [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FULL_SCALAR_SIGN_CHAIN_2026-09-25.md), SHA-256 `dce93c5088cd3ebf3a3d67abb0706a486fcb31d9d59c2975672699c7b6a6f42d`. [Два независимых PAPER-прохода](../routeB_bus/proshka/PROSHKA_GOAL058_FULL_SCALAR_SIGN_INDEPENDENT_AUDIT_2026-09-25.md) не нашли ошибки в (D1)–(D6), (R1)–(R8) и условном (TEST). Но знак полной суммы `Q_m=κ_mΣW_kh♯_k` и `τ_j` открыт: `y_->0` и один семейный `D_±>0` не установлены. Не дублировать запрос.
  [`REQ-2026-09-25-TWO-ENERGY-FULL-QUARTIC-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен в этот активный чат как № **7/10** by 2026-09-25 20:01:55 Europe/Berlin; ответ **RECTANGLE_KILL только для RAW_R6**, не дублировать. [Точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_TWO_ENERGY_FULL_QUARTIC_SIGN_20260925.txt), SHA-256 `5187bfde3c014f73a537cef40876e0c8742fc732e54d9f5c485ac1029cefe98e`; [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_TWO_ENERGY_FULL_QUARTIC_SIGN_2026-09-25.md), SHA-256 `e9502879d0690db71da6283e1b2cef5ee4271cd024182b549dcaf6174691ad2a`. [Два независимых PAPER-прохода](../routeB_bus/proshka/PROSHKA_GOAL058_TWO_ENERGY_FULL_QUARTIC_INDEPENDENT_AUDIT_2026-09-25.md) подтвердили отрицательность обоих достаточных запасов именно для прямой мажоранты. Исправленный anchor-bound (19) убывает, но знак полного центрального `p_c`, `Q_m`, `τ_j` и Schur-floor открыт.
- [`REQ-2026-09-25-REPAIRED-RECTANGLE-CENTRAL-SIGN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен как № **8/10** к 2026-09-25 20:34:53 Europe/Berlin в [активный чат](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab6827b-387c-83eb-a71d-865f68d835d5); ответ **OPEN_REPAIRED_CENTRAL_SIGN** получен, не дублировать. [Точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_REPAIRED_RECTANGLE_CENTRAL_SIGN_20260925.txt), SHA-256 `1994d06ae55f3c584b43267d127ffa959fa9621ecfe976984bce8dd3f3bcecb2`; [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_REPAIRED_RECTANGLE_CENTRAL_SIGN_2026-09-25.md), SHA-256 `bf8963f7a453063cddebd77a84cf060303211243155cac095dd334688cb7ddc8`. Два независимых PAPER-прохода новых тождеств без замечаний при принятых входах. Первый открытый подписанный остаток — корреляция дефекта с `ψ(v)−v`; знак полной формы, `τ_j` и Schur-floor остаётся OPEN. Следующий тест — `TEST_SIGNED_CHEBYSHEV_PRIMITIVE_ON_CENTRAL_DEFECT` со скачком `v=m`.
- [`REQ-2026-09-25-SIGNED-CHEBYSHEV-PRIMITIVE`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) подтверждённо отправлен в [активный чат](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab6827b-387c-83eb-a71d-865f68d835d5) как № **9/10** к 2026-09-25 21:23:52 Europe/Berlin. [Точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_SIGNED_CHEBYSHEV_PRIMITIVE_20260925.txt), SHA-256 `a7853753b606bc61831e8f1c881027db649861e52c718ec757d36ab1fdaedf5a`; два независимых pre-send review-прохода без замечаний. Ответ **OPEN_SIGNED_CHEBYSHEV_PRIMITIVE**, [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNED_CHEBYSHEV_PRIMITIVE_2026-09-25.md), SHA-256 `063f29ca63098fdded75f6764740a79a7807190b698995b95305917f9d35939b`. В PAPER_CHAIN независимо проверены отмена primitive-сглаживания, полный скачок, нормировка zero-side (22) по CCM §3 и алгебра zero-tail (24); константы (13)–(17) не прошли полного аудита. Знак полного центра, `τ_j`, Schur-floor открыты; не дублировать.
- [`REQ-2026-09-25-ZERO-ORBIT-HEAD-MARGIN`](../routeB_bus/PROSHKA_QUEUE.md#2026-09-25--selected-complement-floor) отправлен в [активный чат](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab6827b-387c-83eb-a71d-865f68d835d5) как № **10/10** к 2026-09-25 22:01:13 Europe/Berlin. [Точный intent](../session_protocols/PROSHKA_REQUEST_GOAL058_ZERO_ORBIT_HEAD_MARGIN_20260925.txt), SHA-256 `c25325cac3cfa330e129c1e51189e5c22e26cc1179676d4766ff29b65e899773`; ответ **OPEN_ZERO_ORBIT_HEAD_SIGN** получен, [полное вложение](../routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ZERO_ORBIT_HEAD_MARGIN_2026-09-25.md), SHA-256 `6ed099360406437fc02b1ece2b52ebcc6e94d0884989c4a78126aff27bf20313`. В PAPER_CHAIN независимо проверены endpoint-фаза, оба скачка, арифметика zero-tail, quartet-поляризация и абстрактный барьер знака. Signed margin для выбранной пары и HEAD_TEST_KILL не доказаны; `τ_j` и Schur-floor OPEN. Не дублировать.
- Прежний чат [6aafb38a…](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6aafb38a-a7a4-83eb-9940-84a574eae168) исчерпан для **новых** запросов: точное общее число подтверждённых отправок в нём не восстановлено. Незакрытые ответы проверять по адресам соответствующих строк очереди.
- Подтверждённый запрос `REQ-2026-09-25-INDEPENDENT-COMPLEMENT-FLOOR` отвечен и
  независимо проверен на уровне PAPER; [отдельное исходное вложение](../routeB_bus/proshka/PROSHKA_ATTACHMENT_GOAL058_INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25.md)
  (SHA-256 `e80a26c654928fad714b6cebf2dab347ff68a9eff6b5f0ff430447e5122aad15`)
  не совпадает побайтно с текстом ответа, проверено отдельно в [аудите](../routeB_bus/proshka/PROSHKA_GOAL058_FLOOR_KILL_INDEPENDENT_AUDIT_2026-09-25.md).
  Принято только опровержение одного фиксированного положительного floor; cellwise
  `δ_j`, residual rate и RH открыты. Его строка и адрес сохранены в `docs/routeB_bus/PROSHKA_QUEUE.md`
  (секция `2026-09-25 · selected complement floor`). Незакрытые строки других запросов
  остаются по своим прежним адресам; ответ нельзя переносить между чатами.
- Fokas-запрос `PROSHKA_REQUEST_GOAL058_FOKAS_MATRIX_DEFECT_20260923.txt`:
  исторический UI-rendered ответ восстановлен в bus: [источник и границы](../routeB_bus/proshka/PROSHKA_FOKAS_MATRIX_DEFECT_RECOVERY_2026-09-25.md). Исходный Markdown не верифицирован. Точная формула есть; decay открыт, constant-beta wrapper неприменим. Не повторять отправку.

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
