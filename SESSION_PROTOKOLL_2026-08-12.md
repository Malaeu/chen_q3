# Протокол сессии 2026-08-12 — маршрут стал инфраструктурой, инструмент стал проверяемым

Тело: Linux. Ветка `rh_clean`. Шесть коммитов, все запушены.
Параллельно в том же дереве работала вторая сессия Claude — см. «Две сессии в одном дереве».

---

## Kontext

Вчера собрали конструктор и трижды прогнали его на узле `SIMPLE_EVEN:1`. Собрали запрос к
судье про форму `family = c_N · Лагранж` и **не отправили**.

Сегодня владелец принёс из дома два документа: собственный разбор моста ground→trial и
мастер-маршрут судьи от 11.08.

## Ausgangslage

Маршрут судьи лежал в `docs/_inbox/` прозой. В проекте маршрут — это цепь в `assembly`,
устав-гол, раздел карты и мигратор. Прозы недостаточно: инструменты её не читают.

Запрос по форме `c_N · Лагранж` стоял готовым к отправке.

## Aufgabe

1. Разложить входящее, сверить с деревом.
2. Сделать из маршрута судьи настоящий маршрут проекта.
3. Прокартографировать объекты, выписать контракты ворот.
4. Починить инструменты до того, как на них строить спеки.
5. Прогнать через Codex, прежде чем называть готовым.

---

## Erledigt

### Маршрут 058 заведён как инфраструктура

```
docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md   устав
orchestrator/kb_migrate_route058.py                          мигратор цепи, --check
docs/routeB_bus/MAP.md §8b                                   раздел карты
docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md                   контракты восьми ворот
assembly · REALZERO_GROUND_DIAGONAL_TO_XI                    8 шагов, 2 READY, 6 GAP
```

Инструменты читают его без доработок: `brief.py` показывает восемь шагов, `cheap.py`
раскладывает по цене и сам находит перекрёстную ссылку.

Цепь пишется скриптом, не руками. Прежние цепи вносились напрямую, и происхождение строки
теперь не восстановить.

### Форма `Pstar = c_N · многочлен` убита до отправки

Судья ответила раньше, чем вопрос ушёл. Её аргумент §7.3: у преобразования бесконечно много
нулей на синус-решётке, у ненулевого многочлена конечное число, скаляр их не сравняет.

Мы пришли к тому же независимо тем же утром, разбором порядка роста. Запрос помечен баннером
и сохранён как след; предсказания не разыгрываются.

### Инструмент разбора имён: восемь дефектов

Первый прогон по маршруту дал два правдоподобно неверных адреса: `epsilon` в ординалах
Веблена, `xi` в постороннем файле. Оба — связанные переменные без места объявления. Так же
родился `hermfact1`.

Поставлена классификация провенанса. Адрес выдаётся только настоящей декларации; отвергнутое
совпадение печатается.

Найдено и закрыто своими силами: поля структур не искались вовсе; мёртвая переменная;
пороги длины имени вместо правила; порядок проверок, при котором приведение типа
`(ccmModeFinite N i : ℝ)` читалось как связывание.

### Реестр внешних Lean-баз

`docs/cartographer/lean_bases.yaml`. Базы подключаются как плагины: `origin`, пути-кандидаты
под разные машины, пин, лицензия, `verified_by` с найденными `file:line`.

Прежде чужая база подключалась одним `--foreign`, захардкоженным в манифесте — верно ровно
на одной машине.

**Статьи в реестр не входят.** CCM, Suzuki, Yoshida — бумажные теоремы, они не компилируются
и живут в `litreview/`.

### Ревью Codex: 13 находок, вердикт BLOCKED-CRITICAL

Девять закрыто, одна частично, три открыты. Подробности в разделе «Geprüft».

### Стили вывода починены

`/output-style` убрана из Claude Code; механизм жив как настройка, вход через `/config`.

**Настоящий дефект:** оба наших файла стиля не имели ключа `keep-coding-instructions`.
Условие в бинаре — `keepCodingInstructions === true ? qIb() : null`. Без ключа инструкции по
работе с кодом выпадают из системного промпта. Ключ добавлен в оба; стиль `STE100` включён.

Установлены три стиля из `github.com/alexgreensh/attention-span` (AGPL-3.0): Attention-kind,
Spartan, Rundown. У всех трёх ключ стоит правильно — они знали то, чего не знали мы.

### Запрос судье готов и не отправлен

`PROSHKA_REQUEST_ROUTE058_BEYOND_CCM_SECTION8_2026-08-12.md`.

Счёт очереди обнулён. Новый порядок: один запрос — один файл, владелец относит сам.

---

## Geprüft

### Проверено по первоисточникам, дословно

**CCM §8, стр. 32** — два недостающих шага названы авторами:

> «The first is that ... its smallest eigenvalue ... is simple and that its corresponding
> eigenvector ξ_λ is even. The second step is to establish that k_λ provides a sufficiently
> accurate approximation to **(a scalar multiple of)** ξ_λ ...»

Это наши `G1` и `G3`. **Пробел назван в статье, а не нами.** Присланный разбор утверждал
обратное; утверждение снято.

Скобка «(a scalar multiple of)» объясняет происхождение убитой формы: статья пишет
приближение к скалярному кратному, мы записали равенство. Приближённое стало ложным точным.

**Connes 2026, Теорема 6.1, стр. 26** — движок вещественных нулей, с атрибуцией на совместную
статью с van Suijlekom. Подтверждает соответствующее утверждение разбора.

### Проверено на диске

Поиск по чужой базе работает: найдены `posIndex` `PosIndex.lean:41`, `rank_trace_ineq`
`RankTrace.lean:163`, `finrank_le_posIndex_of_posDefOn` `Sylvester.lean:82`, `hermPosPart :148`,
`vonNeumann_trace_ineq :171`.

Каждый адрес в контрактах ворот сверен построчно. Поймана одна неверная: `Q3.RH` лежит в
`Basic/Defs.lean:177`, не в `Defs.lean`.

Самопроверка разбирателя: 20 имён, ноль провалов. Сверка маршрута с базой: 8 из 8.

### Ревью Codex — таблица находок

| # | Severity | Finding — *по-русски* | состояние |
|---|---|---|---|
| 1 | CRITICAL | External-source counter crash — *падение счётчика на внешней базе* | закрыто |
| 2 | HIGH | Undeclared scope change — *незаявленный файл в наборе* | закрыто |
| 3 | HIGH | Type-ascription false positive — *приведение типа принято за биндер* | закрыто |
| 4 | HIGH | Shadowing and search-order ambiguity — *затенение и порядок поиска* | закрыто |
| 5 | HIGH | Heuristic field loss — *потеря полей структуры* | закрыто |
| 6 | HIGH | Unpinned base identity — *не зафиксирована личность базы* | закрыто |
| 7 | HIGH | Non-executable Mac procedure — *инструкция для Мака неисполнима* | закрыто |
| 8 | HIGH | False-green regression test — *ложно-зелёный тест* | **частично** |
| 9 | HIGH | False license metadata — *ложная лицензия* | закрыто |
| 10 | MEDIUM | Comment poisoning — *отравление комментарием* | закрыто |
| 11 | MEDIUM | Private-declaration visibility collapse | **открыто** |
| 12 | MEDIUM | Unicode identifier misclassification | **открыто** |
| 13 | MEDIUM | Phantom explicit base | **открыто** |

Ноль находок класса WORDING. Сходимости нет, второй проход не делался.

### Ошибка, которую я сделал и исправил

По совпадению времён я заключил, что в репозиторий писал Codex, и доложил это как нарушение
мандата. Владелец поправил. Проверка по журналам показала: писала параллельная сессия Claude
`3f9ceadd`. Codex не писал ничего.

Совпадение времени я принял за причину.

---

## Versendet

Ничего. Наружу не ушло.

Запрос судье лежит готовым, отправка — действие владельца.

---

## Offen — nächste Schritte

**Блокирует всё остальное по маршруту:** ответ судьи на запрос про §8 CCM. От него зависит,
писать ли спеки по восьми воротам или сворачивать маршрут в два шага.

При ответе «разложение» — следующий шаг `G2b`, теорема
`Proposition59GroundLagrangeZeroSetBridge`, схема из семи шагов дана, объекты в дереве.
При ответе «бухгалтерия» — `G2b` снимается, работать над `G1`.

Не начато:

```
трёхслойный разбор в GENEALOGY §12   черновик восьми граф готов, ждёт ответа судьи
спеки по воротам маршрута 058        ждут ответа судьи
три находки MEDIUM 11, 12, 13        ведёт параллельная сессия
второй проход ревью Codex            после её правок
таймаут Codex и старые локи          её шаг 1
comparator                           не начат
```

---

## Wichtige Fakten

**Направление моста вынужденное, а не выбранное.** Вещественность нулей неустойчива к
возмущению: у `z² + ε` при `ε < 0` два вещественных нуля, при `ε > 0` — сопряжённая пара.
Никакая точность приближения её не переносит. Сходимость устойчива, и Гурвиц читает нули
**предела**. Поэтому сходимость переносится на ground-семью, и никогда наоборот.

**Стоп-код маршрута:** `TWO_DIFFERENT_FAMILIES_USED`. Цепь «trial сходится, ground
вещественен, значит RH» использует две разные последовательности и запрещена.

**Инструмент, который нельзя проверить, нельзя и починить.** Обе правки классификатора до
появления самопроверки вносились вслепую, и обе оказались со своими ошибками.

**Правдоподобно неверный адрес хуже отсутствия адреса.** Так родился `hermfact1` и прожил
на карте несколько дней.

**Две сессии в одном дереве.** Сегодня их было две, и они дублировали шаг 1 плана друг
друга. Пересечение по `atom_describe.py` разрешилось само: параллельная сессия чинила
находки, я коммитил связное состояние. Механизма разведения нет.

**Иммунитет контура.** За два дня защита сработала на нас самих трижды: comparator
отверг похожую обёртку `SolutionR6`; строгий валидатор манифеста отверг недозаполненную
карточку `comparator-lite`; затем тот же валидатор остановился на второй подряд
недозаполненной карточке, `lean-env-dump`. Обе карточки были записаны вчера тем же
конвейером, который построил валидатор. Система кусает своих так же, как чужих. Это не
трение — это иммунитет.

**P59 name-lock.** Перед исполнением G2b зафиксирован отдельный исполнимый контракт
`CODEX_DIRECTIVE_ROUTE058_P59_G2B_2026-08-12.md`: единственный допустимый конечный
потребитель G1 — обёртка с буквальным суффиксом `_normalized`; соседняя `_simple` и
внутренние леммы не считаются закрытием CCM-wrapper.

**Исполнение плана после зелёного startup.** `Proposition59GroundLagrangeZeroSetBridge`
доказана в `Proposition59GroundLagrangeZeroSetBridge.lean`: одна строка `xi`, точный
carrier `Finset.Icc (-(N : ℤ)) N`, координата `-L*z/(2*pi)`, три раздельные ветви
removable pole / sine lattice / Cauchy-to-Lagrange и финальный буквальный вызов
`..._simple_normalized`. Direct Lean, target build и full build прошли; публичная
теорема зависит только от `propext`, `Classical.choice`, `Quot.sound`.

Параллельная M1-калибровка одной контрольной ячейки `(lambda_sq,N)=(13,120)` дала
`|overlap| = 0.99999999765405872228…`, projective defect
`4.69188254992912959392e-9` и относительное `inf_{c≠0}`-расстояние
`6.84973178301831727564e-5`; независимый 170-digit replay прошёл. Это строго
`[FINITE_CELL][CONDITIONAL]`. Matrix residual и spectral gap не измерены:
`NO_PERSISTED_MFIN_MATVEC`.

Фоновый EnvDump исключил 6 orphan `.olean`, включая конфликтующий scratch, и после
declared invocation с кодом `0` опубликовал gitignored индекс из 1139 уникальных
деклараций 154 актуальных модулей. 30 stale и 21 never-built модуль остались явно
непокрытыми. `atom_describe.py` читает elaborated-типы только из этого индекса и для
RouteB отказывает без публикации JSON вместо подмены исходным текстом.

---

## Dateien (абсолютные пути)

```
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/PROSHKA_REQUEST_ROUTE058_BEYOND_CCM_SECTION8_2026-08-12.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/OWNER_ROUTE_REASONING_2026-08-11_ground_trial_bridge.md
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_route058.py
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/cartographer/lean_bases.yaml
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/cartographer/atom_describe.py
/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/cartographer/route058_objects.json
/home/chirurgie/.claude/output-styles/ste100.md
```

Коммиты дня: `f82b09f8` · `388e559f` · `d55f7c26` · `36d7568d` · `d85af9c1` · `5b28c9f5`.

---

## Fortsetzung 2026-08-15 — Goal 058 G3 DLMF/l2

Сохранён и локально исполнен следующий Proshka verdict из Download/order
контура. Выбран Jacobi/l2 seam: независимая pole-safe DLMF 30.3.5
characteristic equation должна быть эквивалентна квадрат-суммируемости ровно
нормированной parity-boundary left row.

Теорема
`mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable`
доказана в single-import production file. Forward proof использует бесконечный
contraction-selected right limit и geometric decay; reverse proof использует
positive diagonal symmetrization и discrete-Wronskian uniqueness. Direct Lean,
named build, `q3_check` и full build прошли; axioms только `propext`,
`Classical.choice`, `Quot.sound`. Aristotle не отправлялся: bounded leaf
закрылся локально.

Это не закрывает G3. Следующая стена — независимое отождествление l2 solution
set с indexed even finite-limit/differential spectrum. G1 отдельно остаётся
открытым на actual degree-0/4 pair, CCM Lemma 7.2 и cofinal full-complement
floor. Route B остаётся `CHALLENGER / NOT_RH`; RH claim не сделан.

---

## Fortsetzung 2026-08-15 — Goal 058 G3 spectral-iff judge

После доказанного DLMF-characteristic/l2 листа Mythos предложил полный
production-domain iff с `mode4ClassicalEvenEigenvalue` и отдельный Aristotle
`GrowthDichotomy`. Локальный kill-check нашёл в этом предложении
несуществующий `mode4TailSeparationThreshold`, вакуумный binder
`carrier ≠ Λ → True`, дублирование уже доказанной l2-уникальности, отсутствие
carrier tail и неразрешённый singular endpoint.

Собран byte-verified UTF-8 Proshka request: 7,279 bytes, SHA-256
`f8b095440ae647a9d3ab56bd095bfe60f0d3829e23a035c1a77a6afc95e56419`,
commit `7e04518b`. GitHub blob/raw дали `CACHE_MISS`; Прошка остановилась
fail-closed. Тот же пакет затем был передан exact inline в той же транзакции.
`Answer now` показывалась и не нажималась.

Финальный выбор Прошки:
`B — PRODUCTION_ROOT_TO_CARRIER_ONE_DIRECTION_FIRST`. Честный следующий лист
имеет направление normalized l2 row → DLMF characteristic → literal root →
локальный negative-count jump → один фиксированный finite eigenvalue index →
`mode4ClassicalEvenEigenvalue = Λ`. Он требует `Λ < 20`, но не требует
глобального carrier-growth/tail binder.

Обратное направление `carrier j = Λ → det literalSchur(Λ) = 0` осталось
точной стеной singular endpoint. Нужен contradiction через локальную
стабильность literal negative count при `det ≠ 0`, два соседних конечных
счёта и convergence `j`-го finite eigenvalue. Mythos `GrowthDichotomy`
отвергнут как duplicate. Aristotle `NOT_READY`; сначала Codex-local assembly
одностороннего production theorem против точных текущих деклараций.

Статус: G1 OPEN; G3 OPEN; Route B `CHALLENGER_NOT_RH`; RH claim отсутствует.
Стоп-код:
`G3_ROOT_TO_FINITE_LIMIT_CARRIER_DIRECTION_READY_CARRIER_TO_LITERAL_ROOT_SINGULAR_ENDPOINT_BRIDGE_MISSING`.

### Инструментальная странность 2026-08-15 — `atoms.py --help`

`python3 docs/cartographer/atoms.py --help` не показал справку: скрипт принял
`--help` за имя выходного файла, полностью выполнил анализ и создал в корне
репозитория незакоммиченный файл `--help`. Возможные чтения были: штатный
argparse-help либо отсутствие CLI-разбора. Вывод `[записано] --help` и сам файл
подтвердили второе. Случайный файл сразу удалён; его содержимое нигде не
использовано. Для канонического запуска применяется только зарегистрированная
форма `python3 docs/cartographer/atoms.py <явный-output.json>`.

### Goal 058 G3 — finite-limit spectral iff закрыт, G3 остаётся открыт

После выбранного Прошкой одностороннего листа локально доказано и само
направление `normalized DLMF l2 row -> finite-limit carrier`, и точная обратная
стена `carrier j = Lambda < 20 -> det literalSchur(Lambda) = 0`. Обратный proof
не предполагает singularity: из `det != 0` непрерывность даёт одинаковый
negative count по обе стороны, а convergence того же `j`-го finite eigenvalue
требует counts не более `j` снизу и не менее `j+1` сверху.

Композиция даёт kernel-checked
`mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_exists_finiteLimitSpectrum`.
Оба direct Lean, named builds, `q3_check`, full build и axiom audit прошли;
public axioms только `propext`, `Classical.choice`, `Quot.sound`.

Это закрывает спектральный seam, но не G3. Следующий точный шов — строгий
порядок carrier ниже 20 и zero-based выбор `j=2` для degree four. Actual
degree-0/4 pair, finite Fourier, CCM Lemma 7.2, central-overlap/denominator
floor, coupled schedule и весь G1 остаются открыты. Route B всё ещё
`CHALLENGER / NOT_RH`; RH claim не сделан.

Стоп-код:
`G3_DLMF3035_FINITE_LIMIT_SPECTRAL_IFF_PROVED_STRICT_ORDER_AND_P2_MODE_SELECTION_NEXT`.

### Инструментальная странность 2026-08-15 — Mac axiom audit был fail-open

`./scripts/check_axioms.sh --print-axioms Q3.Main.RH_of_Weil_and_Q3` вызвал
GNU-команду `timeout`, отсутствующую на этом Mac, напечатал
`timeout: command not found` и всё равно завершился кодом 0. Возможные чтения:
сломался только необязательный лимит времени либо сам kernel-аудит вообще не
запускался. Отсутствие строки Lean `depends on axioms` подтвердило второе.
Скрипт переведён на portable fallback через `python3 subprocess.run(...,
timeout=1800)` с передачей настоящего exit-кода; GNU `timeout` сохраняется там,
где он установлен. До повторного успешного прогона прежний зелёный результат
не считается axiom evidence. Повторный реальный прогон напечатал kernel-список
для `Q3.Main.RH_of_Weil_and_Q3` (`propext`, `Classical.choice`,
`Q3.Weil_criterion`, `Q3.prime_term_le_at_t_critical_axiom`, `Quot.sound`), а
plant с заведомо отсутствующим именем завершился кодом 1. Fail-open закрыт.

### Goal 058 G3 — strict carrier order и degree-four index `2` закрыты

На полном source-backed Lean denominator (`256/256`, 2328 declarations,
stale/uncovered `0`, `sorryAx=0`, other axioms `0`) exact supplier preflight
вернул `CANDIDATE_ONLY`: Ferrers и finite-spectrum совпадения оказались
соседними объектами, а не поставщиком нужного типа.

Доказан общий singular inertia bound
`mode4HermitianNegativeEigenvalueCount_eventually_between_of_tendsto`: при
сходимости Hermitian matrices nearby negative count лежит между limiting
negative count и этим count плюс limiting nullity. Для simple carrier root
две выбранные nonsingular последовательности и convergence одного и того же
finite `j`-го eigenvalue дают exact equality `negativeCount(root)=j`.

Отсюда carrier строго упорядочен ниже `20`; значение carrier с index `2`
уникально, а normalized DLMF 30.3.5 row при этом значении square-summable.
Direct Lean, named build (7774 jobs) и `q3_check` по трём изменённым файлам
прошли; public axioms только `propext`, `Classical.choice`, `Quot.sound`.

Это не закрывает G3. Следующий seam: row-to-Ferrers/physical PSWF identity,
затем restricted finite Fourier; mode zero, actual degree-0/4 pair, CCM Lemma
7.2, denominator floor, schedule и G1 остаются отдельно открыты. Route B —
`CHALLENGER / NOT_RH`; RH claim отсутствует.

Стоп-код:
`G3_DEGREE_FOUR_DLMF_ROW_SELECTED_PHYSICAL_PSWF_IDENTITY_AND_FINITE_FOURIER_NEXT`.

### Goal 058 G3 — selected mode zero/four Ferrers and physical solutions

Связка carrier → regular solution теперь выполнена сразу для двух production
индексов. Теорема
`exists_modeZero_modeFour_selectedFerrersRegularEvenProlateSolutions`
строит существующие `Mode4FerrersRegularEvenProlateSolution` при zero-based
even indices `0` и `2` и одновременно доказывает `Lambda_0 < Lambda_2 < 20`.
Оба witness несут normalized DLMF row, exact recurrence, closed-window
continuity, interior `C2`, prolate ODE, zero-flux и уже доказанный physical
scaling. Нового source binder нет, production `ProlatePair` не менялся.

Свежий EnvDump: 256/256 current modules, 2334 declarations, stale/uncovered
`0`, proof holes/nonstandard axioms `0`; exact supplier preflight вернул
`CANDIDATE_ONLY`. Direct Lean, named build (7794 jobs), `q3_check` и
`diff --check` прошли; public axioms только `propext`, `Classical.choice`,
`Quot.sound`. Первый `q3_check` сам поймал запрещённое marker-слово внутри
нашего search-receipt docstring; формулировка исправлена, повторный check зелёный.

Это всё ещё не G3. Не доказаны exact zero counts `0/4`, restricted finite
Fourier, Fourier eigenvalue signs/order, orthogonality, CCM Lemma 7.2,
denominator floor и schedule. Следующий честный seam — endpoint Green/
intertwining для реального интерфейса interior `C2` + zero-flux; старый theorem
требует global `C2` и не может применяться через фиктивное усиление.

Стоп-код:
`G3_SELECTED_MODE_ZERO_FOUR_REGULAR_PHYSICAL_SOLUTIONS_PROVED_ENDPOINT_GREEN_FOURIER_ZERO_COUNTS_AND_LEMMA72_NEXT`.

### Goal 058 G3 — endpoint-flux Fourier eigen-transport

Старый commutation theorem требовал global `C2`, которого выбранный Ferrers
source честно не имеет в текущем интерфейсе. Новый theorem
`finiteFourierAction_preserves_prolateWaveEigenrelation_of_endpointFlux`
работает на настоящем singular domain: closed-window continuity, первая
производная внутри, divergence-form ODE для weighted derivative и два
zero-flux endpoint limits.

Доказательство — две точные FTC-формулы для `p*k'*phi` и `k*p*phi'`. В первом
boundary обнуляет `p=lambda^2-y^2`, во втором — доказанный zero flux. Tietze
extension используется только локально для существующей формулы
дифференцирования Fourier-integral и исчезает по equality on `Icc`.

Fresh EnvDump видел `257/257` modules и `2335` declarations, holes/extra
axioms `0`; supplier preflight вернул `CANDIDATE_ONLY`. Direct Lean, named
build (7745 jobs), `q3_check` и diff check прошли; axioms standard only.

Это ещё не Fourier eigenfunction relation: сохранён только ODE eigenspace.
Нужны physical Ferrers wrapper, proportionality/uniqueness, scalar sign/order,
zero counts и Lemma 7.2. G1/G3 OPEN, Route B `CHALLENGER / NOT_RH`.

Стоп-код:
`G3_ENDPOINT_FLUX_FOURIER_EIGEN_TRANSPORT_PROVED_SELECTED_FERRERS_PHYSICAL_WRAPPER_AND_SCALAR_PROPORTIONALITY_NEXT`.

### Goal 058 G3 — physical Ferrers Fourier ODE transport

Generic endpoint theorem теперь применён к настоящему physical Ferrers
source. Новый module комплексирует physical series, переносит closed-window
continuity, actual first derivative, divergence-form ODE и оба zero-flux
limits через `u/sqrt(mProject)`, затем получает тот же prolate ODE для
finite-Fourier image при `lambda=sqrt(mProject)` и
`theta=Lambda+mode4JacobiG mProject`.

Public theorem принимает только witness `S` и `2 <= mProject`; Fourier
eigenrelation, `chi`, zero count, global `C2` и новый source binder на входе
отсутствуют. Fresh EnvDump: `257/257`, 2336 declarations, holes/extra axioms
`0`; exact query `CANDIDATE_ONLY`. Direct Lean, named build (7775 jobs),
`q3_check` и axiom audit прошли.

Это всё ещё не `Fh=chi*h`: доказано только пребывание Fourier image в том же
ODE eigenspace. Следующий seam — regular-even uniqueness/proportionality и,
вероятно, точная nodal/index identification. Scalar sign/order, zero counts,
ProlatePair, Lemma 7.2, floor, schedule, G1/G3 открыты.

Стоп-код:
`G3_SELECTED_PHYSICAL_FERRERS_FOURIER_ODE_TRANSPORT_PROVED_SCALAR_PROPORTIONALITY_AND_NODAL_SELECTION_NEXT`.

### Goal 058 G3 — physical Ferrers Fourier scalar proportionality

Шов `same prolate ODE eigenspace -> Fh=chi*h` закрыт kernel-checked. Новый
generic receiver доказывает uniqueness двух complex divergence-form решений
по center value и first derivative. Для physical Ferrers source обе center
derivatives равны нулю по evenness, source center ненулевой, поэтому
`chi := Fh(0)/h(0)` и uniqueness дают exact equality сначала на open window,
затем по continuity на closed physical window.

Новая public theorem принимает только accepted witness `S` и
`2 <= mProject`; Fourier scalar/relation, zero count, global smoothness и новый
source binder отсутствуют. Nodal count для proportionality не понадобился.

Fresh EnvDump: `258/258` current modules, `2345` declarations, stale/uncovered
`0`, holes/extra axioms `0`; шесть source-less orphan oleans исключены.
Exact supplier query вернул `CANDIDATE_ONLY`. Direct Lean, named build
(`7779` jobs), `q3_check`, diff/forbidden scan и axiom audit прошли.

Граница: `chi` пока complex. Его real/nonzero/positive/order свойства,
orthogonality, production `ProlatePair`, Lemma 7.2, denominator floor,
schedule, G1/G3 остаются открыты. Route B — `CHALLENGER / NOT_RH`.

Стоп-код:
`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_PROPORTIONALITY_PROVED_SCALAR_REAL_NONZERO_SIGN_ORDER_AND_PROLATEPAIR_NEXT`.

### Goal 058 G3 — physical Ferrers Fourier scalar is real

Complex proportionality scalar усилен до `chi : Real` без нового source
binder. В центре positive-phase kernel буквально равен единице, physical
Ferrers source real-valued, а его center value ненулевой. Поэтому imaginary
part center relation даёт `chi.im=0`.

Exact fresh KB query вернул `no hits`. Direct Lean, named build (7780 jobs),
`q3_check`, diff/forbidden scan и axiom audit прошли; axioms standard only.

Граница: ненулевость, знак и mode-0/mode-4 order ещё не доказаны. Production
`ProlatePair`, Lemma 7.2, floor, schedule, G1/G3 открыты; Route B остаётся
`CHALLENGER / NOT_RH`.

Стоп-код:
`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_REAL_SCALAR_PROVED_NONZERO_SIGN_ORDER_AND_PROLATEPAIR_NEXT`.

### Goal 058 G3 — physical Ferrers Fourier scalar is nonzero

Real scalar усилен до `chi != 0` без source assumption. Материализован entire
complex-frequency extension compact-window Fourier integral и exact real-axis
bridge. Ноль на open source window по analytic identity theorem дал бы ноль
всюду, что противоречит уже существующей Fourier-inversion nonvanishing lemma
для source с nonzero center.

Declared full EnvDump перед write: `260/260` current modules, `2354`
declarations, stale/uncovered `0`, holes/extra dependencies `0`, шесть orphan
oleans исключены. Exact supplier preflight: `CANDIDATE_ONLY`. Direct Lean,
named build (7782 jobs), `q3_check`, diff/forbidden scan и axiom audit прошли.

Граница: знак и mode-0/mode-4 order не следуют из injectivity и остаются
source-locked spectral seam. `ProlatePair`, orthogonality, Lemma 7.2, floor,
schedule, G1/G3 открыты; Route B `CHALLENGER / NOT_RH`.

Стоп-код:
`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_REAL_NONZERO_SCALAR_PROVED_SIGN_ORDER_AND_PROLATEPAIR_NEXT`.

### Goal 058 G3 — normalized Ferrers production ProlatePair

Selected Ferrers witnesses теперь канонически продолжены нулём на всю real
line и честно нормированы в `L2`. Положительность mass доказана из
closed-window continuity и nonzero center; whole-line integral вычислен
точной заменой масштаба и равен положительной нормированной величине из
positive coefficient zero. Restricted Fourier relation и real nonzero scalar
перенесены через normalization.

Второй новый module собирает неизменённый production `D0Pstar.ProlatePair` из
точных selected even indices `0` и `2`. В record уже есть actual normalized
zero-extended Ferrers functions, positive `I0/I4`, nonzero real `chi0/chi2`,
unit norms, support и две exact restricted Fourier relations. Новой family или
source assumption нет.

Direct Lean для двух файлов, named builds (`7783`, `7807` jobs), оба
`q3_check`, diff check и standard-only axiom audit прошли.

Граница теперь точная: production pair существует, но
`IsActualProlateModePair` ещё не доказан. Остались exact zero counts `0/4`,
orthogonality и source positive-phase order `0 < chi2 < chi0`. Затем идут CCM
Lemma 7.2, floor, schedule; G1 отдельно открыт. Route B —
`CHALLENGER / NOT_RH`.

Стоп-код:
`G3_PRODUCTION_PROLATEPAIR_CONSTRUCTED_ACTUAL_MODE_ZERO_COUNTS_ORTHOGONALITY_AND_FOURIER_SIGN_ORDER_MISSING`.
