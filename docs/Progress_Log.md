# Судовой журнал Q3 — развилки, а не события

**Зачем.** Событий у нас пишется много: `INSIGHTS.md` — 51 763 строки, 30 closeout,
49 report, 69 goal, 75 answer. Не пишется другое — **почему свернули**. Из-за этого
летом 2026 потерялось видение проекта, и восстанавливать пришлось агентами по
косвенным следам: `git log`, даты, чужие цитаты.

Журнал ≠ лог. Лог — поток событий, чтобы ничего не потерять. **Журнал — записи
для того, кто вернётся.** Судовой журнал против чёрного ящика: в журнале «взяли
курс на север, потому что шторм с запада»; в ящике — все показания посекундно.

**Правило записи: в момент выбора, не постфактум.** Свернул с пути — одна запись
сразу. Через неделю причина уже не восстановима, проверено.

---

## Формат записи

```
## YYYY-MM-DD — короткое имя развилки

**Развилка:** что выбирали, между чем и чем
**Выбрали:** что именно
**Почему:** причина в одну-две фразы, проверяемая
**Что отвергли и почему:** вторая ветка и её цена
**Техника:** приём/инструмент, который сработал или подвёл
**Следующий ход:** минимальный шаг после этой записи
**Адреса:** file:line, коммит, вердикт — что можно открыть и проверить
**Чей вердикт и аргумент:** только для решений извне — кто решил и ПОЧЕМУ, дословно
```

Восьмая графа обязательна для внешних вердиктов. Все 4 потерянные причины из 48
найденных — это решения, записанные одной буквой («CHOSEN: A») без аргумента.
Если аргумент не прислали — писать `аргумент не предоставлен` явно.

Полные правила записи: `docs/RECORDING_RULES.md`

Заполнять все семь граф. Пустая графа «почему отвергли» — главный источник
будущей археологии.

---

## 2026-09-01 — adaptive explicit-tail reuse убит, выбран exact Schur margin

**Развилка:** продолжать adaptive tail через более поздний cutoff, вернуться к
direct selected-`N` floor, искать новую оценку до существующего cutoff или
перейти к независимому finite-head corrected Schur margin.

**Выбрали:** закрыть только
`ADAPTIVE_REUSE_OF_EXISTING_EXPLICIT_EVEN_TAIL_VIA_C_LE_R_LE_N` и следующим
узлом взять
`FINITE_EVEN_HEAD_CORRECTED_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT`.

**Почему:** Lean доказал, что на каждой selected-клетке `N_k < C_k`; поэтому
никакой `R_k` не может одновременно наследовать существующую explicit estimate
через `C_k <= R_k` и лежать внутри carrier через `R_k <= N_k`. Schur margin
остаётся load-bearing при любом живом tail supplier и уже имеет literal finite
consumer.

**Что отвергли и почему:** немедленный adaptive wrapper отвергнут как перенос
той же недостающей source estimate под новое имя. Direct selected-`N` floor и
новая earlier estimate при `R_k < C_k` не убиты, но остаются research debt без
exact supplier. Pure `toBlocks22` identity остаётся открытым algebraic debt.

**Техника:** `BOUNDARY_CASE`, универсальный natural-order contradiction,
Control-v9 semantic quarantine, независимая byte-exact receipt reconstruction
и detached OpenSSH signature.

**Следующий ход:** зафиксировать exact corrected-head Schur consumer и его
weakest sufficient theorem shape, затем запустить самый дешёвый plant или
kernel-checkable reduction до построения нового tail supplier.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSelectedFerrersAdaptiveTailCutoffObstruction.lean`;
`docs/routeB_bus/CODEX_CLOSEOUT_GOAL058_SELECTED_ADAPTIVE_TAIL_CUTOFF_OBSTRUCTION_2026-09-01.md`;
admission `043440e0`.

**Чей вердикт и аргумент:** Codex + независимый Codex subagent. Аргумент:
`C_k <= R_k <= N_k` противоречит уже admitted `N_k < C_k` для каждого `k`;
это убивает только reuse текущей explicit theorem, но не earlier estimate,
direct selected-`N` floor или abstract block identity.

## 2026-09-01 — direct selected-N cancellation убит, выбран adaptive block crosswalk

**Развилка:** выводить exact selected-`N` floor автоматически из
reflection-even row orthogonality, строить ещё один conditional wrapper,
дробить direct floor через отдельный Rayleigh envelope или перейти к adaptive
tail с явным block crosswalk.

**Выбрали:** закрыть только automatic-cancellation shortcut и следующим
узлом взять `ADAPTIVE_SELECTED_FINITE_TAIL_TO_LITERAL_TOBLOCKS22_CROSSWALK`,
где `ADAPTIVE_SELECTED_CUTOFF_DOMINATION_R_LE_N` остаётся количественным
гейтом.

**Почему:** exact reduction не использует row orthogonality в алгебре: она
передаётся обратно в уже предполагаемый floor. Adaptive high target может
включить exact Rayleigh shift и beta по построению, тогда как отдельный
Rayleigh envelope всё равно не даёт selected-`N` unshifted lower bound.

**Что отвергли и почему:** wrapper `hDirect -> heven` отвергнут как
тавтологический; ортогональность не превращает `Arch - Prime` или scalar
identity shift в row projector. Сам direct source-specific floor не убит и
остаётся alternate research debt. Rayleigh-envelope branch не убит, но
отложен как недостаточный без второй количественной оценки.

**Техника:** complete-shelf supplier preflight, буквальное разворачивание
`ArchPrime = -WR - Prime`, exact consumer trace и независимый semantic review.

**Следующий ход:** определить weakest adaptive cutoff/block interface,
проверить exact `toBlocks₂₂` identity и первым killer-тестом решить, возможно
ли eventual `R_k <= N_k` на selected schedule.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEvenSectorArchPrimeReduction.lean`;
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarArchPrimeSesquilinearForm.lean`;
`docs/routeB_bus/CODEX_CLOSEOUT_GOAL058_DIRECT_SELECTED_N_CANCELLATION_PREFLIGHT_2026-09-01.md`.

**Чей вердикт и аргумент:** Codex + независимый Codex subagent. Аргумент:
`horth` не участвует в algebraic reduction, selected Rayleigh scalar не
является доказанным eigenvalue, а доступная high-tail coercivity начинается
за пределом literal selected carrier.

## 2026-09-01 — фиксированный cutoff убит, выбран direct selected-N

**Развилка:** переносить готовую explicit even-tail coercivity через
фиксированный `sourceWeilEvenTailCutoff <= N`, строить adaptive cutoff или
атаковать форму прямо на literal selected-`N` carrier.

**Выбрали:** закрыть fixed transfer как математически мёртвый и следующим
узлом взять `DIRECT_SELECTED_N_EVEN_TAIL_COERCIVITY`.

**Почему:** Lean доказал строгую противоположность требуемой посылке на каждой
selected-клетке: `N < cutoff`. Direct selected-`N` — слабейший интерфейс,
который уже совпадает с carrier потребителя и не добавляет отдельный долг
`R_k <= N_k`.

**Что отвергли и почему:** фиксированный transfer отвергнут доказанным
контрнеравенством. Adaptive cutoff не убит, но отложен: он добавляет новый
объект и domination/crosswalk до того, как доказана необходимость этой цены.

**Техника:** `BOUNDARY_CASE` плюс central-mode operator-norm lower bound;
точная selected schedule `m=N=k+2`; независимая semantic attestation.

**Следующий ход:** complete-shelf supplier preflight для weakest direct
selected-`N` coercivity, затем один source-faithful decisive test.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSelectedFerrersEvenTailCutoffObstruction.lean`;
`docs/routeB_bus/CODEX_CLOSEOUT_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_2026-09-01.md`;
admission `2db4c33d`.

**Чей вердикт и аргумент:** Codex + независимый Codex subagent. Аргумент:
квантор универсальный, направление строгое `N < cutoff`, поэтому закрывается
только fixed-premise transfer; adaptive и direct finite-carrier методы не
затронуты.

## 2026-08-28 — консолидация вперёд R1: сперва закрепить, потом идти

**Развилка:** после того как вердикт `8aff714d` поставил
`OWNER_REPRESENTATION_RERANK` и запретил всё до выбора владельца, выбирали
между тремя представлениями фронта G6: (1) купить теорему сохранения цели
для относительного спектрального сдвига; (2) вернуться к R2, движущемуся
Крылову с Фешбахом, под отдельным грантом; (3) остановить фронт и
консолидировать закреплённое.

**Выбрали:** третье и первое вместе, но в порядке. Консолидация (3)
делегирована Codex заданием
`docs/Codex/TASK_2026-08-28_goal058_consolidation.md`; фронт Linux-тела идёт
по (1). Порядок владельца дословно: «сначала сделать консолидацию, а потом
идти по маршруту R1».

**Почему:** ночь 27–28.08 дала много закреплённого, и часть живёт **только в
markdown-отчёте** — тождество Вольтерра–Дюамеля, ориентированный один
функционал, замкнутая форма нормы полюсной строки. Отчёт не компилируется, а
численное подтверждение у нас `DIAGNOSTIC_NEVER_A_PROOF`. Пока эти вещи не в
ядре, они держатся на одной выкладке. Плюс два каната
(`SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR`,
`SELECTED_FERRERS_ODD_SECTOR_FLOOR`) открыты неделями и держат три чужих
шага. Вариант (1) выбран головным для нашего тела потому, что он **быстрее
всех отвечает** — часы против ночей — и отрицательный ответ закрывает объект
сразу, а не после ещё одного прохода.

**Что отвергли и почему:** (2) R2 — не отвергнут, отложен. Он не переходник,
а машина: строить, проверять, обвешивать леммами, то есть ночи и отдельный
грант. Брать его параллельно с (1) значит ставить две дорогие ставки, не
получив дешёвого ответа ни от одной. Возвращаться к нему осмысленно после
того, как (1) скажет «да» или «нет».

**Техника:** VOI-гейт применён к самому выбору. Зонд — вариант (1), он
дешевле всех различает. Ветки названы: ЕСЛИ_A (теорема есть) — относительный
объект наследует бесплатную глобальную оценку счёта, локальная всё ещё
требует крейновского гейта отрицательных квадратов; ЕСЛИ_B (теоремы нет) —
R1 закрыт окончательно, и R2 выбирается начисто.

**Следующий ход:** передать задание Codex; Linux-телом искать теорему
сохранения цели по порядку «математика → наши базы (`./ask.sh`) → внешний
поиск → сборка запроса Прошке».

**Адреса:**
`docs/Codex/TASK_2026-08-28_goal058_consolidation.md`;
`docs/routeB_bus/LINUX_CONTROL_STATE_NOTE_OWNER_RERANK_GOAL058_2026-08-28.md`;
вердикт `8aff714d`; ночные отчёты `docs/routeB_bus/LINUX_*_2026-08-28.md`.

**Чей вердикт и аргумент:** решение владельца, 28.08.2026, в чате.
Аргумент дословно: «сначала сделать консолидацию, а потом идти по маршруту
r один». Предшествующий внешний вердикт — Прошка `8aff714d`: математика
параллельного вердикта `ccbfdf4c` забанкована, исполнительская авторизация
отменена, `NEW_TRANSACTION_AUTHORIZED: false`, выбор представления
принадлежит владельцу. Выбор владельца этот блок снимает.

---

## 2026-08-23 — вся алгебраическая цепь F72 закрыта за ночь; paper-входы типизированы

**Развилка:** формализовать ли бумажные асимптотики (Satz 9, Fuchs Th.1) или
оставить их явными типизированными входами и закрыть кернелом всё остальное.
**Выбрали:** второе — судья запретил и axiom, и передоказательство книги;
каждый бумажный вход стал точно типизированной гипотезой об ИМЕННО ТОМ объекте,
который потребляет бинд (никакой подмены свидетеля).
**Почему:** «a citation does not produce a Lean proof term»; при этом
оставшийся paper-вход имеет один точный тип и уже не может быть ослаблен
(не Satz 8 L2, не сырой O(γ^{-3/4}), не другой свидетель).
**Что отвергли и почему:** project axiom — запрещён категорически;
интегрирование sup-ошибки по окну — теряет степень λ (O(λ^{-1}) вместо
O(λ^{-2})); square-only Fuchs-порт — не различает χ и −χ (плант).
**Техника:** цепочка за одну ночь, семь этажей, каждый отдельно допущен:
physical lift (b1e3f177) → selected transport (d624c2e4) → F72.1A0
rate-transfer с денominator-guard-плантом (b6e46975) → F72.1C композиция с
ProjectModeData×2 и границами D0≤1/D4≤91 (ed3a4a12) → F72.3B Fuchs-кроссвок
μ=√(2π)χ сокращением центра + positive branch (193e21c6) → F72.4
center-integral rate из frequency-zero-тождеств (d4c6fafc) → F72.5 zero-mass
пакет с отрицательным Lemma72-scale (61343c78) → F72.6 однократный factor 4
(ffb615b3). Четыре предсказанных судьёй класса сбоя не выстрелили; три файла
прошли с первого прогона.
**Следующий ход:** после аппробации F72.6 — L73_3_SELECTED_FERRERS_ESTAR_
WINDOW_MAIN_ERROR; по вердикту `L73_2_ALGEBRAIC_ASSEMBLY_CLOSED_AFTER_F72_6:
true`, непокрытым остаётся unconditional paper supply.
**Адреса:** вердикты `de86b9bc`→`f9623d8b` в docs/routeB_bus/proshka/;
восемь source records в docs/routeB_bus/.
**Чей вердикт и аргумент:** Прошка, серия REQ-V follow-up: «the raw rate is
an explicit hypothesis about the same source family used by the uniqueness
bind; no rate is generated from a renamed project function».

## 2026-08-22 — ordering front закрыт целиком; physical lift открыт следующим

**Развилка:** после V3.2 куда бить дальше — сразу в F72.1C (композиция bind +
rate) или сперва закрыть недостающий source-объект.
**Выбрали:** судья вскрыл, что F72.1C — композиция ДВУХ поставок
(source/project bind + F72.1A rate), а bind ещё не имеет физического
source-объекта; сначала `REGULAR_EVEN_SPHEROIDAL_TO_SATZ9_SOURCE_DATA_
PHYSICAL_LIFT` — единственно source-only шаг.
**Почему:** «Starting F72.1C now would either accept the rate as a new
hypothesis or build another receiver, neither of which closes more than it
opens» — прямое применение правила W9 судьёй.
**Что отвергли и почему:** принять Satz9-rate как гипотезу — превращает
доказанное в допущение; строить ещё один типизированный receiver вместо
инстанцирования — плодит входы, не закрывает.
**Техника:** физический лифт — чистое масштабирование x↦x/λ применённое к
`spheroidal_normalized_witness`; ключевая проверка — сдвиг θ=Λ+γ² (не Λ)
следует из точного алгебраического тождества `γ²·(x/λ)² = (2πλx)²`, не из
подгонки константы.
**Следующий ход:** физический лифт исполнен (`b1e3f177`), на аппробации;
после неё — `SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT`, затем F72.1A rate,
затем F72.1C композиция.
**Адреса:** вердикт `5cb885c2`
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_22_V_V3_2_...md`);
`G6N1SpheroidalSourcePhysicalLift.lean`.
**Чей вердикт и аргумент:** Прошка: «F72_1C_IS_COMPOSITION_AFTER_SOURCE_BIND_
AND_F72_1A_RATE_NOT_A_REPLACEMENT_FOR_THEM».

## 2026-08-22 — U2.1 снят сдвигом представления; проектная ветвь — классический носитель

**Развилка:** чем обитать projectBranch модульного потребителя и как закрывать
hsrcCut — источником (`P.evenBranch`), численно, или независимым проектным
объектом.
**Выбрали:** `mode4ClassicalEvenEigenvalue` (предел конечных спектров, уже в
ядре) как единственный законный носитель; hsrcCut выводится cutoff-локальным
замком порядка, не оценкой; U2.1 (литеральное DLMF-семейство в Lean) снят с
критического пути.
**Почему:** маршруту нужны только три вещи — ветвь⇒уравнение (U2.3),
уравнение⇒ветвь (U2.4), порядок отождествляет ранги; именованное семейство
λ_{2r}⁰ нигде не несёт нагрузку.
**Что отвергли и почему:** `projectBranch := P.evenBranch` — C10-тавтология
(перечисление согласуется само с собой, независимый носитель стёрт); численный
hsrcCut как посылка — K7 finite-to-universal; глобальный StrictMono — переплата.
**Техника:** индуктивное доказательство судьи: из равенства низких range,
строгости источника и локальной строгости носителя следует и почленное
равенство, и сам срез источника — hsrcCut оказывается ВЫХОДОМ замка, не входом.
**Следующий ход:** V3.0 исполнен (`8dfd0b0d`, с первого прогона, P_V_NEXT_1
подтверждено); ждём семантической аппробации, затем V3.1 cutoff-local lock,
затем V3.2 — закрывает W13.7 selected theta.
**Адреса:** вердикт `a132138c`
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_22_V_...md`);
`G6N1FiniteLimitCharacteristicRange.lean`.
**Чей вердикт и аргумент:** Прошка, REQ-V: «source and project enumerations
meet through one exact low solution set, never by aliasing branches»; U2.1 —
`ELIMINATED_FROM_CRITICAL_PATH by a representation shift, not silently
relabeled PROVED».

## 2026-08-22 — forward-преflight: печатная дробь и limUnder оказались одной конвенцией

**Развилка:** как получить U2.3 (ветка ⇒ характеристическое уравнение) — портировать
доказательство книги через степенные ряды (§3.24, требует Frobenius-аналитичности,
которой нет в Mathlib) или доказать нативно в базисе Лежандра.
**Выбрали:** нативное доказательство в базисе Лежандра: коэффициенты собственной
функции через интеграл по частям (Lagrange identity + `legendre_even_expansion`,
оба уже в ядре) удовлетворяют рекурсии 30.3.7; затем Pincherle-единственность
через исчезающий вронскиан (детерминант δ_q → 0 против убывающего хвостового
решения), без трихотомии роста §1.8 Satz 3.
**Почему:** рекурсия 30.3.7 — это в точности рекурсия коэффициентов Лежандра, а
harvest уже строит всё в этом базисе; аналитическая стена (целость решения,
условие (9) книги) обходится полностью — граничное условие несёт поток, а не ряд.
**Что отвергли и почему:** порт степенного пути §3.24 — требует «ограниченное
решение ⇒ целая функция» (Frobenius у регулярной особой точки), многомесячная
стена; инвертировать обратный кроссволк — запрещено вердиктом (циркулярность).
**Техника:** зарегистрированное судьёй препятствие (печатная дробь vs `limUnder`
у полюсов) растворилось при чтении первоисточника: §1.8 (стр. 92) сам определяет
бесконечную дробь как предел terminal-zero-континуантов — конвенция проекта
буквально; полюса книга сама закрывает оговоркой «bzw. der invertierten
Gleichungen» — это и есть pole-safe кросс-умноженная пара.
**Следующий ход:** транзакция forward-модуля `G6N1SpheroidalCrosswalkForward`
по плану §6 карточки; первым перепроверить нижнюю границу произведения
`Π(Lower/Upper)` (единственная новая оценка).
**Адреса:**
`docs/routeB_bus/litreview/DLMF_3035_FORWARD_MEMBERSHIP_PROJECT_CROSSWALK_2026-08-22.md`;
книга PDF 101–104 (§1.8), 250–252 (§3.24); вердикт `68e9cd78`.
**Чей вердикт и аргумент:** прогон — по CODEX DIRECTIVE вердикта `68e9cd78`
(Прошка): «No Lean source transaction is authorized until this preflight returns
SUCCESS»; преflight вернул `DLMF3035_FORWARD_SOURCE_AND_PROJECT_OBJECT_LOCKED`.
 ## 2026-08-17 — четыре транспорта без входа: узор есть, но он не однородный

**Развилка:** принять наблюдение «четыре раза подряд транспорт написан, а вход в него
никто не поставляет — значит это устройство системы, а не совпадение» — или сперва
сверить все четыре случая по диску.

**Выбрали:** сверить. Узор подтвердился, но **не в той форме**, в какой был заявлен:
четвёртым случаем он не является, а третий устроен иначе, чем первые два.

**Что на диске, с адресами.**

```
1  транспорт  RHRoute.hfam_even_of_spectralData
              H2aPenaltyCoercivity.lean:440
   вход       SpectralData
   поставщик  НЕТ — тот же файл, :446, дословно:
              "SpectralData do not exist anywhere under Q3/"

2  транспорт  sourceCCMComplexRow_even_of_phaseRealification_even
              CCMProposition59SourceTrialFeshbachPreflight.lean:128
   вход       hqEven — точная чётность строки
   поставщик  НЕТ — докстринг там же:
              "the necessary source theorem that the current
               D0Pstar contract does not export"

3  транспорт  parity_dichotomy_of_simple_eigenspace
              SimpleEvenGroundSectorCriterion.lean:95
   вход       hsimple
   поставщик  ЕСТЬ — simplicity_clause, H2aPenaltyCoercivity.lean:255,
              доказан, из PSD-сертификата
   но         другой язык: пучок (K,G) над ℂ против одного
              оператора над ℝ; нужен переход G = I и ℂ→ℝ

4  прибор     sourceCCMComplexOddMass, D0PstarSourceCCMOddMassReflectionDefect.lean
   есть       точное тождество :112, неотрицательность :127,
              две оценки сверху :138 и :205
   нет        критерия oddMass = 0 ↔ чётность строки
```

**Почему четвёртый случай в узор не входит.** Первые три — «транспорт с недостающим
входом». Четвёртый — не транспорт вовсе, а измеритель без калибровки нуля. Разные
дефекты: там нечего подать на вход, здесь нечего прочитать со шкалы. Объединять их в
один счёт значит завышать частоту узора.

**Почему третий случай слабее первых двух.** Заявлено было «поставщик под запретом
импорта». Проверено: `FORBIDDEN_IMPORTS` встречается только в `aristotle_input/*.md` —
это спецификации отдельных заданий Aristotle с полем `OWNED_FILE` и ровно одним
`ALLOWED_IMPORTS`, то есть песочница на одну задачу. Глобальной политики нет, и сам
движок **уже импортируется** тремя рабочими файлами:
`CCMProposition59ComplexTrialComplementSpectral.lean:5`,
`CCMProposition59ComplexTrialComplementRayleigh.lean:2`,
`HermitianUnitMinimumEigenpair.lean:1`. Препятствие не административное, а
техническое: несовпадение языков.

**Что отвергли и почему:** формулировку «четыре раза одна болезнь». Она читается как
диагноз системе, а по факту случаев три, из них один — стыковка, а не отсутствие. Счёт
дефектов, завышенный на четверть, обесценивает и верную часть наблюдения.

**Что уцелело и стоит держать.** Асимметрия реальна: абстрактный движок «для любых
`G, K, J, q`» пишется один раз и красиво, а предъявление конкретных матриц с
сертификатом — грязная работа под конкретный случай, и её откладывают. Верхние этажи
строятся быстрее нижних. Два подтверждённых случая (`1` и `2`) — прямое свидетельство.

**Техника:** сверять узор поимённо, прежде чем называть его устройством. Три команды по
диску: `grep -n` на каждое имя, `grep -rn "^import"` на предполагаемый запрет,
`grep -rn` на форму критерия. Заняло минуту, сняло один ложный случай и переклассифицировало
второй.

**Следующий ход:** закрыть случай `4` — написать `oddMass = 0 ↔ чётность строки`. Дёшево,
проверяется сборкой, и превращает уже написанный прибор в пригодный. Случай `3` —
прикинуть переход `G = I`, `ℂ→ℝ`. Случаи `1` и `2` требуют источника и остаются
открытыми.

**Адреса:** все перечислены в блоке выше, каждый сверен `grep -n` на 17.08.

**Чей вердикт и аргумент:** наблюдение об узоре пришло извне, в пересказе владельца;
проверка и переклассификация наши, по диску.

---

## 2026-08-17 — право расщеплять по чётности само стоит на недоказанной простоте

**Развилка:** принять расщепление `β = min(чётная, нечётная)` как рабочую рамку и
считать два сектора порознь — или сперва спросить, чем обеспечено само право так
делить. Вопрос владельца в лоб: а если состояние сидит *и так, и так одновременно*,
то есть смесью обоих секторов?

**Выбрали:** спросить. Смесь оказалась не экзотикой, а точной границей применимости
всей секторной рамки.

**Почему:** смесь чётного и нечётного — это вектор без определённой чётности, и такой
вектор выживает как основное состояние **ровно при вырождении**. Проверено счётом на
двух связанных ячейках `K = [[0,t],[t,0]]`, смесь `0.7·(1,1) + 0.3·(1,−1) = (1, 0.4)`:

```
   связь t | смесь — собственный вектор? | что это значит
   --------|-----------------------------|---------------------------
     +1.0  |            нет              | чистая чётность вынуждена
     +0.5  |            нет              | чистая чётность вынуждена
      0.0  |            ДА               | вырождение, чётности нет
     −0.5  |            нет              | чистая чётность вынуждена
```

При `t = 0` обе конфигурации имеют одну энергию, поэтому любая их смесь — тоже
основное состояние, и говорить о его чётности бессмысленно. При `t ≠ 0` энергии
различны, смесь не выживает, состояние обязано выбрать сектор.

**Следствие, ради которого запись и делается.** Запрет на смесь — это ровно `hsimple`,
и в контракте G1 он стоит как `LOCAL_HYPOTHESIS finrank (eigenspace M ε) = 1`, то есть
связанная переменная потребителя, **не теорема**. Теорема
`parity_dichotomy_of_simple_eigenspace` устроена честно: берёт простоту на вход и лишь
тогда выдаёт «чисто чётное или чисто нечётное». Убери вход — вывода нет.

> **ПОПРАВКА 2026-08-17, вечер. Вывод ниже был ошибочным и отозван.**
>
> Первоначально здесь стояло: «секторное расщепление `β = min(β⁺, β⁻)` — следствие
> недоказанной простоты». Прошка это опроверг в
> `docs/routeB_bus/proshka/PROSHKA_COFINAL_CCM_EVEN_COMPLEMENT_FLOOR_AT_FIXED_SHIFT_2026-08-17.md`
> (коммит `4aff4062`, поле `LATE_PARENT_CLAIM_THAT_MIN_SPLIT_REQUIRES_HSIMPLE:
> rejected_for_form_floor`), и он прав.
>
> Смешаны два разных утверждения:
>
> ```
> расщепление ФОРМЫ  β = min(β⁺, β⁻)      нужна чётность строки, hsimple НЕ нужен
> чётность ОДНОГО вектора ξ               hsimple нужен
> ```
>
> Разложение `q⊥ = (чётное ∩ q⊥) ⊕ нечётное` — чистая линейная алгебра: достаточно,
> чтобы оператор коммутировал с отражением, а `q⊥` был инвариантен относительно него.
> Второе обеспечивается чётностью строки. Простота тут не участвует вовсе.
>
> Счёт со смесью выше верен и остаётся — но он про **вторую** строку таблицы, а вывод
> я записал про **первую**. Подмена предмета. Механизм ошибки: посчитал одно,
> обобщил на соседнее, потому что оба про чётность.
>
> Что уцелело: `hsimple` действительно недоказан и действительно нужен — но для того,
> чтобы у выбранного основного состояния была определённая чётность, а не для права
> раскладывать дно на два сектора.

**Что отвергли и почему:** трактовку «смесь — вырожденный случай, им можно пренебречь».
Пренебречь можно тем, что запрещено доказанной теоремой; здесь запрет держится на
гипотезе того же пакета, который мы и пытаемся обеспечить. Это круг, если не выписать
его явно.

**Техника:** пять строк арифметики вместо чтения теории. Вопрос «а может ли вообще быть
так» проверяется прямым счётом за минуту, и счёт сразу дал точную границу — `t = 0`, —
а не расплывчатое «при некоторых условиях».

**Следующий ход:** вскрыть, что нужно `hsimple`, чтобы стать теоремой. Наработки от
11.08 уже сводят его к счёту ранга `rank(M − εI) = 2N`
(`docs/cartographer/probes/Probe_Inertia_SimpleAsCount.lean`) и расщепляют чётностью на
два условия размерности `N` (`docs/cartographer/probes/Probe_Parity_KernelSplit.lean`);
ни одно из двух не доказано. Сообщить Прошке, что его `β = min(β⁺, β⁻)` наследует эту
зависимость.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/SimpleEvenGroundSectorCriterion.lean:93`
(`parity_dichotomy_of_simple_eigenspace`, docstring прямо предупреждает
`this theorem does not choose the plus sign`) ·
контракты `docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md:88`, секция G1, строка `hsimple` ·
`docs/cartographer/probes/Probe_Inertia_SimpleAsCount.lean` ·
`docs/cartographer/probes/Probe_Parity_KernelSplit.lean`

**Побочная находка.** Запись контрактов от 11.08 (`ROUTE058_GATE_CONTRACTS.md:109`)
ссылается на те же пробы укороченным путём `probes/…`, которого от корня репозитория
не существует. Ошибка безобидная по смыслу и дорогая по времени: проверяющий получает
«файла нет» и решает, что наработки утеряны. Исправлено здесь; в контрактах путь
оставлен как есть, чтобы не смешивать правку адреса с содержательной записью.

**Чей вердикт и аргумент:** ничей внешний — вопрос владельца, проверка наша, счётом.

---

## 2026-08-17 — дно дополнения расколото по чётности; пустая чётная нога прочитана

**Развилка:** как читать тот факт, что дно `q⊥` раскалывается на `min(чётная, нечётная)`,
причём нечётная нога обвешана четырнадцатью файлами, а чётная не имеет ни поставщика,
ни приёмника. Владелец прочёл это как хороший знак: вся суть сосредоточена в нечётной
ноге. Второе прочтение: нечётная нога — наследство прежнего фронта, а чётная просто не
бралась.

**Выбрали:** второе прочтение.

**Почему:** счёт файлов по имени даёт `odd: 14`, `even: 12` — чётность разрабатывалась
почти столько же, но **в другом гейте**: все чётные файлы сидят на trial-стороне
(Ferrers, DLMF, Лежандр), ни один не про дно. Нечётная линия пришла из `GOAL057`, из
формы Вейля, где нечётный сектор был естественным входом. То есть 14:0 по дну — след
маршрута, а не мера важности. Плюс структурный довод: пробный вектор `q` чётный,
поэтому весь нечётный сектор ортогонален ему **автоматически**, и там остаётся только
оценить энергию; чётный сектор — то самое место, где живёт `q` и где сидел бы
конкурирующий собственный вектор. Нечётная нога заросла потому, что она дешевле.

**Что отвергли и почему:** прочтение «пусто ⇒ там нечего делать» отвергнуто: пустота
записи есть факт о нашем маршруте, а не о предмете. Мифос в вердикте от 14.08 называет
чётную ногу `the real wall` — прямо противоположно оптимистичному чтению.

**Техника:** сравнение двух фронтов счётом файлов (`ls | grep -ci`) до любых выводов о
том, где велась работа. Дёшево и сразу отделило «не разрабатывалось» от «разрабатывалось
не здесь».

**Бонус проверен и оказался условным.** Утверждение «закроем дно — чётность основного
состояния получим даром» держится на трёх звеньях, и все три найдены на диске:
`parity_dichotomy_of_simple_eigenspace` (специально не выбирает знак плюс),
`hermitian_unit_eigen_projective_defect_le_residual_sq_div_beta_sq_of_orthogonal_floor`,
и `sourceCCMComplexRow_even_of_phaseRealification_even`. Третье звено **условно**: его
посылка — точная чётность строки `q`, и собственный комментарий файла говорит, что это
`the necessary source theorem that the current D0Pstar contract does not export`. Под
нарушение уже заведён измеритель загрязнения: `sourceCCMComplexOddMass` с точным
тождеством через дефект отражения. Вывод: бонус реален, но не бесплатен — он висит на
непоставленной чётности строки.

**Следующий ход:** голова №2 очереди Мифоса — `sourceWeilEvenTailAmbientCoercive_explicit`.
Цена снята с диска: в `D0PstarSourceLowBandModeDecay.lean` две теоремы из двенадцати не
знают о чётности вовсе (`norm_fourier_logWindowZeroExtendedMode_le_lowBand_inv` :132 и
`sum_support_inv_nat_shift_sq_le` :368) и переиспользуются как есть; остальные десять —
обёртки над `Odd`-модами, требующие механического близнеца. Новая математика остаётся
ровно в одном месте: дно чётной головы при фиксированном сдвиге.

**Адреса:**
`ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G1_COFINAL_COMPLEMENT_FLOOR_MYTHOS_VERDICT_2026-08-14.md` ·
`Q3/Proofs/RouteB/SimpleEvenGroundSectorCriterion.lean:93` ·
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementSpectral.lean:275` ·
`Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean:128` ·
`Q3/Proofs/RouteB/D0PstarSourceCCMOddMassReflectionDefect.lean:112` ·
`Q3/Proofs/RouteB/D0PstarSourceWeilOddTailCorrectionBound.lean:35` ·
контракты `docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md`, секция G1

**Чей вердикт и аргумент:** Мифос, 14.08.2026, `STOP_CODE:
ODD_TAIL_AND_M13_RECEIVER_DO_NOT_SPECIALIZE_TO_COMPLEMENT_FLOOR_SECTOR_SHIFT_SCHEDULE_MISMATCH_EVEN_COMPLEMENT_SUPPLIER_MISSING`.
Аргумент: оператор коммутирует с чётностью, `B = Q(K − aI)Q` блочно-диагональна, дно
берётся как минимум по двум секторам. Три убийства с явными свидетелями — `F1` рушит
«коммутирует + простой ⇒ чётное основное состояние» на матрице `2×2`; `F2` рушит
«нечётный tail floor ⇒ complement floor» на `Fin 3 collapse plant ⊕ I_n`; `F3` рушит
подмену сдвига между ногами с курсом обмена один к одному против `β`.

---

## 2026-08-11 — B3.0AP correction: stale N=0 proof removed, all-N receiver rebuilt

**Развилка:** сохранить зелёный canonical-`N = 0` результат после обычного
incremental build либо принудительно пересобрать source и проверить, существует
ли доказательство без старого `.olean`.

**Выбрали:** forced clean source rebuild, затем literal all-`N` target и
explicit finite odd-mode-sum crosswalk к exact corrected-CCM energy для каждого
auxiliary `N`.

**Почему:** чистая сборка показала, что большие carrier/operator equalities
timeout/переполняют recursion, а объявленный graph-head `rfl` не является
source proof. Старый PASS пришёл из stale `.olean`. Малый mode-sum descent
действительно kernel-checks и сохраняет исходный `∀ N` без ослабления.

**Что отвергли и почему:** canonical `N = 0` reduction отвергнут как
неподтверждённый source-кодом; также отвергнуты `N = 480/960` вместо symbolic
cutoff, auxiliary `N` как head size, scalar inverse и выбрасывание
`R† C⁻¹ R`, потому что они меняют математический объект.

**Техника:** clean rebuild, public finite-synthesis expansion, normalized odd
mode-sum crosswalk, exact all-`N` form pairing, production-import consumer,
declaration-registry repair (`8` missing / `7` stale → zero drift).

**Следующий ход:** перелочить B3.0AO MINT на corrected proof commit и после
отдельного owner OK просить в том же живом phase chat архитектуру ровно для
all-`N` corrected-energy nonnegativity; знак по-прежнему не доказан.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTargetFloorSchurMatrixReceiver.lean`
·
`docs/routeB_bus/GOAL057_B3_0AP_ALL_N_SCHUR_MATRIX_RECEIVER_CLOSEOUT_2026-08-11.md`
· Goal 057 A60.

**Чей вердикт и аргумент:** local Codex proof; Proshka не вызывалась. Аргумент —
forced clean build опровергает canonical reduction, а kernel-checked finite
mode-sum crosswalk показывает exact all-`N` corrected matrix sign target без
предположения самого знака.

---

## 2026-08-11 — B3.0AO: all-N m=13 Schur receiver, sign still open

**Развилка:** выбрать один удобный `PairIndex.N` для сертификата либо
зафиксировать source-safe цель, которая не позволяет вспомогательной координате
изменить смысл `m = 13` source cell.

**Выбрали:** предикат
`SourceWeilOddTargetFloorSchurPositive13 := ∀ N, Schur(13,N).IsPositive`,
плюс точные scalar-energy и full head–tail block receivers.

**Почему:** `PairIndex.N` не является параметром source-Weil объекта в этой
ветке, но одиночная специализация оставляла бы дыру в кванторе. Универсальный
receiver закрывает эту дыру, не требуя ложного перехода от finite numerics.
Lean отдельно подтвердил `N`-независимость analytic cutoff, lower-bound
constant и literal head synthesis.

**Что отвергли и почему:** один удобный `N` не доказывает source-cell fact;
грубое `rfl`-равенство всех больших graph-carrier operators раскручивает
огромные noncomputable objects и не нужно для честной цели; `N=480/960`
остаётся диагностикой, а не symbolic Schur certificate.

**Техника:** exact symmetry, completion at the actual inverse-weighted
corrector, positivity iff quadratic energy, universal quantifier receiver,
production importing consumer.

**Следующий ход:** после отдельного owner OK отправить в тот же живой phase chat
byte-locked B3.0AO MINT; требовать certificate architecture ровно для
`SourceWeilOddTargetFloorSchurPositive13`.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTargetFloorSchurReceiver.lean`
·
`docs/routeB_bus/GOAL057_B3_0AO_TARGET_FLOOR_SCHUR_RECEIVER_CLOSEOUT_2026-08-11.md`
· Goal 057 A59.

**Чей вердикт и аргумент:** local Codex proof; Proshka ещё не вызывалась.
Аргумент — all-`N` receiver устраняет кванторную подмену, а две exact iff
формы показывают единственный оставшийся знак без его предположения.

---

## 2026-08-11 — B3.0AN: target-floor tail inverted, exact finite Schur sign isolated

**Развилка:** считать вычитание `10^-58` из source-Weil form безопасным по
одной ambient-оценке либо сначала получить coercivity в полном graph norm и
только потом строить actual inverse и Schur complement.

**Выбрали:** exact `c₀`-shifted graph operator, convex combination двух
source-locked lower bounds, actual closed infinite odd tail, literal residual
и completion of the square при `c₀ = 10^-58`.

**Почему:** ambient coercivity контролирует `a`, weighted-energy lower
контролирует `b - L a`; их точная выпуклая комбинация даёт положительную
константу на `a+b=‖x‖²`. Поэтому target-floor tail действительно обратим, а
оставшаяся неопределённость локализуется в точном конечном Schur operator.

**Что отвергли и почему:** прямое вычитание shift без graph coercivity не
сохраняет invertibility; scalar inverse ломает block object; `N=480/960`
подменяет symbolic cutoff; completion identity сама не доказывает знак
конечного Schur complement.

**Техника:** convex combination exact quadratic lower bounds, Riesz graph
operator, closed-tail compression, continuous inverse, exact block completion.

**Следующий ход:** получить source-locked positivity certificate для
`sourceWeilOddTargetFloorSchurComplement`, затем отдельно закрыть literal odd
form-core bridge.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTargetFloorSchurReduction.lean`
· `docs/routeB_bus/GOAL057_B3_0AN_SOURCE_WEIL_ODD_TARGET_FLOOR_SCHUR_REDUCTION_CLOSEOUT_2026-08-11.md`
· Goal 057 A58.

**Чей вердикт и аргумент:** local Codex proof; Proshka не вызывалась, потому
что обе lower bounds и operator seams уже были kernel-checked. Аргумент —
точная convex combination и block completion, проверенные Lean и внешним
production consumer.

---

## 2026-08-11 — B3.0AM: exact shifted Schur positivity closed, strict c0 kept open

**Развилка:** попытаться сразу назвать положительность already-shifted head
compression строгим `c₀`-floor либо сначала элиминировать буквальный
бесконечный odd tail и зафиксировать точный Schur complement без смены
объекта.

**Выбрали:** literal Euclidean low-odd-head synthesis, actual shifted
source-Weil graph operator, exact B3.0AK infinite tail, actual B3.0AL
`R† C⁻¹ R` correction и graph vector `S q - C⁻¹ R q`.

**Почему:** positivity полного shifted operator на этом graph vector даёт
точное cancellation-preserving неравенство correction ≤ head и PSD exact
Schur complement; это source-locked бесконечномерный факт, который можно
доказать локально, не подменяя ещё отсутствующую строгую константу.

**Что отвергли и почему:** shifted semidefinite positivity нельзя переименовать
в strict unshifted `c₀` floor; scalar outer inverse и raw residual norm теряют
block cancellation; finite `N=480/960` Schur matrices не являются exact
closed-tail operator и не доказывают uniform infinite lower bound.

**Техника:** exact block-operator algebra, positivity на
`S q - C⁻¹ R q`, continuous-linear-map adjoints и literal infinite-tail
compression.

**Следующий ход:** построить unshifted либо правильно `c₀`-shifted actual
infinite Schur comparison и доказать его строгий cancellation-sensitive lower
bound; только после этого закрывать `OddTailGradedResolventBound13`.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilShiftedOddHeadSchur.lean`
· `docs/routeB_bus/GOAL057_B3_0AM_SOURCE_WEIL_SHIFTED_ODD_HEAD_SCHUR_CLOSEOUT_2026-08-11.md`
· Goal 057 A57.

**Чей вердикт и аргумент:** local Codex proof; Proshka не вызывалась, потому
что exact block identity и positivity были локально исполнимы из уже
kernel-checked B3.0AK/B3.0AL suppliers. Аргумент — полный shifted quadratic
form на exact graph vector раскладывается в literal head минус actual
inverse-weighted correction; Lean и внешний production consumer это
проверили.

---

## 2026-08-11 — B3.0AL: literal source residual built, quantitative bound kept open

**Развилка:** моделировать `R_out` конечной матрицей, заменить внешний блок
скаляром, либо построить буквальный low-head-to-infinite-tail cross-block
существующего shifted source-Weil graph operator.

**Выбрали:** `EuclideanSpace ℂ (Fin R)` для коэффициентов первых `R`
нормированных нечётных graph modes, их буквальный синтез, actual source
operator и orthogonal projection в замкнутый B3.0AJ tail; при B3.0AK cutoff
этим инстанцирован настоящий B3.0AI `R† C⁻¹ R` correction.

**Почему:** это ровно source-locked infinite cross-block в тех же graph
Hilbert norms и с тем же actual invertible outer block; boundedness следует
из композиции continuous linear maps, а pairing с tail сохраняется точной
теоремой об orthogonal projection.

**Что отвергли и почему:** plain `Fin R → ℂ` имеет sup norm, а не нужную
евклидову норму; raw residual norm и constant-floor inverse теряют
divided-difference cancellation; finite `N=480/960` Schur matrices не равны
infinite closed-tail operator; существование положительной correction не
является количественным `OddTailGradedResolventBound13`.

**Техника:** finite-dimensional continuous linear synthesis, composition of
continuous linear maps, closed-subspace orthogonal projection, exact positive
invertible outer inverse and B3.0AI adjoint correction.

**Следующий ход:** построить literal head block/form и доказать
cancellation-sensitive lower bound для exact Schur complement, сохраняя
B3.0AH divided differences до применения нормы.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailResidual.lean`
· `docs/routeB_bus/GOAL057_B3_0AL_SOURCE_WEIL_ODD_TAIL_RESIDUAL_CLOSEOUT_2026-08-11.md`
· Goal 057 A56.

**Чей вердикт и аргумент:** local Codex proof; Proshka не вызывалась, потому
что production operator, exact tail, coercivity и generic correction interface
уже существовали. Аргумент — буквальная композиция и exact pairing theorem,
проверенные Lean и внешним production consumer.

---

## 2026-08-11 — B3.0AK: explicit coercivity closed, residual kept separate

**Развилка:** ждать named Yoshida/Suzuki crosswalk, импортировать sampled
cutoff, или собрать coercivity напрямую из уже доказанных production
high-frequency, low-band, bounded-form и closure legs.

**Выбрали:** symbolic band radius, literal max/ceil cutoff, exact high/low
integral split and absorption of `W02` and `Prime`, yielding
`SourceWeilOddTailAmbientCoercive i R (1/2)` for every pair index.

**Почему:** все source-locked поставщики уже kernel-checked, а их прямая
композиция даёт более сильную uniform theorem shape без внешнего численного
порога и без смены топологии.

**Что отвергли и почему:** sampled `mpmath` cutoff не имеет универсального
квантора; finite `N=480/960` floors не доказывают infinite closed tail;
mode-wise triangle bound теряет uniformity; paper-name wrapper создавал бы
неподтверждённую атрибуцию при уже существующем прямом доказательстве.

**Техника:** explicit norm target, exponential safe-frequency radius,
max/ceil natural cutoff, Parseval low-band budget, weighted-integral split,
bounded-operator Cauchy--Schwarz and graph-closure transfer.

**Следующий ход:** построить bounded literal source residual into the same odd
tail; затем инстанцировать B3.0AI actual inverse-weighted correction и доказать
настоящий `OddTailGradedResolventBound13` estimate.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailExplicitCoercivity.lean`
· `docs/routeB_bus/GOAL057_B3_0AK_SOURCE_WEIL_ODD_TAIL_EXPLICIT_COERCIVITY_CLOSEOUT_2026-08-11.md`
· Goal 057 A55.

**Чей вердикт и аргумент:** local Codex proof; Proshka не вызывалась, потому
что theorem shape и все production seams были закрыты локально. Аргумент —
quantified integral split plus explicit bounded-leg absorption, проверенный
Lean и external production consumer.

---

## 2026-08-11 — B3.0AK: low-band mass made uniform over the algebraic odd tail

**Развилка:** оценивать по одной нечётной моде и затем надеяться на
треугольник или сразу сохранить ортогональность произвольной конечной
линейной комбинации хвоста.

**Выбрали:** буквальный `Finsupp`-синтез нормированных antisymmetric modes,
Parseval в ambient Hilbert space, конечномерный Cauchy--Schwarz и
телескопическую оценку `Σ_{k∈support} 1/(R+k+1)^2 ≤ 1/R`.

**Почему:** это даёт квантифицированную по всем coefficient supports оценку
`∫_{-T}^T |Ff|² ≤ ε(T,R) ‖f‖²`, где
`ε(T,R) = 2T (4√L/π)^2/R`; именно такой uniform input нужен для
source-Weil coercivity, а не поточечная оценка отдельного столбца.

**Что отвергли и почему:** отвергли сумму mode-wise норм по треугольнику —
она вводит `ℓ¹`-норму коэффициентов и не контролируется ambient `L²`-нормой
uniformly по размеру support; также не использовали finite-`N` sampling.

**Техника:** publicized уже доказанный far-frequency envelope; построены
orthonormal odd family, AE Fourier synthesis, Parseval, Finsupp
Cauchy--Schwarz, telescoping inverse-square tail и set-integral transfer.

**Следующий ход:** совместить эту low-band оценку с symbolic high-frequency
нижней границей arch multiplier и bounded W02/Prime forms; выбрать явные
`T, R, mu` и наполнить `SourceWeilOddTailAlgebraicCoercive`.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLowBandModeDecay.lean` ·
`integral_norm_sourceWeilOddFourierFinsuppShift_sq_le_lowBand` ·
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean` ·
target build `Q3.Proofs.RouteB.D0PstarSourceLowBandModeDecay` PASS.

**Чей вердикт и аргумент:** local Codex proof; Proshka не потреблялась,
поскольку source theorem shape и все необходимые Mathlib seams были найдены
локально.

---

## 2026-08-11 — B3.0AK: sampled `t₀` replaced by a symbolic Lean cutoff

**Развилка:** импортировать найденный `mpmath`-порог для digamma или вывести
неоптимальный, но полностью доказанный high-frequency cutoff из production symbol.

**Выбрали:** kernel-checked порог
`exp (C + |log π| + 6) ≤ |t|`, из которого следует
`C ≤ sourceArchimedeanMultiplier t`.

**Почему:** остаток Стилтьеса уже формализован; он даёт нижнюю оценку через
`log ‖1/4 + iπt‖`, а `‖1/4 + iπt‖ ≥ |t|`. Это полностью убирает sampled
maximum и внешний numerical certificate из первой половины Yoshida.

**Что отвергли и почему:** отвергли `t₀ ≈ 1.7419251e11` как Lean-вход — это
диагностика по точкам, а требование источника квантифицировано по всем
`|t| ≥ t₀`.

**Техника:** `re_digamma_remainder_bound_stieltjes`, явные bounds `2` и `4`
для correction/remainder, монотонность `Real.log` и `Real.log_exp`.

**Следующий ход:** доказать второй независимый leg Yoshida — явную оценку
low-frequency Fourier mass для algebraic high odd modes — и только затем
собрать source-Weil coercivity с bounded W02/Prime.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchHighFrequencyLowerBound.lean` ·
`sourceArchimedeanMultiplier_ge_logNorm_sub_explicitShift` ·
`sourceArchimedeanMultiplier_ge_of_exp_shift_le_abs`.

**Чей вердикт и аргумент:** local Codex proof from the source-locked production
digamma remainder; внешний numerical verdict не потреблялся.

---

## 2026-08-11 — B3.0AK: algebraic Yoshida tail reaches the literal graph closure

**Развилка:** пытаться формализовать source cutoff и топологическое замыкание
одним монолитом или сначала отделить точный algebraic-to-closed-tail seam.

**Выбрали:** отдельный Lean-мост, который переносит coercivity с конечных
линейных комбинаций высоких нечётных мод на буквальное замыкание в
source-Weil graph topology с теми же `R` и `mu`.

**Почему:** Yoshida `K_N(a)` сначала даёт оценку на высоком Fourier-подпространстве,
а B3.0AJ хранит tail как topological closure. Нужны две независимые непрерывности:
Fourier-коэффициента для сохранения нулей и полной raw source-Weil диагонали для
сохранения неравенства.

**Что отвергли и почему:** отвергли Hilbert-`L²` density как замену graph closure
и любой finite-`N` floor как поставщика бесконечной оценки; обе подмены меняют
топологию или квантор.

**Техника:** `Submodule.span_induction`, closed zero-set каждого точного
`V_n_m`-коэффициента и closed sublevel-set непрерывной graph-диагонали.

**Следующий ход:** доказать source-locked high-mode estimate с явными cutoff/constant;
только он может наполнить уже доказанный transport реальным `R, mu`.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailCoercivityClosure.lean` ·
`sourceWeilGraphOddTail_low_fourier_vanish` ·
`sourceWeilOddTailAmbientCoercive_of_algebraic`.

**Чей вердикт и аргумент:** local Codex proof; два запуска Proshka B3.0AK не
выдали тела ответа, поэтому никакой внешний математический вердикт не потреблён.

---

## 2026-08-11 — Yoshida Lemma 3: printed normalization beats the OCR reconstruction

**Развилка:** потребить в B3.0AK реконструкцию формулы из OCR-
карточки/скрипта или остановиться и сверить печатную p. 291.

**Выбрали:** печатную нормализацию: `C₃` содержит
`∫ 2a₀(1+a₀|t|)² dt`, а внешний хвост есть `Σ(1/(πn))²`.

**Почему:** на PDF p. 290–291 эти два множителя видны непосредственно;
карточка и скрипт заменяли это на `C₃ · Σ(a₀/(πn))²`, что меняет
границу `N` в `2/a₀` раза.

**Что отвергли и почему:** отвергли число `N > 1.5488372e34` как
source-locked границу: оно получено из неверной комбинации множителей
и в любом случае было несертифицированной `mpmath`-диагностикой.

**Техника:** PDF render печатных pp. 282, 290, 291 плюс прямая
сверка с `yoshida_analytic_N.py`; различающий тест — исправленный
запуск должен изменить старую границу ровно в `2/log(√13)` раза.

**Следующий ход:** исправить карточку/скрипт, пометить результат
как diagnostic-only и доказывать в Lean саму оценку, а не импортировать число.

**Адреса:** Yoshida PDF printed pp. 282, 290–291 ·
`docs/routeB_bus/litreview/YOSHIDA_HERMITIAN_1992_USAGE_CARDS.md:69` ·
`docs/routeB_bus/phase4_scripts/yoshida_analytic_N.py:107` ·
`docs/routeB_bus/PHASE4_RESULTS_2026-08-10.md:252`.

**Чей вердикт и аргумент:** local Codex source audit; внешний вердикт
не потреблялся.

---

## 2026-08-10 — STARTUP_V5: goal-scoped delivery and one Codex tool authority

**Развилка:** оставить отдельное OK перед каждой записью/commit/push, ручную
доставку `TASK_*.md` и byte-identical внешний картограф либо восстановить
автономный локальный цикл внутри заранее названного goal scope.

**Выбрали:** `GOAL_SCOPED_OPERATIONAL_GRANT`, один валидируемый
`docs/Codex/CURRENT.md` и репозиторный `docs/cartographer/` как канонический
исполнительный картограф; machine-local `codex_specs` оставлен независимым
observer-контуром.

**Почему:** аудит воспроизвёл три сбоя: per-action gate разрывал closeout до Git,
датированные задания после pull не читались автоматически, а startup проверял
repo inventory при маршрутизации Codex во внешние скрипты. Две реализации
`cheap.py` уже давали разные числа объектов — 1425 и 1382.

**Что отвергли и почему:** per-action OK для внутренних шагов отвергнут как
причина недоставленных узлов; ручной prompt-only канал — как невидимый после
pull; обязательный byte-identical `codex_specs` — как второй некоммитимый и
machine-specific источник исполнения. Отдельное разрешение сохранено для
reviewer sends, paid API, destructive действий, policy edits и `PX_RH_CLAIM`.

**Техника:** physical-state audit, SHA/выходное сравнение двух картографов,
repo-path validation в Spine, fail-closed current-task pointer, 97 control plants,
strict startup и генераторные size/diff gates. Census дополнительно исправлен,
чтобы не засасывать `venv_djo` и `aristotle_output`.

**Следующий ход:** доставить STARTUP_V5 scoped commit/push; остановку и чистый
перезапуск многодневного `qmd embed -f` проводить отдельным разрешённым действием.

**Адреса:** `docs/CODEX_CONTROL.md` v5 · `docs/Codex/CURRENT.md` ·
`q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md` · `docs/cartographer/TOOLS.yaml` ·
`orchestrator/spine.py` · `specs_docs/session_start.sh`.

**Чей вердикт и аргумент:** владелец, `ok. go`, после read-only аудита; аргумент
владельца — Codex должен local-first закрывать узел, сразу записывать причину и
делать commit/push, а Прошку вызывать только на настоящей развилке или после
исчерпанных локальных попыток.

---

## 2026-08-10 — literal odd-tail outer block in the graph Hilbert norm

**Развилка:** represent the infinite source outer block on the plain
ambient/product space, reuse a finite Schur floor, or build the actual closed
graph Hilbert carrier and leave the source coercivity theorem visible.

**Выбрали:** B3.0AJ: `WithLp 2` closed graph, literal normalized closed
odd span, exact compressed shifted source-Weil Riesz operator, and the explicit
`SourceWeilOddTailAmbientCoercive` seam.

**Почему:** the graph carrier simultaneously controls the ambient and
square-root-weighted coordinates. The source ambient lower bound and the
already-proved weighted bound therefore combine to a strict graph-norm bound,
which is exactly what continuous invertibility requires.

**Что отвергли и почему:** the plain product was rejected because its max
norm is wrong; the raw span because completeness is unavailable; identity or
`d⁻¹ I` because it erases the actual source block; N=960 because finite evidence
cannot prove the infinite supplier.

**Техника:** closed `LinearPMap.graph` transport, `WithLp` product inner
geometry, Riesz representation, positive orthogonal compression, two-component
coercivity with constant `min mu 1 / 2`, and Mathlib's strict inner-bound
criterion for a unit/continuous equivalence.

**Следующий ход:** source-lock the Yoshida/Suzuki statement and prove an
explicit cutoff/constant instance of `SourceWeilOddTailAmbientCoercive`; keep
the literal residual supplier separate.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailGraphOperator.lean`
· `docs/routeB_bus/GOAL057_B3_0AJ_SOURCE_WEIL_ODD_TAIL_GRAPH_OPERATOR_CLOSEOUT_2026-08-10.md`
· Goal 057 A54.

**Чей вердикт и аргумент:** local Codex proof; no external verdict was
consumed. The exact argument is the two-coordinate graph estimate above.

---

## 2026-08-10 — actual outer inverse kept visible in the Schur correction

**Развилка:** either formalize the generic inverse-weighted correction with
the real outer inverse, or jump directly to a source theorem while leaving the
operator hypotheses and orientation implicit.

**Выбрали:** B3.0AI: an exact dimension-neutral interface with a positive,
continuously invertible outer block and the actual correction `R† C⁻¹ R`.

**Почему:** B3.0AH preserves the odd source cancellation, but the repository
had no reusable theorem ensuring that the real continuous inverse is positive
and that the Schur correction has the correct adjoint orientation. Closing the
generic seam makes the remaining source supplier explicit and testable.

**Что отвергли и почему:** `d⁻¹ R†R` was rejected because it erases the outer
spectral stiffness; finite-dimensional diagonalization and N=960 were rejected
because they cannot supply an infinite theorem; the PSWF Jacobi Schur API was
rejected because it describes a different recurrence operator.

**Техника:** prove positivity of `ContinuousLinearMap.inverse` directly from
the positive symmetric operator and its actual inverse equation, then use
`IsPositive.adjoint_conj` to obtain the exact positive correction and its
operator/quadratic Schur decomposition.

**Следующий ход:** construct the literal source odd-tail Hilbert carrier and
outer block, and prove the source block positive plus continuously invertible;
only then instantiate the generic correction and attack the graded bound.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarOddTailInverseWeightedCorrection.lean`
· `docs/routeB_bus/GOAL057_B3_0AI_ODD_TAIL_INVERSE_WEIGHTED_CORRECTION_CLOSEOUT_2026-08-10.md`
· Goal 057 A53.

**Чей вердикт и аргумент:** local Codex implementation; no external verdict
was consumed. The local source audit found no existing infinite source CCM
outer-block supplier, so the generic interface was closed without pretending
that the source positivity/invertibility obligation had disappeared.

---

## 2026-08-10 — odd source cancellation before the resolvent norm

**Развилка:** either start an abstract infinite Schur-complement interface
immediately, or first expose the exact odd source-beta cancellation that the
interface must preserve.

**Выбрали:** B3.0AH: the exact odd divided-difference identity at `m = 13`
plus its finite corrected-row module sum.

**Почему:** the generic commutator theorem existed, but no public theorem
turned it into the odd residual formula. Without that seam the next proof
could silently take entrywise absolute values and recreate the killed raw
residual estimate.

**Что отвергли и почему:** entrywise bounds before cancellation were rejected
because they destroy `n*beta(k) - k*beta(n)`; the mode-four Jacobi Schur API
was rejected because it belongs to the PSWF recurrence, not the source-Weil
odd matrix; finite N=960 was again rejected as an infinite supplier.

**Техника:** reuse the exact source commutator, prove beta oddness, clear the
two nonzero tail denominators under `0 < n < k`, then distribute the scalar
identity through an arbitrary real module sum before any norm.

**Следующий ход:** define the infinite odd outer-block domain and the weakest
positive/invertible operator interface that makes
`R_out* C_out⁻¹ R_out` lawful; keep summability and the actual graded bound as
separate obligations.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarOddTailDividedDifference13.lean`
· `docs/routeB_bus/GOAL057_B3_0AH_ODD_TAIL_DIVIDED_DIFFERENCE13_CLOSEOUT_2026-08-10.md`
· Goal 057 A52.

**Чей вердикт и аргумент:** local Codex implementation under the archived
Proshka Phase-4 constraint: preserve the transformed divided-difference
cancellation before taking norms; no new Proshka call was made.

---

## 2026-08-10 — topology lemma retained, but resolvent theorem took priority

**Развилка:** after proving the source-Weil form/graph topology reduction and
pulling 29 Linux commits, either continue immediately to a generic odd
form-core theorem or adopt the later Phase-4 audit's source-faithful
resolvent-weighted target.

**Выбрали:** close B3.0AG as exact supporting infrastructure and make
`OddTailGradedResolventBound13` the next proof object.

**Почему:** B3.0AG proves that the bounded W02/Prime diagonal adds no new core
topology, while the later audit shows that the actual obstruction is the
infinite outer correction `R_out* C_out⁻¹ R_out`. The finite `480 -> 960`
nested identity passes, but deliberately leaves all modes above 960 open.

**Что отвергли и почему:** ordinary Hilbert density was rejected because it
does not control the weighted graph norm; the killed surrogate
`d⁻¹ R_out* R_out` was rejected because it loses the outer spectral
stiffness; the finite N=960 PASS was rejected as an infinite theorem because
its quantifier stops at mode 960.

**Техника:** exact energy decomposition plus continuity of the bounded
diagonal, two-sided tendsto reduction on ambient-null sequences, three
negative mutants, and post-pull source-locked comparison with the Phase-4
code audit and nested-Schur report.

**Следующий ход:** formulate the smallest Lean-facing
`OddTailGradedResolventBound13` interface, with the exact odd
divided-difference source identity, infinite outer-block domain, and
inverse-weighted Gram bound explicit; do not reintroduce the constant-floor
surrogate.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilFormCoreTopology.lean`
· `docs/routeB_bus/GOAL057_B3_0AG_SOURCE_WEIL_FORM_CORE_TOPOLOGY_CLOSEOUT_2026-08-10.md`
· `docs/routeB_bus/proshka/PROSHKA_VERDICT_PHASE4_CODE_AUDIT_2026-08-10.md`
· `docs/routeB_bus/REPORT_NESTED_SCHUR_AUDIT_2026-08-10.md`.

**Чей вердикт и аргумент:** local Codex closed only the topology lemma;
Proshka selected the resolvent-weighted representation because replacing
`C_out⁻¹` by `d⁻¹I` destroys the spectral stiffness and kills only the
surrogate, not the floor target.

---

## 2026-08-11 — словарь переводов вперёд атомов: искать надо по смыслу, а не по опорам

**Развилка:** конструктор строился снизу — атомы, описания, пересечение атомных множеств с
чужим деревом. Вопрос был, что дальше: `comparator` (сверка «доказано ли заявленное») или
раздача заданий агентам.

**Выбрали:** ни то, ни другое. Перед обоими встал **словарь переводов** — формулировка
каждого незакрытого шага в терминах, общих с Mathlib.

**Почему:** пробный проход одного шага через весь конструктор. Взяли
`SIMPLE_EVEN_GROUND_TO_REAL_ZEROS:6` (`H2aAt`, статус `GAP`), перевели в три утверждения о
самосопряжённом операторе — и два нашлись готовыми за один `rg`:
`hbottom` целым файлом в `Mathlib/Analysis/InnerProductSpace/Rayleigh.lean`,
`hsimple` в чужом `Zeta23/LinAlg/Inertia.lean`. Шаг, числившийся как «нужна теорема»,
оказался задачей на инстанцирование.

**Что отвергли и почему:** порядок «`comparator` первым», записанный часом ранее в
`CONSTRUCTOR_SPEC.md`. Он неверен: `comparator` сверяет формулировки, а формулировок без
словаря нет — сверять нечего. Отвергли и продолжение атомного пути: пересечение 705 общих
атомов дало `Real.pi`, `mul_nonneg`, `measurableSet_Icc` — фундаменты, по которым нельзя
отличить релевантное от случайного.

**Техника:** проверка схемы на одном шаге целиком, вместо достройки ярусов вслепую. Один
проход показал и то, что работает (поиск по смыслу перевода), и то, что не работает
(поиск по атомам), и где схема требует человека (сам перевод — суждение, машина его не
делает).

**Следующий ход:** пополнять словарь остальными шагами `cheap.py`; `comparator` — после
него; раздача агентам — последней.

**Адреса:** `docs/cartographer/TRANSLATION_DICTIONARY.md` · `CONSTRUCTOR_SPEC.md` (ярус 0
добавлен, порядок исправлен) · `atom_describe.py` · `foreign_atoms.py` ·
`FOREIGN_LEAN_BRIDGE.md`.

**Чей вердикт и аргумент:** владелец — «именно словарь, который по мере работы будет
пополняться»; он же поймал непоследовательность, когда я предложил читать Бомбьери вручную
вместо того, чтобы строить инструмент, который сам покажет нужные места.

---

## 2026-08-10 — пути картографа: считать от себя, а не держать вторую копию

**Развилка:** картограф не работал на Linux из-за путей Мака. Либо вывести пути из
положения самого файла, либо держать на Linux отдельные копии инструментов вне git с
локальными путями.

**Выбрали:** вывод из положения файла, `Path(__file__).resolve().parents[2]`.

**Почему:** на Маке это даёт **буквально ту же строку**, что была прибита вручную —
проверено арифметикой пути. Значит правка не меняет там ничего, а здесь чинит всё.

**Что отвергли и почему:** вторую копию инструментов вне git (предложение владельца).
Она лечит болезнь, которой после вывода путей уже нет, и создаёт три новые: две копии
разъезжаются молча, локальный код невидим Codex и не переживает переустановку, а по
нашему же правилу реестра инструмент без записи в `TOOLS.yaml` не существует.

**Техника:** сравнение вычисленного значения с записанным — до правки, а не после.
Это и позволило утверждать «не сломается», а не «наверное обойдётся».

**Следующий ход:** `TOOLS.yaml` всё ещё указывает пути скриптов в `codex_specs` —
реестр ведёт в несуществующее место. Требует Мака (зеркало), задание 18.

**Адреса:** коммит `3365e24d` · `docs/cartographer/*.py` · `specs_docs/session_start.sh`
секция `КАРТОГРАФ`.

**Чей вердикт и аргумент:** решение владельца после разбора; аргумент — «сначала
проверить, что ломается».

---

## 2026-08-10 — генерёнку инвентаря коммитить, а не игнорировать

**Развилка:** `inventory_RouteB.json` (672 КБ, машинный вывод) — класть в git или в
`.gitignore`.

**Выбрали:** коммитить.

**Почему:** два выигрыша разом. На Маке картограф работает сразу после `pull`, без
прогона генератора. И протухание становится вычислимым: git знает, когда файл обновляли
и что случилось с `.lean` после — этого достаточно, отдельный механизм не нужен.

**Что отвергли и почему:** `.gitignore`. Репозиторий чище на 672 КБ, но на втором теле
два скрипта мертвы до первого прогона, а протухание **необнаружимо в принципе** — git не
знает о файле, спросить не у кого.

**Техника:** проверка «что именно покажет git» до принятия решения. Выяснилось, что сам
git протухание не сигналит — его надо спросить одной строкой; даты файлов не годятся,
mtime не хранится и после клона одинаков у всех.

**Следующий ход:** сторож стоит в старте сессии и падает при расхождении.

**Адреса:** `docs/cartographer/inventory_RouteB.json` · `specs_docs/session_start.sh:*`
секция `КАРТОГРАФ`.

**Чей вердикт и аргумент:** владелец, «коммить».

---

## 2026-08-10 — маршрут получил сторону PASS

**Развилка:** после вердикта GLOWER — считать ли дальше `β_N` (как весь предыдущий месяц)
или строить конечный сертификат Feshbach, а равномерность отдать теореме хвоста.

**Выбрали:** сертификат. Исполнили оба входа как preflight, без записи в Lean.

**Почему:** измерение `β_N` может только убить (верхняя огибающая Ритца) и не может
подтвердить. Сертификат `B_c − d⁻¹R_c*R_c ⪰ 0` впервые даёт **сторону PASS** — то, что
можно доказать, а не только то, чем можно опровергнуть.

**Что отвергли и почему:** продолжение таблицы `β_N` и расчёт при `N = 480` как шага
доказательства — оба запрещены вердиктом, и по существу: экстраполяция `β*_N` однажды уже
дала `DELTA_RATE_UNRESOLVED`.

**Техника:** переиспользование `CCMArbBuilder` из Phase 1 импортом, а не копией формул —
расхождение с сертификатом Phase 1 стало невозможным по построению. Плюс: различающий
исход записывался ДО счёта (порог не должен двигаться с `N`; темп дрейфа должен затухать).

**Следующий ход:** `Lock A` дёшев — обе посылки в дереве с нулём `sorry`. Теорема хвоста
ждёт ответа судьи, какую именно инстанцировать (батч 10.08, вопрос 1).

**Адреса:** `docs/routeB_bus/PHASE4_RESULTS_2026-08-10.md` · `phase4_scripts/` ·
коммиты `a16181ec`, `e3726485` · вердикт
`docs/GLOWER_ODD_FLOOR_10_08_2026/docs/Proshka/PROSHKA_GLOWER_EXACT_CLOSURE_2026-08-09.md`.

**Чей вердикт и аргумент:** Прошка, `PROSHKA_GLOWER_EXACT_CLOSURE_2026-08-09` — дословно:
«L ≥ 0 доказывает не ещё один расчёт `β_N`, а следующая бесконечномерная теорема».

---

## 2026-08-10 — вопрос снят из батча, потому что цену измерили сами

**Развилка:** отправлять ли судье `R2-2` — ранжировать калибраторы `S/B/P/G` по убивающей
силе за цену.

**Выбрали:** снять из батча, оставив три других вопроса.

**Почему:** цена `G` за сутки перестала быть предметом мнения. Внешняя оценка давала
вилку `R(μ=1) ∈ [2·10², 10⁵]` — «вся стоимость проекта сидит в этой вилке». Измерено:
`R = 70`, устойчиво по обрезанию. Спрашивать судью о том, что мы взвесили сами, — трата
батча, который стоит 20+ минут её работы.

**Что отвергли и почему:** отправить как есть. Получили бы ранжирование по устаревшим
ценам, причём для калибратора `G`, три инструмента которого вердикт уже запретил.

**Техника:** прежде чем спрашивать — посчитать. Замер занял минуты, вилку сузил в 500 раз.

**Следующий ход:** батч из четырёх вопросов готов к отправке.

**Адреса:** `docs/routeB_bus/PROSHKA_REQUEST_GLOWER_TAIL_THEOREM_AND_HEAD_DRIFT_2026-08-10.md`
· `PROSHKA_QUEUE.md` Q5 помечен `СНЯТ`.

**Чей вердикт и аргумент:** наш; вилка — из ответа Мифоса от 10.08, `docs/GLOWER_ODD_FLOOR_10_08_2026/docs/Mythos/`.
## 2026-08-10 — G-LOWER turned from operator-first to exact odd form pullback

**Развилка:** require an associated source-Weil operator before any G-LOWER
work, or first restrict the already-constructed source form to the exact
normalized odd finite carrier.

**Выбрали:** the three-declaration form-level child
`ccmOddCoefficientIsometry`, `sourceWeilOddSynthesis13`, and
`sourceWeilOddFormPullback13`.

**Почему:** the source form and its exact finite CCM restriction already exist;
the immediate G-LOWER consumer is a quadratic-form lower bound, not an
`H_m`-valued residual identity.

**Что отвергли и почему:** operator-first work, generic Kato infrastructure,
source acquisition, and N=480 were rejected as the current action because they
do not supply the missing finite odd form restriction.  During implementation,
literal reuse of `ccmFiniteSynthesisEquiv` was also rejected because its apply
bridge is private; widening the upstream API was unnecessary.

**Техника:** normalized antisymmetric CCM basis vectors
`(-a_r/sqrt 2, 0, +a_r/sqrt 2)`, orthonormal-sum isometry, private exact
finite shifted-domain synthesis, and the existing source-Weil finite-form
crosswalk; N=1 positive control plus sign, normalization, and raw/shift mutants.

**Следующий ход:** `GLOWER_ODD_FORM_CORE_OR_DIRECT_TAIL_DOMAIN_MISSING` — prove
either an actual odd form core or a direct tail theorem on the full odd form
domain; Hilbert-norm density alone is insufficient.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddFormPullback13.lean` ·
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL057_B3_0_POST_AE_REPRESENTATION_RERANK_2026-08-10.md` ·
`docs/routeB_bus/GOAL057_B3_0AF_SOURCE_WEIL_ODD_FORM_PULLBACK13_CLOSEOUT_2026-08-10.md`
· Goal 057 A50.

**Чей вердикт и аргумент:** Proshka, post-AE rerank:
“The operator-versus-form fork is resolved for G-LOWER. The immediate wall is
no longer ‘construct an associated operator.’ It is the exact normalized odd
pullback of an already-constructed form.”  Owner's standing direction
authorized immediate adoption of the archived G-LOWER rerank.

---

## 2026-08-10 — B3.0AE closed the energy layer, not the operator layer

**Развилка:** stop after B3.0AD's lower-bounded dense form, package the bounded
perturbations into an extended lower-semicontinuous energy, or jump directly to
an associated operator by inventing missing infrastructure.

**Выбрали:** the narrow extended source-Weil energy with exact finiteness domain
and exact shifted diagonal identity.

**Почему:** the bounded W02/Prime correction is continuous and can be added to
B3.0W's lower-semicontinuous extended Arch energy locally; this proves the
closed-form energy facts that the current library can actually state.

**Что отвергли и почему:** direct operator construction and a hand-rolled Kato
representation theorem were rejected because the pinned Mathlib surface has no
project-ready unbounded self-adjoint/closed-form representation API, and the
selected operator domain would still require a separate proof.

**Техника:** add a norm-shifted continuous nonnegative diagonal correction in
`ENNReal`, transfer lower semicontinuity by addition, and use finiteness plus
`toReal` identities to pin the exact domain and source Weil diagonal.

**Следующий ход:** treat associated-operator representation as a strategic
boundary; identify a lawful supplier or scope generic infrastructure before
any selected-mode graph/domain claim.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilClosedForm.lean` ·
`docs/routeB_bus/GOAL057_B3_0AE_SOURCE_WEIL_SHIFTED_CLOSED_FORM_CLOSEOUT_2026-08-10.md`
· Goal 057 A49.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0AD stopped at the form-to-operator boundary

**Развилка:** assemble the exact source Weil form from the independently closed
W02 and Arch-Prime layers, or copy the monolithic scratch and continue directly
to an associated operator claim.

**Выбрали:** a narrow dense-domain source Weil form with exact finite CCM
restriction and explicit lower bound, stopping before closed extension or
operator representation.

**Почему:** the public B3.0Z/AA seam removes the scratch `hpair` premise, so the
form identity is unconditional; closedness of the bounded perturbation and the
representation theorem are still separate obligations.

**Что отвергли и почему:** the monolithic scratch/operator bundle was rejected
because a lower-bounded Hermitian form on a dense domain does not by itself
prove the full form closed or define the associated operator graph/domain.

**Техника:** exact W02 + Arch - Prime form addition, the existing finite
source-Weil/CCM crosswalk, and norm estimates for the two bounded perturbations.

**Следующий ход:** audit the precise closed-form bounded-perturbation theorem
and then the self-adjoint representation theorem as two explicit seams.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilSesquilinearForm.lean` ·
`docs/routeB_bus/GOAL057_B3_0AD_SOURCE_WEIL_FORM_LOWER_BOUND_CLOSEOUT_2026-08-10.md`
· Goal 057 A48.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0AC replaced a false scratch dependency with V plus AB

**Развилка:** retain the scratch-shaped T-only import, depend on the actual
finite-carrier supplier B3.0V, or hide all dependencies behind the monolithic
scratch module.

**Выбрали:** the exact production pair B3.0V + B3.0AB and only the shifted
Arch-minus-Prime ledger.

**Почему:** Lean showed that the finite shifted synthesis API is supplied by V,
not T; naming that dependency preserves the real carrier and proof provenance.

**Что отвергли и почему:** the T-only import was rejected because it did not
compile once the accidental scratch umbrella disappeared; the umbrella and W02
imports were rejected because they conceal provenance and prematurely assemble
the full source Weil form.

**Техника:** restrict the bounded Prime form to the shifted Arch domain, reuse
V's canonical inclusion/synthesis, and prove both mode-ledger and `-WR - Prime`
finite formulas.

**Следующий ход:** assemble W02 only through AA's unconditional public API.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarArchPrimeSesquilinearForm.lean` ·
`docs/routeB_bus/GOAL057_B3_0AC_ARCH_PRIME_SHIFTED_LEDGER_CLOSEOUT_2026-08-10.md`
· Goal 057 A47.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0AB promoted Prime without assembling Weil

**Развилка:** promote the already compiling Prime scratch by itself or combine
it immediately with Arch/W02 in one production module.

**Выбрали:** byte-identical production of the self-contained ambient Prime form.

**Почему:** its literal-mode and finite `ccmPrimeEntryN1` contracts are already
complete and independently testable; this makes later signs and dependencies
auditable.

**Что отвергли и почему:** immediate Arch/W02 assembly was rejected because it
would hide whether the Prime source pairing and finite carrier were proved or
merely inherited through a broad scratch import.

**Техника:** bounded cosine multiplier on the Fourier-side L2 model, Hermitian
sesquilinear packaging, exact source-mode identity, and canonical finite
synthesis expansion.

**Следующий ход:** restrict Prime to the shifted Arch form domain and close the
exact finite `-WR - Prime` ledger.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPrimeAmbientSesquilinearForm.lean` ·
`docs/routeB_bus/GOAL057_B3_0AB_PRIME_AMBIENT_SESQUILINEAR_FORM_CLOSEOUT_2026-08-10.md`
· Goal 057 A46.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0AA bound W02 only after every source leg was public

**Развилка:** promote the whole ambient-W02/source-Weil scratch, or instantiate
only the concrete ambient W02 form after X, Y, and Z were independently closed.

**Выбрали:** a narrow ambient W02 module with unconditional mode and finite
`ccmW02Entry` crosswalks.

**Почему:** the generic form, physical endpoint functionals, and exact source
identity now meet through public APIs, so no `hpair` premise or finite-to-ambient
inference is hidden.

**Что отвергли и почему:** the full scratch was rejected because it imports
scratch Prime/Arch modules and immediately combines W02 into a source Weil
form and lower bound; those are separate dependency and proof obligations.

**Техника:** continuous rank-two form instantiation, literal endpoint mode
values, exact public source pairing seam, and the canonical finite synthesis.

**Следующий ход:** audit the ambient Prime scratch as an independent production
dependency before combining any source Weil form.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarW02AmbientContinuousForm.lean` ·
`docs/routeB_bus/GOAL057_B3_0AA_W02_AMBIENT_CONTINUOUS_FORM_CLOSEOUT_2026-08-10.md`
· Goal 057 A45.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0Z opened one seam and kept the long proof private

**Развилка:** expose all private W02 endpoint machinery, duplicate the source
algebra in a new module, or publish one literal-integral wrapper theorem.

**Выбрали:** one public wrapper around the already proved private rank-two
identity.

**Почему:** downstream code needs the equality, not the implementation names;
the literal-integral statement is stable and exactly matches Y's mode values.

**Что отвергли и почему:** exposing private helpers was rejected as unnecessary
API growth; copying the long closed-form proof was rejected because two source
proofs could drift while claiming the same identity.

**Техника:** same-module public wrapper with `simpa` over private endpoint
definitions, followed by an external importing consumer.

**Следующий ход:** instantiate X and Y into the concrete ambient W02 form with
no theorem parameter.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean:1148` ·
`docs/routeB_bus/GOAL057_B3_0Z_SOURCE_W02_PUBLIC_RANK_TWO_SEAM_CLOSEOUT_2026-08-10.md`
· Goal 057 A44.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0Y exposed the endpoint supplier without hiding pairing

**Развилка:** bind the physical endpoints directly into an ambient W02 form,
or publish the source endpoint functionals and their mode values first while
leaving the rank-two pairing identity visible.

**Выбрали:** byte-identical production of the endpoint supplier only.

**Почему:** the two continuous maps and their exact mode integrals are fully
proved, while the equality identifying their rank-two combination with
`sourceW02ModePairing` is a separate source fact consumed by X.

**Что отвергли и почему:** defining the concrete W02 form in the same module
was rejected because it would hide whether the pairing identity was proved,
assumed, or merely passed as a theorem parameter.

**Техника:** exact log-window `L2` equivalence, bounded exponential weights,
continuous integral functionals, Fourier-isometry transport, and literal-mode
integral evaluation.

**Следующий ход:** locate and source-lock the rank-two pairing identity, then
instantiate X with the Y functionals.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarW02EndpointFunctionals.lean` ·
`docs/routeB_bus/GOAL057_B3_0Y_W02_PHYSICAL_ENDPOINT_FUNCTIONALS_CLOSEOUT_2026-08-10.md`
· Goal 057 A43.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0X separated the W02 machine from its source

**Развилка:** publish one concrete ambient W02 package, or first isolate the
generic rank-two form machine with explicit hypotheses for endpoint mode
values and the source pairing identity.

**Выбрали:** the generic continuous rank-two form plus conditional literal-mode
and finite `ccmW02Entry` crosswalks.

**Почему:** this makes the remaining source obligation visible: concrete
physical endpoint functionals must still be constructed and evaluated. The
mechanism itself is already exact and independent of that construction.

**Что отвергли и почему:** a concrete W02 wrapper at this step was rejected
because it would make supplied endpoint facts look definitional; treating the
conditional hypotheses as already proved was rejected as mechanism/source
conflation.

**Техника:** bounded `ContinuousLinearMap` rank-two construction, explicit
Hermitian symmetry, literal-mode expansion, and the existing exact finite W02
crosswalk.

**Следующий ход:** materialize the physical plus/minus endpoint functionals and
their exact values on every `V_n_m`, then instantiate the X machine.

**Адреса:** `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarW02RankTwoForm.lean` ·
`docs/routeB_bus/GOAL057_B3_0X_W02_RANK_TWO_FORM_MACHINE_CLOSEOUT_2026-08-10.md`
· Goal 057 A42.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0W separated closed form from the Weil operator

**Развилка:** materialize the 372-line scratch as one closed-form/Weil bundle,
or split the intrinsic archimedean closedness layer from later W02/Prime
bounded perturbations and the associated-operator graph.

**Выбрали:** a narrow B3.0W child containing only the maximal square-root
multiplier, its closed graph, and the lower-semicontinuous extended quadratic
form.

**Почему:** every theorem in this layer follows from B3.0T plus generic
measure/topology APIs; importing the full source Weil scratch would invert the
dependency and hide which analytic property has actually been proved.

**Что отвергли и почему:** the monolithic scratch was rejected because W02,
Prime, full Weil lower bounds, and operator questions have different proof
obligations. Calling the partial multiplier the associated Weil operator was
also rejected because the representation graph is still absent.

**Техника:** `LinearPMap.IsClosed`, `L2` convergence in measure, diagonal
almost-everywhere subsequences, `eLpNorm` Fatou lower semicontinuity, and exact
agreement with the shifted form diagonal.

**Следующий ход:** audit the bounded W02 and Prime ambient forms, then mint the
smallest child that supplies the continuous perturbation without defining the
associated operator.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchClosedForm.lean` ·
`docs/routeB_bus/GOAL057_B3_0W_SHIFTED_ARCH_CLOSED_FORM_CLOSEOUT_2026-08-10.md`
· Goal 057 A41.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.

---

## 2026-08-10 — B3.0V reused the canonical finite carrier

**Развилка:** lift the existing `ccmFiniteSynthesis` through the closed B3.0R
domain inclusion, or reproduce the scratch proof with a separately written
subtype sum and continue directly into ambient W02/Prime machinery.

**Выбрали:** the exact B3.0R-backed lift, followed only by literal-mode
evaluation and the finite `-WR` restriction of the B3.0U form.

**Почему:** the coercion of the lifted synthesis is definitionally the existing
`ccmFiniteSynthesis`, so the locked carrier, coefficient order, and source
crosswalk are preserved rather than re-created.

**Что отвергли и почему:** a duplicate scratch-style finite carrier was rejected
because it creates avoidable membership/order drift; bundling ambient W02,
Prime, the full Weil form, or an operator was rejected because none is consumed
by the finite `-WR` theorem and each changes the semantic boundary.

**Техника:** exact submodule inclusion
`E_m_N_le_sourceArchimedeanShiftedFormDomain`, subtype extensionality, finite
sesquilinear expansion, and the already proved source-to-`ccmWREntry` crosswalk.

**Следующий ход:** run post-V local cartography and select the smallest lawful
closedness/operator or bounded-perturbation successor; do not call Proshka until
a real phase boundary or hard stall.

**Адреса:**
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarArchSesquilinearFormFiniteRestriction.lean`
· `docs/routeB_bus/GOAL057_B3_0V_ARCH_FORM_FINITE_NEG_WR_RESTRICTION_CLOSEOUT_2026-08-10.md`
· Goal 057 A40.

**Чей вердикт и аргумент:** local Codex proof decision under the owner's
`local-first` direction; no external verdict was requested or consumed.
---

## 2026-08-09 — манифест соединён с обратным поиском

**Развилка:** переписать только каталог инструментов или одновременно провести
записи о развилках обратно в startup, прямой поиск, семантический индекс и Spine.

**Выбрали:** `MANIFEST_V2`: машинный каталог семейств плюс три рабочих провода —
startup validation, retrieval и durable `branch_decision` projection.

**Почему:** контрольный `./ask.sh` не находил фразу из `Progress_Log.md`, файл не
входил в `q3_docs`, Spine показывал только старый `INSIGHTS.md`, а все 1784 строки
`journal_entry` происходили из одного исторического файла. Запись существовала,
но обычная следующая сессия её не получала.

**Что отвергли и почему:** YAML-only — он повторил бы дефект `INSIGHTS.md`:
сведения лежат на диске, но не возвращаются через штатный путь поиска. Также
отвергнута пофайловая регистрация сотен генераторов; она быстро протухает, поэтому
они покрываются семействами с обязательной task-local проверкой перед запуском.

**Техника:** live-аудит `ask.sh`, `refresh_q3_docs.py`, `spine.py`, SQLite provenance
и write-path каждого картографического загрузчика; динамические величины заменены
на запросы, а инструменты разделены на read-only, derived writers, canonical writers,
network writers и external surfaces.

**Следующий ход:** прогнать schema/mirror plants, dry-run мигратора, прямой search
plant, corpus-source plant, Spine strict и полный orchestrator test suite; production
`knowledge.db` не менять без отдельного разрешённого goal-close или write action.

**Адреса:** `docs/cartographer/TOOLS.yaml` · `ask.sh` ·
`q3.lean.aristotle/scripts/refresh_q3_docs.py` · `orchestrator/spine.py` ·
`orchestrator/kb_migrate_progress_log.py` · `specs_docs/session_start.sh`.

**Чей вердикт и аргумент:** владелец одобрил точный пакет сообщением
`ОК на пакет MANIFEST_V2`; аргумент — следующая сессия должна знать все рабочие
инструменты и сохранять не только closeout, но и причины выбора и отказа.

---

## 2026-08-09 — Proshka только на реальной развилке

**Развилка:** посылать каждый checkpoint на внешний review или сначала
добивать всё локально и звать Proshka только на неустранимой развилке.

**Выбрали:** `local-first`: Codex сам закрывает всё, что решается диском,
`ask.sh`, вычислением или Lean. Proshka получает один накопленный batch только
на настоящей архитектурной/`MINT`-границе или после зафиксированного hard stall.

**Почему:** в Goal 057 локальная работа уже сняла отдельные Prime-, endpoint-
и lower-bound-вопросы. Отправлять их внешней модели было бы дороже и
медленнее, чем доказать их здесь.

**Что отвергли и почему:** поштучные Proshka-вызовы на каждом шаге — они
дробят контекст, тратят 20+ минут на локально проверяемые вопросы и
замедляют прямой Lean feedback loop.

**Техника:** `PHASE_THEN_BATCH` + `ASK_SHELF_FIRST`; вопросы Q4–Q6 собраны
в один готовый, но не отправленный strategic batch.

**Следующий ход:** closedness/lower-semicontinuity уже доказаны локально;
после отдельного owner `ok` запросить один kill-check production split и первого
`MINT`-child. До `ok` ничего Proshka не отправлять.

**Адреса:** `docs/CODEX_CONTROL.md §4.1, §10, §16.8` ·
`docs/routeB_bus/PROSHKA_QUEUE.md Q4–Q6` ·
`Q3/Proofs/RouteB/D0PstarW02AmbientAndSourceWeilFormScratch.lean` ·
`Q3/Proofs/RouteB/D0PstarShiftedArchClosedFormScratch.lean`.

**Чей вердикт и аргумент:** владелец + Codex. Аргумент владельца:
«сам добиваешь, а Прошка только на настоящей развилке»; локальные зацепки надо сначала
дожать сами, чтобы не тратить её ресурс на нашу работу.

---

## 2026-08-09 — вернуться к публикации или продолжать обход

**Развилка:** продолжать Route B (обход, найденный в июле вне статьи) или
вернуться к маршрутам, которые публикация сама называет живыми.

**Выбрали:** не выбирать до измерения. Заказана сравнительная оценка объёма
у Прошки и Mythos.

**Почему:** маршрут (ii) — мост Судзуки — статья называет «primary live route»,
а в Lean по нему **ноль файлов**. Сравнивать было не с чем.

**Что отвергли и почему:** спрашивать «что нам лучше делать» — такой вопрос
возвращает мнение. Переформулировали в «оцените (ii) против Route B по объёму».

**Техника:** спуск по атомам (`cartographer/cheap.py`), четыре агента на разбор,
чтение публикации до конца вместо пересказа.

**Следующий ход:** Test B (2–5 файлов) — самый дешёвый из трёх калибровочных
тестов Прошки.

**Адреса:** `docs/GENEALOGY.md` · `docs/PROSHKA_ROUTE_COMPARISON_EFFORT_ESTIMATE_2026-08-09.md`
· `full/sections/Main_closure.tex:1374` · коммит `e3e920de`

---

## 2026-08-09 — «поля добавляются даром» убито

**Развилка:** считать три `OWNER_DATA`-поля Route B бесплатными (конструкторов
ноль, значит поле дорисовывается без правок) или нет.

**Выбрали:** признать счёт неверным после kill Прошки.

**Почему:** поле `energyBound` дорисовать легко — это доказывает лишь «если
поле подано, потребитель компилируется». Обеспечить его для канонической семьи —
отдельная теорема. Для `physicalBandwidthCofinal` она построила **контрпример**:
`m_k = 2^((k+1)²)`, `N_k = k+1` — обе координаты кофинальны, а `N_k/log m_k → 0`.
Это доказанная невыводимость, не оценка сложности.

**Что отвергли и почему:** прежний счёт «пять шагов» — он корректен только как
interface count, не как end-to-end.

**Техника:** двухрежимный сплит Прошки — считать отдельно interface-only и
source-faithful. Без него Route B выглядит искусственно дешёвым.

**Следующий ход:** везде, где считаем «шаги до цели», указывать режим счёта.

**Адреса:** вердикт стр. 163–228 · правило `pointwise-vs-uniform` в памяти

---

## 2026-08-09 — прибор найден повторно и записан

**Развилка:** оставить прибор жить в чатах или зафиксировать в репозитории.

**Выбрали:** зафиксировать — `GENEALOGY.md §8` плюс уже существовавший
`MAP.md:192-218`.

**Почему:** прибор терялся один раз: «Инструмент не упомянут в MAP.md ни разу.
Мы его забыли, нашли случайно — четырёхагентной картографией, запущенной по
другому поводу». Второй потери быть не должно.

**Что отвергли и почему:** держать в `codex_specs/` вне репозитория — судьи
и Codex туда не смотрят, файлов на GitHub проекта не было вовсе.

**Техника:** `git commit -o путь` — коммит только своих файлов, не трогая чужой
staged-патч из 19 переименований.

**Следующий ход:** сварить головку с образцом — `SIEG_of_penalty`,
названа в `H2aPenaltyCoercivity.lean:428-443`, не написана.

**Адреса:** `docs/GENEALOGY.md §8` · `docs/routeB_bus/MAP.md:198` · коммит `e3e920de`

---

## 2026-06-25 → 2026-07-12 — как встала PSD-линия (восстановлено задним числом)

**Развилка:** её не было. Это главное открытие.

**Выбрали:** ничего. Работа встала на плановом «следующем патче».

**Почему:** `decisionRule` требовал вердикта пилота; пилот fail-closed и вердикта
не выдал, потому что не было данных; правило записи решения не запустилось.
Последняя попытка 10.07 упала на **сборке** — 7876-модульный bootstrap и
отсутствующий `olean`. «infrastructure validation gap, NOT a counterexample».

**Что отвергли и почему:** ничего сознательно. `DORMANT_2026-06-25` — ярлык,
приклеенный аудитом 06.08 по признаку «0 коммитов за 30 дней». В git до сих пор
`status: ACTIVE`.

**Техника, которая подвела:** журнал решений, завязанный на вердикт автомата.
Автомат честно молчал — журнал молчал вместе с ним.

**Следующий ход:** правило — если механизм записи зависит от чужого вердикта,
дублировать запись вручную.

**Адреса:** `ACTIVE/PSD_STEP33_MONITOR.md:42941-42947` ·
`specs_docs/SESSION_START_AUDIT_2026-08-06.md:665-673` · `GENEALOGY.md §9`

---

## Развилки, извлечённые из INSIGHTS.md (раскопки 2026-08-09)

Четыре агента прошли 51 763 строки `q3.lean.aristotle/docs/INSIGHTS.md`
по четвертям и вытащили моменты выбора. Записи ниже — восстановленные,
не современные: писались не в момент решения, а раскопаны позже.

**Помечать восстановленные записи обязательно.** Развилка, записанная задним
числом, слабее записанной в момент выбора: часть причин уже невосстановима,
и это видно по графам «не записано».

<!-- РАСКОПКИ ЗАВЕРШЕНЫ: все четыре четверти пройдены -->

### Развилки, часть 1 (1–13000) — здесь родилась ошибка конуса

**2026-01-26 — τ-shift AtomCone, три ветки.** Численная фальсификация убила конус:
`min Q = -911.2678` при `τ = 1.689`. Выбрана опция B — рефакторить конус.
Опция A отвергнута словами «not credible». `INSIGHTS.md:2726`

**2026-03-05 — бумажный mainline против живого Lean-mainline.** «Репозиторий имеет
структурное рассогласование: статья рекламирует аналитический равномерный маршрут,
а Lean закрывается через legacy PrimeCert gate». Плюс разнобой масштабов:
`t = 3/20`, `t_sym = 3/50`, `t_rkhs = 1`. `INSIGHTS.md:3610`

**★ 2026-03-07 — ВОТ ГДЕ НАШЛИ ОШИБКУ КОНУСА.** «pivot required. Broad `W_K/W`
слишком широк, чтобы оставаться публичной целью RH». Причина численная:
архимедова плотность уходит в минус — `a(1.5) ≈ -0.405`, `a(2) ≈ -0.693`,
`a(3) ≈ -1.098`. Плюс внешняя проверка формулировки Бомбьери–Вейля.
`INSIGHTS.md:1952` · `docs/insights/target_cone_audit_2026_03_07.md`

**2026-03-07 — `A3-pd` разжалован в пользу `PSD-pd`.** «Не закрывает плотный
mainline сам по себе, потому что близкие столкновения и непрерывность A2 убивают
любой равномерный зазор». `INSIGHTS.md:4100`

**★ 2026-03-08 — компактный скалярный маршрут отвергнут, мост Судзуки стал primary.**
Причина дословно: `a_K* ∈ L¹`, значит `â_K*(u) → 0`, а конечная положительная сумма
косинусов по одновременному приближению «возвращается сколь угодно близко к полной
массе бесконечно часто». `INSIGHTS.md:1835`

**2026-03-08 — сырое bulk-тождество структурно ложно.** «Матрица Q3 тёплицева
с постоянной диагональю, а сырая матрица Судзуки в базисе `χ_n[a]` имеет рост
диагонали порядка `log|n|`; это не ошибка знака, не `2π`, не `(2M+1)` и не эффект
шапки». `INSIGHTS.md:4839`

### Развилки, часть 4 (39000–51763) — закрытие истории PSD

**★ 2026-06-25 — пилот на всём выражении и фактическая заморозка.** Правило
остановки записано ЗАРАНЕЕ: «если результат не `PASS_STABLE_MARGIN`, прекратить
дробление и записать решение». Итог — `NOT_RUN_SOURCE_DATA_GAP`, ни один из
четырёх вердиктов. **После этой записи в файле нет ни одной новой записи
Step33A.1-A — фронт PSD обрывается здесь.** `INSIGHTS.md:46549`

**★ 2026-06-25 — Weil-route audit.** Цель переопределена: «классическая цель
Вейля–Бомбьери — положительность на допустимых эрмитовых квадратах `Φ = g * g♯`».
Поиск готовой цепочки дал `OPEN / NOT_FOUND_READY_CHAIN`. `INSIGHTS.md:46603`

**★ 2026-07-10/11 — Route B поднят как ЧЕЛЛЕНДЖЕР, не как mainline.** Дословно:
«H-bridge остаётся официальным mainline; Route B остаётся `CHALLENGER / NOT_RH`».
И прямо про формулировку «старая дорога заморожена»: «это локальный язык кампании,
а не формальное решение». `INSIGHTS.md:46670`

**2026-08-06/07 — условный ресивер против безусловной теоремы.** Выбран кандидат A —
минимальный ресивер с ВИДИМЫМИ обязательствами. Кандидат B отвергнут, потому что
«прячет, какой множитель отвалится». Здесь же контрпример к кофинальности:
`m_k = 2^((k+1)²)`, `N_k = k+1`. `INSIGHTS.md:51424`

### Две сквозные закономерности

**Первая: в эпоху PSD все убийства были бюджетными, не структурными.** Шесть
развилок 22–25.06 закрываются одной формой: объект построен, покрытие есть,
точное рациональное неравенство ложно (`..._width_fail_rat`). **Ни одна ветка не
отвергнута как «неправильная математика»** — только как «не расходуемая».

**Вторая: после 10.07 сменился жанр развилки.** До Route B выбирали между
вычислительными маршрутами (сегментация / Horner / мажоранты). После — между
ФОРМАМИ ТЕОРЕМЫ: условный ресивер с видимыми обязательствами против безусловной
формулировки. Сильную формулировку убивают не контрпримером, а как
«unsupported theorem shape», и публикуют минимальный ресивер, у которого видно,
какая посылка отвалится.



### Главная закономерность раскопок

**Причина теряется ровно на внешних вердиктах.**

```
своя численная диагностика   причина записана дословно и с числами
чужой вердикт (Proshka/Pro)  записана ТОЛЬКО БУКВА выбора: «CHOSEN: S», «CHOSEN: A»
```

Часть 2 (строки 13000–26000): 12 развилок, причина записана в **9**, отсутствует
в **3** — и все три это внешние вердикты, пришедшие через браузер.
Часть 3 (строки 26000–39000): 12 развилок, причина записана во **всех 12**,
отсутствует в **0** — там решения принимались по локальным аудитам.

И это выстрелило дважды: маршруты, выбранные буквой без аргумента, были отменены
собственными численными аудитами через один-два шага (route B signed, route A2
centered receiver). Работа выброшена, потому что аргумент не был записан и не
подвергся проверке.

### Отобранные развилки, часть 2 (13000–26000)

**2026-05-28 — Step33A.1: переклассификация A → B.** Диагностический реплей
символических определений дал `506/529` отказов; худшая запись `(0,22)`:
символический `sum_rad ≈ 4.1593e20` против импортированного радиуса `≈ 3.9490e-17`.
Причина записана. `INSIGHTS.md:15878-15897`

**2026-06-02 — arch source convention: `Q3.a_star` объявлен авторитетным.**
Расхождение на `d=0.00`: Step22 midpoint `2.467e-1` против Lean `a_star` `-7.890e+1`,
рассогласование `79.14`. Вердикт: «source convention issue, not a radius issue».
Причина записана. `INSIGHTS.md:18879-18966`

**2026-06-04 — route B (signed) выбран внешним вердиктом, отменён своим аудитом.**
Причина выбора НЕ ЗАПИСАНА — только «Louise/Pro chose route B». Через шаг
собственная проверка: min eigenvalue `-1.4183` с 13 отрицательными собственными
значениями. Вся ветка signed-receiver выброшена.
`INSIGHTS.md:19191-19257, 19479-19623`

**2026-06-04/05 — `CHOSEN: S` → `CHOSEN: A`.** Обоснование ни за одной буквой не
записано. Понадобился runtime override в `q3_master_goal.md`, чтобы старый текст
из чата не откатывал маршрут после компакции.
`INSIGHTS.md:19808-19825, 19935-19962, 20013-20028`

**2026-06-05 — interval-residual маршрут закрыт количественной оценкой.**
Наблюдаемый линейный тренд разбиений потребовал бы `≈ 3.26e17` разбиений.
Причина записана числом. `INSIGHTS.md:22864-22926`

### Отобранные развилки, часть 3 (26000–39000)

**2026-06-12 — спейсинг Монтгомери–Вона не закрывает E5'.** `pi/min_gap` растёт
от `4.7e3` при K=2 до `1.9e6` при K=3.5, а измеренные эпсилоны остаются `O(1)`.
«Отказ структурный: общий спейсинг видит скученность узлов и теряет конус».
`INSIGHTS.md:32876-32893`

**2026-06-12 — аффинный Selberg-ресивер: FATAL.** Неравенство треугольника
заставляет `||D_theta|| + ||B_theta|| >= ||D_I||` — «алгебраическая теорема
об отсутствии бесплатного сыра». `INSIGHTS.md:32985-33001`

**2026-06-12 — подмена E5' сглаженным остатком: FATAL.** Тождество
`D_I = D_R - B_R` решающее: доказав малость `D_R`, докажешь не то утверждение,
которое потребляет ledger ниже. `INSIGHTS.md:33003-33020`

**2026-06-20 — три kill-сертификата за день.** Fin16 norm-sum ledger (маржа
`-7.88e-25`), поточечный shifted B14 (контрпример в Lean: `|…| = 38227/16384 > 7/6`),
derivmodel (`modelBound ≈ 1.83e-4` против `derivSlope ≈ 3.73e-18`). Все три с
явной границей: убит конкретный ресивер, соседние маршруты оставлены живыми.
`INSIGHTS.md:34462-34487, 35555-35572, 36485-36520`

### Что из этого следует для правила записи

Добавляется восьмая графа для случая внешнего вердикта:

```
**Чей вердикт и его аргумент:** кто решил и ПОЧЕМУ — дословно.
Одной буквы выбора недостаточно.
```

Дважды за июнь буква без аргумента стоила выброшенной ветки.

---

## 2026-08-13 — Goal 058: finite Feshbach закрыт, source-closure не подменять receiver-ом

**Развилка:** после точного complex-Hermitian connector и конечного
Feshbach-разложения выбирать между ещё одним абстрактным Schur/Temple receiver,
увеличением конечной численной лестницы и настоящей source-теоремой о буквальной
CCM-семье.

**Выбрали:** остановить производство конечных receiver-ов и назвать один
source-level фронт `CCM_P59_CofinalTrialLineFeshbachSourceBounds`: он должен на
одной заранее фиксированной связанной шкале сам вывести положительные
even/odd complement floors, `sourceCCMFiniteResidual / min(floors) -> 0`,
odd-mass decay и весь compact P59 budget.

**Почему:** kernel-checked Feshbach-файл уже доказывает точную конечную алгебру
`K-aI = |q><r| + |r><q| + Q(K-aI)Q`; значит неназванных блоков больше нет.
Любая следующая теорема с `hgap`, `hfloor` или residual-decay в binders потребляет
G1/G3 вместо того, чтобы поставлять их. Конечная ячейка не занимает кофинальный
квантор, а prolate-gap без буквального crosswalk относится к другому объекту.

**Что отвергли и почему:** generic gap/Temple transfer — receiver с искомым
знаменателем в предпосылках; новый finite ladder — калибровка без eventual
bound; prolate gap — `C04 SAME_COORDINATES_TWO_LAWS`; полный cofinal theorem как
задача Aristotle — новая аналитическая теория, не bounded formalization.

**Техника:** точная Hermitian four-block decomposition, production Lean audit,
source-locked Proshka review, primary-source scope audit, карточки C04/C07/C09/C10.

**Следующий ход:** бумажно вывести хотя бы одно буквальное inequality для
complement floor из точного разложения CCM entries
`W02 - WR - Prime`; никакого нового Aristotle submission и никакой большой
численной лестницы до source-faithful theorem shape.

**Адреса:**
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean` ·
`GOAL058_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH_CLOSEOUT_2026-08-13.md` ·
`docs/routeB_bus/proshka/PROSHKA_GOAL058_TRUE_SOURCE_CLOSURE_VERDICT_2026-08-13.md` ·
request commit `c0f7af5ae44f8d1defd0bc1365035cea70155c19`.

**Чей вердикт и его аргумент:** Proshka, дословно:
“every remaining bounded algebra theorem is a receiver or is already assigned;
a theorem taking hgap, hfloor, residual_decay, or tracking as binders assumes
the target; the first honest theorem is a new cofinal analytic source theorem.”
Оперативный класс: `NO_SOUND_ARISTOTLE_TASK_AT_THIS_BOUNDARY`. Mythos независимо
завершил: “the wall now has its true name: one arithmetic definiteness estimate
for the divided-difference form of β — the first theorem of this project that
no amount of plumbing can replace.” Его адрес проверен на диске:
`ccmBetaScalar` и `ccmWeilMatFinite_structured_offdiag` действительно существуют;
вывод о положительности пока не существует и не приписан этим identity.

## 2026-08-13 — Goal 058: residual/floor заменён на parity-weighted energy

**Развилка:** требовать на связанной шкале
`source residual / complement floor -> 0`, оценивать projective defect через
Rayleigh excess, либо продолжать прямую конечную лестницу overlap.

**Выбрали:** source-форму
`omega + alpha_plus / Delta_plus`, где odd mass оплачивается отдельно, а
even-sector excess делится только на even gap. Уже существующий Lean consumer
`weighted_projective_defect_le_rayleigh_excess_div_gap` сохраняется; новый
receiver не строится.

**Почему:** multiprecision на буквальных клетках `(2,4),(3,9),(4,16)` при
80/120 digits и трёх quadrature orders подтвердил, что residual/floor растёт
примерно `0.1586, 7.592, 966.75`, тогда как energy/gap остаётся
`0.00212, 0.00206, 0.00150`, а projective defect убывает. Значит сильный
residual observable не отслеживает уже видимое projective улучшение и не
должен определять следующую source-теорему.

**Что отвергли и почему:** residual/floor как следующий theorem shape отвергнут
по finite discriminator, но его eventual ложность не заявлена; direct overlap
ladder остаётся диагностикой без cofinal квантора; `omega = 0` отвергнуто,
потому что текущий `ProlatePair` хранит только Fourier-center identities, а не
полную eigenrelation или exact parity source theorem.

**Техника:** literal-source multiprecision eigensolve, observable comparison,
exact parity-sector decomposition, type-level audit `ProlatePair -> E_star ->
sourceCCMComplexRow`.

**Следующий ход:** на одной coupled schedule получить три source supplier-а:
odd-mass envelope `omega`, even-ground ordering/gap `Delta_plus`, even-sector
Rayleigh-excess envelope `alpha_plus`; finite odd high tail не переоткрывать.

**Адреса:**
`SESSION_PROTOKOLL_2026-08-13.md` ·
`Q3/Proofs/RouteB/WeightedRayleighProjectiveDefect.lean` ·
`Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean` ·
`docs/routeB_bus/proshka/PROSHKA_M1C_PARITY_SECTOR_PREFLIGHT_2026-08-12.md` ·
oracle card `Goal058.G1.ccmBetaComplementFloor`.

**Чей вердикт и аргумент:** локальный выбор Codex, опирающийся на точную форму
из прежнего вердикта Proshka: “The exact odd budget omega must remain in the
bound.” Новый внешний запрос не отправлялся: численный дискриминатор изменил
форму задачи, но ещё не создал source supplier для проверки.



## 2026-08-14 — Goal 058: odd-mass сведена к физическому дефекту отражения

**Развилка:** занулить нечётную массу из evenness исходной пролатной функции,
оставить `omega` абстрактным binder-ом либо найти буквальную физическую ошибку,
которая его оплачивает.

**Выбрали:** точную формулу
`omega = (1/4)||kTrial_m_N-reflectedFiniteTrial||^2` и receiver: любой ambient
пакет с reflection-even retained coefficients ограничивает `omega` квадратом
реального расстояния до него. Исходная комплексная строка не симметризована.

**Почему:** additive parity `h(-x)=h(x)` не даёт multiplicative inversion
`E(h)(u)=E(h)(u^-1)`. Но CCM Lemmas 7.2--7.3 дают отдельный source-shaped
кандидат: `h_lambda -> h` со скоростью `O(lambda^-2)`, а limit `E(h)` уже
inversion-even; интегрирование даёт paper-level squared defect `O(lambda^-1)`.

**Что отвергли и почему:** тяжёлый global Hilbert-basis reflection operator —
лишняя инфраструктура, target build поймал синтаксис/heartbeat и `sorryAx`;
`omega=0` — ложное усиление; beta-only/Krylov shortcut для G1 — убит точным
3x3 counterexample и зависимостью спектра от диагональной арифметики.

**Техника:** exact finite synthesis, coefficient reflection, Bessel,
production direct/target Lean, primary PSWF/CCM source audit.

**Следующий ход:** для G3 доказать inversion/coefficient crosswalk, contraction
через `P_(m,N)` и eventual lower bound для
`||P_(m,N)E(h_lambda)||`; для G1 — literal even-sector Krylov determinant
lower bound и строгий even/odd ground ordering на той же coupled schedule.

**Адреса:**
`Q3/Proofs/RouteB/D0PstarSourceCCMOddMassReflectionDefect.lean` ·
`GOAL058_SOURCE_CCM_ODD_MASS_REFLECTION_DEFECT_CLOSEOUT_2026-08-14.md` ·
oracle card `Goal058.G1.ccmBetaComplementFloor`.

**Граница:** `PASS_EXACT_REPRESENTATION_AND_RECEIVER`; odd-mass decay, G1, G3,
Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: инверсия доведена до коэффициентов и знаменателя

**Развилка:** принять symmetry коэффициентов и denominator floor как новые
гипотезы либо вывести оба механизма на буквальных production-объектах.

**Выбрали:** точный transport `g(u^-1)=g(u) -> <V_-n,g>=<V_n,g>`, его прямой
odd-mass corollary и неравенство
`||<V_0,f>||-||gTrial_m-f|| <= ||gTrial_m_N||`.

**Почему:** первый theorem убирает круговую coefficient-symmetry гипотезу, а
второй точно показывает, какого конкретного source input не хватает для
положительного normalization floor: ненулевого central overlap и ошибки
аппроксимации меньше него.

**Что отвергли и почему:** `TrialNonzero` как количественный floor — это только
строгая ненулевость для каждого индекса; generic inversion-even binder как
закрытие G3 — это receiver без поставщика; симметризацию source row — она
меняет производственный объект.

**Техника:** `du/u -> dx`, отражение `x -> L-x`, exact integer phase,
orthogonal projection и Cauchy--Schwarz; direct/target Lean и `q3_check`.

**Следующий ход:** определить явную polynomial-Gaussian функцию CCM Eq. (7.1),
доказать Poisson/Fourier inversion для `E_star h`, ненулевой central overlap и
реальную Lemmas 7.2--7.3 rate на одной coupled cofinal schedule; G1 отдельно
требует literal even-sector gap arithmetic.

**Адреса:**
`Q3/Proofs/RouteB/D0PstarInversionCoefficientCrosswalk.lean` ·
`GOAL058_INVERSION_COEFFICIENT_DENOMINATOR_CROSSWALK_CLOSEOUT_2026-08-14.md` ·
`GOAL058_SOURCE_CCM_ODD_MASS_REFLECTION_DEFECT_CLOSEOUT_2026-08-14.md`.

**Граница:** `PASS_EXACT_CROSSWALK_AND_FLOOR_BRIDGE`; explicit limit packet,
rate, denominator floor, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: явный CCM-limit и Poisson-инверсия доказаны

**Развилка:** принять Fourier/inversion symmetry предельного пакета как binder,
симметризовать trial либо построить буквальную Eq. (7.1) функцию и вывести всё
в production Lean.

**Выбрали:** `explicitCCMLimitH`, точное
`fourier_explicitCCMLimitH` и
`E_star_explicitCCMLimitH_inv : u>0 -> E_star h u⁻¹ = E_star h u`.

**Почему:** существующий coefficient crosswalk требовал настоящего физического
inversion-even supplier. Абстрактная гипотеза повторяла бы цель, а
симметризация меняла бы source family.

**Что отвергли и почему:** Fourier eigenrelation в binders — receiver;
inversion-even binder — receiver; Hermite-пакет с теми же качествами, но без
буквальной Eq. (7.1) формулы — object drift; объявить этот лист G3 — потерять
реальные Lemma 7.2 rate, central floor и coupled schedule.

**Техника:** Gaussian Fourier transform, second/fourth derivative moments,
cocompact `O(|x|^-2)` decay, exact Fourier scaling, Poisson summation,
even integer sum и square-root rescaling.

**Следующий ход:** source-lock actual normalized two-mode prolate `h_lambda`,
доказать uniform `O(lambda^-2)` к `explicitCCMLimitH`, ненулевой central
overlap и projected denominator floor на одной заранее выбранной `(m,N)`
schedule; параллельный G1 остаётся на quantitative even-sector gap arithmetic.

**Адреса:**
`Q3/Proofs/RouteB/D0PstarExplicitCCMLimitFourier.lean` ·
`GOAL058_EXPLICIT_CCM_LIMIT_FOURIER_POISSON_CLOSEOUT_2026-08-14.md` ·
CCM `literature/zotero/H8ULBMAL/fulltext.md:1256-1308,1410-1468`.

**Чей вердикт и его аргумент:** локальный kernel-checked closeout Codex; новый
внешний запрос не нужен, потому что выбранный supplier прошёл все production
валидаторы. Предыдущий source audit остаётся ограничителем: paper rate ещё не
экспортирован на текущую Lean family.

**Граница:** `PASS_EXACT_LIMIT_PACKET_AND_INVERSION`; prolate rate, central
floor, coupled schedule, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: limit-anchor положителен, найдена настоящая G3-стена

**Развилка:** считать denominator floor отдельной source-гипотезой и искать
bare `ProlatePair` constructor либо сначала доказать положительность точного
limit-anchor и проверить, полисит ли record настоящие prolate-моды.

**Выбрали:** доказать на буквальном Eq. (7.1) пакете
`re(E_star h u)>0` для `u>=1` и отдельно проверить, выражает ли production
`ProlatePair` настоящие prolate-моды.

**Результат:** положительность прошла kernel-check. Mythos подтвердил аудит:
текущий record хранит parity/support/norm/integrals/centre identities, но не
eigenfunction equation и не lowest-even selection. Поэтому bare constructor
может вернуть не-моды.

**Почему:** denominator floor теперь можно выводить переносом от
конкретного положительного limit-anchor, но сначала нужны source-locked actual
modes и опубликованная CCM Lemma 7.2 rate. До появления actual-mode predicate
честной Aristotle-задачи нет.

**Что отвергли и почему:** bare `ProlatePair` constructor — record допускает
не-моды; independent floor binder — повторяет искомый source input; raw
`PairIndex` schedule как production closure — не даёт `CentralIndex` и
selected nonzero transform; Aristotle submit — success predicate пока можно
обмануть не-модой.

**Техника:** exact factorization
`(pi/2)*x^2*(2*pi*x^2-3)`, positivity при `x>=1`, summability transport с
integer series, `tsum_pos`, direct/target/full Lean и public axiom audit;
отдельно browser-verdict Mythos и локальная проверка type surface.

**Следующий ход:** внешний source-locked actual-mode predicate поверх
неизменённого `ProlatePair`, постоянный loose-pair falsifier и analysis-ledger
для Lemma 7.2. G1 отдельно остаётся на новом количественном theorem target для
divided-difference beta формы.

**Адреса:**
`Q3/Proofs/RouteB/D0PstarExplicitCCMLimitFourier.lean` ·
`GOAL058_EXPLICIT_CCM_LIMIT_POSITIVE_ANCHOR_CLOSEOUT_2026-08-14.md` ·
`MYTHOS_VERDICT_GOAL058_G1_G3_ACTUAL_SOURCE_CLOSURE_2026-08-14.md` ·
`TASK_2026-08-14_goal058_g3_prolate_rate_floor.md`.

**Граница:** `PASS_EXACT_LIMIT_POSITIVE_ANCHOR / SOURCE_OBJECT_GAP`; G1, G3,
Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: actual-mode смысл заперт отдельным predicate

**Развилка:** усиливать production `ProlatePair`, оставить типовую дыру или
описать source meaning внешним predicate и посадить постоянный falsifier.

**Выбрали:** `IsActualProlateModePair` поверх неизменённого record плюс
`looseProlatePairPlant_not_actual`.

**Почему:** downstream API остаётся стабильным, но bare inhabitation больше
нельзя выдать за construction настоящих degree-0/4 prolate-мод.

**Что отвергли и почему:** новые поля в `ProlatePair` — parallel strengthened
family и API churn; abstract `Actual` binder без literal equations — не
полисит source; Aristotle submit — existence/selection всё ещё analysis-scale.

**Техника:** literal prolate ODE, restricted finite-Fourier eigenrelations,
positive phase, orthogonality, eigenvalue ordering, Sturm interior zero counts;
явный normalized interval-indicator record plant и exact rejection theorem.

**Следующий ход:** доказать существование/selection production pair,
удовлетворяющего predicate, затем формализовать published CCM Lemma 7.2 rate.

**Адреса:**
`Q3/Proofs/RouteB/ProlateActualModeSourceLock.lean` ·
`GOAL058_ACTUAL_PROLATE_MODE_SOURCE_LOCK_CLOSEOUT_2026-08-14.md` ·
`PSWF_STURM_LIOUVILLE_SOURCE_DOSSIER.md`.

**Граница:** `PASS_SOURCE_OBJECT_LOCK_AND_WEAK_RECORD_PLANT`; actual-mode
existence, Lemma 7.2, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: constructor audit отделил готовые детали от новой математики

**Развилка:** пытаться ещё раз собрать actual prolate pair из текущих generic
операторных файлов либо адресно проверить наличие спектрального constructor.

**Выбрали:** адресный capability audit Mathlib, текущих prolate-файлов и
mode-four coefficient backend с отдельным I/O-ledger для G1/G3.

**Почему:** готового constructor нет. Mathlib имеет predicate компактности,
но compact self-adjoint spectral theorem помечен TODO; project-файлы закрывают
intertwining/regularity/nonvanishing и mode-four recurrence, но не PSWF
existence, ordered degree-0/4 selection и Lemma 7.2 rate.

**Что отвергли и почему:** commutator-only и beta-only G1 shortcuts убиты
exact plant и `N=1` factorization; ещё один conditional prolate receiver и
Aristotle submit отвергнуты, потому что actual source constructor отсутствует.

**Техника:** full-repo declaration audit, Mathlib Spectrum TODO inspection,
exact commutator plant, source-shaped `N=1` characteristic factorization,
direct/target/full Lean, `q3_check`, RouteB check и strict startup.

**Следующий ход:** formalize singular Sturm--Liouville/PSWF construction либо
Ferrers-series convergence + ODE + endpoint flux + zero count, затем Lemma 7.2
и denominator floor; G1 параллельно требует literal CCM quantitative
gap/sector-order и same-trial cofinal tracking.

**Адреса:**
`GOAL058_G1_G3_CURRENT_PROBLEM_IO_LEDGER_2026-08-14.md`.

**Граница:** `G1_OPEN / G3_OPEN / TWO_FALSE_SHORTCUTS_KILLED`; Route B остаётся
`CHALLENGER / NOT_RH`.

## 2026-08-14 — Goal 058: recurrence row стал настоящей mode-four ODE-функцией

**Развилка:** оставить coefficient backend как формальную рекурсию либо
доказать, что её бесконечный Ferrers-ряд реально сходится, дважды
дифференцируется и удовлетворяет source prolate ODE.

**Выбрали:** точный путь через geometric tail splice, sharp Legendre bound,
две законные termwise differentiation и отдельные absolutely summable
three-band shifts с явной обработкой нулевой строки.

**Почему:** это минимальный локально доказуемый source theorem за стеной
actual-mode constructor. Он превращает существующий matching root в реальную
нормированную `C2`-внутри функцию, не требуя изобретать compact spectral
theorem и не подменяя existence новым binder.

**Что отвергли и почему:** формальную перестановку несуммируемых рядов,
`l2 -> l1` shortcut и пропуск `q=0` отвергли как ложные; объявить полученную
функцию degree-four PSWF нельзя без endpoint/zero-count/order selection и
finite-Fourier eigenrelation.

**Техника:** coefficientwise shifted-Legendre ODE; energy monotonicity;
geometric polynomial moments; uniform derivative majorants; legal `tsum`
one-step shifts; exact three-band recurrence cancellation; direct/target/full
Lean and public axiom audit.

**Следующий ход:** физическое scaling/endpoint realization и точная
third-even selection для mode four, затем mode zero и restricted Fourier
relations; только после этого CCM Lemma 7.2 и denominator floor.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4OrdinaryLegendreIntervalBound.lean` ·
`Q3/Proofs/RouteB/D0Mode4FerrersCoefficientAbsoluteSummability.lean` ·
`Q3/Proofs/RouteB/D0Mode4FerrersInteriorRegularity.lean` ·
`Q3/Proofs/RouteB/D0Mode4FerrersProlateDifferentialEquation.lean` ·
`GOAL058_MODE4_FERRERS_PROLATE_ODE_CLOSEOUT_2026-08-14.md`.

**Граница:**
`MODE4_FERRERS_ODE_PROVED_MODE0_SELECTION_FOURIER_AND_LEMMA72_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: unrestricted Sturm head сужен до одного nodal interval

**Развилка:** пытаться одним Wronskian-доказательством получить ноль
higher-parameter solution между любыми двумя нулями lower solution либо
сначала замкнуть точный comparison kernel на одной последовательной nodal
interval.

**Выбрали:** точный theorem head
`exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval` с
`hNodal`, который запрещает внутренние нули lower solution между endpoints.

**Почему:** на одной nodal interval обе функции можно независимо привести к
положительному знаку, а производная weighted Wronskian равна буквально
`(LambdaLo - LambdaHi) * u * v`. Это минимальный theorem, который потребляет
уже доказанные actual derivatives, common potential и simple endpoint zeros.

**Что отвергли и почему:** unrestricted head не ложен, но не является одним
bounded Wronskian leaf: ему отдельно нужны compact zero-set finiteness и
consecutive-subpair extraction. Разные `mProject` отвергнуты, потому что тогда
potential не сокращается. Повторный Aristotle run отвергнут после локального
kernel proof как платный дубликат без нового evidence.

**Техника:** common-potential weighted Wronskian, continuous-nonzero
constant-sign lemma, endpoint derivative signs from `HasDerivAt` plus simple
zeros, `StrictAntiOn` contradiction; direct Lean, target/full builds,
`q3_check`, forbidden scan и public axiom audit.

**Следующий ход:** доказать compact-interior finiteness/consecutive nodal-pair
extraction, затем source-faithful index-4 oscillation/selection; независимо
остаются mode zero, physical scaling, finite-Fourier identification, Lemma 7.2
и denominator floor.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean` ·
`GOAL058_G3_STURM_NODAL_COMPARISON_PROSHKA_VERDICT_2026-08-14.md` ·
`GOAL058_G3_STURM_NODAL_COMPARISON_CLOSEOUT_2026-08-14.md` ·
`GOAL058_G3_PSWF_INDEX_SOURCE_PIN_PACKET_2026-08-14.md`.

**Чей вердикт и его аргумент:** Прошка,
`REPAIR_G3_STURM_COMPARISON_TO_NODAL_INTERVAL`: «The unrestricted statement
between any two distinct lower-parameter zeros is not false, but it needs a
separate compact-zero-set and consecutive-subpair layer. A single bounded
Wronskian/Picone proof needs the lower solution to have a fixed sign between
the two endpoint zeros.» Codex принял ремонт и замкнул его локальным Lean
proof без Aristotle submission.

**Граница:**
`G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON_PROVED`; compact zero finiteness,
ordered `psi4`, matching root existence, mode zero, Fourier, Lemma 7.2, G1,
G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: compact zero selection снимает nodal guard

**Развилка:** просить внешний глобальный zero-count theorem либо сначала
использовать уже доказанную простоту каждого interior zero для локального
компактного выбора соседней пары.

**Выбрали:** kernel-checked цепочку `simple zero -> isolated zero -> discrete
compact zero set -> finite set -> first zero to the right`, после чего применён
готовый Sturm theorem на автоматически выбранной nodal interval.

**Почему:** unrestricted comparison между любыми двумя lower zeros требует не
глобального подсчёта, а лишь существования одной последовательной подпары.
`HasDerivAt.eventually_ne` даёт точную локальную изоляцию, а
`IsCompact.finite` превращает её в конечность на внутреннем `Icc`.

**Что отвергли и почему:** новый zero-count binder или source assumption не
вводились; они скрыли бы оставшуюся index-4 selection wall. Внешний запрос
Прошке/Aristotle не отправлялся, потому что после последовательного
knowledge preflight лист полностью закрылся локально.

**Техника:** subtype compactness, closed preimage of `{0}`, punctured
neighborhood from nonzero derivative, discrete-set finiteness, `Finset.min'`
и повторное использование exact weighted-Wronskian consumer.

**Следующий ход:** доказать source-faithful oscillation/order selection,
которая связывает matching root с ordered degree-four PSWF; затем построить
mode zero и закрывать physical scale, finite Fourier, Lemma 7.2 и denominator
floor. Параллельный G1 blocker не изменился.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4FerrersCompactZeroSelection.lean` ·
`ACTIVE/pipeline/oracle_questions/2026_08_14_goal058_g3_compact_zero_selection.md` ·
`GOAL058_G3_COMPACT_ZERO_SELECTION_CLOSEOUT_2026-08-14.md`.

**Чей вердикт и его аргумент:** локальный Codex/Lean verdict. Четыре
последовательных `q3_docs` запроса не нашли готового project supplier, но
указали на уже доказанные `interior_zero_simple` и Sturm head; Mathlib дал
ровно два недостающих generic primitive-а. Kernel принял финальную сборку.

**Граница:**
`G3_MODE4_UNRESTRICTED_STURM_COMPARISON_PROVED`; global zero count, ordered
`psi4`, matching root existence, mode zero, Fourier, Lemma 7.2, denominator
floor, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058: mode-four Ferrers physical scaling

**Развилка:** ждать полного source `psi4` crosswalk либо отдельно закрыть уже
source-locked алгебраический транспорт dimensionless Ferrers solution на
физическое окно.

**Выбрали:** bounded leaf `x=u/sqrt(mProject)` с actual first/second derivative
interfaces, physical `C2` и буквальным `PW_lambda` ODE.

**Почему:** этот транспорт не зависит от пока отсутствующего ordered-mode
selection и не требует нового hypothesis. Он одновременно проверяет scale
`lambda=sqrt(mProject)`, potential `(2*pi*lambda*u)^2` и eigenvalue
`Lambda+mode4JacobiG mProject`.

**Что отвергли и почему:** не объявляли root-conditioned physical row готовым
`h4`: matching-root existence, index 4 и finite-Fourier phase по-прежнему не
доказаны. Внешний review не отправлялся, потому что весь leaf скомпилировался
локально после последовательного knowledge preflight.

**Техника:** `ContDiffOn.comp`, два exact `HasDerivAt.comp` chain rules,
`sqrt(m)^2=m`, field normalization и повторное использование принятого
dimensionless ODE.

**Следующий ход:** exact Route-C bridge `classical regular psi4 Legendre row ->
current minimal right tail -> mode4RootFunction = 0`, затем normalization
uniqueness; независимо нужен mode-zero companion.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4FerrersPhysicalProlateScaling.lean` ·
`ACTIVE/pipeline/oracle_questions/2026_08_14_goal058_g3_mode4physicalscale_mode_four_ferrers_sqrt_m_sqrt_m_pw_lambda_ode.md` ·
`GOAL058_G3_MODE4_PHYSICAL_SCALE_CLOSEOUT_2026-08-14.md`.

**Чей вердикт и его аргумент:** локальный Codex/Lean verdict. Параметрическая
формула была заранее source-pinned в принятом architecture memorandum; direct
Lean проверил, что обе derivative scale factors и potential transport
совпадают буквально, а не только размерностно.

**Граница:**
`G3_MODE4_PHYSICAL_SCALE_PROVED`; source `psi4` crosswalk, ordered index 4,
matching-root existence, mode zero, finite Fourier, Lemma 7.2, denominator
floor, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058 G1: checker заперт на буквальном complex trial complement

**Развилка:** продолжать искать простоту из `ccmBeta`/rank-two commutator либо
сначала зафиксировать проверяемый положительный floor ровно на complement
буквальной complex P59 trial line.

**Выбрали:** exact Gram-certificate checker
`Q(K-aI)Q - beta Q = R^*R`, `beta>0`, специализированный на неизменённые
`sourceCCMFiniteMatrix`, `sourceCCMComplexRow` и source Rayleigh value.

**Почему:** это первичный G1 объект из принятой архитектуры: положительный floor
сразу исключает второй ground direction и даёт количественный знаменатель для
уже существующего Feshbach/projective слоя. При этом checker не выдаёт
сертификат за математику его существования.

**Что отвергли и почему:** beta-only и commutator-only простота отвергнуты
навсегда точным `Fin 3` all-ones plant. Lean одновременно проверяет
source-shaped rank-two commutator и явный второй ground vector, ортогональный
выбранной комплексной unit trial line; поэтому любой `beta>0` и любой такой
Gram certificate невозможны.

**Техника:** complex Hermitian projection/complement algebra,
`Matrix.posSemidef_conjTranspose_mul_self`, exact rational-complex falsifier,
direct/target Lean, `q3_check`, forbidden-token/claim scan и public axiom audit.

**Следующий ход:** `Goal058.G1.CofinalComplementFloor` — построить для
буквальной CCM-арифметики finite-head Gram certificate и Lean-checked uniform
tail, дающие явный положительный floor на одной precommitted cofinal family;
параллельно дождаться отдельного owner send approval для уже byte-locked G3
Mythos crosswalk request.

**Адреса:**
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementFloor.lean` ·
`ACTIVE/pipeline/oracle_questions/2026_08_14_goal058_g1_literal_complex_trial_complement_floor_gram_checker.md` ·
`GOAL058_G1_LITERAL_COMPLEMENT_FLOOR_GRAM_CHECKER_CLOSEOUT_2026-08-14.md`.

**Чей вердикт и его аргумент:** локальный Codex/Lean verdict. Три
последовательных `q3_docs` запроса не нашли готового literal supplier; kernel
принял exact Gram soundness, а тот же checker отверг exact commutator collapse.

**Граница:**
`G1_LITERAL_COMPLEMENT_FLOOR_GRAM_CHECKER_PROVED_COFINAL_LITERAL_CCM_ARITHMETIC_AND_UNIFORM_TAIL_FLOOR_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058 G1: finite spectral receiver собран до literal source wrapper

**Развилка:** после exact Gram-checker продолжать смешивать source-поставку
`beta` с generic спектральными последствиями либо сначала kernel-check замкнуть
весь receiver и оставить один чистый arithmetic blocker.

**Выбрали:** построить unit minimum Hermitian eigenpair, перенести
trial-complement floor на ортогональное дополнение настоящего ground vector,
доказать separation остальных eigenvalues и squared-residual projective
tracking, затем специализировать всё на literal CCM source objects.

**Почему:** это убирает неопределённость из следующего шага. Теперь любой
будущий `sourceCCMComplexTrialComplementFloor` немедленно даёт ровно тот finite
gap/tracking пакет, который требует архитектура; повторный поиск generic
min--max или residual lemma больше не нужен.

**Что отвергли и почему:** не добавляли ground eigenpair, simplicity или gap
как source assumption и не называли условный receiver G1. Положительный
`beta`, finite-head certificate, uniform tail и cofinal schedule всё ещё надо
получить из буквальной CCM-арифметики.

**Техника:** Mathlib Hermitian eigenbasis, explicit two-plane cancellation,
codimension-one eigenvector separation, orthogonal residual decomposition,
finite Hilbert Cauchy--Schwarz и source-faithful wrapper.

**Следующий ход:** `Goal058.G1.CofinalComplementFloor.FiniteHead` плюс
`Goal058.G1.CofinalComplementFloor.UniformTail` на одной precommitted schedule;
затем проверить, что same-family squared residual делится на этот floor с
нужным decay.

**Адреса:**
`Q3/Proofs/RouteB/HermitianUnitMinimumEigenpair.lean` ·
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementRayleigh.lean` ·
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialResidualTracking.lean` ·
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementSpectral.lean` ·
`ACTIVE/pipeline/oracle_questions/2026_08_14_goal058_g1_cofinal_complement_floor_spectral_receiver.md`.

**Чей вердикт и его аргумент:** локальный Codex/Lean verdict. Три адресных
запроса не нашли complete project supplier; kernel принял всю finite chain и
literal wrapper с public axioms только
`[propext, Classical.choice, Quot.sound]`.

**Граница:**
`FINITE_CELL_CONDITIONAL_RECEIVER_PASS`; stop-code не меняется:
`G1_LITERAL_COMPLEMENT_FLOOR_GRAM_CHECKER_PROVED_COFINAL_LITERAL_CCM_ARITHMETIC_AND_UNIFORM_TAIL_FLOOR_MISSING`.
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058 G3: exact Schur parameter order и simple-root kernel

**Развилка:** снова принимать endpoint inertia/count как binder либо сначала
доказать на буквальном infinite-tail Schur object две внутренние опоры
корневой лестницы: направление движения по `Lambda` и простоту ядра в нуле.

**Выбрали:** доказать монотонность finite backward tails и их exact limit,
затем точное разложение разности Hermitian Schur matrices в
`(Lambda_2-Lambda_1)I` плюс неотрицательную диагональную поправку. Отдельно
через несовместимость двух соседних нулевых continuant-ов, обратимость
principal minor и rank-nullity доказано ровно одномерное ядро при любом exact
matching root.

**Почему:** это реальные свойства production root backend, а не ещё один
receiver. Они снимают две неопределённости source-faithful index ladder:
матрица строго опускается при росте параметра, а каждый нулевой crossing имеет
nullity one.

**Что отвергли и почему:** не ввели monotone eigenvalues, simple root,
endpoint count или PSWF index как hypotheses. Aristotle submission был
подготовлен как резерв для tridiagonal kernel leaf, но не отправлен: более
короткий minor/rank proof замкнулся локально.

**Техника:** monotone continued-fraction step на contraction box, переход
порядка через два `Tendsto`, exact diagonal matrix identity,
`Matrix.PosSemidef.diagonal`, трёхчленная continuant recurrence,
`cRank_submatrix_le`, rank-nullity и `exists_mulVec_eq_zero_iff`.

**Следующий ход:** source-producing endpoint inertia и формальный
one-direction inertia jump для одной precommitted root ladder; затем выбрать
третье even crossing и состыковать его с pinned `psi_4`. Mode zero, restricted
finite Fourier, Lemma 7.2 и denominator floor остаются отдельными узлами.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4JacobiRightTailMonotonicity.lean` ·
`Q3/Proofs/RouteB/D0Mode4SchurSpectralParameterOrder.lean` ·
`Q3/Proofs/RouteB/D0Mode4SchurSimpleKernel.lean` ·
`docs/Codex/TASK_2026-08-14_goal058_g3_prolate_rate_floor.md`.

**Чей вердикт и его аргумент:** локальный Codex/Lean verdict. Mathlib не
содержит готовой tridiagonal simple-spectrum или numbered-eigenvalue
monotonicity lemma, но его exact matrix rank и PSD primitives приняли прямую
сборку. Все public heads имеют axioms только
`[propext, Classical.choice, Quot.sound]`.

**Граница:**
`SCHUR_PARAMETER_DROP_AND_SIMPLE_ROOT_PROVED_ENDPOINT_INERTIA_LADDER_AND_INDEX4_SELECTION_MISSING`;
matching-root existence, indexed `psi4`, mode zero, finite Fourier, Lemma 7.2,
denominator floor, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058 G3: строгий Schur drop даёт скачок отрицательного индекса

**Развилка:** переносить полный внешний слой `posIndex`/Sylvester, принимать
монотонность занумерованных eigenvalues как binder либо доказать ровно тот
subspace theorem, который потребляет уже готовый буквальный Loewner drop.

**Выбрали:** узкий kernel-checked theorem
`hermitian_negativeCount_add_nullity_le_of_strict_drop`, затем его
специализацию к exact mode-four Schur family и corollary в simple root:
`n_-(A(Lambda)) + 1 <= n_-(A(LambdaHi))` при `Lambda < LambdaHi`.

**Почему:** strict drop делает всё спектральное подпространство исходной
матрицы с eigenvalue `<= 0` отрицательно определённым для новой матрицы. Его
размерность буквально равна `negativeCount + nullity`, поэтому Sylvester
даёт скачок без выбора или непрерывного отслеживания eigenvalue labels.

**Что отвергли и почему:** полный перенос семи файлов `RHLinalg` отвергнут как
лишняя поверхность; numbered-eigenvalue monotonicity отвергнута, потому что её
нет в текущем Mathlib; endpoint counts `2/3` и index-4 identification не были
введены hypotheses под видом source proof. Внешний запрос не отправлялся:
локальная точная ветка ещё давала проверяемую дельту.

**Техника:** spectral functional calculus через явную Hermitian
diagonalization, rank spectral projector, positive/negative parts,
negative-definite subspace injection, rank-nullity, literal Schur PSD drop и
ранее доказанная nullity-one root theorem. Архитектура subspace-index proof
атрибутирована `zeta-23-lean` commit `3635e74`, Apache-2.0; реализация узкая и
переписана под текущий real-Hermitian contract.

**Следующий ход:** получить source-producing начальный endpoint count и
достаточную ordered crossing/existence ladder, чтобы третий even crossing был
не просто корнем, а pinned `psi_4`; затем замкнуть DLMF row/function identity.
Mode zero, finite Fourier, Lemma 7.2 и denominator floor остаются отдельными
узлами; G1 требует literal cofinal complement floor.

**Адреса:**
`Q3/Proofs/RouteB/D0HermitianNegativeIndexDrop.lean` ·
`Q3/Proofs/RouteB/D0Mode4SchurRootQuadraticCrossing.lean` ·
`Q3/Proofs/RouteB/D0Mode4SchurSpectralParameterOrder.lean` ·
`Q3/Proofs/RouteB/D0Mode4SchurSimpleKernel.lean` ·
`docs/cartographer/lean_bases.yaml` ·
`docs/Codex/TASK_2026-08-14_goal058_g3_prolate_rate_floor.md`.

**Чей вердикт и его аргумент:** локальный Codex/Lean verdict. Четыре exact
shelf query и три semantic query не нашли endpoint-count supplier; audit
зарегистрированной базы нашёл корректный Sylvester subspace mechanism.
Текущий Lean kernel принял general jump, literal family specialization и
simple-root corollary с public axioms только
`[propext, Classical.choice, Quot.sound]`.

**Граница:**
`ROOT_QUADRATIC_AND_ONE_DIRECTION_INERTIA_JUMP_PROVED_SOURCE_ENDPOINT_COUNTS_AND_INDEX4_SELECTION_MISSING`;
matching-root/indexed-`psi_4` existence, mode zero, restricted finite Fourier,
Lemma 7.2, denominator floor, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058 G3: точные корни получили инъективную инерционную метку

**Развилка:** после одностороннего скачка сразу вводить номер литературного
`psi_4` как внешний binder либо сначала доказать всё, что уже следует для
любых двух буквальных корней Schur family.

**Выбрали:** доказать строгую эквивалентность порядка корней и порядка
`negativeCount`, а затем равенство корней из равенства их инерционных меток.

**Почему:** simple root даёт скачок минимум на единицу, а тот же аргумент в
обратном порядке исключает несовпадение параметров при равных counts. Теперь
каждый построенный source root можно честно маркировать инерцией без
continuous eigenvalue indexing.

**Что отвергли и почему:** не объявляли существование трёх even roots,
endpoint counts или соответствие count-two корня с `psi_4`. Pinned
Bonami--Karoui/Osipov источники дают ordered differential spectrum, но Lean
crosswalk от него к существованию Schur roots всё ещё не построен.

**Техника:** exact simple-root negative-index jump, линейный порядок
спектрального параметра и натуральная арифметика. Никакой новой спектральной
гипотезы, численного endpoint или конечной аппроксимации.

**Следующий ход:** source-producing construction/extraction of the ordered
even roots (or an exact ordered-spectrum-to-Schur-root crosswalk), then prove
that the count-two root is the pinned degree-four coefficient row. Separately,
G1 still needs the literal cofinal complement floor.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4SchurRootInertiaLabel.lean`.

**Чей вердикт и его аргумент:** локальный Codex/Lean verdict. Три exact shelf
query не нашли готового root-label theorem; Lean kernel принял обе public
теоремы с axioms только `[propext, Classical.choice, Quot.sound]`.

**Граница:**
`SCHUR_ROOT_INERTIA_LABEL_INJECTIVE_SOURCE_ROOT_EXISTENCE_ENDPOINT_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING`;
indexed-`psi_4`, mode zero, restricted finite Fourier, Lemma 7.2, denominator
floor, G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-14 — Goal 058 G3: post-inertia endpoint-count proposal rejected

**Развилка:** материализовать Mythos placeholders и пытаться доказать `0/3`
endpoint counts либо сначала проверить их против буквального infinite-tail
Schur object и текущего source program.

**Выбрали:** восстановить source lock точными вложениями в существующем чате и
получить повторный Proshka judge verdict. Все четыре SHA совпали; strict startup
и Route status были зелёными.

**Почему:** literal object имеет binders `(mProject : ℕ) (Λ : ℝ) (K : ℕ)`, а
четыре имени Mythos отсутствуют. Production receiver требует moving endpoints,
`ΛUpper ≤ 20` и counts `2/3`; `20 + ε` и `0/3` относятся к другой программе.

**Что отвергли и почему:** placeholder endpoint theorem и Gershgorin-Aristotle
task отвергнуты. Bonami--Karoui локализует classical differential eigenvalues,
но без независимого classical-spectrum-to-literal-Schur-inertia crosswalk это
не доказывает negative count exact Schur complement.

**Техника:** byte-exact source-lock recovery в том же живом Proshka-чате,
проверка четырёх SHA-256, literal declaration/arity audit и сопоставление
предложенных endpoint counts с binders production Schur matrix и уже
доказанным receiver `counts_two_three`.

**Следующий ход:** read-only source packet для
`MODE4_CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK`, включая
доказательство точного finite-split offset. Aristotle не авторизован.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_POST_INERTIA_SOURCE_CROSSWALK_JOINT_REQUEST_2026-08-14.txt` ·
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_POST_INERTIA_SOURCE_CROSSWALK_MYTHOS_VERDICT_2026-08-14.md` ·
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_POST_INERTIA_SOURCE_CROSSWALK_PROSHKA_SOURCE_LOCK_STOP_2026-08-14.md` ·
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_POST_INERTIA_SOURCE_CROSSWALK_PROSHKA_VERDICT_2026-08-14.md`.

**Чей вердикт и его аргумент:** Proshka:
`REJECT_PLACEHOLDER_ENDPOINT_COUNTS_REQUIRE_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK`.
Все четыре SHA-256 совпали; предложенные endpoints и counts относятся не к
literal production object, а Bonami--Karoui без независимого
classical-spectrum-to-Schur-inertia crosswalk не доказывает его negative count.

**Граница:**
`CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — Goal 058 G3: DLMF characteristic equation получила точный l2-смысл

**Развилка:** продолжать finite inertia/count ladder без бесконечного
solution-set theorem либо сначала материализовать независимый Jacobi carrier:
точная DLMF characteristic equation эквивалентна существованию именно
нормированной square-summable recurrence row.

**Выбрали:** `JACOBI_INERTIA` в source-faithful форме. Сначала доказан
бикондиционал между pole-safe DLMF 30.3.5 equation на split `2*(K-1)` и
квадрат-суммируемостью parity-normalized left row. Следующая отдельная теорема
должна связать этот l2-spectrum с independently indexed even spectrum.

**Почему:** finite counts без такого identification только переименовывают
отсутствующий solution-set theorem. Независимые literal left/right branches и
infinite contraction-selected ratio уже существовали, поэтому l2 seam был
минимальным theorem с настоящим downstream consumer.

**Что отвергли и почему:** полный differential-spectrum import отложен как
слишком широкий первый шаг; finite terminal tail отвергнут как surrogate;
переход через `mode4RootFunction`, arbitrary coefficient row, endpoint counts
и finite negative-count stability запрещён как circular или недостаточный.

**Техника:** literal three-term recurrence, exact split splice, invariant-box
geometric summability, positive diagonal symmetrization и private
discrete-Wronskian uniqueness для двух square-summable Hermitian tails.

**Следующий ход:** source theorem
`mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_finiteLimitSpectrum`, затем
strict ordered carrier и endpoint separators. Параллельный G1 требует actual
degree-0/4 pair, CCM Lemma 7.2 и cofinal full-complement floor.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean` ·
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DLMF3035_L2_SOLUTION_CROSSWALK_CLOSEOUT_2026-08-15.md` ·
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G1_G3_POST_DLMF_CHARACTERISTIC_PROSHKA_VERDICT_2026-08-14.md`.

**Чей вердикт и его аргумент:** Proshka выбрала `JACOBI_INERTIA`: сначала
`characteristic equation <-> normalized parity-boundary recurrence row is
square-summable`, потому что одна inertia/count-jump лестница без l2-spectral
identification стену не сокращает. Codex локально закрыл exact head; Aristotle
не вызывался.

**Граница:**
`G3_L2_CHARACTERISTIC_CROSSWALK_PROVED_FINITE_LIMIT_SPECTRUM_SOURCE_THEOREM_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — Goal 058 G3: полный spectral iff сужен до честного направления

**Развилка:** принять Mythos production-domain iff и отправить отдельный
`GrowthDichotomy` в Aristotle либо проверить, действительно ли count ladder
пересекает singular carrier endpoint в обе стороны.

**Выбрали:** после byte-locked Proshka judge оставить только направление
`normalized l2 row → literal root → finite-limit carrier`. Оно использует
локальный Schur count jump и convergence одного фиксированного finite
eigenvalue index, поэтому не требует глобального carrier tail.

**Почему:** полный iff скрывал пять проблем: несуществующий threshold,
вакуумный separation binder, дублирующий growth leaf, отсутствие carrier
growth и круг на `det = 0` ровно в carrier endpoint. Односторонний proof эти
проблемы не переименовывает.

**Что отвергли и почему:** Mythos `GrowthDichotomy` отвергнут как duplicate:
новый l2 crosswalk уже доказывает recessive-tail summability, исключает
nonmatching dominant branch и даёт square-summable uniqueness. Aristotle
`NOT_READY`.

**Техника:** l2/characteristic biconditional, exact split root adapter,
one-dimensional literal Schur kernel, quadratic crossing, два nonsingular
endpoint count transports, full finite DLMF spectrum crosswalk и pinching
fixed-index limit.

**Следующий ход:** Codex-local assembly
`mode4DLMF3035EvenLeftCoefficient_sqSummable_imp_exists_finiteLimitSpectrum`
с `Λ < 20`. После него отдельная reverse wall:
`mode4ClassicalEvenEigenvalue_eq_imp_literalSchur_det_eq_zero_of_lt_twenty`.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_PRODUCTION_SPECTRAL_IFF_PROSHKA_JUDGE_REQUEST_2026-08-15.txt` ·
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/PROSHKA_VERDICT_GOAL058_G3_PRODUCTION_SPECTRAL_IFF_2026-08-15.md`.

**Чей вердикт и его аргумент:** Proshka выбрала
`B — PRODUCTION_ROOT_TO_CARRIER_ONE_DIRECTION_FIRST`: локальный count jump
фиксирует один finite eigenvalue index и пропускается к его пределу; обратное
направление всё ещё требует singular-endpoint local-count contradiction.

**Граница:**
`G3_ROOT_TO_FINITE_LIMIT_CARRIER_DIRECTION_READY_CARRIER_TO_LITERAL_ROOT_SINGULAR_ENDPOINT_BRIDGE_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — Goal 058 G3: singular endpoint закрыт, spectral iff доказан

**Развилка:** остановиться после выбранного Прошкой направления
`normalized l2 row -> finite-limit carrier` и вынести reverse endpoint наружу
либо проверить, закрывается ли точная стена уже имеющимися continuity,
count-stability и fixed-index convergence suppliers.

**Выбрали:** сначала доказать точный Proshka-head, затем локально закрыть
`carrier j = Lambda < 20 -> det literalSchur(Lambda) = 0` и скомпоновать полный
production-domain iff.

**Почему:** обратная стена была уже сведена к одному falsifiable contradiction.
При `det != 0` Schur negative count локально постоянен с обеих сторон, но
convergence одного и того же `j`-го finite eigenvalue заставляет нижний count
быть `<= j`, а верхний `>= j+1`. Никакой новой source hypothesis не требуется.

**Что отвергли и почему:** `GrowthDichotomy` отвергнут как duplicate уже
доказанной l2/recessive uniqueness; invented threshold, vacuous separation
binder, assumed singularity, endpoint counts и `j=2` не вводились.

**Техника:** независимый DLMF characteristic/l2 crosswalk, Schur root inertia
label, непрерывность literal Schur matrix, local negative-count stability,
finite-to-literal count transport и fixed-index eigenvalue convergence.

**Следующий ход:** доказать strict order carrier ниже 20 и зафиксировать
zero-based degree-four index `j=2`; затем провести выбранную row в actual
`psi_4` и отдельно закрывать mode zero/Fourier/Lemma 7.2/floor chain.

**Адреса:**
`Q3/Proofs/RouteB/D0Mode4DLMF3035EvenL2ToFiniteLimitSpectrum.lean` ·
`Q3/Proofs/RouteB/D0Mode4ClassicalCarrierToDLMF3035EvenL2.lean` ·
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DLMF3035_FINITE_LIMIT_SPECTRAL_IFF_CLOSEOUT_2026-08-15.md`.

**Чей вердикт и его аргумент:** Proshka сначала выбрала
`B — PRODUCTION_ROOT_TO_CARRIER_ONE_DIRECTION_FIRST` и дословно локализовала
reverse: «assume `det != 0`, obtain local constancy of the literal negative
count, transport the same count to two nearby finite sections, and contradict
convergence of the `j`-th finite eigenvalue through that interval». Codex/Lean
проверил именно этот argument и закрыл его без внешнего запроса.

**Граница:**
`G3_DLMF3035_FINITE_LIMIT_SPECTRAL_IFF_PROVED_STRICT_ORDER_AND_P2_MODE_SELECTION_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — Goal 058 G3: strict order и degree-four selection

**Развилка:** считать monotone finite-limit carrier уже source-ordered либо
доказать отсутствие collisions через literal singular Schur root.

**Выбрали:** доказать singular Hermitian semicontinuity, затем pin
`negativeCount(root)=j` двумя nonsingular последовательностями и convergence
фиксированного finite eigenvalue index.

**Почему:** monotone limits могут совпадать; simple kernel сам по себе не
запрещает collapse нескольких finite indices. Нижняя/верхняя semicontinuity
оставляет у simple root ровно adjacent inertia values и закрывает этот зазор
без нового source binder.

**Что отвергли и почему:** monotonicity alone отвергнута как недостаточная:
пределы строго упорядоченных finite spectra могут collide. Simple kernel без
semicontinuity также не фиксирует, какой finite index пришёл в этот root.

**Техника:** negative/positive spectral subspaces, exact nullity partition,
two-sided nonsingular selection, finite-to-literal count transport,
fixed-index convergence, finite-head bound `carrier 2 < 20`.

**Результат:** `negativeCount(root)=j`; carrier строго упорядочен ниже `20`;
index `2` уникален для третьего even value; normalized degree-four DLMF row
square-summable. Axioms standard only.

**Следующий ход:** соединить выбранную DLMF row с существующей Ferrers regular
even prolate solution и physical scaling, не предполагая function identity;
затем отдельно finite Fourier и Lemma 7.2/floor chain.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DLMF_STRICT_ORDER_DEGREE_FOUR_SELECTION_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_DEGREE_FOUR_DLMF_ROW_SELECTED_PHYSICAL_PSWF_IDENTITY_AND_FINITE_FOURIER_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — selected mode-zero/mode-four regular physical solutions

**Развилка:** отдельно оставить root-conditioned Ferrers constructor либо
скомпоновать его с новым strict carrier index selection сразу для modes `0/4`.

**Выбрали:** один парный theorem на zero-based even indices `0` и `2`, без
нового data wrapper и без изменения production `ProlatePair`.

**Почему:** тот же source-locked recurrence/Ferrers constructor параметризован
spectral carrier и честно строит обе необходимые моды; повторять две отдельные
цепочки или вводить parallel pair не нужно.

**Что отвергли и почему:** две раздельные theorem chains и новый parallel pair
wrapper: они дублируют один параметризованный constructor и создают лишнюю точку
расхождения с production `ProlatePair`.

**Техника:** carrier-to-literal-Schur singularity, positive determinant/root
factor, two root-conditioned normalized Ferrers constructors, strict carrier
order below `20`, existing physical scaling.

**Результат:** существуют regular normalized solutions at carrier indices
`0` and `2`, and `Lambda_0 < Lambda_2 < 20`. Direct Lean, 7794-job named build,
`q3_check` and axiom audit pass; axioms standard only.

**Следующий ход:** prove Green/intertwining on the actual interior-`C2` plus
zero-flux endpoint domain, then derive restricted finite-Fourier proportionality
without assuming global `C2`; zero counts and Lemma 7.2 remain separate.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_MODE_ZERO_FOUR_SELECTED_FERRERS_PHYSICAL_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_SELECTED_MODE_ZERO_FOUR_REGULAR_PHYSICAL_SOLUTIONS_PROVED_ENDPOINT_GREEN_FOURIER_ZERO_COUNTS_AND_LEMMA72_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — endpoint-flux Fourier eigen-transport

**Развилка:** усиливать selected Ferrers source до global `C2` либо доказать
Green/FTC transport на его реальном singular endpoint domain.

**Выбрали:** отдельный theorem с closed-window continuity, interior derivative,
divergence-form ODE и двумя zero-flux limits.

**Почему:** global `C2` не следует из текущего source object и был бы ложным
interface strengthening. FTC на произведениях требует интегрируемость уже
взвешенной производной, а не самой потенциально плохой endpoint derivative.

**Что отвергли и почему:** global `C2` strengthening: оно не следует из
текущего source object и подменяет реальную zero-flux endpoint domain более
сильной недоказанной гипотезой.

**Техника:** два FTC product identities, exact endpoint cancellation, Tietze
extension только для reuse differentiation-under-integral, kernel prolate swap.

**Результат:** finite Fourier action сохраняет тот же prolate ODE eigenspace.
Direct Lean, 7745-job named build, `q3_check` и axiom audit PASS; axioms
standard only.

**Следующий ход:** source-specific physical Ferrers wrapper, затем
scalar proportionality/uniqueness. Zero counts, scalar sign/order and Lemma 7.2
remain separate.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_ENDPOINT_FLUX_FOURIER_EIGEN_TRANSPORT_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_ENDPOINT_FLUX_FOURIER_EIGEN_TRANSPORT_PROVED_SELECTED_FERRERS_PHYSICAL_WRAPPER_AND_SCALAR_PROPORTIONALITY_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — physical Ferrers Fourier ODE transport

**Развилка:** оставить endpoint theorem generic либо сразу проверить, что
accepted physical Ferrers object действительно удовлетворяет его exact
domain contract.

**Выбрали:** отдельный source-specific module без изменения production types.

**Почему:** real-to-complex lift, square-root scale и one-sided endpoint
filters являются load-bearing стыками; их нельзя считать автоматическими.

**Что отвергли и почему:** оставить endpoint theorem generic, полагая, что
physical Ferrers object удовлетворяет его exact domain contract автоматически:
три стыка (real-to-complex lift, square-root scale, one-sided endpoint filters)
несут нагрузку, и непроверенное «подходит по типу» здесь означало бы
незамеченную подмену domain contract.

**Техника:** closed-window scale map, actual derivative lifts, complexified
physical ODE algebra, exact identity
`(m-u^2)h_phys' = sqrt(m)(1-(u/sqrt(m))^2)h'`, endpoint-filter composition,
generic endpoint Fourier theorem.

**Результат:** finite Fourier image of any accepted physical Ferrers witness
solves the same prolate ODE with eigenvalue `Lambda+G`. Direct Lean,
7775-job named build, `q3_check` and standard-only axiom audit PASS.

**Следующий ход:** regular-even eigenspace uniqueness/scalar proportionality;
exact nodal/index identification remains a separate possible prerequisite.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_PHYSICAL_FERRERS_FOURIER_EIGEN_TRANSPORT_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_SELECTED_PHYSICAL_FERRERS_FOURIER_ODE_TRANSPORT_PROVED_SCALAR_PROPORTIONALITY_AND_NODAL_SELECTION_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — physical Ferrers Fourier scalar proportionality

**Развилка:** требовать nodal count/ordered eigenspace simplicity либо
использовать center Cauchy data для regular-even ODE solutions.

**Выбрали:** exact complex divergence-form IVP uniqueness at the center.

**Почему:** accepted source уже even и имеет nonzero center; finite-Fourier
image solves the same ODE and is even. Поэтому значения и derivatives в нуле
определяют proportionality без дополнительной zero-count гипотезы.

**Что отвергли и почему:** требовать nodal count/ordered eigenspace simplicity: center Cauchy data решает proportionality без zero-count гипотезы, а nodal selection — отдельная предпосылка; тянуть её сюда значило бы удорожать теорему лишней недоказанной гипотезой.

**Техника:** complex flux-state ODE, local Gronwall uniqueness plus connected
propagation, compact-window differentiation under the Fourier integral, two
literal derivative integrals, evenness under symmetric integration,
`chi=Fh(0)/h(0)`, closure `Ioo -> Icc`.

**Результат:** для любого accepted physical Ferrers witness существует
`chi : Complex` с exact restricted relation `Fh=chi*h` на closed physical
window. Direct Lean, 7779-job named build, `q3_check` and standard-only axiom
audit PASS.

**Следующий ход:** prove the scalar real and nonzero, then source-locked
sign/order and production `ProlatePair` assembly. Zero-count selection is not
needed for this proportionality theorem.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_PHYSICAL_FERRERS_FOURIER_SCALAR_PROPORTIONALITY_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_PROPORTIONALITY_PROVED_SCALAR_REAL_NONZERO_SIGN_ORDER_AND_PROLATEPAIR_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — physical Ferrers Fourier scalar is real

**Развилка:** считать scalar real по classical PSWF convention либо вывести
это из уже доказанной restricted complex proportionality.

**Выбрали:** exact center calculation, без нового source field.

**Почему:** при `x=0` positive-phase kernel равен `1`; physical source —
complexification real function и имеет nonzero center value.

**Что отвергли и почему:** считать scalar real по classical PSWF convention: конвенция — не доказательство; точное вычисление в центре выводит real-ность вместо того, чтобы её постулировать.

**Техника:** взять imaginary parts exact center equality, переписать integral
через `integral_complex_ofReal`, исключить source-center zero и заменить
complex scalar его real part.

**Результат:** существует `chi : Real` с exact `Fh=(chi:Complex)h` на closed
physical window. Direct Lean, 7780-job named build, `q3_check` and
standard-only axiom audit PASS.

**Следующий ход:** analytic continuation/injectivity для `chi != 0`, затем
source-locked sign/order и production `ProlatePair` assembly.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_PHYSICAL_FERRERS_FOURIER_REAL_SCALAR_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_REAL_SCALAR_PROVED_NONZERO_SIGN_ORDER_AND_PROLATEPAIR_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — physical Ferrers Fourier scalar is nonzero

**Развилка:** добавить nonzero scalar как source field либо вывести его из
compact-window analyticity и Fourier inversion.

**Выбрали:** generic entire-extension/injectivity bridge без нового binder.

**Почему:** restricted equality `Fh=chi*h` сама по себе не исключает `chi=0`;
нужно перенести ноль с window на всю frequency line.

**Что отвергли и почему:** добавить nonzero scalar как новый source field: новый binder повторял бы выводимое; ноль исключается entire-extension и identity theorem, а не постулатом.

**Техника:** complex-frequency integral, dominated differentiation,
`Differentiable -> AnalyticOnNhd`, identity theorem from real accumulating
zeros, exact real-axis bridge, existing Fourier-inversion nonvanishing theorem.

**Результат:** для accepted physical Ferrers witness существует
`chi : Real`, `chi != 0`, с exact restricted relation на closed physical
window. Direct Lean, 7782-job named build, `q3_check` and standard-only axiom
audit PASS.

**Следующий ход:** source-locked sign/order identification, затем zero
extension, normalization, orthogonality and production `ProlatePair` assembly.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_PHYSICAL_FERRERS_FOURIER_NONZERO_SCALAR_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_REAL_NONZERO_SCALAR_PROVED_SIGN_ORDER_AND_PROLATEPAIR_NEXT`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — normalized Ferrers production ProlatePair

**Развилка:** ждать полного source sign/order theorem до production assembly
либо сначала доказать все независимые normalization/record fields.

**Выбрали:** canonical zero extension and `L2` normalization of the already
selected Ferrers witnesses, then direct construction of the unchanged
production `ProlatePair`.

**Почему:** support, unit norm, positive integrals and restricted Fourier
relations do not depend on the missing oscillation/sign theorem. Their early
materialization narrows the source wall without weakening its statement.

**Что отвергли и почему:** ждать полного source sign/order theorem до production assembly: support, unit norm и positive integrals от sign/order не зависят и доказуемы уже сейчас — ожидание сериализовало бы работу без нужды.

**Техника:** indicator zero extension, continuous positive interval mass,
exact scale substitution for the integral, normalization transport through
the finite Fourier action, production record assembly at selected indices
`0/2`.

**Результат:** production pair exists with positive `I0/I4`, nonzero real
`chi0/chi2`, exact restricted eigenrelations, unit norms and compact support.
Direct Lean, 7783/7807-job named builds, `q3_check` and standard-only axiom
audit PASS.

**Следующий ход:** source-lock exact zero counts `0/4`, orthogonality and
`0 < chi2 < chi0`; then apply the existing actual-mode and Lemma 7.2 chain.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_FERRERS_PRODUCTION_PROLATEPAIR_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_PRODUCTION_PROLATEPAIR_CONSTRUCTED_ACTUAL_MODE_ZERO_COUNTS_ORTHOGONALITY_AND_FOURIER_SIGN_ORDER_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — Ferrers production orthogonality

**Развилка:** считать ортогональность ещё одним внешним source field либо
вывести её из уже принятого differential endpoint package.

**Выбрали:** direct Lagrange identity for distinct prolate eigenvalues with
zero endpoint flux, then exact transport through zero extension and
normalization.

**Почему:** strict spectral order and both endpoint flux limits already exist
for the selected Ferrers witnesses.  They are precisely the hypotheses of the
self-adjoint Sturm–Liouville orthogonality argument.

**Что отвергли и почему:** ортогональность как ещё один внешний source field: она выводима из уже принятого differential endpoint package (Lagrange identity при zero endpoint flux); внешний field дублировал бы формализуемое.

**Техника:** continuous endpoint extension of each flux, Wronskian derivative
on the open window, interval FTC, indicator reduction and real-normalization
algebra.

**Результат:** exact whole-line production identity
`integral (star h0 * h4) = 0`. Direct Lean, 7808-job named build, `q3_check`
and standard-only axiom audit PASS.

**Следующий ход:** source-lock exact zero counts `0/4` and positive-phase
Fourier order `0 < chi2 < chi0`; then construct `IsActualProlateModePair` and
invoke the existing Lemma 7.2 chain.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_FERRERS_PRODUCTION_ORTHOGONALITY_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_PRODUCTION_PROLATEPAIR_ORTHOGONAL_ZERO_COUNTS_AND_FOURIER_SIGN_ORDER_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — normalized Ferrers zero-count transport

**Развилка:** ждать внешнего combined source carrier либо сначала закрыть
локально вопрос, сохраняют ли normalization и zero extension точное число
внутренних нулей.

**Выбрали:** exact set-level transport через положительное масштабирование,
плюс uniqueness real Fourier scalar на nonzero center.

**Почему:** внешний источник должен поставлять только математические факты о
безразмерных selected modes; он не должен повторять уже формализуемую
механику project normalization и не должен создавать параллельную family.

**Что отвергли и почему:** ждать внешнего combined source carrier: внешний источник должен поставлять только математические факты о безразмерных selected modes, а не повторять формализуемый здесь transport числа нулей.

**Техника:** раскрытие indicator внутри open physical window, деление на
positive `L2` normalization, injectivity `t ↦ sqrt(mProject)*t`, exact
`Set.ncard_image_of_injective`, cancellation общей ненулевой функции в двух
restricted finite-Fourier eigenrelations.

**Результат:** source-free K3 transport доказан. Direct Lean, 7785-job named
build, `q3_check`, cartography/catalog sync и standard-only axiom audit PASS.

**Следующий ход:** принять только exact dimensionless zero-count and
positive-phase/order source contract для уже selected Ferrers witnesses,
затем локально собрать `IsActualProlateModePair`.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_NORMALIZED_ZERO_COUNT_TRANSPORT_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_NORMALIZED_ZERO_COUNT_TRANSPORT_PROVED_DIMENSIONLESS_COUNTS_AND_POSITIVE_PHASE_FOURIER_ORDER_SOURCE_LOCKS_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — normalized actual-mode local fields

**Развилка:** довериться prose-утверждению, что analytic fields уже доступны,
либо kernel-check'ом собрать их для точного normalized zero extension до
source verdict.

**Выбрали:** source-free local proof of real-valuedness, interior `C²`, and
the literal normalized `prolateWaveExpression` eigenrelation.

**Почему:** после импорта классических zero-count/phase-order facts record
assembly не должен обнаружить ещё один формальный разрыв.

**Что отвергли и почему:** довериться prose-утверждению, что analytic fields уже доступны: record assembly не должен обнаруживать формальный разрыв после импорта классических фактов — поля собираются kernel-check'ом до source verdict.

**Техника:** exact indicator reduction on the open window, complex-linear
coercion of real `ContDiffOn`, accepted raw first derivative and weighted-flux
derivative, local `EventuallyEq.fderiv_eq`, constant normalization algebra.

**Результат:** все non-source analytic fields точного normalized production
witness kernel-check'нуты. Direct Lean, 7786-job named build, `q3_check`,
cartography/catalog sync и standard-only axiom audit PASS.

**Следующий ход:** получить judge-approved source lock только для selected
degree `0/4` nodal counts and positive plus-phase Fourier order, затем
локально собрать `IsActualProlateModePair`.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_NORMALIZED_ACTUAL_MODE_LOCAL_FIELDS_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_NORMALIZED_ACTUAL_MODE_LOCAL_FIELDS_PROVED_ONLY_CLASSICAL_NODAL_AND_FOURIER_ORDER_SOURCE_LOCKS_MISSING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — dimensionless finite-Fourier scaling

**Развилка:** оставить scale/sign convention внутри будущего внешнего
source-carrier либо сначала доказать project transport локально.

**Выбрали:** source-free exact change of variables from dimensionless
plus-phase Slepian action to the existing normalized physical Ferrers mode.

**Почему:** внешний supplier должен утверждать только classical mathematics
для тех же selected witnesses, а не повторять проверяемую integral scaling и
positive normalization algebra.

**Что отвергли и почему:** оставить scale/sign convention внутри будущего внешнего source-carrier: supplier должен утверждать classical mathematics для тех же witnesses, а не повторять проверяемую локально integral scaling.

**Техника:** `intervalIntegral.integral_comp_div`, exact identity
`c=2*pi*(sqrt mProject)^2`, set-integral/interval-integral conversion,
indicator reduction inside the physical window, factoring the positive
normalization constant.

**Результат:** physical scalar is kernel-checked as
`sqrt mProject * dimensionless scalar`. Direct Lean, 7787-job named build,
`q3_check`, cartography/catalog sync и standard-only axiom audit PASS.

**Следующий ход:** дождаться exact Proshka judgment on the two source
carriers, then execute only the ratified kernel/source boundary.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DIMENSIONLESS_FOURIER_SCALING_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_DIMENSIONLESS_TO_PHYSICAL_FOURIER_SCALING_PROVED_CLASSICAL_ZEROCOUNT_AND_PHASE_ORDER_SOURCE_CARRIERS_PENDING`;
G1, G3, Route B promotion и RH остаются открыты.

## 2026-08-15 — regular Ferrers coefficient uniqueness

**Развилка:** считать два current regular witness одним source object по
совпадению ODE/параметров либо сначала закрыть их равенство внутри текущего
package без внешнего zero-count.

**Выбрали:** точную uniqueness coefficient row при фиксированных
`mProject`, `K`, `Λ`.

**Почему:** source citation не может доказывать same-witness identity.  Но
current recurrence, positive zeroth phase and weighted normalization уже
достаточны, чтобы снять внутреннюю неоднозначность kernel-путём.

**Что отвергли и почему:** считать два current regular witness одним source object по совпадению ODE/параметров: source citation не доказывает same-witness identity — неоднозначность снимается kernel-путём через recurrence и weighted normalization.

**Техника:** recurrence propagation from coordinates `0/1`, nonzero
superdiagonal, positive scalar ratio, uniqueness of the stored weighted
`HasSum` normalization.

**Результат:**
`mode4FerrersRegularEvenProlateSolution_coefficients_eq` kernel-check'нут.
Direct Lean, 7771-job named build, `q3_check`, strict refresh and standard-only
axiom audit PASS. Scoped commit: `3ba54773`.

**Следующий ход:** получить exact global nodal-index supplier: formal singular
Sturm oscillation for the current class либо nonzero-scalar identity with a
formal DLMF `Ps^0_{2p}` carrier owning the `2p` count.  Citation alone and
zero-count binder запрещены.

**Адреса:**
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_REGULAR_FERRERS_COEFFICIENT_UNIQUENESS_CLOSEOUT_2026-08-15.md`.

**Граница:**
`G3_UNIQUE_CURRENT_REGULAR_SOLUTION_TO_CLASSICAL_PSF_ZEROCOUNT_SOURCE_GAP`;
G1, G3, Route B promotion и RH остаются открыты.

### Счёт раскопок

| четверть | строки | развилок найдено | причина записана | причина отсутствует |
|---|---|---|---|---|
| 1 | 1–13000 | 12 | 12 | 0 |
| 2 | 13000–26000 | 12 | 9 | 3 (все — внешние вердикты) |
| 3 | 26000–39000 | 12 | 12 | 0 |
| 4 | 39000–51763 | 12 | 11 | 1 (внешний вердикт) |
| **всего** | **51 763** | **48** | **44 (92%)** | **4 (8%)** |

Доля развилок с записанной причиной — прямая мера того, насколько проект
восстановим без археологии.

---

## До 2026-03-07 — старые записи

Прежний формат журнала (дата · задача · что сделано · критическая техника ·
следующий шаг) вёлся до 07.03.2026 и оборвался за три дня до публикации.
Сорок строк. Дальше писался только `INSIGHTS.md`.

Архив прежних записей: `git log -- docs/Progress_Log.md`

## 2026-09-03 — развилка: абсолютный пол отвергнут, прямая кривизна выбрана главной ветвью

**Что произошло.** Вердикт Прошки `0c0a2b37` (`REQ-2026-09-03-CURVRITZ`,
`RUN_RELATIVE_RITZ_DECISIVE_TEST`): маршрут кривизна → нормальность → Витали →
ZeroEscape сохранён; интерфейс через один фиксированный абсолютный пол `β`
(`complexTrialComplementFloor`, `r_k = ‖Res‖²/β²`) отвергнут как форма кофинальной
цели; цель `inf(λ₂−λ₁) > 0` убита как форма; полилог-бюджет `B_k` через тот же
`r_k` помещён в карантин как переоткрытие остановленного темпа. Относительный
Ritz признан корректным **новым** интерфейсом для входа A, не переписыванием.
Прямой скалярный функционал `κ_k = −F_k''(0)/(2F_k(0))` выбран главной
аналитической ветвью. Следующий несущий разрыв:
`P59_CURVATURE_DUAL_ANNIHILATOR_OR_SCALAR_SCHUR_IDENTITY`.

**Почему.** Леджер (прекоммит `c5db76d6`, чекпойнт `b25c91b5`): `λ₁` падает как
`10^{−1.9m}`, `λ₂` так же; `κ_m = 0.0259, 0.0263, 0.0258` плоская;
`R_m(0.40) ≈ 1.078` плоская; классика (KMS 1953, Widom 1958) и CC 2106.01715
говорят то же про абсолютную щель. Выбор сделан судьёй по этим данным, без
новой теоремы.

**Что закрыто:** фиксированный абсолютный пол как кофинальный consumer; форма
цели «абсолютная щель»; `B_k`-fallback в текущем виде. **Что открыто:** двухпорядковое
сокращение скобки в `F''(0)`; проективная ошибка входа A через `ε_k/(g_k−1)`;
Lean-обвязка второго джета и абстрактного моста (у Codex).

**Следующий ход:** добить леджер (`m=163`, N-проверки), снять зонды 1 и 4 по
замороженным правилам, добавить описательные колонки относительного Ritz, если
trial-вектор доступен на тех же ячейках; затем бумажная атака
`P59_CURVATURE_DUAL_ANNIHILATOR`.

**Адреса:** вердикт и его чат-предшественник в `docs/routeB_bus/proshka/`;
обзор `litreview/SURVEY_WALLS_A_B_DELTA_2026-09-03.md`; зонды
`docs/routeB_bus/phase5_scripts/`.

## 2026-09-03 (вечер) — развилка: кривизна как наклон окаймлённого секулярного детерминанта

**Что произошло.** Вердикт `d7c7df36` (`REQ-2026-09-03-SCHURLOEWNER`,
`TRY_SECULAR_IDENTITY_FOR_CURVATURE`). Секулярное уравнение полюсного члена даёт корень
`λ₁` точно, но НЕ вычисляет смешанное спаривание `⟨c,(D−λ₁)⁻¹b⟩`: вектор `c = 1/(2π²n²)` не
равен ни `b`, ни `C_L`. Ремонт представления: `1/12 − S(z) = ½∂_tΦ(t,z)|₀`, где
`Φ = det(K+t(e₀wᵀ+we₀ᵀ) − z)/det(D − z)`, `w = (1/12, c)`; при `z = λ₁` имеем `Φ(0,λ₁) = 0`.
Новый несущий разрыв: `|∂_tΦ(0,λ₁)| ≤ C/L²` без нормы резольвенты и без абсолютной щели.
Лёвнер-структура source-faithful на уровне разделённых разностей и displacement rank 2
(Lean: `ccmWeilTau_structured_offdiag`, `ccmWeilMatFinite_commutator`), но операторная
монотонность и каноническая `h` не даны. Вход A типизирован на проективной ошибке `p_k`;
два расписания доказательства к одному приёмнику отвергнуты, нужно общее кофинальное
уплотнение.

**Почему.** Зонды 1–6 (Probe 3 BOUNDED, Probe 4 CONFIRMED, Probe 5 CONFIRMED) плюс
классика Лёвнера; двумерный плант `K_t = [[λ+b²/t, b],[b, λ+t]]` показывает, что общая
Лёвнер-структура не даёт темпа `L⁻²`.

**Что закрыто:** R1; полюсное секулярное как вычислитель кривизны; строгая одноцветность
вычетов; композиция двух расписаний. **Что открыто:** источниковая формула наклона
`∂_tΦ` и его сокращение до нормы (Codex preflight, read-only); общее кофинальное
уплотнение для входа A и нормальности.

**Адреса:** вердикт в `docs/routeB_bus/proshka/`; задание
`docs/Codex/TASK_2026-09-03_goal058_curvature_bordered_secular_source_preflight.md`.

## 2026-09-03 (поздний вечер) — мост «кривизна → ограниченность» доказан на бумаге без Адамара; HS-тождество исправлено множителем 1/2

**Что произошло.** Вердикт CURVBRIDGE (`926c1865`; судья заменил два коммита одним force-push): для трансформа P59 явное
произведение `F/F(0) = Π_j(1 − z²/ρ_j²)·Π_{k>N}(1 − z²/x_k²)` даёт `|F(z)| ≤ |F(0)|e^{κ|z|²}`,
`κ = −F''(0)/(2F(0)) = Σ1/ρ_j² + (L²/4π²)Σ_{k>N}1/k²`, на фактах Mathlib 4.26
(`Complex.tendsto_euler_sin_prod`, `Polynomial.Splits.eq_prod_roots_of_monic`,
`Real.prod_one_add_le_exp_sum`, `hasSum_zeta_two`). `MATHLIB_GAP` Codex снят: общая
факторизация Адамара не нужна. Сильнейшая атака (устранимые узлы решётки) отбита через
`P_N(x_j) = v_j Π_{k≠j}(x_j − x_k)` и точную выборку `F(x_j) = √L(−1)^j v_j`.
HS-представление: тождество `κ = ‖(D_log)⁻¹‖²_HS` ложно как заявлено (стандартная норма
считает ±μ), верно `κ = ½‖(D_log)⁻¹‖²_HS`; наивная L²-норма ядра Грина отвергнута:
не та метрика. Ранжирование стены: секулярный наклон (9/3), HS-след (8/6), отталкивание
нулей (7/8). Lemma 7.3 не даёт отталкивания нулей ground-семьи: не та семья.

**Почему.** Прошка выполнил доказательство по запросу владельца «дать ему доказать»;
наблюдатель ошибся в HS-множителе (K6 0.80 → REFUTED).

**Что закрыто:** `P59_SPECIFIC_CURVATURE_TO_LOCAL_BOUNDEDNESS` на бумаге; Codex item 5.
**Что открыто:** `P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND` (аналитика; preflight у
Codex дал `ONLY_RENAMES_CURVATURE` в черновике); равномерная HS/след-оценка в
модифицированной метрике; общее кофинальное расписание.

**Следующий ход:** Codex формализует `Proposition59ExplicitProductCurvatureBridge.lean`
по директиве вердикта.

## 2026-09-03 (ночь) — развилка: кривизна переезжает в нечётный сектор (reciprocal-mode displacement)

**Что произошло.** Вердикт `3dc82357` (`REQ-2026-09-03-NEWMECH`, запрос владельца «пусть
судья думает»). Из четырёх кандидатов наблюдателя выжил один (C1: перенос 2-джета
trial → ground через проективную ошибку, с ремонтом якоря; одна скорость
`J_k = |A_k| L^{5/2} √p_k`). Убиты: дихотомия ¬RH (энергия не ограничивает лог-вторую
производную минимизатора), относительная щель как единая теорема (нужна положительность
`λ₁` и неверное направление minmax; второй trial даёт верхнюю, не нижнюю оценку `λ₂`; на
production-ячейках `Rayleigh(q)/λ₁ ≤ C` ложно), цепь де Бранжа (нет общего
Hermite–Biehler-генератора, пополнение условно на RH). Судья предложил своё C5:
reciprocal-mode displacement. С `X = diag(n)`, `R = X⁻¹`, `η = 1`, `r = Rη` (нечётный),
из источникового коммутатора `XD − DX = βηᵀ − ηβᵀ` следует `DR − RD = brᵀ − rbᵀ`; чётность
даёт `⟨r,Ab⟩ = 0`, `A = (D−λ₁)⁻¹`; корень Шура `⟨b,Ab⟩ = a₀−λ₁`; точное тождество
`⟨Rr,Ab⟩ = ⟨r,A(Rb)⟩ − (a₀−λ₁)⟨r,Ar⟩` и `κ = (L²/4π²)·E_k`,
`E_k = ½‖r‖² − ⟨r,A(Rb)⟩ + (a₀−λ₁)⟨r,Ar⟩ + Σ_{n>N}1/n²`. Опасная вторая чётная пара
исключена чётностью: наблюдаемая кривизны живёт в нечётном секторе `D`.

**Почему.** Все убитые формы делили объект и платили `1/λ₂`; C5 работает с полной
суммой и меняет сектор, где сидит резольвента.

**Что закрыто:** C2, C3 (как единая теорема), C4. **Что открыто:** источниковая оценка
`E_k ≤ C/L²` (нечётный Gram-дефект), поставщик `p_k` для C1.

**Следующий ход:** read-only preflight `GOAL058_RECIPROCAL_MODE_ODD_GRAM_SOURCE_PREFLIGHT`
(судья, K6 `P_C5_ODD_COBBOUNDARY_EXISTS` 0.45); численный зонд 8 по нечётному сектору
(прекоммит, наш канал).

## 2026-09-03 (ночь) — мост «кривизна → ограниченность» для P59 KERNEL_GREEN; C5 закрыт preflight-ом и зондом 8

**Что произошло.** `Proposition59ExplicitProductCurvatureBridge.lean` (1483 строки, агент
Linux-Claude на Opus, коммиты `f962c1e3…d96c17d8` после `5293a75f…de108de0`): все семь
шагов директивы `926c1865` kernel-green, 33 декларации, только `propext`,
`Classical.choice`, `Quot.sound`, проверено наблюдателем в главном checkout. Главные
теоремы: `proposition59_curvature_coercion` (κ вещественна), `proposition59Curvature_nonneg`,
`proposition59Curvature_eq_root_sum_add_tail`, `proposition59_compact_envelope`
(`‖F z‖ ≤ ‖F 0‖·exp(κ‖z‖²)` для ВСЕХ z), `proposition59_curvature_closed_form`,
`proposition59_normalized_bound_on_ball`. Без Адамара, без предиката порядка: хвост Эйлера
только ОЦЕНЕН, не отождествлён; неравенство продолжено по непрерывности с плотного
множества на узлы. Планты A–D пройдены. Единственный остаток `P59_EULER_TAIL_LIMIT_API_GAP`
сужен до шага 4b в узлах и ничего в §2.1 не блокирует. Отклонение от списка судьи:
`Real.prod_one_add_le_exp_sum` не использован (лемма для `Finset`, корни — `Multiset`),
заменён четырёхстрочной индукцией `norm_quadProduct_le_exp`.

Параллельно: preflight C5 (Opus) вернул `C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE`
(кограница существует, но строится из ground-вектора; `E_k = Σ_{n≤N}(1+2ξ_n/ξ₀)/n² + хвост`
тождественно, E-CLOSED); зонд 8 опроверг обе посылки C5 численно: нечётный сектор
схлопывается как чётная `λ₂` (`μ_odd,min = 6e-28 … 3e-158`), `T2`, `T3` порядка `1/μ_odd`.
Наблюдатель: E-CLOSED переписывается в `κ_k = 2Σ_{n≤N}(−1)^n(F_k(x_n)/F_k(0) − 1)/x_n² + O(L²/N²)`
— знакопеременная решёточная сумма Римана для `(f−1)/x²`, то есть стена B есть вход A с
весами `(−1)^n/x_n²`. Наблюдение, не теорема.

**Что закрыто:** `P59_SPECIFIC_CURVATURE_TO_LOCAL_BOUNDEDNESS` в Lean; `CODEX_ITEM_5_MATHLIB_GAP_NAMED`;
C5 как механизм. **Что открыто:** поставщик `p_k` для C1 (единственная живая ветвь);
`P59_EULER_TAIL_LIMIT_API_GAP` (только косметика 4b).

**Следующий ход:** батч Прошке: E-CLOSED + знакопеременная форма как окончательная запись
стены, судьбы `P_C5_ODD_COBBOUNDARY_EXISTS 0.45` и двух K6 зонда 8, некруговой поставщик `p_k`.

## 2026-09-03 (поздняя ночь) — развилка: знакопеременная форма точна; нормальность и вход A остаются разными

**Что произошло.** Вердикт `f788d2fa` (`REQ-2026-09-03-LATTICEWALL`). Тождество
`κ_k = 2Σ_{n≤N}(−1)^n(f_k(x_n)−1)/x_n² − (L²/2π²)Σ_{n>N}(−1)^n/n²` ТОЧНО, хвост
`|T| ≤ L²/(2π²(N+1)²)`, неравенство `κ ≤ S_Ξ + (L²/2π²)W + |T|`; голова `S_Ξ,k` ограничена и
стремится к `κ_Ξ` (квадратура по полуячейкам). `W = O(L⁻²)` закрывает НОРМАЛЬНОСТЬ. Но
(1) `W` не слабейшее: точное знаковое разложение слабее; (2) `W` не закрывает вход A:
веса `1/n²` дают сходимость только при фиксированном `n`, то есть в `x_n → 0`; вход A
требует `sup_{n ≤ XL/2π}|Δ_n| → 0` при каждом `X` — невзвешенный профиль на растущем
диапазоне. Моё утверждение «стена B и вход A — одно» опровергнуто как сформулированное
(`P_WEIGHTED_ERROR_IS_WEAKEST_SUFFICIENT` REFUTED_AS_STATED). Лемма 7.3 CCM даёт
`O(λ^{-1/2})` для континуального trial, прямого импорта в конечный trial проекта нет.
Узловой перенос ground → trial точен с усилением `√L`; одна ставка `|A|L^{5/2}√p = O(1)`
подтверждена с починкой якоря.

**Почему это развилка.** Самая узкая щель переехала: не «докажи `W = O(L⁻²)`», а
`P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY` — центрально-нормированное собственное
уравнение `R(y)_n = (K̃y)_n − y_n(K̃y)_0 = 0` для `y = ξ/ξ_0`, записанное на низких модах
как рекуррентность ДО любого обращения. Судья оценивает 0.40, что рекуррентность
замыкается до щели. Провал регистрируется как
`P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP` и возвращает к проективному
двухджетовому маршруту.

**Что закрыто:** знакопеременная форма (бумага, точно); `W ⇒ нормальность`;
`C5_AS_NEW_BOUND`; `W_AS_WEAKEST`; `W_ALONE_AS_INPUT_A`. Шесть Lean-ready пунктов для
`Proposition59AlternatingLatticeCurvature.lean` (позднейшая транзакция).
**Что открыто:** `P59_WEIGHTED_LATTICE_ERROR_SOURCE_BOUND` (кривизна),
`P59_WEIGHTED_AND_COMPACT_LATTICE_PROFILE_SOURCE_BOUND` (весь маршрут).

**Следующий ход:** read-only preflight `GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT`
(задание `docs/Codex/TASK_2026-09-04_goal058_normalized_xi_lattice_eigen_equation_preflight.md`).
По методу «крыша → атом»: кандидат в атом сменился с `W` на низкомодовую рекуррентность
нормированного ground-вектора; карточка объекта дополнена.

## 2026-09-04 (00:50) — развилка: собственное уравнение нормированного ξ — фиксированная точка, не оценка; новый некруговой объект

**Что произошло.** Preflight агента (Opus, read-only) по заданию судьи `f788d2fa`:
код `P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP`, предсказание судьи
`P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP 0.40` REFUTED. Наивного провала нет: после
расщепления Лёвнера по квадратам узлов коэффициенты хвоста убывают как `1/j²` с явными
исходными формулами, а полюсная часть `W02` в чётном секторе имеет ранг ОДИН и сворачивается
в один скаляр `Ŝ` (LATTICE-2). Но `Ŝ` — аффинная функция самого `E` (LATTICE-3), а хвост
`j > n₀` — это `1/j²`-взвешенный хвостовой момент того же `E`. Уравнение есть соотношение
неподвижной точки для величины, которую нужно оценить, а не оценка. Вверх по модам оно
некаузально, вниз теряет убывание коэффициентов.

**Новый объект (некруговой, из планта):** `P59_ARCH_PRIME_DIAGONAL_DEFECT_NONDEGENERACY`:
`|D_n| = |W_ℝ(n,n) + Prime(n,n) + a_n + λ₁| ≥ δ(L) > 0` для `n ≤ n₀` — чисто исходная величина
(архимедов интеграл + сумма фон Мангольдта + `λ₁`), которую плант обнуляет; никакая
Lean-запись её не поставляет. Второй вход, `P59_LATTICE_TAIL_MASS_BOUND`, круговой.

**По методу «крыша → атом»:** кандидат в атом от судьи (низкомодовая рекуррентность)
раздроблен: одна половина = сам `E`, другая = `D_n`-невырожденность. Пять тождеств Lean-ready.
Странности §8: `x_n ≈ −1/2` — артефакт полюса (S4); чётный сектор половинит displacement
rank (S5); `Ŝ ≈ −1/(√2L²)` — резкое непроверенное предсказание (S6).

**Следующий ход:** зонд 10 по аддендуму 11 (тождества, размеры членов, `min|D_n|`, `Ŝ`);
вердикт SHELLSEARCH; отчёт судье с кодом и новым объектом.

## 2026-09-04 (01:20) — развилка: оболочка найдена; атом = одна энергия `‖diag(1/n)Δ‖² ≤ C/L⁴`

**Что произошло.** Вердикт `99927f01` (`REQ-2026-09-03-SHELLSEARCH`, запрос по методу
владельца «найди оболочку, входы которой уже доказаны»). Семь оболочек ранжированы. Оболочки с
нулём открытых входов нет (по проверенному корпусу, не невозможность). Лучшая, H1: неравенство
Коши–Буняковского в reciprocal-mode координатах. Один открытый вход, он же новый атом:
`Σ_{n≤N}|Δ_n|²/n² ≤ C/L⁴`. Из него сразу обе компоненты: `W ≤ π√C/(√6L²)` и
`sup_{n≤XL/2π}|Δ_n| ≤ X√C/(2πL)`. Атом сильнее, чем N+I, но структурно меньше, чем
устойчивость собственного уравнения: один скаляр, без обращения, без рекуррентности, без
trial-посредника. Полная цепь: 2 аналитических входа (`COFINAL_SIMPLE_EVEN_FINITE_GROUND`,
энергия) + 2 Lean-транзакции = 4 обязательства до потребителя.

**Слепое сравнение.** Запечатанный кандидат наблюдателя («энергия Вейля прижимает к нулям
дзеты») УБИТ: без RH зеро-сторонняя эрмитова сумма индефинитна, «энергия мала ⇒ значения малы»
кругово; и он давал только I. Моё предсказание совпадения 0.35 опровергнуто. Предсказание
«лучшая оболочка с одним открытым входом» 0.55 подтверждено.

**Оболочка CCM в типизированном виде (Q3):** H6, два открытых входа: crosswalk конечный ↔
континуальный trial и одна ставка `|A|L^{5/2}√p = O(1)`. Строго сильнее H1 как обязательство.

**Следующий ход:** read-only preflight `GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT`
(уточняет провалившийся eigen-equation preflight: искать исходное тождество для `‖RΔ‖²`);
при провале H2 (дискретный Харди по разностям соседних мод), затем H6.

## 2026-09-04 (01:50) — зонд 10: тождества решёточного уравнения точны; хвостовая связь НЕ ведущий член; диагональный дефект не вырождается

**Что произошло.** Зонд 10 (аддендум 11, пять production-ячеек, 146 с). Тождества LATTICE-1/2
из preflight воспроизводят матрицу билдера до `1.6e-233` (dps 240) и `9.6e-892` (dps 900):
вывод агента верен алгебраически. `P_LATTICE_IDENTITIES_EXACT` CONFIRMED.
`P_DIAGONAL_DEFECT_NONDEGENERATE` CONFIRMED: `min|D_n|/max|D_n| = 0.015…0.054`, без спада от
`m=13` до `163`; `min|D_n| = 0.047…0.117`. Новый объект живой.
`P_TAIL_COUPLING_IS_LEADING` REFUTED: `|ρ_n(⌊L⌋)|/|D_n y_n| ≤ 0.254` везде, на `m=163`
`0.006, 0.023, 0.061` для `n=1,2,3`. `P_SHAT_SHARP` REFUTED: `Ŝ ≈ +1/(√2L²)`, положительный,
`Σ_j y_j/d_j ≈ −6e-3` почти не зависит от `L`.

**Странность, записанная до объяснения.** Preflight назвал уравнение неподвижной точкой,
потому что хвост `j > n₀` есть хвост самого `E`. Численно этот хвост составляет ≤ 25 % от
`D_n y_n`, а на `m=163` единицы процентов, и доля падает с `m`. Два прочтения. (A) Хвост мал
численно, но структурно остаётся хвостом `E`, и любая оценка обязана его контролировать: тогда
малость ничего не даёт без априорной оценки хвостовой массы. (B) Хвост мал настолько, что
уравнение на низких модах есть сжимающее отображение с коэффициентом ≤ 0.25: неподвижная точка
с сжатием ЕСТЬ оценка, и тогда нужна не хвостовая масса, а только коэффициент сжатия из
исходных формул плюс `|D_n| ≥ δ`. Различающий исход: выражается ли коэффициент
`|ρ_n|/|D_n y_n|` через исходные коэффициенты `n²(|b_j|+|b_n|)/j²` без `y_j`, то есть
как оператор-норма, а не как значение на конкретном `y`. Передано агенту energy-preflight.

**Следующий ход:** energy-preflight (идёт) с этими числами; отчёт судье по обоим preflight и
зонду 10 в одном батче.

## 2026-09-04 (02:20) — развилка: точное тождество для энергии есть; цена — нечётный пол 10⁻⁴, не 10⁻³⁰⁰

**Что произошло.** Energy-preflight (Opus, read-only, по директиве `99927f01`): код
`P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP`, половина GAP. Тождество (MAIN) найдено,
точное, без обращения: `Σ δ_n|Δ_n|²/n² + 2Σ_{n≠m}(b_n−b_m)Δ_nΔ_m/(n²−m²) = −ΣΔ_n𝓡(y)_n/n² +
(ν−λ₁)ΣΔ_n(1−y_n)/n²`, обе части равны `½⟨RΔ,(D−λ₁)RΔ⟩`. Полюс входит одним скаляром в квадрате,
и этот скаляр — знаковый `W`-момент, то есть цель под другим именем, с усилением `L√m`. Левая часть
— нечётно-секторная форма; её диагональ `δ_n = D_n − 32π²A_L n²/d_n² ≈ 10⁻⁴`. Чтобы дойти до
`‖RΔ‖²`, нужен нечётный пол: граница `SELECTED_FERRERS_ODD_SECTOR_UNIFORM_SOURCE_COERCIVITY…`,
закрытая 30.08 как NO_SOURCE («вход только с новой математикой»).
Сжатие (прочтение B зонда 10): коэффициент выражается как операторная норма из источника, но он
`≥ 4.8…15.9`, растёт как `√m`; 25 % зонда 10 — значение на конкретном векторе, не малость
оператора. Прочтение A подтверждено. Единственная починка — Шерман–Моррисон по полюсу ранга один,
и она упирается в тот же нечётный пол через `q_ap = ‖diag(D)⁻¹Off^{ap}‖ < 1`.

**Два новых факта.** S7: `D_n` (архимед + простые + `λ₁`) и полюсная диагональ
`32π²A_L n²/d_n²` (из `W02`), построенные из непересекающихся частей источника, совпадают до
четырёх знаков при низких `n`, и совпадение улучшается с `m`. Прочтение A: тень исходного
тождества, эквивалентная «`b_n` постоянна по `n` до `10⁻⁴` на низких модах» — новое утверждение об
источнике. Прочтение B: совпадение на пяти ячейках. Различает `D^odd_{12}`: A предсказывает
`≤ 3·10⁻⁴` при полюсной части `−2.31`. S8: нечётный пол измерен впервые: `10⁻⁴`, не `10⁻³⁰⁰`;
утверждение C5, что нечётный сектор избегает схлопнутой чётной пары, верно.

**Следующий ход:** зонд 11 (аддендум 12: тождество, `D^odd_{12}`, `λ_min` нечётного блока,
`q_ap`, `ρ_stab`, вариация `b_n`); батч судье `REQ-2026-09-04-ENERGYFLOOR`: оба preflight + зонд
10 + вопрос о повторном открытии границы 30.08 на основании S7/S8.

## 2026-09-04 (03:10) — S7 разоблачён: «совпадение из разных частей источника» есть определение δ_n; первый датум аксиомы владельца

**Что произошло.** Таблица S7 без собственной задачи (`phase5_codex/s7_table.py`, 588 окон
`m = 13…600`, `n ≤ 12`, 11 с): отношение `D_n/P_n → 1` (при `n=1`: `1.0018` на `m=13`,
`1.000008` на `m=600`), `δ_n > 0` на всех 7056 записях, `δ_n ≈ n²·δ_1(m)` при малых `n`
(отношения `1, 4.1, 9.6, 18, 31, 49`), `δ_1·L²` колеблется в `[4.6e-4, 5.2e-3]` без тренда —
арифметическая величина (зависит от простых около `m`), не гладкая в `L`.
Проверка в arb: `δ_n ≡ τ(n,n) − τ(n,0)` до `10⁻⁶¹`, и `W02(n,n) ≡ A_L/d_n − 32π²n²A_L/d_n²` точно.
Значит утверждение energy-preflight «`D_n` и полюсная диагональ построены из непересекающихся
частей источника» ЛОЖНО: `D_n = −W_ℝ(n,n) − Prime(n,n) − b_n + p_n` содержит полюс через `a_n`, и
`D_n − P_n` есть ровно `τ(n,n) − b_n`, то есть определение `δ_n` из того же отчёта (§3.3). S7 не
новое тождество, а переписанное определение. Утверждение «`b_n` постоянна по `n` до `10⁻⁴`» тоже
ложно: вариация `b_n` на `n ≤ 8` от 0.04 до 3.0.
**Датум аксиомы владельца (04.09):** агент Opus подал тавтологию как «странность, требующую
внимания судьи». Проверено другим каналом (arb, свой скрипт) за 11 секунд.

**Что настоящее.** Диагональ нечётного сектора `δ_n = τ(n,n) − τ(n,0)` мала, положительна на 588
окнах, `∝ n²`, арифметична. В картине разделённых разностей: `τ(n,n)` — производная, `τ(n,0)` —
хорда; `δ_n` — кривизна профиля `B(u) = u·b(√u)` у `u = 0`. Пол нечётного блока (`λ_min`) может
быть меньше `δ_n` из-за внедиагонали — измеряет зонд 11.

**Следующий ход:** gplearn на форме `δ_n/δ_1(m)` по `(n, L)`; зонд 11; батч судье с этой поправкой.

## 2026-09-04 (вечер 03.09 по часам машины, ≈21:15 CEST) — зонд 11: тождество энергии верно и бесполезно; нечётный пол схлопнут; строка Ξ — квазисобственный вектор

**Что произошло.** Зонд 11 (аддендум 12, некруговая проверка: левая часть из собственного
вектора и нечётного блока билдера, правая из невязки через произведение матрицы на вектор).
`P_ENERGY_IDENTITY_EXACT` CONFIRMED: тождество (MAIN) выдержало пятый канал. Остальные четыре
предсказания REFUTED. Итоги, в порядке важности:
1. **Строка Ξ почти решает собственное уравнение.** `‖R𝓡(y)‖ = 4.5e-10, 7.2e-16, 3.9e-23,
   1.5e-38, 5.9e-67` на `m = 13…163` (спад ≈ `10^{−0.4m}`), `ν(y) = (K̃y)_0` того же порядка.
   При этом `‖RΔ‖ = 2.7e-2 … 9.9e-3`: ground-вектор отличается от строки Ξ на `10⁻²`, хотя
   обе имеют невязку `< 10⁻¹⁰`. Отношение `ρ_stab = 6e7 … 1.7e64`. Смысл: собственное
   уравнение НЕ содержит информации о `Δ` на масштабе `10⁻²`; любая оценка `Δ` через невязку
   платит `10^{64}` и выше. Это самая точная формулировка стены за всё время.
2. **Нечётный пол схлопнут:** `λ_min((D−λ₁)|_odd) = 6.4e-28, 1.5e-48, 3.6e-87, 2.9e-158,
   6.4e-290` — тот же порядок, что чётный `λ₁ ≈ 10^{−1.9m}`. S8 («`10⁻⁴`, не `10^{300}`»)
   ЛОЖЬ агента: он взял диагональ за пол. Спектр нечётного блока убывает геометрически
   (`4.46, 1.9e-2, 3.0e-5, 4.9e-8, 7.8e-11 …`, множитель ≈ `1.6e-3` на моду). C5 избегает
   второй чётной пары, но не схлопывания.
3. **Тождество (MAIN) точное и бесполезное:** его значение `Q = 1e-19 … 2.6e-134` при членах
   порядка `10⁻⁴…10⁻⁶`; глубина сокращения растёт как `10^{−0.7m}`.
4. `q_ap = 6.4 … 20` (сжатия нет), `D^odd_{12} = 1.7e-3 … 2.9e-4` при полюсной части
   `−0.23 … −1.4`: внедиагональ нечётного блока тоже почти нулевая на низких модах.
   Вариация `b_n` 0.14 … 2.8.

**Датумы аксиомы владельца за ночь:** S7 (тавтология), S8 (диагональ выдана за пол), «сжатия
нет» из неполной таблицы (E2), асимптотика вне режима (`n ≪ L/4π` требует `m > 2.9·10⁵`).
Формулы устояли во всех случаях; лгали выводы и заголовки. Пять каналов на тождество: агент,
самопроверка, слепой вывод, зонд 11, судья (ждём).

**Кандидат в объяснение схлопывания (relay, не проверено):** матрицы с displacement rank 2
(Лёвнер/Пик/Коши) имеют геометрически убывающие сингулярные числа (Beckermann–Townsend 2017,
Zolotarev numbers; Beckermann 2000 для PSD Hankel). Если это теорема для нашего столбца, то
`λ₁ ≈ 10^{−1.9m}` доказано, и все полы во всех секторах мертвы структурно, навсегда.

**Следующий ход:** батч судье `REQ-2026-09-04-QUASIEIGEN`: (а) строка Ξ как квазисобственный
вектор с невязкой `10^{−0.4m}` — какая НЕспектральная структура выделяет ground-вектор среди
квазисобственных (вещественные нули P59? минимальность? знаки?); (б) Beckermann–Townsend как
теорема о схлопывании; (в) статус H1/H2/H6 после зонда 11.

## 2026-09-04 — проверка пола нечётного блока вторым каналом (наблюдатель, свой код): зонд 11 верен; ошибка была у судьи, пересказавшего S8 агента

Владелец усомнился в числе зонда 11 («пять каналов сходятся, у зонда ошибка»). Пересчёт своим кодом
(`conventions.odd_block`, `full_matrix`, `acb_mat.eig`, dps 120/150/240): `λ_min(odd) − λ₁ =
6.409e-28, 1.511e-48, 3.649e-87` на `m = 13, 23, 43` против зонда `6.4088e-28, 1.5112e-48, 3.6487e-87`.
Нечётный спектр убывает геометрически (~5 порядков на моду), все значения положительны. Полная матрица:
минимум = чётный `λ₁` (`7.9e-31, 7.3e-52, 1.0e-90`), второе = нечётный минимум — прямое подтверждение
простого чётного дна на этих ячейках; относительная щель ПОЛНОЙ матрицы ≈ `800, 2000, 3600`, а не
`3.6e5…3.6e8` внутри чётного блока. Итог: зонд 11 верен; «`10⁴`, не `10³⁰⁰`» у судьи в живом чате —
пересказ S8 из отчёта агента на GitHub. Аксиома «вывод агента ложен, пока не проверен» действует и на
судью, когда он читает отчёты агентов.

## 2026-09-04 — зонд 12 (наблюдатель, руками): вещественные нули различают ground-вектор и строку Ξ; нули ground сходятся к γ_j как √λ₁

**Что произошло.** Аддендумы 13–14. Числитель P59-трансформа степени `2N`, корни в arb
(`phase5_codex/xi_row_zeros.py`, выход `out/xi_row_zeros.md`).
1. Ground-вектор: все корни вещественные на `m = 13, 23, 43` (`P_GROUND_REAL_ZEROS_IMPL` CONFIRMED;
   мой первый прогон показал «все комплексные» — баг сравнения шаров arb со строгим порогом, урок
   записан в скрипт).
2. Строка Ξ: 16/26, 28/46, 50/86 корней КОМПЛЕКСНЫЕ (`P_XI_ROW_TRANSFORM_REAL_ZEROS` 0.50 REFUTED).
   **Вещественность нулей — неспектральное свойство, отличающее ground-вектор от строки Ξ.** Ответ на
   Q2(a) QUASIEIGEN получен до вердикта.
3. Знаковый узор одинаков (`P_SIGN_PATTERN_SAME` CONFIRMED): не различает.
4. **Нули ground-трансформа равны нулям дзеты экспоненциально точно:** `|ρ₁ − γ₁| = 2.2e-8, 8.4e-18,
   2.0e-36` на `m = 13, 23, 43` (`P_ZERO_RATE_EXPONENTIAL` CONFIRMED с запасом: наклон `−0.93`/ед. `m`
   = `√λ₁` при `λ₁ ~ 10^{−1.9m}`); первые шесть нулей — `≤ 10^{−0.4m}`. Значения в узлах при этом
   сходятся лишь как `1/log² m` (зонд 9).

**Почему это развилка.** Ground-вектор прижат к Ξ через НУЛИ экспоненциально, а через значения в
узлах — полилогарифмически. Идентификация предела может идти через нули (Гурвиц + единственность
Адамара для чётной вещественной функции порядка 1 с заданными нулями и нормировкой), а не через `Δ_n`.
Механизм, согласующийся с числами: `⟨ξ,Kξ⟩ = λ₁ ≈ Σ_γ F_k(γ)²` ⇒ `F_k(γ_j) ~ √λ₁` ⇒ смещение нуля
`~ √λ₁`. Это запечатанный кандидат наблюдателя, убитый судьёй как круговой без RH (сумма по нулям вне
прямой индефинитна). Числа с ним согласны и НИЧЕГО не доказывают. Вопрос судье: есть ли безусловная
форма — например, «нули ground-трансформа в окне сходятся к нулям Ξ» как утверждение о конечной
форме Вейля (Groskin 2607.02828, конечный словарь Guinand–Weil), и достаточно ли сходимости нулей
плюс ограниченной кривизны для потребителя.

**Следующий ход:** после вердикта QUASIEIGEN — батч `ZEROPIN`: (а) сходимость нулей как замена
входа A; (б) безусловность механизма; (в) Lean: Гурвиц + Адамар-единственность для чётных
вещественных функций класса Лагерра–Пойи с нормировкой (что есть в Mathlib).

## 2026-09-04 — ERRATUM к зонду 12 (наблюдатель против себя): смещения нулей `2e-8 / 8e-18 / 2e-36` были артефактом поиска корней; истина сильнее

**Что произошло.** Прямая проверка: `F(ρ₁) = −1.2e-10 ≠ 0` в «корне» многочлена, а `F(γ₁) = 4.6e-29`
в настоящем нуле дзеты (m=13). `acb_poly.roots()` на числителе степени `2N` с коэффициентами `10²⁹`
вернул корни с точностью лишь `10⁻⁸` — я принял точность корневого поиска за физику. Урок записан в
скрипт: нули трансформа проверять прямым вычислением `F` и Ньютоном, не корнями многочлена.
Пункт 4 записи зонда 12 и наблюдение аддендума 14 читать так:
- `F_ground(γ_j) = C_j(m)·λ₁`, где `C_1(m) = 57.9, 58.1, 52.3, 45.5` на `m = 13, 23, 43, 83`
  (`C_1·√L ≈ 93…103`, почти постоянно); `C_2 ≈ −8e3…−4e3`, `C_3 ≈ 2.6e5…7e4`. **Значения
  ground-трансформа в нулях дзеты порядка САМОГО `λ₁` (`10^{−1.9m}`), не `√λ₁`.** Сдвиг нуля
  `ρ_j − γ_j ≈ F(γ_j)/F'(γ_j) ~ 10⁻²⁶` уже на m=13. `P_ZERO_RATE_EXPONENTIAL` CONFIRMED с запасом
  в двадцать порядков, но по другой причине, чем записано.
- Комплексные нули строки Ξ — настоящие (Ньютон на `F_y`: `z = −18.8595 + 24.6602i`, `|F_y(z)| = 0`).
  Вывод зонда 12 «вещественность нулей отличает ground-вектор от строки Ξ» стоит.

**Странность S9 (записана до объяснения).** `F_k(γ_j) ∝ λ₁` с коэффициентом, зависящим от `j`
и слабо от `m` (`∝ L^{−1/2}`). Прочтение A: точное тождество из явной формулы — `(Kξ)(γ) = λ₁ξ(γ)`,
спаренное с функционалом вычисления, даёт `F(γ) = λ₁·G_k(γ)` с `G_k` из архимедовой и простой
частей; тогда «нули ground-трансформа лежат в нулях Ξ с точностью `λ₁`» — теорема о конечной форме
Вейля, и идентификация через нули получает поставщика. Прочтение B: числовое совпадение.
Различает: выписать `G_k(γ)` из источника и сравнить с `C_j(m)` (руками, секунды на ячейку).
Механизм остаётся под вердиктом 99927f01 (сумма по нулям без RH индефинитна); числа согласны с ним
и не доказывают.

## 2026-09-04 — S9, различающий тест на пяти ячейках: для первого нуля закон `C_1(m)·L → ≈ 205` (прочтение A), для j ≥ 2 закона пока нет

`C_j(m) := F_k(γ_j)/λ₁` (единичный чётный ground-вектор). `C_1 = 57.9, 58.1, 52.3, 45.5, 40.1` на
`m = 13, 23, 43, 83, 163`; `C_1·L = 148.5, 182.1, 196.7, 201.1, 204.2` — монотонно, сходится
(`C_1·√L` не монотонно: 92.7, 102.9, 101.5, 95.6, 90.5). Вывод: `F_k(γ_1) ≈ ℓ_1·λ₁/L`, `ℓ_1 ≈ 205…210`;
для первого нуля S9 — закон, не совпадение. `C_2/C_1 = −141, −124, −103, −85, −72` — убывает; для
`j ≥ 2` зависимость от `m` иная, закон не выделен. Тест не круговой: `γ_j` входят как точки оси.
`λ₁(163) = 2.40e-294`, невязка обратной итерации `0`. Смысл для маршрута: ошибка ground-вектора
относительно Ξ (`Δ ~ 10⁻²`, полилог) устроена так, что её трансформ ГАСИТ ошибку интерполяции строки Ξ
в `γ_j` (`F_Ξrow(γ_1) = 10⁻¹⁰`, `F_ground(γ_1) = 8·10⁻²⁹` при m=13): ground-вектор — интерполянт,
подогнанный к обнулению в нулях дзеты с точностью `λ₁`. Кандидат в тождество для судьи (ZEROPIN Q2).

## 2026-09-04 — канаты пути через нули, ручная проверка (b) и (c)

(b) **Лишние нули уходят.** Положительных нулей числителя `N`; привязанных к `γ_j` (`|z−γ| < 0.05`):
`6, 12, 26` на `m = 13, 23, 43`, до высоты `37.6, 56.5, 92.5` (`≈ 1.3·x_N`, `x_N = 31.8, 46.1, 71.8`);
наименьший непривязанный ноль `41.0, 59.4, 95.0` — растёт с окном. На компактах нули сходятся к
`{±γ_j}` (три ячейки; `P_EXCESS_ZEROS_ESCAPE` 0.60 поддержано, не доказано).
(c) **Кривизна сходится к `κ_Ξ`.** Из зонда 4: `κ_k − κ_Ξ = 0.0028, 0.0032, 0.0027, 0.0021, 0.0014`
на `m = 13…163`, `(κ_k − κ_Ξ)·L² ≈ 0.018, 0.031, 0.038, 0.041, 0.036` — спад `~1/L²`, тот же темп,
что у `W_k`. Множитель `e^{az²}` в единственности Адамара численно обнуляется.
Открытыми остаются (a) поставщик сходимости нулей, (d) безусловность, (e) Lean-единственность.

## 2026-09-04 — развилка: вердикт QUASIEIGEN `9b822624` — линейные оболочки собственного уравнения исчерпаны; атом = селектор вещественно-нулевых квазисобственных векторов

**Что сказал судья.** (Q1) Квазисобственность строки Ξ: теорема не выведена; темп не `10^{−cm}`, а
растянутая экспонента `exp(−π²m/(2 log m))` — это хвост `Ξ ~ e^{−πt/4}` на краю окна `x_N = 2πm/L`;
механизм: строка Ξ как периодизация глобальной нулевой строки (Пуассон) плюс усечение; ни в CCM 7.3,
ни у Groskin этого нет. (Q2) **Общая жёсткость по вещественным нулям МЕРТВА**: плант Робена
`cos(πz/h)` и `cos(πz/h) − a(πz/h)sin(πz/h)` — обе чётные, вещественно-нулевые, одного типа,
совпадают на ВСЕЙ решётке Найквиста и различны. Минимальность без модуля мертва (плант 2×2).
Кривизна — не селектор (аффинное множество уровня). Новый атом: **модуль селектора** `ω_m(ε) =
sup ‖R(v−y)‖` по чётным центр-нормированным строкам с невязкой `≤ ε` и точным исходным свойством
вещественных нулей; цель `ω_m(ε_m) = O(log⁻² m)`. (Q3) Beckermann–Townsend не применим (A = B = X);
одноузловая структура Лёвнера ⇒ схлопывание — МЕРТВО (конфлюэнтный плант Эрмита реализует любую
диагональ). (Q4) H1 закрыта как нерешающее представление, H2 закрыта, H6 только после нового
источникового теоремы; точная формулировка: «нет ЛИНЕЙНОГО поставщика устойчивости из собственного
уравнения»; атом переезжает в идентификацию.

**Сверка с зондом 12 (руками, до вердикта).** Судья пишет «вещественность нулей строки Ξ неизвестна,
RH её не даёт». Зонд 12: она ЛОЖНА — 16/26, 28/46, 50/86 комплексных нулей, Ньютон подтверждает.
Это в пользу SEL: строка Ξ не в допустимом множестве, и вопрос — насколько тонок вещественно-нулевой
компонент вокруг неё. Плант Робена не бьёт по пути через НУЛИ: у `cos` и у функции Робена нули
разные; сходимость нулей (канат a) плюс контроль типа/кривизны (канат c) — это и есть единственность,
которую плант не опровергает. Черновик ZEROPIN уточнён и привязывается.

**Убито:** общая вещественно-нулевая жёсткость на решётке; устойчивость квазиминимизатора без модуля;
displacement ⇒ схлопывание; кривизна как идентификатор. **Открыто:** SEL-модуль; теорема о темпе
невязки строки Ξ; теорема о схлопывании.
**Следующий ход:** preflight судьи `GOAL058_P59_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT`
(агент Opus, read-only) + батч ZEROPIN.

## 2026-09-04 — SEL (модуль селектора судьи) убит фальсификатором: вещественно-нулевой конус не селективен

**Preflight агента** (`AGENT_REPORT_…_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT.md`): код
`P59_REALZERO_CONE_NOT_SELECTIVE`. Сильнейший предикат из Thm 5.10 на произвольной строке схлопывается
в «числитель имеет `2N` вещественных полупростых корней» (Теорема A отчёта: самосопряжённость
относительно какой-нибудь положительной формы ⟺ диагонализуемость над ℝ); удерживать метрику
самого оператора = круговщина. Допустимое множество открыто вокруг любой вещественно-нулевой строки;
`ω_m(ε) ≥ ‖R(x−y)‖` бесплатно; строгое перемежение и положительные norming constants у ground-строки
ЛОЖНЫ (5/9/20 смен знака). Фальсификатор с `Θ(1)`-нижней оценкой агент не предъявил (счёт запрещён).

**Второй канал (наблюдатель, руками).** Направление `d` = второй чётный собственный вектор с
центральной коррекцией, единичный в `R`-норме; `v(t) = x + t·d`. Невязка `v(t)` ≈ `t·λ₂` ≪ `ε_m`.
Радиус гиперболичности: в сторону `−d` корень уходит в ℂ при `t = 1.20e-3` (m=13), `5.84e-4` (m=23);
в сторону `+d` корни остаются вещественными до `t = 64` (предел поиска). При этом `‖R(x−y)‖ = 2.7e-2`.
**Фальсификатор предъявлен:** `v = x + 64·d` — чётная, `v_0 = 1`, вещественно-нулевая, невязка
`~10⁻²³`, `‖R(v−y)‖ ≥ 63`. `ω_m(ε_m) ≥ 63` на двух ячейках. SEL мёртв как атом.
Побочный факт: конус вещественных нулей вокруг дна ОДНОСТОРОННЕ тонкий (`~10⁻³`, убывает с m) —
дно сидит у края конуса, не внутри; направление «внутрь» ведёт от `Ξ`, а не к ней.

**Что живо после этого.** Только путь через НУЛИ (ZEROPIN, запрос `ea2bffe9` у судьи): плант Робена
и фальсификатор SEL оба про значения/конус, не про сходимость нулей к `γ_j`. Ждём вердикт.

## 2026-09-04 — развилка: вердикт ZEROPIN `1529837d` — частичное множество нулей не идентифицирует Ξ; атом = полный нулевой дивизор; R2-тождество судьи ПРОШЛО ручной тест

**Судья.** Идентификация из «ограниченная κ + вещественные нули + сходимость низких нулей» ОТВЕРГНУТА:
плант `P(z)` и `P(z)(1+εz⁴)` — одни вещественные нули, якорь, второй джет, чётность, порядок; разные
функции. Несёт нагрузку ПОЛНОЕ равенство дивизоров: сходимость счётчика нулей с кратностями на каждом
компакте, уход лишних нулей С массой `Σ1/ρ²` → 0, crosswalk к Ξ. Второй джет убирает `e^{az²}` только
ПОСЛЕ этого. Безусловного поставщика сходимости нулей в источниках нет (Groskin, CCM 5.10/7.3/§8).
Q3: сходимость низких нулей на прямой совместима с ¬RH; контрпример Гурвица требует ПОЛНОГО
поставщика; путь через нули = представление открытого моста (ground → trial), не замыкание.
Адамар в Lean НЕ нужен: выбран маршрут явного произведения; первая Lean-цель —
`QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND` (`‖Π(1−a_i z²) − 1‖ ≤ exp(‖z‖²Σa_i) − 1`).
Мои предсказания: «нули замыкают вход A» опровергнуто как сформулировано; «судья назовёт путь через
нули главным» опровергнуто; уход лишних нулей и сходимость κ — не разрешены (нужна масса, не только уход).

**R2 — кандидат в тождество для S9: `e(γ) = K·b(γ)` с `b` ограниченным.** Ручной тест
(наблюдатель; НЕ прекоммичен — записан как наблюдение, предсказания на расширение см. аддендум 15):
компоненты `⟨e(t),u_i⟩/λ_i` по собственным векторам чётного блока.
- `t = γ₁`: `+57.9, −4.6, +1.0, −0.22, −0.28, +0.14` (m=13); `−58.1, +4.7, −1.0, +0.25 …` (m=23);
  `+52.3, −4.4, +0.99, −0.22 …` (m=43). `‖b‖₂ = 58.1, 58.3, 52.5`. Первая компонента = `C_1` из S9.
- `t = 15` (не ноль дзеты): `‖b‖₂ = 8e26, 8e47, 7e86` — растёт как `1/λ₁`.
**Вектор вычисления в нуле дзеты лежит в хорошо обусловленном образе матрицы Вейля; в не-нуле — нет.**
Контраст 80 порядков. Это конечная явная формула в действии и утверждение БЕЗ ground-вектора:
про `K` и `γ`. Его равномерность по `m` — содержание теоремы; его RH-статус (что для нуля вне прямой?)
— вопрос судье. Следствие: `F_ground(γ) = λ₁⟨b,ξ⟩` — S9 объяснён при условии тождества.

**Следующий ход:** аддендум 15 (расширение теста: `m = 83, 163`; `γ_2, γ_3`; комплексная точка
`γ₁ + 0.1i`; предсказания заморожены до счёта); бумажный preflight на вывод `e(γ) = Kb` из конечного
словаря Guinand–Weil (Groskin 2607.02828); Lean `QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND`.

## 2026-09-04 — зонд 13 (аддендум 15, руками): тождество образа `e(γ) = K b(γ)` держится по `m`, по `j`, и видит прямую

`|F_ground(γ_j)/λ₁|` (= первая компонента `b(γ_j)`; `‖b‖` совпадает с ней до 0.5 %):
| m | γ₁ | γ₂ | γ₃ | не-ноль t=15 | вне прямой γ₁+0.1i |
|---|---|---|---|---|---|
| 13 | 57.9 | 8.2e3 | 2.6e5 | 8e26 | 1.7e26 |
| 23 | 58.1 | 7.2e3 | 1.8e5 | 8e47 | 1.8e47 |
| 43 | 52.3 | 5.4e3 | 1.1e5 | 7e86 | 1.4e86 |
| 83 | 45.7 | 3.9e3 | 6.8e4 | 10^158 | 10^158 |
| 163 | 39.8 | 2.9e3 | 4.4e4 | 10^291 | 10^290 |
`P_RANGE_IDENTITY_UNIFORM_IN_M` CONFIRMED (45.7, 39.8 ∈ [30,80]); `P_RANGE_IDENTITY_HIGHER_ZEROS` CONFIRMED
(≤ 1e6 везде; `C_j` УБЫВАЕТ с m для j ≥ 2); `P_RANGE_IDENTITY_SEES_THE_LINE` CONFIRMED (точка γ₁+0.1i
ведёт себя как не-ноль: `10^86` против `52` на m=43). Оговорка: «видит прямую» здесь значит лишь, что
точка вне нулевого множества плохая; нулей вне прямой для теста не существует — RH-статус тождества
решает бумага (агент + судья), не эта таблица.
**Датум аксиомы (против наблюдателя):** в пакетном прогоне точки `γ_j` были созданы до установки
`ctx.dps` (15 знаков) → ложное `2e10` для γ₂ на m=13; поймано сверкой прямого и спектрального счёта
(`−8159` оба). Второй прецизионный баг за вечер того же класса; правило в скрипты: точность ставится
ДО создания любого arb/acb.

## 2026-09-04 — бумажный preflight по R2 (НЕ ПРОВЕРЕНО): `K = Σ_z E(z)E(z)ᵀ` по всем нулям дзеты (Groskin Thm 2.5 + CCM 5.9); тест суммой запущен

**Агент** (`AGENT_REPORT_2026-09-04_GOAL058_P59_EVALUATION_RANGE_IDENTITY_PREFLIGHT.md`, 475 строк):
`tau_entry = w02 − wr − prime` есть `Q∞` Гроскина; `E(z)` — вектор фурье-образов базиса (CCM 5.9,
(5.25)); утверждаемое тождество `⟨v,Kv⟩ = Σ_{z: ζ(1/2+iz)=0} F_v(z)²`, абсолютно сходится, безусловно,
без хвостовых членов. Следствия: под RH `|F_{u_i}(γ)| ≤ √(λ_i/2)` (полстепени слабее наблюдаемого
`F ~ λ₁`; агент: «первый недостающий шаг — ровно полстепени `λ₁`»); `e(γ)=Kb(γ)` как «range identity»
пусто (`K` обратима), содержание в `‖b‖`; kill-power R2 против полного дивизора ≈ 0; `1/L` в
`C_1·L → 205` выведен через воспроизводящее ядро `2R(γ,γ) ≈ L`; сама 205 не предсказана;
`F_ground(γ) = λ₁⟨b,ξ⟩` — тавтология. RH-статус: тождество безусловно, но рабочее направление
«малая энергия ⇒ малые значения в нулях» требует неотрицательности внелинейного вклада = RH; это
механизм, убитый в `99927f01`.

**Решающая проверка (наблюдатель, правило 13, запущена):** если `K = Σ_z E E ᵀ` точно, то для
ЛЮБОГО `v` `⟨v,Kv⟩ = Σ_z F_v(z)²`. Тест на единичных модах, где нет малых чисел: `τ(0,0)` против
`Σ_γ 2F_{e₀}(γ)²`, `τ(1,1)` и `τ(1,0)` аналогично, по 3000 нулям (до `γ ≈ 4000`). Если суммы не
сходятся к `τ`, тождество агента неверно КАК СФОРМУЛИРОВАНО (веса, знак, усечение или другой
трансформ). Отдельно: для дна `Σ_z F_ξ(z)² = λ₁ ≈ 10⁻³⁰` потребовало бы, чтобы `F_ξ` была крошечной
во ВСЕХ нулях, включая далеко за окном, где непривязанные нули дна отстоят от `γ_j` на 0.1–0.6 —
это выглядит невозможным без дополнительных членов. Записано до результата.

## 2026-09-04 — тождество `K = Σ_z E(z)E(z)ᵀ` ПРОВЕРЕНО суммой; сомнение наблюдателя опровергнуто; `λ₁` = утечка за окно

**Тест суммой (наблюдатель, 3000 нулей до γ ≈ 3533, 23 мин):** `τ(0,0) = 0.045333` против частичных
сумм `0.039784, 0.042515, 0.044086, 0.044768` (J = 100, 300, 1000, 3000); `τ(1,1) = 0.046512` против
`0.045947`; `τ(1,0) = 0.045720` против `0.045155` (m=13); на m=23 то же с невязкой `4.6e-4`. Хвост
`~log γ/γ` объясняет остаток. **Тождество агента верно: `⟨v,Kv⟩ = Σ_{z: ζ(1/2+iz)=0} F_v(z)²`** для
базисных мод, следовательно для всех `v` (билинейность). Датум против наблюдателя: априорное
«сумма была бы 10⁻², а не 10⁻³⁰» — ложь, см. ниже почему.

**Механизм (руками):** чётные моменты единичного дна `M_{2p} = Σ_k c_k x_k^{2p}`: `M_0 = 5e-15`
(m=13, `√λ₁ = 9e-16`), `M_0 = −2e-25` (m=23, `√λ₁ = 3e-26`), `M_0 = 9e-45` (m=43, `√λ₁ = 1e-45`);
`M_2, M_4, …` растут ступенями `~10^{5…6}`. Амплитуда `|F_ξ(t)|` ЗА окном: `3.5e-17, 4.3e-18, 7.4e-19`
на `t = 3x_N, 10x_N, 100x_N` (m=13); `3e-28 … 2e-29` (m=23); `2e-47 … 6e-49` (m=43) — везде `~√λ₁`.
**Ground-трансформ — функция, сосредоточенная в окне с утечкой `√λ₁` наружу.** Отсюда
`λ₁ = Σ_z F_ξ(z)² ≈ Σ_{|γ|>x_N} F_ξ(γ)²` — энергия Вейля дна есть УТЕЧКА ЗА ОКНО; внутренние нули дают
`F ~ λ₁`, вклад `λ₁²`, пренебрежимо. S9 объяснён: внутри окна обнуление в `γ_j` — эффект второго
порядка (первый порядок «бесплатен»), снаружи — первый. «Непривязанные нули» дна (41, 44, 50, 63 …)
лежат там, где `|F| ~ √λ₁`, и физического смысла не имеют.

**Что это меняет.** (1) Есть безусловное исходное тождество, связывающее матрицу с нулями: явная
формула на базисе окна (Groskin Thm 2.5 / CCM 5.9). (2) Под RH все члены `≥ 0` ⇒ `|F_ξ(γ)| ≤ √(λ₁/2)`
для ВСЕХ нулей — сходимость дна к нулям Ξ ВНУТРИ окна с точностью `√λ₁`; это условно (RH). (3) Без RH:
нуль вне прямой `ρ = γ + iδ` даёт член `2Re F_ξ(ρ)²` (с `ρ̄`), возможно отрицательный; `λ₁ > 0` на всех
`m` наблюдается. Вопрос судье: даёт ли `λ₁ > 0` (или структура утечки) что-нибудь безусловное.
**Следующий ход:** батч `REQ-2026-09-04-LEAKAGE`.

## 2026-09-04 — проверено по тексту CCM: теорема 5.10 НЕ зависит от знака `λ₁`; «дверь 2» в форме «5.10 выключается при `λ₁ < 0`» ложна

CCM 2511.22755, §5.2 и Thm 5.10 (pdftotext, строки 899–930, 1251–1256): «Let ε_N be the smallest
eigenvalue of QW_λ^N assumed simple and ξ the corresponding eigenvector assumed even»; операторная
конструкция использует `T := QW − ε_N⟨|⟩`, и «We now assume that T is even simple and positive» —
`T ≥ 0` выполнено ПО ОПРЕДЕЛЕНИЮ `ε_N` как наименьшего собственного значения, при любом знаке `ε_N`.
Следствие: при ¬RH и `λ₁ < 0` (критерий Вейля на большом окне) теорема 5.10 продолжает давать
вещественные нули ground-трансформа. Противоречия отсюда по-прежнему нет: тождество
`Σ_z F_ξ(z)² = λ₁ < 0` лишь говорит, что вклад нулей вне прямой отрицателен и `|F_ξ(ρ)|² ≳ |λ₁|`, что
совместимо с классом Лагерра–Пойи. Где RH прячется на самом деле: в шаге «все члены ≥ 0 ⇒ `F_ξ`
мала в нулях ⇒ идентификация предела». То есть идентификация ⇔ позитивность на семье окон.
§8 CCM дословно: два недостающих шага — simple-even для всех λ и «convergence of the zeros of ξ̂_λ
towards the non-trivial zeros» — это наш ZEROPIN, авторы целят туда же.
Поправка к батчу LEAKAGE Q4: посылка «5.10 требует положительности» неверна; судья читает статью сам.

## 2026-09-04 — развилка: вердикт LEAKAGE — тождество подтверждено; позитивность выбранной ячейки ≠ RH без исчерпания; литкарточка позитивности Вейля

**Судья (LEAKAGE).** (Q1) Тождество `⟨v,K_even v⟩ = Σ_z F_v(z)²` подтверждено для вещественного чётного
сектора, без усечения, с цепочкой Groskin L2.1/L2.2/Thm 2.5 + CCM 5.9. Для Lean явная формула — новый
аналитический импорт. (Q2) `λ₁ = min Σ_z F_v(z)²/‖v‖²` безусловно; «энергия нулей» как сумма
неотрицательных членов — только под RH (внелинейный квартет даёт `4Re F(z₀)²`, знак любой).
Позитивность для ВСЕХ `N` на кофинальной семье окон плюс crosswalk к ядру формы ⇔ позитивность
Вейля ⇔ RH. Наше расписание `N = m` (одна ячейка на окно) НЕ эквивалентно RH без теоремы исчерпания:
даёт позитивность только на выбранных подпространствах. Маршрут через позитивность =
переформулировка RH; маршрут через вещественно-нулевую семью ЭТИМ не убит. (Q3) Безусловная норма
утечки отвергнута (индефинитность вне RH); под RH `K` — положительный Gram-оператор выборки в
вещественных ординатах нулей, `λ₁` = квадрат наименьшего сингулярного числа; ближайшие имена:
локализованный минимизатор Bombieri 2000 и концентрация Слепяна; стандартного имени нет. (Q4) ¬RH ⇒
отрицательное локализованное направление Вейля ⇒ отрицательная конечная компрессия (форма теоремы,
Bombieri: отрицательный индекс = половина числа нулей вне прямой). «Невещественный ноль дна при ¬RH»
УБИТ: 5.10 не зависит от знака `λ₁` (совпало с моим чтением). Круг назван: доказать позитивность на
исчерпывающем ядре = доказать RH, 5.10 и Гурвиц для этого не нужны.
**Новый дискриминатор:** разность чисел вращения `F_ground` и `F_trial` на границе компакта (принцип
аргумента; плант `F·(1 − z²/a²)` даёт +2). Следующий ход судьи: бумажный preflight
`P59_ANCHORED_LOG_DERIVATIVE_FIXED_COMPACT` — «winding lock»: граница без нулей и
`length/(2π)·sup|разность лог-производных| < 1` ⇒ равные числа нулей с кратностями.

**Литкарточка** (`litreview/WEIL_POSITIVITY_OBJECT_CARD_2026-09-04.md`, агент, локаторы + цитаты):
все безусловные доказательства позитивности останавливаются на `L = log 2` (Yoshida 1992 Thm 1
`a ≤ log2/2`; Bombieri 2000 Thm 12 `|I| < log 2`; Connes–Consani 2021 Thm 1/6.11 `supp ⊂ [2^{−1/2},
2^{1/2}]`; Suzuki 2606.09096 «sufficiently small»). Connes 2602.04022 §4.1 о методе Yoshida: «no
conceptual reason … when primes are involved». Наше окно `m=13`: `L = 2.565`, в 3.7 раза дальше,
девять простых степеней внутри. Пункт 3: позитивность на конечномерном подсемействе строго слабее RH
(`λ₁(m,N)` невозрастает по `N`, CCM Prop 3.4; Groskin Rem. 2.6 «no claim … arbitrary test
functions»); эквивалент RH только при двойном кванторе «все m и все N» — то же, что сказал судья.
CCM НЕ предполагают `λ₁ > 0` (третий канал). Единственная линия «конечный срез → безусловный
результат» идёт через СИГНАТУРУ (Alpöge–Furman 2608.13637, Lamzouri 2609.02882: доля 67.25 %), не
через пол. Открытые долги: порог `a₀` Yoshida (тот же объект, что наш «абсолютный пол»?), мост
Lagarias 2007 (Li ↔ Вейль), Li/Bombieri–Lagarias/Voros/Sekatskii — UNVERIFIED (нет PDF).

**Итог ночи одним абзацем.** Стена названа тремя каналами одинаково: идентификация предела ⇔
позитивность Вейля на исчерпывающем семействе окон; наше расписание это семейство не исчерпывает, и
потому `λ₁ > 0` на всех ячейках — не RH, а позитивность на выбранных подпространствах. Живой
незакольцованный путь один: полный нулевой дивизор на компактах через принцип аргумента (winding
lock) плюс масса лишних нулей плюс второй джет. Всё остальное этой ночи — либо переформулировка,
либо диагностика.

## 2026-09-04 — winding lock: круг проваливается (мнимая ось), тонкий прямоугольник держится; связывающий член — относительная ошибка в ОДНОЙ точке на вещественной оси

**Preflight агента** (`AGENT_REPORT_2026-09-04_GOAL058_WINDING_LOCK_FIXED_COMPACT_PREFLIGHT.md`): после
сокращения общего множителя `2L^{−1/2} sin(zL/2)` (и `Q(z)` тоже) разность лог-производных ground/trial
есть `P_g'/P_g − P_t'/P_t`, интеграл по `∂D` равен разности чисел корней многочленов степени `2N`;
форма «длина/(2π)·sup < 1» ⇒ ноль. Для пары ground/Ξ в форме Руше первый неконтролируемый член — одно
вещественное граничное значение `|F_g(R)|` (не `Δ_n`, слабее), закрываемое выбором `R` на узле, где
`F_g(x_n) = √L(−1)^n v_n` точно (Lean-теорема есть); в «длинной» форме — хвостовая масса `Σ1/ρ²`
далёких нулей. Три находки: круг структурно вне бюджета для ground/Ξ (несовпадение типов), концентрический
замок слеп к сдвинутому нулю (а это конфигурация ¬RH), Mathlib: есть `logDeriv`, дивизоры мероморфных,
формула Йенсена, Неванлинна; НЕТ числа вращения, принципа аргумента, Руше, Гурвица, Адамара.

**Проверка руками (аддендум 16, записан после прогона).** Круг `|z| = R`: Руше ПРОВАЛИВАЕТСЯ на всех
ячейках, худшая точка `z = iR` (мнимая ось): `1.18, 2.21, 3.77` при `R = 18, 23, 28` (m=13), хуже с `m`.
Находка агента подтверждена: типы расходятся вдоль мнимой оси. Тонкий прямоугольник
`[−R,R]×[−h,h]`, `h = 0.5…2`: ДЕРЖИТСЯ везде, худшая точка на вещественном конце `(±R, h)`:
`0.66/0.66/0.60` (R=18), `0.97/0.95/0.90` (R=28) на m = 13/23/43; от `h` почти не зависит; убывает с `m`.
**Следствие:** на тонком прямоугольнике равенство чисел нулей с кратностями между `−R` и `R` СЕРТИФИЦИРОВАНО
Руше на наших ячейках, и связывающая величина — относительная ошибка `|F_g − Ξ|/|Ξ|` в одной вещественной
точке `x = ±R`. Вопрос полного дивизора на компакте свёлся к компоненте I (`f788d2fa`) в её слабейшей
форме: поточечная сходимость на вещественной оси с точностью «меньше единицы относительно `Ξ`», не sup
по узлам и не → 0. Локальный вариант (прямоугольник вокруг одного `γ_j`) даёт положение нуля с точностью
`δ` при `|Δ| < δ|Ξ'(γ_j)|` — тот же член. Нормальность и хвостовая масса из вопроса о СЧЁТЕ выпали.
Чего замок НЕ даёт: сдвиг нуля внутри (агент, находка 3) — закрывается локальными прямоугольниками;
Lean: нужен полиномиальный принцип аргумента (меньше общего). **Следующий ход:** батч `WINDLOCK`.

## 2026-09-04 — зонд 14, продолжение (предсказания аддендума 16, счёт до и после убийства фоновой задачи)

Прямоугольник `h = 1`: `R=28`: `0.809` (m=83), `0.674` (m=163) — `P_RECT_LOCK_R28_IMPROVES` CONFIRMED (< 0.85, < 0.80).
`R=40`: m=13 — `1.000` в точке `x = −34.8` (за окном `x_N = 31.8`): FAILS/на грани — снаружи окна `F_g ≈ √λ₁ ≈ 0`
и отношение `|0 − Ξ|/|Ξ| → 1`, Руше не строго; m=83 — `0.968` HOLDS; m=163 — `0.900` HOLDS —
`P_RECT_LOCK_R40_FAILS_AT_M13` CONFIRMED. Ответ на Q2(b) WINDLOCK числом: за окном `e(R) → 1` снизу,
замок «бесплатно» там НЕ закрывается (нужно строго `< 1`); внутри окна `e(R)` убывает с `m` при
фиксированном `R` (`0.971 → 0.946 → 0.897 → 0.809 → 0.674` при R=28) — темп на глаз ~`1/L`.
Инцидент: фоновая задача убита harness'ом посреди счёта (третий раз за ночь); m=163 досчитан в переднем плане.

## 2026-09-04 — вердикт WINDLOCK: «атом одной точки» ЛОЖЕН (плант с четырьмя нулями); полный забор остаётся минимальным замком счёта

**Судья** (`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM_2026-09-04.md`).
(Q1) Руше на всём заборе прямоугольника — верная форма: `sup_∂D|F − X| < inf_∂D|X|` ⇒ равные числа нулей с
кратностями. Сведение к одной точке `e(R) < 1` — ЛОЖЬ: плант `X = 1`, `F = (1 − z²/a²)(1 − z²/b²)`,
`a² + b² = R²` — `F(R) = X(R) = 1`, `e(R) = 0`, четыре вещественных нуля внутри. `e(R) < 1`
сертифицирует лишь ненулёвость и общий знак в `±R`. Неравенство `|P(x+iy)| ≥ |P(x)|` — факт про
одну функцию, для разностей следствий нет; для Ξ без RH — кругово. Независимость от `h` —
диагностика. (Q2) Независимого поставщика для одной точки нет; лучшая починка — проективный перенос
ground → trial в одном узле (не обход); «точный узел + тождество Вейля» значение не определяет;
утечка как поставщик запаса УБИТА: `e → 1`, не `< 1` (совпало с моим счётом на m=13, R=40).
(Q3) Ошибки на концах ≠ сходимость дивизора. Достаточный сертификат на компакте: строгое Руше или
число вращения на всём внешнем заборе + на заборе каждой изолирующей области + кратности + сумма
локальных счётов = внешнему, для сколь угодно малых областей. На компакте хвост и второй джет НЕ
нужны (они для глобального произведения). Необходимости нет: `e^{az²}X` — тот же дивизор.
(Q4) Полиномиальный принцип аргумента на ОКРУЖНОСТИ формализуем в Mathlib 4.26 (`Polynomial.Splits.
eval_eq_prod_roots`, `logDeriv_prod`, `circleIntegral.integral_sub_inv_of_mem_ball`, Коши–Гурса вне
счётного); на прямоугольнике — новая аналитика (нет индекса/числа вращения). `centeredXi` на полке
(`Q3.RouteB.differentiable_centeredXi`). Следующий ход: Lean-плант убийства атома одной точки.

**Датум против наблюдателя.** Я вывел «атом одной точки» из того, что худшая точка забора численно
на конце. Числа верны, вывод нет: сертификат требует супремум по всему забору, и одна точка его не
заменяет. Урок в правило: численный максимум на заборе — не доказательство редукции к этой точке;
плант строится за минуту (`(1−z²/a²)(1−z²/b²)` с `a²+b²=R²`), и его надо было построить самому до
батча. Что устояло: замок на полном заборе прямоугольника, численно с запасом (`0.67` при R=28, m=163).
**Атом счёта после вердикта:** `inf_∂D|X| − sup_∂D|F − X| > 0` на всём заборе тонкого прямоугольника +
то же на изолирующих областях. Поставщик: проективный перенос ground → trial на заборе (R1 судьи).

## 2026-09-04 (глубокая ночь) — компонента I впервые измерена при ФИКСИРОВАННОМ x: сходимость `1/L²` с одной формой; лестница `Ξ·x^{2j}`; лестница как trial ПРОВАЛЕНА

**Самопроверка по указанию владельца («ты и есть Мифос, спроси себя»).** Выведено и проверено числом:
(1) `⟨Δ,KΔ⟩ = ⟨y,Ky⟩` до всех знаков (энергия Вейля разности = энергия наложения строки Ξ): `1.23e-17,
2.36e-28, 1.93e-43` на m = 13, 23, 43. (2) `Δ = ξ − y` в единичных чётных координатах: `⟨Δ,u₂⟩ ≈ 0.039, 0.043,
0.038` (доминирует), `⟨Δ,u₁⟩ ≈ 0.027` (якорь), `⟨Δ,u₃⟩ ≈ 2e-3`, дальше ×10 на моду; `‖Δ‖₂ ≈ 0.05` НЕ убывает.
(3) Трансформы `u₂, u₃` — m-НЕЗАВИСИМЫЕ функции: `max 0.76` в `x = 6.9` (u₂) и `9.9` (u₃) на m = 13…83;
они НЕ уезжают к краю окна (мой поспешный вывод «`F_{u₂}` должна уйти с компакта» — ЛОЖЬ, пойман за минуту).
(4) **Сходимость при фиксированном x (впервые; все прежние Δ были в узлах, а узлы едут):**
`Δ(x) := F_g(x)/F_g(0) − Ξ(x)/Ξ(0)`, x = 7: `−4.0e-2, −4.4e-2, −3.9e-2, −3.0e-2, −2.1e-2` на m = 13…163;
`Δ(7)·L² = −0.26, −0.44, −0.55, −0.58, −0.53` → константа с m = 43. Мой второй поспешный вывод («при
фиксированном x не сходится») — ЛОЖЬ: `⟨Δ,u₂⟩` постоянен между единичными векторами, а сходимость меряется в
якорных трансформах. (5) **Одна форма:** профиль `Δ(x)/Δ(7)` совпадает с `ψ(x)/ψ(7)`, `ψ = g₂ − g₂(0)·Ξ/Ξ(0)`
(якорная трансформа второго собственного вектора) в пределах `4–7 %` при x = 3, 5, 10 (m = 43, 83); скаляр
`a·L² = 0.57, 0.60`. Чистый `g₂` без якоря — расходится при x = 3, 5 (`P_DEVIATION_IS_SECOND_EIGENVECTOR_SHAPE`
0.65 REFUTED как сформулировано, CONFIRMED после якорной починки; `P_DEVIATION_L2_LAW` 0.70 CONFIRMED).
(6) **Лестница:** `g_i/Ξ` — чётные многочлены степени `2(i−1)`: `u₁/Ξ ≈ 0.90 − 0.0025x²` (deg-4 подгонка 0.02 %),
`u₂/Ξ ≈ 0.65 − 0.072x² + 0.0002x⁴` (0.4 %), `u₃/Ξ` квартика (0.2 %), `u₄` секстика (3 %). Почти-нулевое
пространство формы Вейля на окне ≈ `Ξ·{1, x², x⁴, …}`; идентификация = примесь `x²` в дне: `a₂/a₀ = −0.0027`
при m=43; проверка `−0.0025·49/0.90 = −0.136` против `Δ(7)/Ξ(7) = −0.126`.
(7) **Лестница как trial-семья ПРОВАЛЕНА** (аддендум 18, все три предсказания REFUTED): 4-мерный Рэлей–Ритц
на `Ξ·x^{2j}` даёт `μ₁/λ₁ = 1.7e6, 1e16, 3e36`; дефект `p = 1.0e-4, 6.5e-4, 8.5e-4` (растёт); `c₁/c₀·L² =
−0.013, −0.012, −0.008` (не закон `1/L²`, ближе к `1/L⁴`). Дно — полоснозаграниченная поправка к `Ξ·p`,
которую явные многочлены на масштабе `λ₁` не ловят; пролатный trial CCM (`p = 4.7e-9`) лучше на 5 порядков.

**Что стоит после всего:** компонента I в измеримой форме — `Δ(x) = a(m)·ψ(x) + O(мода 3)`, `a(m)·L² → ≈ 0.6`,
`ψ` фиксирована. Требуемая теорема: `a(m) = O(1/L²)` — коэффициент второго собственного вектора в якорной
нормировке. Это вырожденная теория возмущений ВНУТРИ схлопнутого подпространства, где щель входит только
как отношение утечек. Датумы против наблюдателя за час: два поспешных вывода, оба пойманы своими же числами.

## 2026-09-04 — вердикт ONESHAPE + зонд 17: точное якорное разложение подтверждено четырьмя оценками; поправка судье — якорь плоский, убывает сам `d₂`

**Судья** (`ONESHAPE`): представление починено в ТОЧНОЕ тождество: `y = Σ d_j u_j` (строка Ξ по собственному
базису), `ψ_j = F_{u_j} − ℓ(u_j)·X`, `d₁ℓ₁(G − X) = e − Σ_{j≥2} d_j ψ_j`; двухмодовая форма `G − X = a·ψ₂ + R`,
`a = −d₂/(d₁ℓ₁)`. Несущие входы: `a = O(L⁻²)` И остаток `R = o(1)` на компакте; «`u₁ → X`» как вход
запрещён (это цель). Лестница точна только как тождество с поправкой; малость поправки и порядок утечек по
степени из усечения не следуют (плант 2×2 Грама переворачивает порядок). Картинная норма ≠ норма Рэлея
(объяснение `μ₁/λ₁ = 10³⁶`: поправка живёт в спектрально дорогих направлениях; блок Фешбаха). Ход ранга 1,
цена 1/10: посчитать `a_spec` и точный остаток на готовых ячейках.

**Зонд 17 (аддендум 19, руками, все четыре предсказания CONFIRMED):**
| m | d₁ℓ₁ | d₂ | d₂·L² | a_spec | a_7 | a_LS | a_κ | a_spec·L² | max|R|/|Δ| |
|---|---|---|---|---|---|---|---|---|---|
| 13 | 0.928 | −0.0391 | −0.257 | 0.04214 | 0.04185 | 0.04127 | — | 0.277 | 0.078 |
| 23 | 0.934 | −0.0434 | −0.427 | 0.04653 | 0.04626 | 0.04558 | — | 0.457 | 0.077 |
| 43 | 0.927 | −0.0376 | −0.532 | 0.04056 | 0.04034 | 0.03986 | 0.03773 | 0.574 | 0.064 |
| 83 | 0.915 | −0.0284 | −0.555 | 0.03105 | 0.03090 | 0.03064 | 0.02939 | 0.606 | 0.047 |
| 163 | 0.904 | −0.0196 | −0.508 | 0.02164 | 0.02156 | — | — | 0.562 | 0.032 |
Точное тождество всех мод: `lhs = rhs` до трёх знаков на каждой ячейке. `κ(G) = 0.025843, 0.025168` совпали с
зондом 4 (другой код) — перекрёстная проверка; `κ(ψ₂) = 0.0726, 0.0702`.
**ПОПРАВКА СУДЬЕ (числом):** объяснение «`d₂` может оставаться O(1), потому что `d₁ℓ₁` растёт как `L²`» — ложно:
`d₁ℓ₁ = 0.93 → 0.90`, ПЛОСКО. Убывает сам сырой коэффициент `d₂ = ⟨y,u₂⟩`: `d₂·L² → ≈ −0.5`. Моё «`⟨Δ,u₂⟩` плоский»
было верно только на `m = 13…43`. Значит цель ранга 2 у судьи («`d₁ℓ₁ ≥ cL²`, `d₂ = O(1)`») надо заменить на:
`d₁ℓ₁ → const ≈ 0.9`, `d₂ = O(1/L²)` — чисто ℓ²-утверждение о перекрытии строки Ξ со вторым собственным
вектором, без якорей.
**Атом после ONESHAPE:** `⟨y, u₂⟩ = O(1/L²)` (+ хвост мод `≥ 3` `o(1/L²)` на компакте, численно 3–8 % и убывает;
+ `ψ₂ → ψ` фиксированная, численно да). Всё прочее ночи — либо переформулировка, либо диагностика.

## 2026-09-04 (утро) — тест механизма Q3 OVERLAP руками: `d₂/d₁ ≈ ∫X²q₂ / ∫X²q₁` с точностью 10 %

Профили из подгонок (deg 4): m=43: `q₁ = 0.9027 − 2.448e-3x² + 2.7e-6x⁴`, `q₂ = 0.6387 − 0.07046x² + 1.48e-4x⁴`;
m=83: `q₁ = 0.8971 − 1.840e-3x²…`, `q₂ = 0.6421 − 0.06893x²…`. Континуальные интегралы (mpmath, Ξ точная):
`I₁₁ = ∫X²q₁² = 6.283, 6.283`; `I₂₂ = 6.18, 6.22`; `I₁₂ = ∫X²q₁q₂ = −3.0e-2, −1.8e-2` (ортогональность до 0.5 %);
`I₀₁ = ∫X²q₁ = 7.142, 7.144`; `I₀₂ = ∫X²q₂ = −0.293, −0.218`.
**`I₀₂/I₀₁ = −0.0411, −0.0305` против `d₂/d₁ = −0.0366, −0.0279`** (m = 43, 83): 12 % и 10 %. Перекрытие строки Ξ
со вторым собственным вектором на ~90 % задаётся одними полиномиальными профилями; остаток — полосно-
заграничная поправка (того же порядка, что `I₁₂/I₁₁ ≈ 0.5 %`, помноженная на масштаб). Убывание `d₂` с `m` —
это дрейф коэффициентов `q₂` (`c₀ 0.6387 → 0.6421`, `c₂ −0.0705 → −0.0689`) при почти постоянном `q₁`.
Кандидат-тождество (не проверено): при точной ортогональности `d₂/d₁ ≈ (c₂'/c₀')·∫X²x²q₂/∫X²q₁ + (I₁₂-член)`,
где `c₂'/c₀' = −2.7e-3` — примесь `x²` в профиле дна: тот же малый параметр (`P_D2_IS_SAME_PARAMETER_AS_C2`).
Следующий зонд (после вердикта OVERLAP): проверить это соотношение числом и его закон `1/L²`.

## 2026-09-04 (утро) — тот же малый параметр: `d₂` на 105 % объясняется примесью `x²` в профиле дна, полосная поправка даёт −10…−13 %

Точное разложение при `q₁ = c₀' + (q₁ − c₀')`: `I₀₂ = (I₁₂ − ∫X²(q₁−c₀')q₂)/c₀'` (проверено до 4 знаков).
Вклад в `d₂/d₁` (m = 43 / 83): от члена `−c₂'x²` профиля дна — `105 % / 105 %`; от `x⁴` — `−6 % / −5 %`;
от полосно-заграничной невязки ортогональности `I₁₂` — `−13 % / −10 %`; сумма даёт измеренное с точностью
`10 %`. **Вывод:** `d₂ = ⟨y,u₂⟩` и примесь `x²` в профиле дна `c₂'/c₀'` — один и тот же малый параметр с
m-независимым множителем `∫X²x²q₂/∫X²q₁` (`P_D2_IS_SAME_PARAMETER_AS_C2` 0.55 — численно поддержано до 10 %).
Значит атом «`⟨y,u₂⟩ = O(1/L²)`» ⇔ «профиль дна `u₁/X` имеет примесь `x²` порядка `1/L²`» ⇔ «`κ(G) − κ(X) = O(1/L²)`»
(второй джет — тот же скаляр). Три записи одного числа; поставщик нужен для любой из них.

## 2026-09-04 (утро) — вердикт OVERLAP + зонд 18: точное тождество переноса кривизны; `d₂` и `α = κ(G) − κ(X)` — одно число; круг дня замкнулся на кривизне

**Судья** (`OVERLAP`): атом в чистом ℓ² подтверждён (`d₂ = ⟨y,u₂⟩ = O(L⁻²)` + комбинированный остаток
`H = o(L⁻²)` + `ψ₂ → ψ`). Точная решёточная пара без щели: `Tr_m(F_v F_w) = 2π⟨v,w⟩`; `2π d₂ = ℓ₁ Tr_m(X F₂)`;
`Tr_m(G F₂) = 0` (ортогональность); **тождество переноса кривизны** `d₂ = (ℓ₁/2π)(α M − E)`, `α = κ(G) − κ(X)`,
`M = Tr_m(z² X F₂)`, `B = G − X + α z² X`, `E = Tr_m(B F₂)`. Чистый Эйлер–Маклорен по шагу решётки как источник
`L⁻²` УБИТ (алиасинг супералгебраичен; `L⁻²` идёт от m-зависимого профиля / полосной поправки). Одна ячейка вне
`[0.4, 0.8]` маршрут не убивает (квантор). Пять конечных тождеств Lean-ready (директива, файл
`Proposition59AnchoredSecondModeOverlap.lean`, агент запущен).

**Зонд 18 (аддендум 20, руками, пять ячеек):**
| m | κ(G) | α = κ(G)−κ(X) | α·L² | M | E/(αM) | d₂/α | невязка тождества |
|---|---|---|---|---|---|---|---|
| 13 | 0.025896 | 2.79e-3 | 0.018 | −102.33 | 0.048 | −14.01 | 2e-16 |
| 23 | 0.026263 | 3.16e-3 | 0.031 | −102.52 | 0.070 | −13.76 | 2e-16 |
| 43 | 0.025843 | 2.74e-3 | 0.039 | −102.22 | 0.066 | −13.73 | 1e-15 |
| 83 | 0.025168 | 2.06e-3 | 0.040 | −101.74 | 0.052 | −13.77 | 2e-15 |
| 163 | 0.024520 | 1.41e-3 | 0.037 | −101.23 | 0.037 | −13.83 | 3e-15 |
(`κ(X) = 0.0231049931`; `κ(G)` по ТОЧНОЙ формуле второго джета, совпадает с зондом 4.)
Судьбы: `P_M_STABLE_NONZERO` CONFIRMED; `P_D2_OVER_ALPHA_STABLE` CONFIRMED (2 %); `P_E_OVER_ALPHA_M_DECREASES`
REFUTED как сформулировано (13→23 рост), но с m=23 убывает `0.070 → 0.037`, `< 0.3` — дискриминатор судьи
(«`M` устойчив, `E/(αM) → 0`») ПОДДЕРЖАН на пяти ячейках; сторона успеха его следующего шага
(`P59_SECOND_MODE_CURVATURE_TRANSFER_REMAINDER_LOWER_ORDER`) численно.

**Смысл.** `d₂ = −13.8·α` с точностью 2 %: перекрытие строки Ξ со второй модой и разность кривизн — одно число
с фиксированным множителем `ℓ₁M/2π·(1 − E/αM) ≈ −14.6·0.95`. Значит атом идентификации есть ровно
**`κ(G_m) → κ_Ξ` с темпом `1/L²`** — сходимость кривизны, и у `κ(G)` ЕСТЬ точная конечная формула
`(L²/2)[1/12 + (1/2π²v₀)Σ_{n≠0} v_n/n²]` (Lean, 03.09). Круг дня замкнулся: утром 03.09 «κ ограничена ⇒
нормальность» (Lean), вечером 04.09 «κ → κ_Ξ ⇔ идентификация» (точное тождество + числа). Стена — один скаляр,
линейный функционал от строки дна, и его асимптотика `α_m·L² → ≈ 0.04`.

## 2026-09-04 (утро) — `κ(строки Ξ) = κ_Ξ` до `10⁻¹¹`; атом = знаковая взвешенная сумма узловых ошибок `Σ Δ_n/n² = O(1/L⁴)`

По точной конечной формуле второго джета кривизна строки Ξ-выборки `κ(y) = (L²/2)[1/12 + (1/2π²)Σ_{n≠0} y_n/n²]`
равна `0.0231049931` на всех пяти окнах, отклонение от `κ_Ξ` `1.5e-11` (точность моего эталона). Следствие:
`α = κ(G) − κ(y)` целиком, и по линейности `α = (L²/2π²)·Σ_{n≥1} Δ_n/n²` (raw-отношения, `Δ_n = x_n − y_n`).
Числа: `α·L² → 0.037…0.040` ⇒ **`Σ_{n≥1} Δ_n/n² ≈ 0.8/L⁴`** при `|Δ_n| ~ 0.1/L²` поштучно: знаковая сумма
сокращается на два порядка по `L` относительно суммы модулей. Это тот же `S_Δ` из `f788d2fa` (знакопеременная
форма кривизны), теперь как ЕДИНСТВЕННЫЙ атом: линейный функционал от строки дна минус его значение на строке Ξ.
Всё, что нужно для идентификации на компактах (через `d₂ = −13.8α` и тождество переноса), — скорость `1/L⁴`
этой суммы; всё, что нужно для нормальности, — её ограниченность (уже Lean). Поставщик открыт.

## 2026-09-04 (утро) — переоценка темпа: `α ≈ 0.35·T_tail = 0.35·L²/(4π²m)`, экспоненциально по `L`, а не `0.04/L²`; атом возвращается к СЧЁТУ нулей за окном

**Preflight агента** (`AGENT_REPORT_2026-09-04_GOAL058_SECOND_MODE_CURVATURE_TRANSFER_SOURCE_PREFLIGHT.md`,
код `REMAINDER_LOWER_ORDER` на конечных ячейках). Три утверждения, проверенные мной: (1) `E ≡ αM − 2πd₂/ℓ₁`
тавтологично (невязка 1e-15 — арифметика, не механизм); (2) по определению кривизны в Lean
(`κ = Σ_ρ 1/ρ² + (L²/4π²)Σ_{k>N}1/k²`) `α = T_tail − Def`, `Def = κ_Ξ − Σ_ρ 1/ρ²` — дефицит обратных квадратов
нулевого дивизора дна; (3) **`α/T_tail = 0.226, 0.298, 0.332, 0.348, 0.352`** (m = 13…163) — монотонно сходится
к ≈ 0.35, тогда как `α·L² = 0.018, 0.031, 0.039, 0.040, 0.037` разворачивается на m=163; `α·m/L² = 5.5e-3 → 8.9e-3`
сходится. **Прочтение `α ∝ L²/m` (экспоненциально по `L`) предпочтительнее `c/L²`.** `Def/T_tail → 0.65`.
Δ(7)·m/L² = −0.079 → −0.129 (ещё растёт 3 %/шаг) против Δ(7)·L² (разворот): тот же вывод, слабее.
Различитель: одна ячейка `m = 313` (прочтения расходятся в 4–6 раз); запущена отцепленным процессом.

**Смысл.** Весь «закон `1/L²`» суток был артефактом короткого диапазона `m = 13…83`, где `L²/m` и `1/L²`
неразличимы. Кривизна дна сходится к `κ_Ξ` как `L²/m`, то есть `e^{−L}·L²`. Тогда идентификация на компактах
(через `d₂ = −13.8α` и тождество переноса) выполняется с огромным запасом — ЕСЛИ контролируется `α`. А `α` по
(2) есть бухгалтерия ДАЛЁКИХ нулей: `T_tail` — явный хвост решётки, `Def` — недостача обратных квадратов нулей
дна за окном (`~1/x_N`, обе величины). Поставщик без щели, названный агентом: односторонний СЧЁТ нулей
`N_G(t) ≥ N_Ξ(t)` до `t ≈ 1.5·x_N` плюс безусловный хвост Римана–фон Мангольдта, суммирование Абеля ⇒
`α = O(L²/m)`. Это WINDLOCK на масштабе окна (растущий `R ~ 1.5x_N`), не на фиксированном компакте.
Опции (a)/(b)/(c) как поставщики проваливаются: `κ(Ξ-строки) − κ_Ξ` суперэкспоненциально мала (0 % от α),
утечка объясняет только внутренность окна, pinning — круг `99927f01`.
**Ловушки:** `ZerosRealOn` для дна проверена только на m = 13, 23, 43 (Probe 12); m = 83, 163 несут тренд и
не проверены; формула `κ` в EVEN-координатах требует `1/√2` (в зонде 18 учтено).

## 2026-09-04 (утро) — различитель `m=313`: `α ∝ L²/m` ПОДТВЕРЖДЕНО, `1/L²` ОПРОВЕРГНУТО

Ячейка `m = N = 313` (dps 1450, обратная итерация, юнит systemd, 27 мин): `κ(G) = 0.0240357`, `α = 9.307e-4`.
| m | α·L² | α·m/L² | α/T_tail |
|---|---|---|---|
| 83 | 0.0403 | 8.77e-3 | 0.348 |
| 163 | 0.0367 | 8.89e-3 | 0.352 |
| 313 | 0.0307 | 8.82e-3 | 0.349 |
`α·L²` упало на 17 % за шаг; `α·m/L²` и `α/T_tail` — в пределах 1 %. **Кривизна дна сходится к `κ_Ξ` как
`≈ 0.35·L²/(4π²m)`**, экспоненциально по `L`. Все «законы `1/L²`» суток 03–04.09 (Δ_n, W_k, κ_k − κ_Ξ, a(m), d₂) —
артефакт диапазона `m ≤ 83`; их надо перечитать как `L²/m` (или `L^p/m`). Запись сделана post hoc (K6 на
`m=313` не был заморожен мною — различитель предложил агент; фиксирую честно).
**Следствие для маршрута:** компонента I (идентификация на компактах) следует из `α = O(L²/m)` с экспоненциальным
запасом; стена — в `Def = κ_Ξ − Σ_ρ 1/ρ²` (недостача обратных квадратов нулей дна), т.е. в счёте далёких нулей
за окном на масштабе `~1.5·x_N`. Это WINDLOCK на масштабе окна.

## 2026-09-04 — ловушка закрыта на m=83: все 166 нулей числителя дна вещественны; привязка к γ_j до ≈1.57·x_N

Юнит `q3-zeros83` (dps 700, 27 с): числитель степени 166, `NONREAL = 0`, 83 положительных нуля, 54 привязаны к `γ_j`
(порог 0.05) вплоть до `184.85 = 1.57·x_N` (`x_N = 118.0`); первый непривязанный `150.1` (на этой высоте шаг нулей
`≈ 1.9` и порог 0.05 строг — привязка с пропусками, не потеря). Вещественность нулей дна на ячейке, несущей тренд,
подтверждена. Запущен тот же тест на m=163 (юнит `q3-zeros163`).

## 2026-09-04 (полдень) — вердикт RATE: `α = T − Def` точно; моё направление неравенства было НЕВЕРНЫМ; счёт нулей — не поставщик; m=163 — 326 вещественных нулей

**Судья.** (Q1) `α_m = T_m − Def_m` — точное конечное тождество с замком определений (Lean). `T_m ~ L²/(4π²m)`
с двусторонними оценками. **Починка направления:** «`Def ≤ (1−c)T`» даёт `α ≥ cT` — оценку СНИЗУ, не сходимость.
Атом темпа: `|α| ≤ C·T`, т.е. `Def` в полосе `[(1−C)T, (1+C)T]`. `α/T → 0.35` — подгонка, не закон. Идентификация на
компактах требует сверх того: ненулевой момент переноса, остаток `o(α)`, когерентный профиль, комбинированный
остаток → 0. (Q2) `κ_Ξ = Σ_γ 1/γ²` по вещественным `γ` — RH-условно (безусловный объект — комплексный дивизор с
квартетной группировкой); односторонний счёт `N_G ≥ N_Ξ` даёт верхнюю оценку `Def` = нижнюю `α` (не то
направление); вещественность + степень НЕ дают нижнего счёта в растущем окне (плант: все корни можно вынести за
`R`; принудительных корней при `R = 1.5x_N` ≈ `N/2` против `≈1.5N` у Ξ). `Def` — не только внутренний рассогласованный
кусок. (Q3) Замок на масштабе окна бесполезен: на границе `G/X → 0`, относительная ошибка → 1. (Q4) `α` и `Δ(x)`
перечитать как `L²/m`-кандидаты; `a(m)`, `d₂` условно; `W`, `sup|Δ_n|`, энергия — из `α` НЕ следуют (знаковый
момент не контролирует модули): при профильных гипотезах `W = O(L/m)`, `sup = O(L²/m)`, энергия `O(L³/m²)`.
Убито: `Def ≤ (1−c)T` как поставщик; `κ_Ξ` как вещественная сумма безусловно; степень → счёт; знаковый момент →
абсолютные нормы. Мои предсказания: 2 из 4 опровергнуты (внутренний mismatch; односторонний счёт), одно
опровергнуто как универсальное; `α = T − Def` подтверждено.
**Датум против наблюдателя:** «`Def ≤ (1−c)T`» как атом — неравенство не в ту сторону; судья исправил за минуту.
Верный атом: `|α_m| ≤ C·T_m`, двусторонняя полоса для `Def`.

**Ловушка закрыта полностью:** m=163 (юнит, 231 с): 326 корней, `NONREAL = 0`, 163 положительных, 107 привязаны к
`γ_j` до `329.0 = 1.64·x_N` (`x_N = 201.1`). Вещественность нулей дна проверена на всех пяти production-ячейках.

## 2026-09-04 (полдень) — ручной зонд объекта судьи: `S_G(y) − S_X(y)` на мнимой оси

**Что считал (за секунды, до агента, правило 13).** `S_f(y) = −f'(iy)/(2iy f(iy))` центральной
разностью по мнимой оси для `G` = нормированный P59-трансформ дна и `X = Ξ/Ξ(0)`; `D(y) = S_G(y) − S_X(y)`.
Для вещественнокорневого `G`: `S_G(y) = Σ_ρ 1/(ρ²+y²) + Σ_{k>N} 1/(x_k²+y²)`, `S_G(0) = κ(G)`.

**Результат.** `D(y)/α_m` на m = 13, 23, 43, 83:

| y | 0.25 | 1 | 2 | 5 | 10 | 20 | 50 | 200 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| m=13 | 1.00 | 1.00 | 1.00 | 0.98 | 0.91 | 0.69 | 0.06 | −1.02 |
| m=83 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 0.98 | 0.93 | n/a (потеря точности) |

`D(y)` **плоская в y** до масштаба окна: до `y ≈ x_N/4` она равна `α_m` с тремя знаками. Вес `1/(ρ²+y²)`
ничего не подавляет при малых y: разность `D(y) − D(0) = −y²·(Σ_ρ 1/ρ⁴-разность) + …` ничтожна. Смена
знака только при `y ≳ x_N` (m=13: `D(200) = −1.02α`, `x_N = 31.8`), где `S_G` доминирует явный решёточный
хвост (`tail(y)` = 2.9e-3 из `S_G` = 4.1e-3).

**Два прочтения (записаны до ответа агента).** (A) R1 судьи — это переименование `α`: при любом
`y_m → 0` с `y_m ≪ x_N` разность есть ровно `α_m`, «хвостовой функционал» появляется лишь при `y ≳ x_N`,
и вся трудность — интерполяция по y от масштаба окна к нулю (Стилтьес-монотонность для `X` без RH
не даётся). (B) Существует y-режим `y ~ c·x_N`, где разность становится явным `O(T_m)`-функционалом
и откуда её можно спустить к нулю. Различит: агент-префлайт (код SOURCE_IDENTITY / ONLY_RENAMES).
Мой прогноз: `P_R1_ONLY_RENAMES = 0.70`.

**Странности, записанные сразу.** (1) `S_X(0.5)` = NaN: `Ξ(i/2) = ξ(0)` считается как `0·Γ(0)`;
`Ξ(0.4999i)/Ξ(0) = 1.0058`, нуля нет — артефакт реализации `centered_xi`, не математика. (2) При
`y ≥ 100` часть значений NaN при 60 dps (`sin(iyL/2)` растёт как `e^{yL/2}`): для больших y нужен dps
по y. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (день) — LOGDERIV-префлайт: R1 судьи только переименовывает кривизну

**Агент (Opus, 13.5 мин, только чтение):** код `P59_LOG_DERIVATIVE_ONLY_RENAMES_CURVATURE`; прогноз судьи 0.35
опровергнут, мой `P_R1_ONLY_RENAMES = 0.70` подтверждён. Отчёт:
`docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH_PREFLIGHT.md`.
**Проверено мной другим каналом (mpmath, своя конструкция, m=13):** корневая-свободная формула `S_G(y)` совпала с
прямым счётом на 12 знаков при y = 0.3, 1, 5, 20 (в ней `c_k` — ПОЛНЫЕ коэффициенты мод, `c_k = v_k/√2`);
`κ_X = ½[−8 + ¼ψ'(1/4) + (ζ'/ζ)'(1/2)] = 0.0231049931154` = `S_X(10⁻⁴)`; `S_X(1/2) = 1 + γ_E/2 − ½log 4π` на 40 знаков.
`α_13` из корневой-свободной формы: 2.79127e-3 — совпадает с таблицей. Агентская посылка «`S_X` — Стилтьес
положительной меры ⟺ RH» — бумага, отсюда не проверена, но элементарна (полюсы `−z_j²` вещественны ⟺ `z_j`
вещественны или чисто мнимы; чисто мнимые исключены `ξ > 0` на ℝ).
**Итог для стены:** обе стороны `α` теперь явные скаляры источника и цели; вопрос — темп `L²/m` для
`(L²/2)[1/12 + (1/2π²v₀)Σ v_k/k²] − ½(log ξ)''(1/2)`, утверждение о собственном векторе дна и только о нём.
Очередь: `LOGDERIV` OPEN, не отправлена (фаза-потом-батч). Карта стены обновлена.

## 2026-09-04 (день) — Probe 19: R2 судьи своими зондами — второй джет дно / трал CCM / Ξ

**Владелец:** «давай R2 своими зондами». Скрипт `docs/routeB_bus/phase5_codex/r2_second_jet.py`
(точная формула `κ(v) = (L²/2)[1/12 + (1/(π²c_0))Σ_{k≥1} c_k/k²]` для ЛЮБОГО чётного вектора мод; трал — projected
prolate `k1/g04` из кэшей `portable_k_coeffs`; предсказания записаны до чисел, addendum 21).

| ячейка | T_m | α_G = κ(G)−κ_X | α_q = κ(q)−κ_X | δ = κ(G)−κ(q) | δ/T | α_q·m | p = 1−⟨ξ,q⟩² |
|---|---|---|---|---|---|---|---|
| (13,13) | 1.234e-2 | +2.791e-3 | −1.562e-3 | +4.353e-3 | 0.353 | −0.0203 | 3.66e-3 |
| (23,23) | 1.059e-2 | +3.158e-3 | −0.875e-3 | +4.033e-3 | 0.381 | −0.0201 | 2.98e-3 |
| (43,43) | 8.236e-3 | +2.738e-3 | −0.466e-3 | +3.204e-3 | 0.389 | −0.0200 | 1.86e-3 |
| (13,120) | 1.383e-3 | −1.567e-3 | −1.562e-3 | −4.6e-6 | −0.003 | −0.0203 | 4.69e-9 |

**Три факта.**
1. **Трал → Ξ во втором джете по чистому закону `1/m`:** `κ(q_m) = κ_X − a_m/m`, `a_m = 0.020307, 0.020123, 0.020016`;
   подгонка `a_m = a_∞ + b/m` по m = 23, 43 даёт `a_∞ = 0.019892`, `b = 0.0053`, предсказывает `a_13 = 0.020302`
   (измерено 0.020307). **`1/(16π) = 0.019894`.** На вещественной оси `F_q(x)/F_q(0) = (Ξ(x)/Ξ(0))·(1 + a_m x²/m + O(x⁴))`
   с тем же `a_m` на трёх знаках для `x ∈ [0.05, 8]`. Прочтение: prolate-множитель с `c = 2πm` даёт
   `1 + z²/(8c)`; это утверждение о трале и только о нём (источник-явный объект, без RH). Не проверено: вывод
   из CCM §7 / Lemma 7.3; это кандидат для агента-чтеца.
2. **Дно − трал:** `δ_m ≈ 0.38·T_m` (0.353, 0.381, 0.389) и `δ_m ≈ 0.073·√p_m` (0.072, 0.074, 0.074). На широком окне
   (13,120) `δ ≈ 0`, `p = 4.7e-9`. Относительный Ритц на N = m пуст: `R(q)/λ₁ = 5e14, 2e25, 3e49` (relritz), но `p ~ 1e-3` —
   трал не Ритц-вектор на производственном окне, а хорошее направление по другой причине.
3. **Разложение на всех шести ячейках:** `α_G = δ + α_q`, и `(α_G + a_∞/m)/T_m = 0.350, 0.380, 0.389, 0.389, 0.381, 0.373`
   на m = 13..313. «`α/T → 0.35`» судьи — сумма двух законов: `0.38·T_m` (дно−трал) минус `1/(16πm)` (трал−Ξ);
   `1/(mT) = 4π²/L²`, отсюда медленный дрейф.

**Судьбы предсказаний:** `P_TRIAL_JET_WITHIN_T` 0.35 → ПОДТВЕРЖДЕНО (|α_q|/T ≤ 0.13); `P_GROUND_TRIAL_JET_GAP_WITHIN_T`
0.40 → ПОДТВЕРЖДЕНО (δ/T ≤ 0.39); `P_TRIAL_JET_WORSE_THAN_GROUND` 0.65 → ОПРОВЕРГНУТО (трал ближе к Ξ, чем дно).
**Что R2 делает со стеной.** R2 = C1 (NEWMECH, DEVELOP) с точной конечной формулой. Трал-кусок замкнут численно
законом `1/m` с явной константой; остаётся **дно−трал в одном скаляре**: `δ_m = (L²/2π²)Σ_k (ξ_k/ξ_0 − q_k/q_0)/k²`,
где `q_k/q_0` теперь источник-явен. Атом: `|δ_m| ≤ C·T_m` (наблюдается C ≈ 0.4). Поставщик `p_m` через Ритц мёртв на
N = m. Генерация трала (83,83) при `MAX_DEGREE = 600` запущена юнитом `q3-trial83`. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (день) — константа трала выведена: `a_∞ = 1/(16π)` точно, `b = 13/(256π²)`; слепой тест пройден

**Агент (Opus, 19 мин, чтение + короткие проверки):** код `TRIAL_JET_CONSTANT_DERIVED_EXACT`. Отчёт:
`docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_TRIAL_SECOND_JET_CONSTANT_DERIVATION.md`.
Вывод: P59-трансформ вектора мод трала равен Mellin-трансформу `k_λ` (множители `λ^{±iz}` сокращаются, `L/2 = log λ`);
`M(E(f))(s) = ζ(s+½)M(f)(s+½)`, поэтому в `Φ_m = [F_q/F_q(0)]/[Ξ/Ξ(0)]` **ζ сокращается тождественно** — множитель
чисто архимедов, простые в `1/m`-отклонении не участвуют. `PW_λ = λ²H + ∂_x(x²∂_x)` точно, `ε = 1/m` — настоящий
параметр возмущения; вся первая поправка — одна примесь `h_8` с амплитудой `√105/(−16π)`. Итог:
`a_∞ = 1/(16π)` точно (`= 1/(8c)`, `c = 2πm`), `b = 13/(256π²)`, первая квартика `[z⁴]Φ_m = 1/(512π² m²)`.
`Φ_m(iy)` вещественна, `= 1 − y²/(16πm) + O(1/m²)`. **Lemma 7.3 не даёт темпа** (теряет его дважды; Lemma 7.2 даёт
`O(λ⁻²)`, 7.3 его не переносит). Код `g04` = `k_λ` статьи построчно; `k_λ` — суммационное (Eisenstein) отображение,
не ядро×срез и не свёртка.
**Мой слепой тест (другой канал — мои `a_m` из вещественной оси, агенту не даны):** `b_m = m(a_m − a_∞)` = 0.005364,
0.005265, 0.005209; экстраполяция по m = 23, 43 даёт `b = 0.005143`, предсказание агента `13/(256π²) = 0.005145`;
квартика при m=13, x=8: измерено 0.1052, квадратика 0.09997, с квартикой 0.10477. **Пройдено.** Канал агента
(Mellin-логпроизводная `h_λ`, без `c_n` и без ядра P59) воспроизвёл мои `a_m` на 6–7 знаках при данных ему пяти.
Не проверено мной символьно: само тождество сокращения ζ — читается по статье; числа с ним согласны.
**Следствие для стены:** трал-кусок R2 закрыт как явная архимедова формула. Открыт ровно один скаляр:
`δ_m = κ(G_m) − κ(q_m) ≈ 0.38·T_m`. Замечание агента к инфраструктуре: `MAX_DEGREE` не перепривязывается
`with_tp_context` (мой юнит `q3-trial83` ставит его на модуле — работает).

## 2026-09-04 (16:50) — ячейка m=83 в Probe 19: закон держится

Трал (83,83) сгенерирован юнитом `q3-trial83` (`MAX_DEGREE = 600`, 10394 с, `coeff_diff` 3.6e-91). Строка:
`κ(G) = 0.0251680715`, `κ(q) = 0.0228645503`, `α_G = +2.063e-3`, `α_q = −2.404e-4`, `δ = +2.304e-3`, **`δ/T = 0.389`**
(43: 0.389), `p = 9.75e-4`, `δ/√p = 0.0738` (13..43: 0.072, 0.074, 0.074). Константа: `a_83 = 0.0199568` измерено,
формула агента `1/(16π) + 13/(256π² m)` даёт 0.0199564 — расхождение 4e-7, порядок следующего члена. Четыре
production-ячейки: `δ_m/T_m = 0.353, 0.381, 0.389, 0.389`. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (вечер, судья думает над TRIALJET) — ошибка трала одноформна: 99.5–99.8 % вдоль `u₂`; кривизна аффинна вдоль `u₂`

**Зонд 1 (невязка трала в собственном уравнении, arb, без float до печати).** `‖(K−λ₁)q‖ = 1.9e-8, 3.2e-14, 5.4e-21, 1.1e-35`
(m = 13..83), `⟨q,(K−λ₁)q⟩ = 4.2e-16, 1.4e-26, 2.6e-41, 9.3e-71` (13..43 совпадают с relritz). `‖r‖/λ₂ = 7e16 .. 7e62`:
Davis–Kahan по щели пуст на 16–62 порядка. **Странность, записанная сразу:** первый прогон во float дал `‖r‖ = 1e-17`
на m = 43, 83 — это пол округления float64 на элементах ~0.1, не невязка. Правило: arb до печати (второй раз за сутки).
**Зонд 2 (масса ошибки трала по собственному базису).** Доля `p = 1 − ⟨ξ,q⟩²` на `u₂`: **99.5 %, 99.6 %, 99.8 %**
(m = 13, 23, 43); на `u₃`: 0.5, 0.4, 0.2 %; остаток `1e-13·p` на верхних собственных значениях (он и даёт всю невязку).
**Зонд 3 (аффинность κ вдоль `u₂`; `u₂` с фиксированной ориентацией `(u₂)₁ > 0`).**

| m | cos(q−ξ, u₂) | cos(y−ξ, u₂) | `A_q = ⟨q,u₂⟩` | `A_y = ⟨y,u₂⟩` | `(κ(q)−κ(G))/A_q` | `(κ(y)−κ(G))/A_y` | `(κ(y)−κ(q))/(A_y−A_q)` |
|---|---|---|---|---|---|---|---|
| 13 | +0.9972 | +0.9986 | 0.0604 | 0.0381 | −0.0721 | −0.0734 | −0.0700 |
| 23 | +0.9978 | +0.9986 | 0.0545 | 0.0421 | −0.0740 | −0.0749 | −0.0709 |
| 43 | +0.9987 | +0.9990 | 0.0431 | 0.0366 | −0.0743 | −0.0748 | −0.0712 |

`y` — Ξ-строка (`y_k/y_0 = (−1)^k Ξ(x_k)/Ξ(0)`, `κ(y) = κ_X` на 8 знаках). Три строки — дно, трал, Ξ-строка — лежат на одной
прямой вдоль `u₂`, по одну сторону от дна; кривизна вдоль неё аффинна с наклоном `s_m ≈ −0.074` (разброс 2–5 %).
Согласие с OVERLAP: `d₂/α = −13.8` ⇔ `1/s = 13.5`.
**Переписывание атома (моё, источник-только).** `α_G = s_m·A_y`, `δ = s_m·A_q`, `A_y − A_q = α_q/s_m = −1/(16π m s_m)`. Отсюда
`α_G = s_m·⟨q_m, u₂(m)⟩ − 1/(16π m)·(1 + O(1/m))`: **в атоме больше нет Ξ** — только явный prolate-трал `q_m`, второй
собственный вектор `u₂` конечной матрицы Вейля и явный наклон `s_m` (линейный функционал от `u₂`: `κ` линейна по `v/v₀`).
Атом: `s_m·⟨q_m,u₂⟩ = 1/(16πm) + O(T_m)`. Два прочтения. (A) Это поставщик: `u₂` — второй prolate-подобный мод
(лестница `u_i/Ξ ≈` чётные многочлены), и `⟨q,u₂⟩` считается из структуры prolate + Вейля без Ξ. (B) Переименование:
`q − y = Ξ-строка·(Φ_m − 1) ≈ Ξ·x²/(16πm)`, и `⟨q,u₂⟩ = d₂ + (1/(16πm))⟨Ξx², u₂⟩` возвращает `d₂`. Различит: судья (в
батче TRIALJET Q3(c) это кандидат «two-mode form with X replaced by the explicit trial»). Числа: `⟨Ξ·x²,u₂⟩ ≈ 1/|s| = 13.5`
(ещё не измерено прямо — следующий зонд). DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

**Зонд 4 (различающий; прочтение B побеждает).** `q − y` есть `x²`-модуляция Ξ-строки: `cos(q − y, (y⊙x²)⊥y) = 0.9996, 0.9999, 1.0000`;
`(a_m/m)·⟨(y⊙x²)⊥, u₂⟩ = 0.974, 0.986, 0.992 · (A_q − A_y)`. И **`⟨(y⊙x²)⊥y, u₂⟩ = 13.93, 13.91, 13.93` — константа по m**,
равная `1/|s_m|` (13.5–13.9): наклон кривизны вдоль `u₂` и `x²`-момент Ξ-строки на `u₂` — один объект. Значит переписывание
«без Ξ» возвращает `d₂`: `⟨q,u₂⟩ = d₂ + (a_m/m)·13.93`, атом `s_m⟨q,u₂⟩ = 1/(16πm) + O(T)` ⇔ `d₂ = O(T)` (OVERLAP). Датум против
наблюдателя: моё `P_DELTA_ATOM_IS_RENAMING = 0.35` (зарегистрировано в TRIALJET, не редактируется) выглядит заниженным —
явный трал не меняет ландшафт поставщиков сам по себе; он лишь фиксирует, что все три строки различаются одной формой `u₂`
с известными коэффициентами. Что остаётся честно нового: (i) `α_G = s·d₂` с `s = −1/⟨(y⊙x²)⊥,u₂⟩` — точное конечное
тождество-кандидат (проверить символьно: κ линейна по `v/v₀`); (ii) число 13.93 не зависит от m на трёх ячейках — странность,
записана; прочтения: (A) `u₂/y → (x² − c)`-форма с нормировкой, дающей константу; (B) совпадение на малых m. Различит m = 83
(u₂ через обратную итерацию со сдвигом). DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (вечер) — m=83 различил: константа 13.9 есть Ξ-инвариант; `u₂` = `x²`-модулированная Ξ-строка

Владелец: «давай сделаем следующий зонд». `u₂(83)` через дефлированную обратную итерацию (`inverse_iteration_deflated`,
полка; `λ₂ = 1.2556e-154`, совпало с relritz; невязка 2.5e-200; 23 с). Результат m=83: доля `p` на `u₂` 99.9 %,
`cos(q−ξ,u₂) = 0.9993`, `cos(y−ξ,u₂) = 0.9994`, наклоны `−0.0738 / −0.0741`, `⟨(y⊙x²)⊥,u₂⟩ = 13.951`,
`cos(q−y, (y⊙x²)⊥) = 1.0000`, `(a/m)⟨w,u₂⟩/(A_q−A_y) = 0.996`. Все законы держатся на четвёртой ячейке.
**Странность разрешена (прочтение A).** `‖(y⊙x²)⊥y‖ = 13.9811` на ВСЕХ четырёх ячейках (m = 13..83, 5 знаков): это
стандартное отклонение `x²` под весом Ξ-строки, и решётка его не видит (трапеции спектрально точны для Ξ²).
Непрерывный Ξ²-вес на [0,∞): continuous Xi^2-weight: <x^2>=10.207565 <x^4>=299.6655 sd(x^2)=13.981099. `cos(w,u₂) = 0.9963, 0.9952, 0.9963, 0.9978`: **`u₂` есть `(y⊙x²)⊥y` с точностью 0.2–0.5 %**
— лестница `u_i/Ξ ≈` чётные многочлены на второй ступени, теперь с числом. Отсюда наклон кривизны вдоль `u₂`:
`|s_m| ≈ 1/13.98 = 0.0715` (измерено 0.072–0.075; остаток — 0.5 % не-`x²` части `u₂`).
**Что это меняет.** Вся геометрия трёх строк (дно, трал, Ξ-строка) описывается одним Ξ-инвариантом `σ₂ := sd_Ξ²(x²) = 13.98`
и одной неизвестной `d₂(m) = ⟨y,u₂⟩`: `α_G ≈ d₂/σ₂`, `δ ≈ ⟨q,u₂⟩/σ₂`, `⟨q,u₂⟩ − d₂ = a_m σ₂/m` (проверено 0.996–0.992).
Стена по-прежнему `d₂ = O(T_m)`; новое — `u₂` явная с точностью 0.5 % (форма `Ξ·(x² − ⟨x²⟩)`), так что `d₂ ≈ ⟨y, (y⊙x²)⊥⟩/σ₂ = 0`
в нулевом приближении — `d₂` живёт целиком в 0.5 %-остатке `u₂ − w/‖w‖`. Следующий вопрос судье (в очередь, не сейчас):
`d₂` как перекрытие Ξ-строки с остатком `u₂ − (y⊙x²)⊥/σ₂`; можно ли остаток выразить через третью ступень лестницы
и явный трал. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

**Зонд 6 (остаток `u₂` по лестнице Ξ).** `rem := u₂ − w/‖w‖`, `‖rem‖ = 0.086, 0.098, 0.086, 0.066` (m = 13..83).
`cos(rem, (y⊙x⁴)⊥{y,w}) = −0.895, −0.899, −0.903, −0.904`; `cos(rem, (y⊙x⁶)⊥…) = 0.04–0.06`; `⟨y,rem⟩/‖rem‖ = 0.442, 0.431, 0.425, 0.424`.
Сумма квадратов 0.997: **`u₂` лежит в span{`y`, `y⊙x²`, `y⊙x⁴`} на 99.7 %** — Ξ-строка, умноженная на чётный многочлен степени 4;
`d₂ = ⟨y,u₂⟩ = 0.43·‖rem‖` с почти постоянным отношением. `‖rem‖/T_m = 7.0, 9.2, 10.5, 11.1` и `d₂/T_m = 3.1, 4.0, 4.4, 4.7` — оба
растут медленно (это тот же дрейф, что `α/T = 0.23 → 0.35`). Лестница на второй ступени: `u₂ = c₀ y + c₂ (y x²)⊥ + c₄ (y x⁴)⊥⊥ + 0.3 %`.
Ортогональность `⟨u₂,ξ⟩ = 0` связывает `c₀ = d₂` с `A_y` тавтологически; нового поставщика зонд не даёт, но даёт явную
трёхчленную форму `u₂` для будущего расчёта `d₂` через коэффициенты лестницы. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (вечер) — вердикт TRIALJET (`33d863fa`): объектная подмена найдена; класс `TRY_P59_FINITE_PROJECTED_TRIAL_JET_CROSSWALK`

**Судья.** Q1: «`F_q` = Mellin-трансформ `k_λ`» ОПРОВЕРГНУТО как сказано: строка проекта `q` — нормированная конечная
Фурье-проекция `P_N f_λ`; точная починка `F_q = ‖P_N f‖⁻¹(H_λ − E_{λ,N})`, `H_λ = ζ(w)M_λ(w) − B_λ`. Два остатка: нижний
мультипликативный хвост окна `B_λ` и хвост конечной проекции `E_{λ,N}`. ζ сокращается точно только в неоконном главном
члене. `Φ` мероморфна, не целая. Расщепление prolate точное; первая поправка через `h_8` ПОДТВЕРЖДЕНА на уровне формального
коэффициента, строгий остаток открыт. **Знак второго члена починен:** `κ(q) = κ_X − 1/(16πm) − 13/(256π²m²)`.
Q2: честная теорема — континуальная оконная под четырьмя допущениями; Lemma 7.3 темпа не даёт, нужна новая теорема.
Q3: `|δ| = O(T)` ⇔ `|α_G| = O(T)` (эквивалентно по темпу, но `δ` — лучший источник-обращённый наблюдаемый); поставщика
без щели нет; ранжир: R1 sublevel-envelope кривизны (10/10), R2 trial-relative one-shape (9/10), R3 adjoint coboundary (8/10),
R4 weighted Davis–Kahan убит как generic. Следующее: paper-префлайт `FINITE_PROJECTED_TRIAL_JET_CROSSWALK` (точные `B_λ`,
`E_{λ,N}`, вторые джеты, цель `O(λ⁻⁴)`, p = 0.55). Lean-ready: конечное тождество `κ(v) − κ(q)`.
**Датумы против наблюдателя.** (1) В запросе я написал `+13/(256π²m²)` в кривизне — опечатка при переносе (`a_m = a_∞ + b/m`,
`κ = κ_X − a_m/m` ⇒ минус); данные с минусом согласны. (2) `P_ZETA_CANCELLATION_CONFIRMED 0.85` опровергнуто как сказано:
я передал утверждение агента о `k_λ` как утверждение о строке проекта. Судья прав: объекты разные.
**Ручная проверка после вердикта (правило 13).** Масса `f_λ` за пределами `|n| > m`: 5.2e-16 (m=13, из кэша N=120), 9.8e-41
(m=43, из кэша N=86); `κ(q)` меняется на −4.1e-11 (m=13, N: 13→26/120) и на 0 (m=43, N: 43→86). `E_{λ,N}` экспоненциально мал на
зарегистрированных ячейках; `λ⁻²`-член фальсификатора там численно исключён. Это не доказательство: судья хочет точную
бухгалтерию с константами. Запущены два Opus-агента: paper-префлайт (`B_λ`, `E_{λ,N}`) и Lean-файл
`Proposition59GroundTrialSecondJetDifference.lean` (политика владельца: Codex мёртв, Lean-задачи агентам).
Прогноз (мой, до агентов): `P_FINITE_PROJECTION_SECOND_JET_TAIL_LOWER_ORDER` судьи 0.55 — я ставлю 0.85 на SUCCESS для
`E_{λ,N}` (экспоненциально мал), 0.55 для `B_λ` (нижнее окно `u < 1/λ`: `h_λ` там мала, но оценка через две производные
не очевидна). DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-04 (вечер) — Lean: `Proposition59GroundTrialSecondJetDifference.lean` KERNEL_GREEN, сильнее директивы

Opus-агент (6.5 мин), проверено мной: `lake env lean` EXIT 0 без ошибок, `q3_check ok`, аксиомы обеих главных теорем
`[propext, Classical.choice, Quot.sound]`, `sorry/admit/exact?` = 0. Доказано для ЛЮБОЙ чётной строки с ненулевым центром
(без гипотез о нулях, без спектра): `κ(F_v) − κ(F_q) = (L²/(2π²))Σ_{k=1}^N (v_k/v_0 − q_k/q_0)/k²`, плюс замкнутая форма
`κ = (L²/2)(1/12 + (1/(2π²v₀))Σ_{k≠0} v_k/k²)` и её вариант по положительным модам. Находка агента: указанный судьёй маршрут через
`proposition59_curvature_closed_form` заблокирован его же запретами — та лемма несёт `ZerosRealOn`, потому что `proposition59Curvature`
ОПРЕДЕЛЕНА как сумма по корням + хвост; сама величина `−F''(0)/(2F(0))` нулей не требует, и агент передоказал форму в три строки
из `proposition59RawTransform_secondDerivative_zero` + `proposition59RawTransform_at_zero_eq_sqrt`. Файл импортирует только
`Proposition59EntireTransform`. Второй канал агента: контурные интегралы против строк, 2.3e-41. Отчёт:
`docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-04_GOAL058_P59_GROUND_TRIAL_SECOND_JET_DIFFERENCE.md`. Мигратор перезапущен после
появления файла (дрейф 388/389 закрыт; второй прогон шёл дольше 3 мин — записать в backlog как трение).

## 2026-09-04 (ночь) — префлайт судьи CROSSWALK: `P59_FINITE_PROJECTED_TRIAL_JET_RATE_CROSSWALK` (SUCCESS); фальсификатор не сработал

**Агент (Opus, 18 мин, чтение + короткие проверки):** отчёт
`docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_FINITE_PROJECTED_TRIAL_JET_CROSSWALK_PREFLIGHT.md`.
(1) `κ(P_{λ,N}) = −(L²/2π²)Σ_{n>N}(c_n/c_0)/n²` — тождество (то же, что Lean-файл `GroundTrialSecondJetDifference`), геометрически
мало: `exp(−π²m/(2 log m))·poly`; измерено `4.09e-11` (13: N 13→120) = `6.9e-9·λ⁻⁴`, `5.0e-24` (43: 43→86), модель `6.9e-41` при m=83.
(2) `κ(B_λ) = [A(0)B''(0) − A''(0)B(0)]/(2A(0)(A(0)−B(0)))`, экспоненциально мала в m: `exp(−πm)·poly`, `1.8e-18` (m=13) … `5.7e-114` (m=83).
(3) `E_{λ,N}(0) = 0` точно; `E''_{λ,N}(0) = −(L^{5/2}/π²)Σ_{n>N} c_n/n²` — Lean-ready. (4) Точное тождество выборки
`c_n = (−1)^n L^{-1/2} H_λ(2πn/L)`: строка коэффициентов трала ЕСТЬ оконный Mellin-трансформ на решётке; `c_n/c_0 = (−1)^n [Ξ(t_n)/Ξ(0)]·Φ^arch(t_n)`.
(5) `f_λ` без скачков на концах (правый: носитель `h_λ` + концентрация PSWF, `g04(1) = O(e^{−πm})`; левый: на линии `h₀/h₄` фазы
`i⁰ = i⁴` совпадают, нулевой интеграл ⇔ нуль в начале с точностью до дефекта). Цель `O(λ⁻⁴)`: одно интегрирование по частям;
`k = 3` даёт `O(λ⁻⁸ log⁵λ)`. Внешняя ссылка нужна одна: количественная асимптотика PSWF на конце при фиксированном индексе и большом c.
Честная дыра агента: кэши m=13, 43 упираются в пол точности (`|c_n|` выходит на плато = `|g04(1)|`), `B_λ` оценена структурно;
чист только m=83 до n=83.
**Мой второй канал (m=83, кэш `MAX_DEGREE=600`):** `c_n/c_0 ÷ (−1)^n Ξ(t_n)/Ξ(0)` = 1.000486 (n=1), 1.001946 (2), 1.012228 (5) против
`1 + t²/(16πm)` = 1.000485, 1.001938, 1.012115 — тождество (4) и первый порядок `Φ^arch` подтверждены на 1e-6..1e-4; при n ≥ 20 растут
старшие члены `Φ` (22.5 при n=80 против 4.1 первого порядка — ожидаемо, `t = 114`). Закон спада `n^{7/4}e^{−π²n/(2L)}` держит
экспоненту на 34 порядках (префактор в пределах 0.3..120). `|c_83/c_0| = 3.9e-35`, масса при n ≥ 70: 1.2e-58. Мои хвосты
5.2e-16 (13) и 9.8e-41 (43) — те же плато точности, что назвал агент; m=83 — первая чистая ячейка.
**Итог для трал-куска:** оба остатка ниже `λ⁻⁴` на порядки; константа `1/(16π)` принадлежит строке проекта с точностью до этих остатков.
Предсказание судьи `P_FINITE_PROJECTION_SECOND_JET_TAIL_LOWER_ORDER 0.55` → на пути к CONFIRMED (доказательство — по частям, бумага).
Моё: 0.85/0.55 → оба в сторону подтверждения. Остаток стены неизменен: `δ_m = κ(G) − κ(q)`, поставщик — R1 sublevel-envelope.
DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-04 (ночь) — Probe 20: R1 судьи (sublevel-envelope) мёртв как сублевел Рэлея; S-лемма в числах

**Владелец:** «сначала зонды, потом батч». Огибающая линейного функционала `κ` на `S_ε = {v₀ = 1, vᵀKv ≤ ε}` в замкнутой форме
(`v_c = K⁻¹e₀/(e₀ᵀK⁻¹e₀)`, `W(ε) = √((ε − ε_min)·g)`, `g = ℓ⊥ᵀ(PKP)⁺ℓ⊥`), arb на четырёх ячейках:

| m | T_m | ε_min | ε_q = R(q)/q₀² | `κ(v_c) − κ_X` | W(ε_q) | W(уровень λ₂) | W(2ε_min) |
|---|---|---|---|---|---|---|---|
| 13 | 1.2e-2 | 2.5e-30 | 1.4e-15 | +2.791e-3 | **3.1e+3** | 0.078 | 1.3e-4 |
| 23 | 1.1e-2 | 2.8e-51 | 5.7e-26 | +3.158e-3 | **2.7e+8** | 0.079 | 6.1e-5 |
| 43 | 8.2e-3 | 4.7e-90 | 1.3e-40 | +2.738e-3 | **1.5e+20** | 0.078 | 2.9e-5 |
| 83 | 5.9e-3 | 1.8e-161 | 5.3e-70 | +2.063e-3 | **6.7e+40** | 0.077 | 1.2e-5 |

Три факта. (1) Центр эллипсоида — дно: `κ(v_c) − κ_X = α_G` на всех знаках (`K⁻¹e₀ ∝ ξ`). (2) На уровне Рэлея трала множество
содержит строки с кривизной, отличающейся на `1e3 … 1e40` — **фальсификатор судьи для R1 срабатывает на каждой ячейке**;
«множество малого Рэлея, содержащее дно и `q`» не сертифицирует ничего. (3) `W(уровень λ₂) = 0.078` — константа = наклон `s/ξ₀`
(эллипсоид вытянут вдоль `u₂`); чтобы `W ≤ T`, нужно `ε − ε_min ≤ λ₂(T/s)² ≈ 0.006·λ₂` — знание Рэлея строки с точностью малой доли
схлопнувшейся щели. R1 = стена щели под другим именем, если допустимое множество не несёт ничего, кроме Рэлея.
Судьбы: `P_ENVELOPE_WIDTH_AT_TRIAL_LEVEL_GG_T` 0.90 ПОДТВЕРЖДЕНО; `P_WIDTH_AT_LAMBDA2_LEVEL_GG_T` 0.70 ПОДТВЕРЖДЕНО;
`P_CENTRE_CURVATURE_NEAR_GROUND` 0.80 ПОДТВЕРЖДЕНО (точно).
**R2 судьи в числах (из зондов 3–6).** Остаток `δ − A_q/σ₂` = +3.4e-5, +1.4e-4, +1.2e-4, +7.2e-5 = 0.3–1.5 % от `T` (0.8–3.7 % от `δ`; исправлено: в первой записи два значения были занижены в 10 раз при переносе):
дискриминатор R2 «остаток высших мод `o(T)`» держится; коэффициент второй моды `A_q = d₂ + a_m σ₂/m`, и всё упирается в
`d₂ = ⟨y,u₂⟩`. По аффинному закону `d₂ = α_G·σ₂`: `d₂/T = 3.16, 4.17, 4.65, 4.87, 4.91, 4.88` (m = 13..313) — насыщение около 4.9:
`d₂ ≈ 4.9·T_m`, `α_G ≈ 0.35·T_m`. Атом остаётся `d₂ = O(T_m)`; форма дна в функциях: `G(x) ≈ Ξ(x)·(1 − d₂(x² − ⟨x²⟩_Ξ)/σ₂)`.
DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-04 (ночь, судья думает над D2SUPPLY) — Probe 21: сжатие `K` на лестницу Ξ не даёт `d₂`; все три предсказания опровергнуты

`V_n = span{y⊙x^{2j}, j < n}`, ортонормировано; `K|V_n`; два нижних собственных вектора, обратно в решётку.

| m | n=3: `λ̃₁/λ₁` | n=3: `d₂⁽³⁾/d₂` | n=5 | n=8: `λ̃₁/λ₁` | n=8: `d₂⁽⁸⁾/d₂` |
|---|---|---|---|---|---|
| 13 | 8.7e6 | 0.59 | 0.73 | 1.3e3 | 0.87 |
| 23 | 2.7e18 | 0.27 | 0.51 | 1.6e8 | 0.80 |
| 43 | 3.7e39 | 0.14 | 0.27 | 6.3e26 | 0.44 |
| 83 | 5.8e79 | 0.07 | 0.14 | 3.6e64 | 0.23 |

Лестница — плохое Ритц-пространство: её дно не достаёт до `λ₁` на 3–80 порядков (при этом `⟨y,ũ₁⟩ = 1 − 1e-5`: дно лестницы —
сама Ξ-строка, чей Рэлей `1e10…1e84·λ₁`). `d₂⁽ⁿ⁾` растёт к `d₂` медленно, и нужная степень растёт с m. Q2(a) моего же запроса
(«`d₂⁽³⁾` из CCM-элементов») численно мёртв: `P_LADDER3_D2_WITHIN_20PCT` 0.50 ОПРОВЕРГНУТО, `P_LADDER_GROUND_RAYLEIGH_LT_10_LAMBDA1` 0.40
ОПРОВЕРГНУТО, `P_LADDER_CONVERGES_BY_N8` 0.60 ОПРОВЕРГНУТО. Датум против наблюдателя: в D2SUPPLY стоит `P_LADDER_COMPRESSION_COMPUTABLE 0.60`
— «вычислимо», да, но остаток `d₂ − d₂⁽³⁾` есть 40–93 % от `d₂`; это идёт в интейк вердикта. Прочтение: `u₂` на 99.5 % есть степень-2
модуляция Ξ, но `d₂` живёт в хвосте лестницы (высокие степени `x^{2j}` при `j ~ m`?) — то же, что «`d₂` в 0.5 %-остатке». DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (ночь) — вердикт D2SUPPLY (`87e123ea`): R1 убит, лестница — только «голова»; класс `RUN_P59_LADDER_FESHBACH_D2_REMAINDER_DISCRIMINATOR`

**Судья.** Q1: R1 (огибающая на сублевеле Рэлея) УБИТ как поставщик без щели — точное тождество ширины S-леммы + плант 2×2
(`K = diag(μ₁,μ₂)`, ширина `2R` произвольна); аудит пяти кандидатов «источник-определённого множества»: ни одного с независимым
включением дна и шириной `O(T)`. Q2(a): 3×3 сжатие вычислимо из `tau_entry` против выборок Ξ, но сырой второй Ритц-вектор `d₂` НЕ
определяет: точный остаток `d₂ − d₂⁽³⁾ = ⟨e₀, p − z₂⁽³⁾⟩`, где `p` — компонента настоящего `u₂` в лестнице, управляемая Фешбах-матрицей
`A − C(D − λ₂)⁻¹C*`; плант `u(θ) = √(1−θ²)b₁ + θy`: 99.5 % направления не дают контроля `d₂`. Q2(b): объект стандартный
(Ritz/Feshbach), цитируемой асимптотики второго вектора нет (не Ханкель безусловно, не Sonin CC, не Suzuki). Q2(c): теорема
`|⟨y_m,u₂,m⟩| ≤ C·T_m`, первый провал `P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M`. Q3: ранжир — (1) тождество переноса кривизны
`2πd₂ = ℓ₁(αM − E)` с точным расщеплением трал/дно (страж объекта: `E_m` ≠ `E_{λ,N}`), (2) y-компонента Фешбаха, (3) прямой y-блок
Шура `|d₂|⁻² = 1 + ‖(D − λ₂)⁻¹b‖²` (риск щели), (4) физический второй момент — не селектор, (5) производная `λ₁` по окну УБИТА
(изоспектральная ротация). Следующее: `RUN_P59_LADDER_FESHBACH_D2_REMAINDER_PREFLIGHT` на `V₂, V₃, V₄`. Lean-ready: блок-уравнения,
Фешбах, тождество остатка, плант `u(θ)` (`P59XiLadderFeshbachRemainder.lean`). Судьбы: 4 моих подтверждены, `P_LADDER_IS_KNOWN_OBJECT`
опровергнуто.
**Дискриминатор судьи уже посчитан (Probe 21, до вердикта, тот же объект):**

| m | `D⁽²⁾` | `R⁽²⁾` | `D⁽³⁾` | `R⁽³⁾` | `D⁽⁸⁾` | `R⁽⁸⁾` | `d₂/T` |
|---|---|---|---|---|---|---|---|
| 13 | 0.99 | 2.10 | 1.81 | 1.27 | 2.67 | 0.41 | 3.08 |
| 23 | 0.56 | 3.42 | 1.08 | 2.90 | 3.17 | 0.81 | 3.98 |
| 43 | 0.32 | 4.12 | 0.62 | 3.82 | 1.94 | 2.50 | 4.44 |
| 83 | 0.17 | 4.54 | 0.33 | 4.37 | 1.09 | 3.61 | 4.70 |

Голова `V₃` несёт исчезающую долю (`D⁽³⁾ → 0`), Фешбах-остаток — практически весь `d₂` (`R⁽³⁾ → d₂/T ≈ 4.9`). **Замороженный кандидат
`V₃` ПРОВАЛИВАЕТ дискриминатор**; нужная степень лестницы растёт с m (при `V₈` остаток 0.4 → 3.6). Это финитный провал `V₃`, не всей
теоремы (по scope судьи). Ориентация второго Ритц-вектора когерентна (все `d₂⁽ⁿ⁾ > 0`). Инвариант судьи: «малая координата `d₂` живёт
в поправке; скалярный контроль строже контроля формы» — совпадает с моим прочтением зонда 21.
**Следствие для стены.** Смыкаются все дороги: `P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M` — y-компонента Фешбах-поправки при
`λ₂` в схлопнувшемся спектре. Runner-up: перенос кривизны с явным тралом (`E_m = O(T)`). Lean-агент на директиву запущен
(политика владельца). DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

**Дополнение к дискриминатору (V₄, как в спецификации судьи `V₂, V₃, V₄`):** `D⁽⁴⁾ = 2.27, 1.58, 0.90, 0.49`, `R⁽⁴⁾ = 0.81, 2.40, 3.54, 4.21`
(m = 13..83); `λ̃₂/λ₂ = 6e5 … 2e78`; поднятая невязка `‖(K − λ̃₂)ũ₂‖ = 2.7e-10, 5.2e-15, 2.7e-23, 1.5e-38` и она вся равна связи с дополнением
`‖Cᵀz‖` (те же числа): Фешбах-самоэнергия не мала относительно `λ₂` ни на одной ячейке (`‖Cᵀz‖/λ₂ = 1e15 … 1e116`). Вывод по scope
судьи: замороженный `V₃` (и `V₄`) провален; вложенная селекция когерентна. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (ночь) — Lean: `P59XiLadderFeshbachRemainder.lean` KERNEL_GREEN (директива D2SUPPLY)

Opus-агент (15 мин), проверено мной: `lake env lean` EXIT 0 без ошибок, `q3_check ok`, все 26 теорем/лемм с аксиомами
`[propext, Classical.choice, Quot.sound]`, `sorry/admit/exact?` = 0. Над `Matrix (Fin n) (Fin n) ℝ`, `K.IsSymm`: ортонормированный синтез
лестницы `B` (`Fin 3`), проекторы `P = BBᵀ`, `Q = 1 − P` (симметричные идемпотенты, `PQ = 0`); блоки `A, C, D`; два спроецированных
собственных уравнения для точной пары; `d₂ = ⟨e₀,p⟩ = ⟨Be₀,u⟩`; точное тождество остатка `d₂ − ⟨e₀,z⟩ = ⟨e₀, p − z⟩`, нормированная
форма и оценка Коши–Шварца; Фешбах под слабейшей гипотезой `G((D − λ)r) = r` (обратимость на одном векторе): `r = −GCᵀp`,
`(A − CGCᵀ − λ)p = 0`, плюс вывод из Q-блочного обратного; плант `u(θ)` с точными скалярными произведениями и `Tendsto`.
CLOSES `P59_XI_LADDER_COMPRESSION_BLOCK_EQUATIONS`, `P59_XI_LADDER_D2_EXACT_REMAINDER`; OPENS ничего. Второй канал агента: numpy 9×9,
невязки 1e-14..1e-17, оценка строгая (0.38 ≤ 0.45). Полка: `CCMProposition59ComplexTrialLineFeshbach.lean` — другой объект (ранг 1,
комплексный). Не тронуто: `FIRST_FAILURE` судьи — e₀-координата самоэнергии `CGCᵀ`; когерентный выбор второй моды. Девятый Lean-файл
фронта. Отчёт: `docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-05_GOAL058_P59_XI_LADDER_FESHBACH_REMAINDER.md`.

## 2026-09-05 (ночь) — РАЗВИЛКА владельца: широкие окна и C3 заново с явными формулами

Владелец, на вопрос «куда роем» и ответ «на широком окне (13,120) дно = трал до 5e-9, джет трала явный»: «конечно смотрим широкие
окна и C3 заново с сегодняшними явными формулами». Записано в момент выбора. C3 (NEWMECH, 926c1865→…): убит как единственный
безусловный механизм (POSITIVITY_TYPE_PREMISE + WRONG_MINMAX_DIRECTION), сохранён как условная лемма `p ≤ (C−1)/(g−1)` при
`0 < λ₁ < λ₂` и `R(q) ≤ C·λ₁`. Что сегодня новое для C3: (i) джет трала явный (`κ(q) = κ_X − 1/(16πm) − …`), так что на окне, где трал —
Ритц-вектор, `α_G = α_q + O(√p)` известна; (ii) `c_n = (−1)^n L^{-1/2} H_λ(2πn/L)` — коэффициенты трала явные, `R(q_N)` = энергия усечённого
трала вычислима; (iii) хвост трала спадает как `e^{−π²n/(2L)}`, а `λ₁(m,N)` при фиксированном m должна насыщаться (континуальное дно) —
значит есть `N*(m)`, за которым трал Ритц-точен. Первый зонд (Probe 22): при m=13 по чистому кэшу (13,120): `λ₁(N), λ₂(N), R(q_N),
ε(N) = R/λ₁, g(N) = λ₂/λ₁, p(N)`, лемма C3 `p ≤ (ε−1)/(g−1)`, для N = 13..120. Предсказания: `P_LAMBDA1_SATURATES_IN_N` 0.60 (λ₁(13,N)
меняется < 10× между N=80 и 120); `P_EPS_CROSSES_BELOW_10_BY_N_3M` 0.50 (ε(N) < 10 при N ≤ 40); `P_C3_LEMMA_HOLDS_NUMERICALLY` 0.90.
Стратегическая оговорка (моя, до чисел): `R(q) ≤ C·λ₁` — нижняя оценка дна относительно явной энергии трала, RH-подобная посылка
(судья это и назвал). Развилка исследует, ЧТО именно нужно на широком расписании, не обещает обойти посылку. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (ночь) — Probe 22: широкие окна при m=13 — трал становится Ритц-вектором при N ≥ 4.5m; дно насыщается; лемма C3 держится

Чистый кэш (13,120) (dps 110), усечения `q_N = P_N f`, `λ₁, λ₂` обратной итерацией (дефлированной для `λ₂`):

| N | λ₁ | λ₂ | g | R(q_N) | ε = R/λ₁ | p | C3-оценка (ε−1)/(g−1) | α_G | α_q |
|---|---|---|---|---|---|---|---|---|---|
| 13 | 7.9e-31 | 2.8e-25 | 3.6e5 | 4.2e-16 | 5.3e14 | 3.7e-3 | 1.5e9 | +2.79e-3 | −1.56e-3 |
| 26 | 4.9e-45 | 1.3e-38 | 2.7e6 | 2.5e-32 | 5.1e12 | 1.9e-4 | 1.9e6 | −0.61e-3 | −1.56e-3 |
| 40 | 9.5e-54 | 7.7e-47 | 8.1e6 | 2.3e-46 | 2.4e7 | 8.6e-6 | 3.0 | −1.36e-3 | −1.56e-3 |
| 50 | 3.0e-57 | 5.9e-50 | 2.0e7 | 1.8e-54 | 607 | 4.2e-7 | 3.0e-5 | −1.52e-3 | −1.56e-3 |
| 60 | 1.0e-58 | 3.7e-51 | 3.7e7 | 1.1e-58 | **1.12** | 4.1e-10 | 3.3e-9 | −1.561e-3 | −1.562e-3 |
| 80 | 4.5e-59 | 1.7e-51 | 3.8e7 | 5.7e-59 | 1.28 | 5.6e-9 | 7.2e-9 | −1.567e-3 | −1.562e-3 |
| 120 | 3.5e-59 | 1.3e-51 | 3.8e7 | 4.7e-59 | 1.35 | 4.7e-9 | 9.4e-9 | −1.567e-3 | −1.562e-3 |

Четыре факта. (1) `λ₁(13,N)` насыщается: 1.0e-58 → 3.5e-59 между N = 60 и 120 (континуальное дно при λ² = 13); `g` насыщается у 3.8e7.
(2) `ε(N)` падает с 5e14 до 1.12 между N = 13 и 60: трал становится Ритц-вектором при `N* ≈ 4.5m`; `ε_∞(13) = 1.35` (Phase 1 это и видела).
(3) Лемма C3 `p ≤ (ε−1)/(g−1)` держится на всех N (при N ≥ 60: p = 4e-10..5e-9 против 3e-9..9e-9). (4) **На насыщенном окне кривизна дна
равна явному джету трала:** `α_G → α_q = −1/(16πm)·(1+…)` с точностью 3e-6 (N ≥ 60): стена кривизны на широком расписании — явная формула.
Судьбы: `P_LAMBDA1_SATURATES_IN_N` 0.60 ПОДТВЕРЖДЕНО; `P_EPS_CROSSES_BELOW_10_BY_N_3M` 0.50 ОПРОВЕРГНУТО (переход при N ≈ 4.5m, не 3m);
`P_C3_LEMMA_HOLDS_NUMERICALLY` 0.90 ПОДТВЕРЖДЕНО.
**Что это значит (моё прочтение, до судьи).** На широком расписании `N ≥ 4.5m` идентификация дна с Ξ = лемма C3 (условная, у судьи
сохранена) + явный трал (сегодняшние формулы) + `g → ∞` (наблюдается). Единственная посылка: `ε_∞(m) = R(q)/λ₁ ≤ C` — дно формы
Вейля не ниже явной энергии трала более чем в C раз. Это нижняя оценка дна = количественная положительность Вейля на кофинальном
семействе; при ложной RH дно уходит в минус (Yoshida/Bombieri) и посылка ложна. То есть широкое расписание переводит стену из
«перекрытие второй моды `d₂`» (собственный вектор, без механизма) в «`λ₁ ≥ R(q)/C`» (собственное значение, классическая форма,
конечный сертификат на каждой ячейке — рамка `FINITE_CERTIFICATE_PRINCIPLE`). Не обход посылки, а её самая чистая форма.
Запущены генерации широких кэшей: (23,110) dps 220 и (43,200) dps 300, MAX_DEGREE 300 (юниты `q3-wide-23`, `q3-wide-43`), чтобы
измерить `ε_∞(m)` на трёх m: ограничена ли `C`. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

**Probe 22 при m=23 (кэш (23,110), dps 220, quad 192):** `λ₁` ещё падает (1.9e-103 при N=90 → 4.3e-109 при N=110, насыщения нет до N=110 ≈ 4.8m,
в отличие от m=13, где насыщение при N ≈ 60 = 4.6m); `α_G → α_q` монотонно (−8.46e-4 при N=110 против −8.75e-4). **Странность, записанная
сразу:** `R(q_N)` выходит на плато 6e-84 при N ≥ 90 — это пол квадратуры (QUAD_ORDER = 192 даёт ~1e-42 в коэффициентах при n ~ 90, L = 3.1),
не энергия трала; `ε` при N ≥ 90 «растёт» только из-за пола. Различит: тот же кэш при QUAD_ORDER = 512 и N = 160. Юнит `q3-wide-43`
(quad 192) остановлен мной — при m=43 нужен пол ≤ 1e-125, quad 192 его не даёт; перезапуск после калибровки на m=23. Запущен `q3-wide-23q`
(N = 160, dps 220, quad 512). Прогноз: `P_QUAD512_LOWERS_FLOOR_BELOW_1E-100` 0.70; `P_LAMBDA1_23_SATURATES_BY_N160` 0.55.

## 2026-09-04 — Probe 22 (формат директивы владельца «materialize REQ-2026-09-04-FULLCHAIN»): широкие ячейки N ≥ 4m

Ячейки в кэше с N ≥ 4m: (13,120) сертифицированная, (23,110) (dps 220, quad 192). (43,86) и (13,26) не проходят порог. (23,160) генерируется
(юнит `q3-wide-23q`, quad 512) — в таблицу не вошла. `T_{m,N} = (L²/4π²)Σ_{k>N}1/k²`, `κ_X = 0.0231049931154`.

| cell | λ₁ | λ₂ | R(q) | R(q)/λ₁ | (R−λ₁)/(λ₂−λ₁) | sin²(G,q) = p | δ = κ(G)−κ(q) | T_{m,N} | δ/T | note |
|---|---|---|---|---|---|---|---|---|---|---|
| (13,120) | 3.484e-59 | 1.312e-51 | 4.720e-59 | 1.355 | 9.42e-9 | 4.69e-9 | −5.0e-6 | 1.383e-3 | −0.0036 | certified; saturated (N = 9.2m) |
| (23,110) | 4.340e-109 | 8.124e-101 | 6.460e-84 | 1.49e25 | 7.95e16 | 1.77e-7 | +2.9e-5 | 2.253e-3 | +0.0129 | NOT saturated (N = 4.8m); R(q) floored by quadrature (order 192; plateau 6e-84 from N = 90) |

Судьбы предрегистрированных (Mythos, frozen): `P_WIDE_RAYLEIGH_RATIO_LE_10` 0.35 → CONFIRMED на (13,120) (1.355); на (23,110) NOT_MEASURABLE
(пол квадратуры). `P_WIDE_DK_RATIO_LE_1e-6` 0.45 → CONFIRMED на (13,120) (9.4e-9); (23,110) NOT_MEASURABLE. `P_SECOND_WIDE_CELL_DELTA_LE_1e-5`
0.60 → REFUTED на доступной второй ячейке (δ = 2.9e-5 при N = 4.8m, ячейка не насыщена; `α_G` ещё идёт к `α_q`). Честная оговорка:
вторая широкая ячейка есть, но не насыщена и с полом; чистая вторая ячейка ((23,160), quad 512) придёт из юнита. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (20:35) — ПРЕДВАРИТЕЛЬНЫЙ вердикт FULLCHAIN от быстрой модели (`f3b0c97d` → `20b9ddb6`); настоящий судья ещё думает

Владелец: «быстрая модель ответила, сказала, что всё сделала; посмотри, не хуйня ли; Прошка реально думает». Файл лежит на
`EXPECTED_VERDICT_PATH` (184 строки против 700–1300 у судьи). **Оценка наблюдателя: не хуйня, но тонко.** Форма соблюдена: `IRREDUCIBLE_ATOM`
= `P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M`; S1 (тождество второго джета, THEOREM, верное имя теоремы), S2 (блок/Фешбах, THEOREM, верный файл),
S3 (скалярный остаток, THEOREM), S4 (кофинальный темп, NEW-MATH); честная пометка, что SHA-256 не пересчитан вне коннектора; верная форма
опровергателя (конечный кэш не опровергает кофинальный O-big); аудит расписания: (13,120) — сильное конечное свидетельство, не закон,
(23,110) не насыщена и с полом; две сохранённые перепредставления: перенос кривизны (`E_m = O(T)`) и широкое расписание с `sameCofinalGuard`
+ теорема насыщения/дополнительной щели. Судьбы Mythos проставлены моделью: атом 0.70 CONFIRMED, Feshbach/E_m 0.55 CONFIRMED, широкая цепочка
0.30 REFUTED, ноль NEW-MATH 0.10 REFUTED; K6 модели: цепочка на полке 0.08, NEW-MATH за пределами CCM §7 0.90, широкое расписание сокращает
укрытия 0.65. **Проверка её порогов на моих числах:** «adverse: для каждого n `R_83 ≥ 1.25·R_43`» — n=3: 1.14, n=4: 1.19, n=8: 1.44 → НЕ сработал
(не для каждого n); «FESHBACH_REMAINDER_DOMINANT: `|d₂−d₂⁽³⁾| ≥ 0.75|d₂|` на ≥ 3 ячейках» — 0.41, 0.73, 0.86, 0.93 → две ячейки, не три.
Чего нет по сравнению с судьёй: ни одного нового расчёта, ни плантов, ни разбора, куда именно переезжает трудность на широком расписании
(только названо). Статус: очередь FULLCHAIN остаётся OPEN до вердикта настоящего судьи; этот файл будет перезаписан его коммитом
(история git сохранит оба). Интейк судеб Mythos — после полного вердикта. DIAGNOSTIC_NEVER_A_PROOF.

**Probe 22, чистая ячейка (23,160) (quad 512, dps 220):** `λ₁` насыщается при N ≈ 145 ≈ 6.3m: 8.2e-112 (130) → 2.4e-112 (145) → 1.8e-112 (160);
`p → 4.8e-10`, `δ = −1.5e-6` при N=160 (`δ/T = −0.0010`): дно ≡ трал, как на (13,120). Судьба Mythos `P_SECOND_WIDE_CELL_DELTA_LE_1e-5` 0.60:
на насыщенной второй ячейке CONFIRMED (на ненасыщенной (23,110) было REFUTED — обе записи стоят). `P_LAMBDA1_23_SATURATES_BY_N160` 0.55
CONFIRMED. **Странность:** `R(q)` по-прежнему на плато 7e-84 при quad 512 — пол НЕ квадратурный; `P_QUAD512_LOWERS_FLOOR_BELOW_1E-100` 0.70
ОПРОВЕРГНУТО. Прочтения: (A) коэффициенты пишутся в json с ограниченным числом знаков (~42) → пол в квадрате 1e-84; (B) сам prolate-модель
(`MAX_DEGREE`/Legendre) даёт шум 1e-42. Различит: длина десятичных строк в кэше и `coeff_diff`. `ε(23)` до устранения пола не измерим.
**Пол разрешён (прочтение B):** в кэше (23,160) хранится по 90 значащих цифр, но сами значения `c_n` при n = 100, 130, 160 равны 3.2e-43, 8.9e-45,
9.2e-44 — плато в вычислении, не в формате. Источник: усечение Лежандра–Галёркина `MAX_DEGREE = 180` (relritz проверял «сходимость» 180..900
в double, т.е. до 1e-16, не до 1e-40+). Для (83,83) я уже ставил `MAX_DEGREE = 600` (|c_83/c_0| = 3.9e-35 без плато). Перезапуск: `q3-wide-23d` =
(23,160), dps 220, `MAX_DEGREE = 600`, quad 512; кэш с плато перенесён в scratchpad (не удалён). Правило в TOOLS/backlog: для широких окон и
малых `λ₁` `MAX_DEGREE` должен расти с нужной глубиной, ориентир `|c_N|² ≲ λ₁(m,∞)`. Прогноз: `P_MAXDEG600_FLOOR_BELOW_1E-100` 0.75.

## 2026-09-04 (ночь) — вердикт FULLCHAIN, полный (`660a072c`, второй проход судьи): IRREDUCIBLE_ATOM = сам потребитель G3; фаза бухгалтерии ЗАКРЫТА

**Судья (пересуд по слову владельца; предварительный вердикт быстрой модели `1e92ef48` понижен до «представление-специфичной подзадачи»).**
Атом: **`FiniteGroundTransformToCCMTrialLocallyUniform`** — существует предзаявленное расписание `N(m) ≥ m`, принятое `sameCofinalGuard`, такое что
`sup_K |F_ground(m,N(m)) − F_trial(m,N(m))| → 0` на каждом компакте открытой центрированной полосы (Lean-форма: `TendstoLocallyUniformlyOn`).
Почему не Фешбах-атом: `d₂ = d₂⁽³⁾ + ⟨e₀, p − z₂⁽³⁾⟩`, и полка не доказывает НИ `|d₂⁽³⁾| ≤ C₀T`, НИ `|⟨e₀,p−z⟩| ≤ C₁T`; доказать только второе — не
закрыть; широкое расписание может атаковать потребителя без сырой 3×3 лестницы; K8A требует слабейший неизменный интерфейс потребителя.
Минимальное недостающее тождество: источник-определённая факторизация `F_ground − F_trial = E_source` на одном носителе и нормировке с
`sup_K|E_source| ≤ ε_m(K) → 0`, где `E_source` строится из `K_{m,N}`, его нижнего спектрального проектора и буквального трала ДО любой
операторно-нормовой оценки через щель. Опровергатель: компакт, ε и кофинальная подпоследовательность с `sup ≥ ε` для КАЖДОГО допустимого
расписания; конечные кэши не опровергают. Дискриминатор на кэшах: прямой компактный P59-дефект на `K0 = {|Re z| ≤ 1, |Im z| ≤ 1/4}`, adverse
`COMPACT_DEFECT_NONDECAY` если `E_43 ≥ 0.9E_23` и `E_83 ≥ 0.9E_43` (убивает только N=m-представление). Три представления: R1 полная проекция
второй моды (не один Фешбах-слагаемый) 9/10·8/10; R2 перенос кривизны, решённый некругово (контроль момента переноса и остатка дна без
`α = O(T)`) 9/10·7/10; R3 широкое расписание: предзаявить `N(m)`, `sameCofinalGuard` + источник-специфичная кофинальная оценка насыщения
Рэлея / дополнительной щели, чьё компактное произведение → 0 — 10/10·9/10. Аудит расписания: N=m — одно представление, не теорема; (13,120) —
сильное конечное свидетельство; трудность сменой расписания НЕ снимается, «в меньше укрытий» — правдоподобно, не доказано (0.72).
S1, S2 — THEOREM (наши два Lean-файла, blob'ы названы); S3 — тождество THEOREM, обе оценки NEW-MATH; S4 — NEW-MATH (атом).
Судьбы Mythos (в YAML судьи): `P_JUDGE_RETURNS_IRREDUCIBLE_ATOM` 0.70 CONFIRMED; `P_ATOM_IS_FESHBACH_Y_COMPONENT_OR_E_M` 0.55 REFUTED как
операционный атом (CONFIRMED только как два представления); `P_JUDGE_BUILDS_CHAIN_ON_WIDE_SCHEDULE` 0.30 REFUTED на срезе запроса;
`P_CHAIN_HAS_ZERO_NEW_MATH_STEPS` 0.10 REFUTED. K6 судьи: цепочка на полке 0.03; NEW-MATH за CCM §7 — 0.97; расписание → меньше укрытий 0.72.
**Ход по правилу 13 — дискриминатор судьи посчитан (Probe 23, addendum 24):**

| cell | `E = sup_{K0}|f_G − f_q|` | argmax | E на [−1,1] | `A_q` | `E/A_q` |
|---|---|---|---|---|---|
| (13,13) | 4.525e-3 | (−1, −0.25) | 4.253e-3 | 0.0604 | 0.075 |
| (23,23) | 4.189e-3 | (−1, −0.25) | 3.937e-3 | 0.0545 | 0.077 |
| (43,43) | 3.327e-3 | (−1, −0.25) | 3.127e-3 | 0.0431 | 0.077 |
| (83,83) | 2.393e-3 | (−1, −0.25) | 2.249e-3 | 0.0312 | 0.077 |
| (13,120) | 4.813e-6 | (−1, −0.25) | 4.524e-6 | — | — |

`E_43/E_23 = 0.79`, `E_83/E_43 = 0.72` — adverse-правило (≥ 0.90) НЕ сработало: N=m-представление компактного спада живо. `E ≈ |δ_m|` (4.53e-3 против
4.35e-3; на (13,120) 4.8e-6 против 4.6e-6): **компактный дефект на K0 есть ровно кривизна** `δ·z²·Ξ`, одна форма и здесь. Судьбы (мои):
`P_COMPACT_DEFECT_NONDECAY` 0.35 REFUTED; `P_E_SCALES_LIKE_A_q` 0.70 CONFIRMED (0.075–0.077); `P_E_13_120_BELOW_1E-4` 0.85 CONFIRMED.
`TWO_RATE_FAILURE` (S3) не сработал (D: 0.62→0.33; R: 3.83→4.37, порог 1.25×).
**Итог дня.** Фаза бухгалтерии закрыта в обе стороны: восемь батчей, девять Lean-файлов, шесть убитых дорог с числами, и атом = сам
потребитель G3 «дно → трал локально равномерно на предзаявленном расписании». Следующая фаза — только механизм, из R1/R2/R3.
DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-04 (21:05) — «Go»: фаза механизма, линия R3 (широкое расписание); план измерений и предсказания

Владелец: «так делаем, go». Линия R3 по его выбору (широкие окна + C3 с явными формулами). Порядок: числа и чтение, потом батч
в формате закрытия. Запущено: (1) paper-агент — типизация цепочки R3 по CCM: что доказано о дне `λ_min(λ)` (верхняя оценка через
`Q(k_λ)`, есть ли нижняя и при какой гипотезе), насыщение `λ₁(m,N) → λ₁(m,∞)`, требования крыши к расписанию (`sameCofinalGuard`,
`rh_of_canonical_strip_slots`), эпистемический файрвол: связь посылки `ε_∞(m) = R(k_λ)/λ₁(m,∞) ≤ C` с RH (Yoshida/Bombieri при ¬RH;
количественная положительность при RH; известна ли импликация «положительность на НЕисчерпывающем семействе ⇒ RH»);
(2) юнит `q3-wide-43d`: трал (43,320), dps 320, `MAX_DEGREE 900`, quad 768 (часы) — третья точка `ε_∞(m)`; (3) `q3-wide-23d` продолжает.
Предсказания до чисел: `P_EPS_INF_BOUNDED_BY_2` 0.55 (`ε_∞(23), ε_∞(43) ≤ 2`); `P_NSTAR_GROWS_FASTER_THAN_LINEAR` 0.65 (`N*/m`: 4.6, 6.3, → > 7
при m=43); `P_CCM_HAS_NO_LOWER_BOUND_ON_BOTTOM` 0.75 (в статье нет нижней оценки `λ_min` без RH); `P_ROOF_ACCEPTS_N_OF_M` 0.60 (крыша
принимает `N(m) ≠ m` без правок Lean). Контроль фоновых задач: тест `sleep 420` (21:01:28) — жив после foreground-вызова.

## 2026-09-04 (21:25) — R3-префлайт: посылка широкого расписания `ε_∞(m) ≤ C` есть RH целиком, по неравенству самой статьи CCM

**Агент (Opus, 10 мин, чтение):** `docs/routeB_bus/AGENT_REPORT_2026-09-05_GOAL058_WIDE_SCHEDULE_R3_CHAIN_PREFLIGHT.md`. Типизированная цепочка R3:
S0 предзаявить `N(m)` — LEAN-READY; S1 `sameCofinalGuard` принимает путь — THEOREM (`CanonicalRHRouteSkeleton.lean:69`); S2 `λ₁(m,N) ↓ λ₁(m,∞)` —
THEOREM (CCM Prop. 3.4, только предел); S3 темп насыщения — NEW-MATH; **S4 `ε_∞(m) = R(q_m)/λ₁(m,∞) ≤ C` кофинально — NEW-MATH, RH-hard**;
S5 относительная щель `g ≥ g₀ > 1` — NEW-MATH (min–max даёт ВЕРХНЮЮ оценку `λ₂`, не ту сторону); S6 `p ≤ (ε−1)/(g−1)` — THEOREM (условная);
S7 `p → 0 ⇒ sup_K|F_ground − F_trial| → 0` — NEW-MATH (ℓ²-угол ≠ компактная sup-норма; это и есть атом судьи); S8 трал → Ξ — THEOREM (Lemma 7.3,
для континуального `k_λ`, не `P_N k_λ`); S9 вещественные нули + крыша — THEOREM/COND.
**Три опровержения моих посылок (агент; два из трёх проверены мной по тексту статьи):** (1) CCM НЕ доказывают никакой оценки `λ_min` ни в
одну сторону — ни верхней через `Q(k_λ)`, ни нижней, ни «почти-минимизатор»; **Cor. 3.7 дословно: «Note that we cannot assert that µ_λ ≥ 0»**
(проверено: pdftotext, строка 559). Темп `e^{−4πλ²+9 log λ}` — Fuchs 1964 для prolate-дефекта `1 − χ₄`, не для `ε_λ`; связь — только Figure 4.
(2) В Lean `N = m` нигде не зафиксировано: `PairCofinal` = `m → ∞ ∧ N → ∞` независимо (проверено: `D0CanonicalApproximation.lean:67`);
`N(m) = 6m` или `c·m·log m` допустимы как есть; страж ничего не ограничивает и ничего не поставляет. (3) Под RH количественного пола нет
нигде: Bombieri 2000 Thm 12 — только `|I| < log 2` (m ≤ 2) и размера `O(1)`; нужно `e^{−4πm}` при m ≥ 13.
**Файрвол, проверен мной по (3.27):** статья: `λ > λ′ ⇒ µ_λ ≤ µ_λ′` (строка 561). Значит `µ_λ > 0` кофинально по λ ⇒ `µ_λ′ > 0` для ВСЕХ λ′ ⇒
положительность Вейля на всех окнах ⇒ RH (Weil / Yoshida 1992 Thm 2). Посылка S4 влечёт `λ₁(m,∞) > 0` кофинально, т.е. **R3 не сводит RH
ни к чему более слабому: он переносит всю RH в одно неравенство `µ_λ ≥ Q(k_λ)/C` с явной вычислимой правой частью**. Кофинальность ничего
не покупает из-за монотонности. Судьбы: `P_CCM_HAS_NO_LOWER_BOUND_ON_BOTTOM` 0.75 CONFIRMED (и верхней нет); `P_ROOF_ACCEPTS_N_OF_M` 0.60
CONFIRMED. **Новое число агента:** насыщенное дно спадает на 5.33 декады на единицу m (13→23) против показателя Fuchs `4π/ln 10 = 5.46`;
при `N = m` наклон 2.10 — `N = m` никогда не меряет континуальный объект. Предсказание агента `λ₁(43,∞) = 10^{−219.5}`: мой скан `q3-sat43`
даёт 5.8e-216 при N = 260 (ещё падает) — совместимо; финал скана покажет. Оговорка к агенту: кэши dps 110 не мерят `ε` (R(q)), но `λ₁`
меряется из even block в arb при любом dps — его фраза «не могут измерить λ₁» неточна.
**Что это значит для развилки владельца.** Линия R3 (широкие окна + C3) честно кончается так: механизм = сама положительность Вейля,
количественная, на всех окнах; конечный сертификат на каждой ячейке есть, кофинально это RH. Линия N = m (R1/R2) положительность
посылкой НЕ использует — потому судья и оставил её; но механизма там не найдено. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-04 (21:40) — директива из живого чата (relay, не верифицирована): `RUN_WIDE_SCHEDULE_SOURCE_MECHANISM_PREFLIGHT`

Владелец вставил YAML: PRIMARY `RUN_WIDE_SCHEDULE_SOURCE_MECHANISM_PREFLIGHT`; ARISTOTLE: `SUBMIT_FULL_ATOM_NOW: false`, `SUBMIT_AFTER_PREFLIGHT: true`
(«точная конечная алгебра уже формализована; не хватает источник-специфичной кофинальной аналитической оценки»); ранжир R3 (10/10, две насыщенные
широкие ячейки) > R2 (9/10, риск круговой темп) > R1 (9/10, два независимых недоказанных остатка); NEXT_TESTS: `CLEAN_23_160_INSTRUMENT_FLOOR`,
`RESIDUAL_TO_SOURCE_TAIL_MECHANISM`, `ONE_PRECOMMITTED_THIRD_WIDE_CELL`; PROBE_SCHEDULE `N(m) = 8m`, предзаявлено только для следующей
невиданной ячейки; предсказания (заморожены): `P_ARISTOTLE_CLOSES_FULL_ATOM_FROM_CURRENT_SHELF` 0.12, `P_WIDE43_PROJECTIVE_ERROR_LE_1E_7` 0.67,
`P_WIDE_RESIDUAL_HAS_SOURCE_TAIL_EXPLANATION` 0.58, `P_CURVATURE_ROUTE_BEATS_WIDE_SCHEDULE_AFTER_PROBES` 0.27; smallest gap
`WIDE_SCHEDULE_SOURCE_RESIDUAL_OVER_SECOND_SEPARATION_RATE`.
**Возражение наблюдателя, записано до исполнения:** ранжир не учитывает файрвол 21:25 — посылка R3 ⇒ `µ_λ > 0` кофинально ⇒ по (3.27) на всех
окнах ⇒ RH. R3 пока «RH в одном неравенстве», не механизм. Идёт первым пунктом в следующий батч. Исполнение тестов при этом: (1) чистый
пол (23,160) — юнит `q3-wide-23d` идёт; (2) остаток → хвост источника — измерить на насыщенных ячейках, как `ε − 1` (избыток энергии трала над
дном: 0.35 при m=13) соотносится с prolate-дефектом `1 − χ₄` (Fuchs) и нижним окном `B_λ`; (3) третья широкая ячейка по предзаявленному `N = 8m`:
запущен `q3-wide-43p` = (43,344) в дополнение к уже идущему (43,320) (nproc позволяет; 320 не выбрасываю — даст проверку насыщения).
Тест на `P_WIDE43_PROJECTIVE_ERROR_LE_1E_7`: `p = 1 − ⟨ξ,q⟩²` на (43,344). DIAGNOSTIC_NEVER_A_PROOF.

**Тест (2) директивы на насыщенной ячейке (13,120), полный eig (121×121, dps 300, 12 с):** `λ₁ = 3.484e-59, λ₂ = 1.312e-51, λ₃ = 1.091e-44`; `p = 4.692e-9`,
масса вне дна на `u₂` — **100.00 %** (одна форма и на широком окне). Избыток энергии трала `R − λ₁ = 1.236e-59` (спектральная сумма = прямое
значение) делится: `u₂` — 49.8 % (`λ₂·p`), `u₃` — 22.5 %, `u₄` — 6.2 %, верх спектра (`λ_j > 1e-40`, масса 7e-13 % от p) — 27.7 %. Значит
`p ≈ (ε−1)/(2g)`: оценка C3 `p ≤ (ε−1)/(g−1)` точна до множителя 2 (9.4e-9 против 4.7e-9). «Объяснение остатка хвостом источника»
(`P_WIDE_RESIDUAL_HAS_SOURCE_TAIL_EXPLANATION` 0.58): половина остатка — это сама вторая мода (`u₂ ≈ Ξ·(x²−⟨x²⟩)`, известна), вторая половина
размазана по схлопнувшейся полосе `u₃…` и верху; отдельного «хвоста источника» (`B_λ`, `E_{λ,N}`) в спектральной картине не видно — их
ℓ²-массы (`e^{−πm}`, `e^{−π²m/2L}`) на 20+ порядков больше `p`, а энергии — нет; пока UNRESOLVED, склоняется к REFUTED. Насыщение m=43:
`λ₁(43,300) = 1.057e-219` при предсказании агента `10^{−219.5} = 3.2e-220` (N=340 покажет). DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-04 (22:00) — условное решение судьи (живой чат, relay): R3 на карантине; аудит пяти переходов по тексту CCM — выполнен наблюдателем

**Судья (conditional ruling, не bus-verdict):** возражение принято; `QUARANTINE_R3_WIDE_SCHEDULE_UNTIL_CCM_NONCIRCULARITY_AUDIT`. R3 как конечная
диагностика — сохранён; как первый proof-route — отозван; как прямое RH-достаточное условие — правдоподобно, ждёт source-lock; как дешёвая
промежуточная лемма — не авторизован. Зонды продолжать, статус FINITE_CELL only; NEVER: широкие ячейки не доказывают `ε_∞ ≤ C`, `µ_λ > 0`, RH.
Требуемый аудит: (1) что такое `µ_λ`; (2) диапазон и направление (3.27); (3) как `ε_∞ ≤ C` даёт eventual strict positivity; (4) требует ли
переход к RH `µ_λ > 0 ∀λ` или больше; (5) совпадает ли бумажная `ε_∞` с нашими конечноклеточными величинами (опасность C04).
**Аудит по тексту `docs/routeB_bus/litreview/pdfs/2511.22755.pdf` (pdftotext, строки указаны):**
(1) Cor. 3.7 (стр. 11, строка 557–558): `µ_λ` — «the largest lower bound of the spectrum of A_λ», т.е. дно полулокальной формы Вейля
`Q_{Wλ}` на `L²([λ⁻¹, λ], d*u)`; существует минимизатор `φ`. (2) (3.27) там же, для `λ > λ′` при `λ > 1`, направление `µ_λ ≤ µ_λ′`; доказательство через
ядро кусочно-гладких функций и эквивалентность `ν ≤ µ_λ ⇔ Q_{Wλ}(f,f) ≥ ν‖f‖²` для носителей в `[λ⁻¹, λ]` (расширение носителя не увеличивает
дно). (3) Наша `ε_∞(m) := lim_N R(q_{m,N})/λ₁(m,N)`; при `R(q) > 0` из `ε_∞ ≤ C` следует `λ₁(m,∞) ≥ R/C > 0`; связь с бумажным объектом — пункт (5).
(4) **Cor. 3.8 (строка 573): «If the limit when λ → ∞ of the decreasing function µ_λ is equal to 0 then RH holds.»** Наша цепь: `µ_λ > 0`
кофинально ⇒ (3.27) `µ_λ > 0 ∀λ` ⇒ `lim µ_λ ≥ 0`; и `µ_λ ≤ R(q_λ) → 0` (энергия трала → 0; численно `e^{−4πm}`, в статье — Figure 4, не теорема)
⇒ `lim = 0` ⇒ RH по Cor. 3.8. Дополнительных условий нет; нужна лишь `R(q_λ) → 0` (или любая последовательность пробных функций с энергией → 0).
(5) **Prop. 3.4 (строка 414–421): «the lower bound of Q_{Wλ} is the limit, when N → ∞, of the smallest eigenvalue of the restriction of Q_{Wλ} to
the linear span E_N of the functions V_k with |k| ≤ N»** — наше насыщение `λ₁(m,N) → λ₁(m,∞)` есть ровно `µ_λ` при `λ² = m`; C04 закрыт для `λ₁`.
Для `R(q_N)`: `q_N = P_N f_λ`, `R(q_N) → Q(k_λ)/‖k_λ‖²` при `N → ∞` (проекция на ядро). Итог аудита: **обе стрелки зафиксированы в тексте CCM;
`ε_∞ ≤ C` (кофинально по m) ⇒ RH через (3.27) + Cor. 3.8 + `R(q_λ) → 0`.** Кофинальность не ослабляет. Переименование судьи принято:
R3 = `CCM_UNIFORM_ERROR_RH_ATOM`, не механизм.
**Ответ на вопрос владельца «значит, доказали?» — нет.** Цепь доказывает импликацию «ЕСЛИ `ε_∞(m) ≤ C` для всех больших m, ТО RH». Мы
измерили `ε_∞(13) = 1.35` — одно число при одном m; m = 23, 43 считаются. Конечное число ячеек не доказывает «для всех больших m»; если бы
доказывало, это была бы RH, потому это и не может быть дёшево. Числа могут только опровергнуть посылку (если `ε_∞(m)` уходит в бесконечность).
Что изменилось: мы теперь точно знаем, что посылка широкой линии — это RH, переписанная через Cor. 3.8. DIAGNOSTIC_NEVER_A_PROOF.
PX_RH_CLAIM: NOT_MADE.

**Скан насыщения m=43 (`q3-sat43`, done):** `λ₁(43,N)` = 1.0e-90 (43), 2.2e-137 (86), 7.8e-170 (130), 1.4e-190 (170), 2.1e-206 (215), 5.8e-216 (260),
1.06e-219 (300), **2.62e-220 (340)**; `g = λ₂/λ₁` растёт до 6.0e9. Предсказание агента по закону Figure 4 `λ₁(43,∞) = 10^{−219.5} = 3.2e-220` —
попадание в 20 % (ещё небольшой спад 300→340, множитель 4). `N*(43) ≈ 7.5–8·m`; `N*/m = 4.6, 6.3, ≈8` (m = 13, 23, 43) —
`P_NSTAR_GROWS_FASTER_THAN_LINEAR` 0.65 CONFIRMED; предзаявленное `N(m) = 8m` судьи при m = 43 попадает как раз на насыщение. `µ_λ` при
`λ² = 13, 23, 43`: 3.5e-59, 1.8e-112, 2.6e-220 → декад на единицу m: 5.33 (13→23), 5.40 (23→43); показатель Fuchs `4π/ln10 = 5.46`. DIAGNOSTIC.

## 2026-09-04 (22:40) — чистая ячейка (23,160), `MAX_DEGREE 600` (3175 с): `ε_∞(23) = 1.33`; пол снят; знак-свободная оценка Ритца точна до 1.35×

`|c_100| = 2.3e-48, |c_130| = 4.0e-57, |c_160| = 5.7e-58` — плато исчезло (`P_MAXDEG600_FLOOR_BELOW_1E-100`: коэффициенты ниже 1e-57 на краю; R(q) чист до
2e-112 — CONFIRMED по назначению). `ε(N) = R/λ₁`: 3.9e6 (110), 4.66 (130), 1.16 (145), **1.33 (160)**; `(R−λ₁)/(λ₂−λ₁)`: 2.1e-2, 1.0e-8, 3.4e-10, 6.5e-10;
`p`: 1.8e-7, 1.4e-9, 2.2e-10, 4.8e-10. **`ε_∞(23) ≈ 1.33` против `ε_∞(13) = 1.35`** — `P_EPS_INF_BOUNDED_BY_2` держится на двух m (третья точка m=43 —
юниты (43,320), (43,344)). Знак-свободная оценка `p ≤ (R−λ₁)/(λ₂−λ₁)` точна до множителя 1.35 (на (13,120) — до 2). DIAGNOSTIC; FINITE_CELL only
(по условному решению судьи: широкие ячейки не доказывают ни `ε_∞ ≤ C`, ни положительность, ни RH).

## 2026-09-04 (23:05) — живой чат судьи (relay): «если посылка доказана — RH доказана; текущие числа посылку не доказывают»

Судья подтверждает файрвол: строгое eventual `µ_λ > 0` ⇒ RH через (3.27) и глобальную положительность формы Вейля; конечные `ε_{λ,N} = λ_min(Q_W^N)`
убывают к `µ_λ` (Prop. 3.4), значит **вычисленные положительные `λ₁(m,N)` — ВЕРХНИЕ границы для `µ_λ`**, а нужна нижняя; модель `1, 1/2, 1/3, …`.
Широкие ячейки — сильное FINITE_CELL evidence (`p` = 4.7e-9, 4.8e-10), не кофинальная теорема. Нужный мост: «finite certified cells →
uniform/cofinal continuum lower bound» (Вариант 1: `ε_{λ,N} − TailError_{λ,N} > 0` со строго доказанной оценкой хвоста; Вариант 2: теорема
`ε_∞ ≤ C ⇒ eventual µ_λ > 0` плюс независимое доказательство `ε_∞ ≤ C` для того же континуального объекта). Находка судьи по статье: CCM
сами называют два недостающих шага (simple-even нижнего состояния; строгая близость `k_λ` к `ξ_λ`) и пишут, что строгое доказательство
сходимости спектров установило бы RH. Поправка наблюдателя к тексту судьи: пересчёт (23,160) при `MAX_DEGREE 600` уже завершён — `ε_∞(23) = 1.33`,
плато снято (22:40). Согласие: ничего не доказано; батч SIGNFREE спрашивает ровно про мост, но снизу от знака — достаточно ли потребителю
`λ₁ ≥ −o(λ₂)` вместо `µ_λ > 0`. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-04 (23:30) — вердикт SIGNFREE (`0cee3192`): ответ B — `(P−)` RH-эквивалентно; три моих утверждения убиты; route score 4

**Судья.** Класс `KILL_PMINUS_AS_STRICTLY_WEAKER_THAN_RH`. Конечное неравенство (SF) `(λ₂−λ₁)p ≤ R(q) − λ₁` принято как знак-свободное и LEAN-READY.
Но `(P−)`: `λ₁ ≥ −o(λ₂)` на семействе CCM (континуальном и на любом широком `N(m) ≥ m`) **эквивалентно RH**. Доказательство (Q1.1, проверено мной):
второй уровень ограничен СВЕРХУ равномерно по окну — min–max на фиксированном двумерном пространстве гладких функций из одного окна,
допустимом во всех больших окнах, форма на нём не меняется ⇒ `ν₂(λ) ≤ M`. Тогда `o(λ₂) = o(1)`, `(P−)` даёт `µ ≥ −e_m M → 0`, по (3.27) все окна
неотрицательны ⇒ RH. Cor. 3.8 (нулевой предел) не нужен. Обратно, RH ⇒ `(P−)` с `e_m = 0`. Q1.2: конечно-диагональный мост (REC) — восстановление
фиксированной гладкой пробной функции на диагонали `N ≥ m` с оценкой `C_f √m (1+L)² (L/N)² → 0` (вывод судьи из формы Connes–Consani 2106.01715
Prop. 2.1 / CCM (3.7)–(3.11)); при ¬RH фиксированный отрицательный свидетель даёт `b_{m,N(m)} ≤ −c` кофинально. Q1.3: чётный сектор — через
чётный критерий Вейля (Yoshida 1992 Prop. 1(2), по нашей карточке). Q1.4: при ¬RH `(−b_m)/s_m ≥ c/M` — отрицательная часть НЕ мала относительно
второго уровня. **Убито (датумы против наблюдателя):** (1) `(P−)` как строго более слабое; (2) «`C(K,L) = poly(L)`» — ЛОЖНО вне вещественной оси:
`C_N(K,L) ≤ √(sinh(σL)/σ)` (Бессель на явном ядре), масштаб `m^{σ/2}`; (3) «CCM не дают нижней оценки ни в одну сторону» — ЛОЖНО как сказано:
Prop. 3.3 — полуограниченность снизу, явная грубая форма `µ_λ ≥ a_min − 2(λ−λ⁻¹) − 2Σ_{n≤λ²}Λ(n)/√n` (ухудшается, не `−o(ν₂)`); (4) «`p → 0 ⇔ η → 0`» —
только `⇒`: плант `diag(0,1,m²)`; (5) «`p → 0 ⇒` компактный спад» — контрпример с полюсными ядрами (`√2/σ ≠ 0`); (6) выборка как нижняя оценка якоря
`|q₀| ≥ c` — нет (`q₀ ~ c/√L` для фиксированной гладкой функции). Также поправка к relay: `R/µ ≤ C` не даёт `µ ≥ R/C` без знака µ. Оставлено живым:
(SF), независимое доказательство RH-достаточной оценки, маршрут дно–трал. Q3(a): 2608.24827 — свежий препринт с сертификатами на фиксированных
окнах за классическим диапазоном (не проверен, не импортирован). Q3(c): `Q_W(k_λ) ≤ e^{−4πλ²+…}` — не теорема (Figure 4 — график). Ранжир: (1) аудит
готового знак-свободного и якорно-взвешенного леджера на кэшах; (2) точный якорный функционал ошибки; (3) полный взвешенный бюджет.
Судьбы: `P_SIGNFREE_PREMISE_STRICTLY_WEAKER_THAN_RH` 0.55 REFUTED; `P_COMPACT_TRANSFER_LEAN_READY` 0.75 CONFIRMED только для ядра (poly(L) отвергнуто);
`P_JUDGE_NAMES_UNCONDITIONAL_LOWER_BOUND` 0.15 REFUTED для цели; `P_NOT_RH_NEGATIVE_PART_IS_LARGE` 0.50 CONFIRMED условно; `P_CCM_HAS_NO_LOWER_BOUND`
0.75 REFUTED как сказано; остальные UNRESOLVED/CONFIRMED по ledger'у. Codex-директива: `P59SignFreeRitz.lean` — (SF) с плантами (агенту, политика
владельца). Route score 5 → 4. Класс прогресса: FALSIFICATION.
**Леджер судьи посчитан (arb, оболочки):** (13,120): `Δ = 1.3119e-51, a−b = 1.2360e-59, p = 4.6919e-9, η = 9.4217e-9`, `(a−b) − Δp = 6.205e-60` ∈
[6.20e-60, 6.20e-60] → (SF) PASS сертифицированно; невязки 3e-97. (23,160): `Δ = 9.2973e-104, a−b = 5.998e-113, p = 4.782e-10, η = 6.452e-10`,
`(a−b) − Δp = 1.552e-113` → PASS; невязки 4e-156. Якорный страж `√(2η) ≤ |q₀|/2`: 1.4e-4 ≤ 0.27 и 3.6e-5 ≤ 0.25 — OK (первый вывод показал FAIL из-за
знака `q₀ = −0.54`: ошибка моего скрипта, не математики). Норма ядра `C_N(z)` при `z = 0, 7, i/4, 7 + i/4`: 1.6015, 1.6013, 1.6565, 1.6562 (m=13) и 1.7707,
1.7696, 1.8617, 1.8606 (m=23) — совпадают с оценкой Бесселя `√L`, `√(sinh(σL)/σ)` на 4 знака: формула судьи точна, poly(L) мой — ложь.
DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-04 (23:50) — внешний вход: arXiv:2608.24827 (Xuefeng Zhu, v2 2026-09-02) — разбор по правилу 14; судья на GPT-6 Astra

Владелец: «делаем разбор». Полка: `ask.sh` — не найдено (индекс неполон); `paper.sh 2608.24827` — PDF, bib, Zotero, строка REFERENCES
(`XUEFENGZHU-2026`, NEEDS_CARDS). Агент-чтец пишет карточку. **Из аннотации (мой первый разбор, до карточки):** объект — профиль
`λ*(L) = inf Q(f)/‖f‖²` формы Вейля на окне носителя `[−L, L]` (в логарифмической переменной; наше окно `[1/λ, λ]` ↔ полуширина
`L_half = (log m)/2` = 1.28, 1.57, 1.88 при m = 13, 23, 43). (a) **Безусловная нижняя оценка (сертификат):** `Q(f) ≥ 8.9e-18‖f‖²` при
`supp f ⊆ [−0.8, 0.8]` (носитель автокорреляции 1.6, в 2.3 раза больше классического `log 2`); метод — «one-stroke reduction»: поточечная
огибающая символа Вейля с оптимальной (по Вейлю) константой гребёнки сводит положительность на окне к PSD одной конечной матрицы,
связь с хвостом 1e-100; нечётный сектор: **основное состояние окна простое и чётное с сертифицированными двусторонними
разделениями** — ровно спектральная гипотеза программы Connes–Consani–Moscovici–van Suijlekom; разведочный расчёт при носителе 2.38
(полуширина 1.19 — чуть меньше нашей m=13) и **дважды экспоненциальная цена сертификата**. (b) **Безусловные верхние оценки** до
`3.2e-283` при `L = 2` (только геометрическая сторона: простые, архимедов интеграл, полюс, интервальная арифметика) и эмпирический
закон `−ln λ*(L) ≃ 2π² N(T*)/ln N(T*)`, `T* = 2πe^{2L}` — спад быстрее любой экспоненты, константа `2π²` = темп Ландау–Видома, подогнана,
не выведена; под RH `λ*(L) ≤ exp(−Le^L)`. (c) **Почему маршрут положительности не достигает RH без помощи:** любой сертификат этого
типа должен разрешать частоты до `T₁(L) = 2πe^{A_L}`, `A_L ~ 4e^L` — порог растёт дважды экспоненциально, никакая поточечная оценка
гребёнки его не снижает, а спектральный запас схлопывается с темпом Ландау–Видома. **Что это для нас (предварительно):** прямое
подтверждение файрвола судьи с другой стороны; наш закон 5.4 декады/m ↔ их закон через `N(T*)` — проверить кроссволк на наших
трёх точках (задача агенту); их простота+чётность основного состояния на окнах ≤ 1.6 — это S9 (`simple-even`) для малых окон, не
кофинально; сертификаты на наших окнах (полуширина ≥ 1.28) стоят дважды экспоненциально. Карточка и вердикт — после агента.
**Судья:** владелец сообщил апгрейд на GPT-6 Astra (выпуск 2026-09-03). Официальная guidance по промптингу: цель, границы, автономия,
определение «сделано», приоритет инструкций — совпадает с нашим форматом батча закрытия; специальных правил для многошаговой
математики нет; `reasoning.effort` до `max`. Записано в память. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (00:20) — Lean: `P59SignFreeRitz.lean` KERNEL_GREEN (директива SIGNFREE), десятый файл фронта

Opus-агент (15 мин), проверено мной: `lake env lean` EXIT 0 без вывода, `q3_check ok`, все 26 именованных деклараций с аксиомами
`[propext, Classical.choice, Quot.sound]` (при печати в одну строку; ни `sorryAx`, ни неизвестных констант), `sorry/admit/exact?` = 0.
Полка: `RelativeRitzFinite.lean` — комплексная эрмитова, только делённая форма, с `0 < λ₁` и строгой щелью в голове; процитирована, добавлено
лишь недостающее. Доказано без знака (вещественное скалярное пространство, ортонормированный базис собственных векторов, `Monotone lam`,
`‖q‖ = 1`; симметрия K следует): `signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess`; равенство `R − λ₁ = Σ(λ_j − λ₁)w_j`; делённая
форма ТОЛЬКО под `0 < lam 1 − lam 0` (строка 167 — единственное место с положительностью); дистанционные следствия `d² = 2(1−√(1−p)) ≤ 2p`.
Планты судьи: `diag(−2,−1)` — равенство `Δp = R − λ₁ = t²`; нулевая щель без деления; `diag(0,1,m²)` — `p = 1/m²`, `η = 1` при каждом `m ≥ 1`
и `∀ε ∃m: p < ε ∧ η = 1`. Второй канал агента: 14000 случайных симметричных матриц, 5743 с полностью отрицательным спектром, нарушений нет
(2.7e-15 шум). Закрывает только конечную алгебру S1; не `(P−)`, не якорь, не G3, не RH. Отчёт:
`docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-05_GOAL058_P59_SIGN_FREE_RITZ.md`.

## 2026-09-05 (00:40) — карточка Чжу готова; закон Ландау–Видома воспроизводит наши дна на 0.006 %; фронт сертификатов m = 4.95

Агент (17 мин): объект совпадает (`L_Zhu = (log m)/2`); закон `−ln λ* = 2π² N(2πm)/ln N(2πm)` даёт `k(13) = 19.5146` против интерполяции Чжу 19.5135,
`k(23) = 20.1302` против 20.1244 (наши `λ₁` — внешне проверены). Полный разбор в `CHAT_DIGESTS` (2026-09-05). Датум против наблюдателя: моё
«5.33–5.40 против Fuchs 5.46» — не закон, локальный наклон Чжу растёт от 4.84 до 5.82. Предрегистрация агента на m=43 (`−220.00 ± 0.15` по Чжу против
`−220.95` Fuchs против `[−219.75, −219.05]` R3-отчёта): наше `λ₁(43,340) = 2.62e-220` (`−219.58`, ещё падает) — скан продлён (`q3-sat43b`, N = 380..460).
REFERENCES: `XUEFENGZHU-2026` → HAVE. DIAGNOSTIC.

## 2026-09-05 (01:10) — судья написал себе запрос на доказательство: `REQ-2026-09-04-WEILPROOF` (a23dc64d); мой PROVE — superseded

Владелец: «это Астра сама написала себе запрос… давай учиться из этого». Проверено: файл на `a23dc64d`, blob `6f60ccbe…`, SHA-256 `00222547…`,
18460 байт, 144 строки, LF — квитанция судьи совпадает. Содержание: цель W — положительность Вейля на ПОЛНОМ комплексном классе `C_c^∞`,
буквальная форма CCM (3.7)–(3.11) на свёрточных квадратах `f* * f`; допустимая цель C — `QW_λj ≥ −r_j‖f‖²`, `r_j → 0`; конечная цель F —
`c*K_{m,N(m)}c ≥ −e_m‖c‖²` для КАЖДОГО вектора плюс восстановление каждого фиксированного гладкого теста (endpoint jumps, архимедов
множитель, простые, полюса); SIGNFREE Q1.2 — PAPER_DERIVATION_TO_RECHECK; запреты на подмену; три кода результата; фальсификатор для
каждой репрезентации. Десять правил текста записаны в проектный `CLAUDE.md` («Батч доказательства») и в память (`proof-attempt-batch`).
Мой `REQ-2026-09-05-PROVE` (e058bff0) помечен SUPERSEDED_BY_WEILPROOF (стоит, только если уже доставлен). WEILPROOF связывается в очередь
с моими предрегистрациями: `P_RESULT_PARTIAL_WITH_REMAINDER` 0.80, `P_NEW_LEMMA_PROVED` 0.45, `P_PROOF_CANDIDATE_COMPLETE` 0.03,
`P_ATTEMPT_REFUTED_WITH_COUNTEREXAMPLE` 0.15.

## 2026-09-05 (01:20) — вердикт WEILPROOF (`b8b0dc95`, blob `a3fb1622`): PARTIAL_PROOF_WITH_PRECISE_REMAINDER; тождества проверены мной на 4e-18

**Судья (GPT-6 Astra, по собственному запросу).** Класс `TRY_WEIL_EXACT_TRANSLATION_GRAM_AND_SIGNED_ARITHMETIC_REMAINDER`. Доказано (PAPER):
(1) точный логарифмический перенос полной формы `𝒬(g) = QW(f,f)` на всём комплексном `C_c^∞` с автокорреляцией `C_g`, весом `a(t) = e^{−t/2}/(1−e^{−2t})`,
полюсными функционалами `A_±`, `c₀ = log 4π + γ`; (2)–(3) энергия сдвигов `𝒟(g) = ∫a(t)‖τ_tg − g‖²dt ≥ 0`, `−W_ℝ = 𝒟 − c_A H`, `c_A = γ + log 8π + π/2`,
полюсный член `= 2|C_L|² − 2|S_L|²` (разность квадратов; по одному не положителен — контрпример `x·χ(x)`; норма отрицательного функционала
`s_L = sinh(L/2) − L/2` точная, cosh ⊥ sinh на `J_L`); (5) **безусловная нижняя оценка на всех направлениях** `𝒬(g) ≥ b(L)‖g‖²`,
`b(L) = J(L) − c_A − 2A_L − 2sinh(L/2) + L`, `J(L) = 2(artanh e^{−L/2} + arctan e^{−L/2})` — но `b(L) → −∞`, C из неё не следует (независимые
оценки трёх вкладов не дают знак); (8) **буквальная CCM-матрица = Грам минус скаляр минус один квадрат:** `K_{m,N} = Γ − c_L I − 2ββ*`, `Γ ⪰ 0`
(Грам сдвигов + простых + `2αα*`), `c_L = c_A + 2A_L − J(L)`, `α_n, β_n` явные (7), entries сверены с `ccmQKernel/ccmW02Entry/ccmPrimeEntryN1/ccmWREntry`;
первое оставшееся для F: (GAP-GRAM) `c*Γc ≥ (c_L − e_m)‖c‖² + 2|β*c|²`; плант `Γ = diag(0,2), c_L = 1 ⇒ K = diag(−1,1)`; (9) **точное арифметическое
разложение** `𝒬(g) = 𝒥(g) − d_A‖g‖² + 𝒮(g)`, `𝒥 = ∫k(t)‖τ_tg − g‖²`, `k = a − e^{−t/2} > 0`, `d_A = c_A − 4 > 0`,
`𝒮 = 2∫₀^L Δ(t)e^{−t/2}(C_g' − C_g/2)dt`, `Δ(t) = ψ(e^t) − (e^t − 1)` (расхождение Чебышёва, без PNT); (NEG) **фальсификатор:** замена простых их средней
плотностью (Δ ≡ 0) даёт форму `𝒬_mean = 𝒥 − d_A H`, строго отрицательную на растянутых тестах `g_b` (`≤ −d_A/2` при `b² ≥ 52‖g'‖²/(125 d_A)`) —
знак несёт именно арифметическая поправка `𝒮`, необходимое условие (11) `𝒮(g_b) ≥ d_A − 26‖g'‖²/(125b²)`; (REC) восстановление фиксированного
теста на диагонали `N ≥ m` перепроверено с явными бюджетами (12)–(16): скачки на концах учтены (TV ≤ (L+2)ε), архимедов член без H¹,
полюса `≤ 4m^{1/4}(|A₊|+|A₋|)ε`, простые `≤ 8‖g‖√m L^{3/2}ε`, итог `E_g ≤ C_g√m(1+L)²(L/N)² → 0`. Не доказано: (GAP-ARITH) — знак функционала
`∫k‖τg−g‖² + 2∫Δe^{−t/2}(C' − C/2) ≥ (d_A − r_j)‖g‖²`, либо (GAP-GRAM). Lean-heads: `weil_pole_difference_of_squares` (алгебра),
`weil_translation_gram_minus_shift` (8), `weil_smooth_test_diagonal_recovery` (REC). Судья зарегистрировал два предсказания на независимую
проверку: (12)–(16) без ослабления 0.80; (8) совпадает с entries CCM 0.85. Route score 4; класс PROOF_PROGRESS + FALSIFICATION.
**Мой второй канал (mpmath, замкнутая автокорреляция тригонометрического полинома, m=13, N=6, случайный комплексный вектор, против буквальной
полной матрицы `full_matrix(CCMArbBuilder)`):** (1) относительная невязка 3.8e-18; (2)(3) 3.8e-18; (9) 3.8e-18 с `𝒥 = 15.475`, `d_A H = 14.193`,
`𝒮 = 2.738`; формула (6) для `J(L)` против квадратуры 1.1107176 = 1.1107176; `b(13) = −14.97`. Все четыре тождества выдержали — на одной ячейке,
одном векторе; это FINITE_CELL-проверка алгебры, не доказательство. Предсказание судьи о (8) (0.85): в форме квадратичных форм — PASS.
**Судьбы моих предсказаний на WEILPROOF:** `P_RESULT_PARTIAL_WITH_REMAINDER` 0.80 CONFIRMED; `P_NEW_LEMMA_PROVED` 0.45 CONFIRMED ((8), (9), (NEG),
(5) — новые для проекта, новизна в литературе не заявлена); `P_PROOF_CANDIDATE_COMPLETE` 0.03 REFUTED; `P_ATTEMPT_REFUTED_WITH_COUNTEREXAMPLE`
0.15 REFUTED (контрпример — к суррогату, не к попытке). **Стена теперь:** один знак в двух точных представлениях, (GAP-ARITH) — знак
Чебышёвской поправки против энергии сдвигов; (GAP-GRAM) — нижняя frame-оценка Грама сдвигов. Впервые за фронт стена записана без
спектральных неизвестных: `Λ(n)`, `ψ`, автокорреляция теста, явные константы. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

**Скан насыщения m=43, продлён (`q3-sat43b`):** `λ₁(43,N)` = 2.062e-220 (380), 1.871e-220 (420), 1.731e-220 (460) — ещё падает ~8 % за 40 мод;
`log10 = −219.76` при N = 460. Полосы: Чжу `[−220.15, −219.85]`, R3-отчёт `[−219.75, −219.05]` (уже ниже его), Fuchs `−220.95`. Тренд идёт к полосе
Чжу; не решено до насыщения (N ≈ 600?). DIAGNOSTIC.

## 2026-09-05 (01:40) — Probe 24 (первая точка): на дне m=13 знак несёт арифметическая поправка на 61 %

(9) на единичном дне чётного блока (13,13), mpmath: `𝒥(ξ) = 0.5405`, `𝒮(ξ) = 0.8316`, `𝒥 + 𝒮 − d_A = 2.4e-20` (= `λ₁` в пределах точности float-вектора),
`d_A = 1.37218`. Доля Чебышёвской поправки `𝒮/d_A = 0.606`, доля энергии сдвигов `𝒥/d_A = 0.394`: **средняя форма `𝒥 − d_A` на дне
отрицательна (−0.83), положительность восстанавливает `𝒮`** — (NEG) судьи виден на самом минимизаторе. m = 23, 43, 83 считает юнит `q3-split`
(numpy-автокорреляция). Предсказания — addendum 25. DIAGNOSTIC.

## 2026-09-05 (02:05) — Probe 24 полностью: расклад (9) на дне не зависит от m; Чебышёвская поправка несёт 60 % на четырёх ячейках

| m | `λ₁` | `𝒥(ξ)` | `𝒮(ξ)` | `𝒥 + 𝒮 − d_A` | `𝒮/d_A` | `𝒥/d_A` |
|---|---|---|---|---|---|---|
| 13 | 7.9e-31 | 0.5405 | 0.8316 | 3.7e-12 | 0.606 | 0.394 |
| 23 | 7.3e-52 | 0.5372 | 0.8349 | 4.6e-12 | 0.609 | 0.392 |
| 43 | 1.0e-90 | 0.5415 | 0.8306 | 8.4e-12 | 0.605 | 0.395 |
| 83 | 3.2e-162 | 0.5484 | 0.8238 | 5.1e-12 | 0.600 | 0.400 |

(`d_A = 1.37218`; невязка `𝒥 + 𝒮 − d_A ≈ 1e-11` — точность float-вектора дна и численной производной `C'`, равна `λ₁` в пределах точности.)
Судьбы: `P_S_SHARE_GE_HALF` 0.55 CONFIRMED; `P_J_ALONE_BELOW_dA` 0.80 CONFIRMED (средняя форма `𝒥 − d_A` на дне = −0.83 < 0 — (NEG) судьи на самом
минимизаторе); `P_SHARES_STABLE_IN_m` 0.50 CONFIRMED (разброс 1.5 % при требуемых < 20 %).
**Странность, записана сразу:** доли не зависят от m в пределах 1.5 % при `λ₁`, меняющейся на 130 порядков. Прочтение (A): дно — одна форма (Ξ-строка
с точностью 0.5 % по OVERLAP/ONESHAPE), и `𝒥(ξ_m) → 𝒥_∞ := ∫k(t)(2 − 2C_Ξ(t))dt` — Ξ-инвариант (энергия сдвигов нормированного профиля Ξ с весом
`k = e^{−5t/2}/(1−e^{−2t})`), а `𝒮(ξ_m) → d_A − 𝒥_∞` — тогда на Ξ-строке тождество `𝒥 + 𝒮 = d_A` есть явная формула Вейля в нашем разложении
(форма на «собственной строке цели» равна нулю в пределе). Прочтение (B): совпадение в узком диапазоне m. Различит: `𝒥(y)` на точной Ξ-строке
(не на дне) при m = 43, 83 — должно дать те же 0.54. Следствие для стены: (GAP-ARITH) на Ξ-строке — равенство; стена целиком про ДРУГИЕ тесты,
где `𝒮(g)` меньше `d_A − 𝒥(g)`; вопрос судье в следующий батч: тождество `𝒥_∞(Ξ) + 𝒮_∞(Ξ) = d_A` как явная формула и структура `𝒮(g) − 𝒮(Ξ)` для
`g = Ξ·(1 + малое)`. DIAGNOSTIC_NEVER_A_PROOF.

**Различающий зонд (прочтение A):** `𝒥` на точной Ξ-строке `y` (не на дне): **`𝒥(y) = 0.570642` при m = 43 и при m = 83 — совпадение в шести
знаках**, m-независимый Ξ-инвариант `𝒥_∞ = ∫k(t)(2 − 2C_Ξ(t))dt = 0.570642`, `𝒥_∞/d_A = 0.4159`. Дно даёт 0.5405, 0.5372, 0.5415, 0.5484 — сходится
к `𝒥_∞` медленно (отклонение первого порядка по `d₂ ≈ 5T_m` — одна форма). Значит на Ξ-строке `𝒮(y) = d_A − 𝒥_∞ + R(y) ≈ 0.801538` (энергия Ξ-строки
`R(y)` ничтожна: 1e-20..1e-78). Прочтение A подтверждено: тождество `𝒥_∞ + 𝒮_∞ = d_A` на профиле Ξ — явная формула Вейля в разложении (9):
Чебышёвская поправка автокорреляции Ξ равна `d_A − 𝒥_∞` в пределе. Два явных числа для батча: `𝒥_∞(Ξ) = 0.570642`, `𝒮_∞(Ξ) = 0.801538`.
Вопрос судье: (i) доказать `𝒥_∞(Ξ) + 𝒮_∞(Ξ) = d_A` из явной формулы (это должно быть тождество, не оценка); (ii) для `g = Ξ·(1 + ε)` разложить
`𝒮(g) − 𝒮(Ξ)` и `𝒥(g) − 𝒥(Ξ)` до второго порядка — (GAP-ARITH) в окрестности Ξ есть знак квадратичной формы второго порядка, и её можно
записать явно. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (02:20) — континуальная проверка: `𝒥_∞(Ξ) + 𝒮_∞(Ξ) = d_A` выполняется на 5e-11; поправка Чебышёва на Ξ несётся простыми ≤ 59

Профиль Ξ-строки в пределе: автокорреляция `C_∞(t) = ∫Ξ(x)²cos(xt)dx / ∫Ξ²` (преобразование Фурье `Ξ²`). Континуум (mpmath, сетка 0..60 шаг 1/8):
`𝒥_∞ = ∫k(t)(2 − 2C_∞)dt = 0.5706416` (решётка при m = 43, 83: 0.570642 — совпадение в 6 знаках);
`𝒮_∞ = 2∫₀^T Δ(t)e^{−t/2}(C_∞' − C_∞/2)dt = 0.801542` при `T = log 3000`, причём голова до `log 59` даёт 0.801542, хвост от 59 до 3000 — `−1.0e-22`;
`𝒥_∞ + 𝒮_∞ − d_A = −5.5e-11`. **Прочтение A доказано численно в континууме:** тождество `𝒥_∞ + 𝒮_∞ = d_A` есть явная формула Вейля на
каноническом тесте `f` с `f̂ ∝ Ξ` (форма Вейля равна сумме `|f̂(ρ)|²`-типа по нулям, а `Ξ` на нулях обращается в нуль — безусловно, без RH).
Два следствия для стены. (1) В координатах (9) стена (GAP-ARITH) на Ξ — точное равенство; открытое неравенство — про отклонения от Ξ:
`g = Ξ·(1 + ε)`, второй порядок по ε — знак квадратичной формы, которая и есть матрица Вейля в базисе отклонений. (2) Чебышёвская поправка на
Ξ определяется простыми до 59 с точностью 1e-22: `C_∞(t)` спадает сверхэкспоненциально (Фурье-образ `Ξ²`), поэтому вклад `Δ(t)` при `t > 4`
исчезает. Это объясняет, почему CCM-матрица «видит» так мало простых, и почему дно принимает форму Ξ. Кандидат в PUBLICATION_PLAN.
DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-05 (02:40) — Lean: `WeilGramMinusShift.lean` KERNEL_GREEN (две LEAN-READY головы вердикта WEILPROOF), одиннадцатый файл фронта

Opus-агент (14 мин), проверено мной: `lake env lean` EXIT 0 без вывода, `q3_check ok`, все 25 теорем на `[propext, Classical.choice, Quot.sound]`,
`sorry/admit/exact?` = 0. Содержание (пространство имён `Q3.RouteB`, над ℂ, `Matrix.PosSemidef`): `weil_pole_difference_of_squares`
(`2Re(A·B̄) = 2|(A+B)/2|² − 2|(A−B)/2|²`, с прочтением через `C_L, S_L`); `weil_translation_gram_minus_shift` для `K := Γ − c_L·1 − 2ββ*`, `Γ ⪰ 0`:
(a) квадратичная форма, (b) `K + c_L·1 + 2ββ* ⪰ 0`, (c) `λ_min(K) ≥ −(c_L + 2‖β‖²)` через доказанный дискретный Коши–Шварц, (d) плант
`Γ = diag(0,2), c_L = 1, β = 0 ⇒ K = diag(−1,1)`, не PSD (свидетель `![1,0]`), (e) `K ⪰ 0 ↔ (GAP-GRAM)` (переформулировка открытого вопроса в Lean,
не сужение), (f) PSD Грама `⟪v_j, v_k⟫` (в Mathlib нет `gramMatrix` — доказано), PSD неотрицательной конечной суммы, `weilGamma_posSemidef`.
Не заявлено: `K ⪰ 0`; интегральная `Γ` (только конечная взвешенная сумма); кроссволк к буквальным entries CCM — предсказание судьи о (8) остаётся
PENDING как Lean-факт (численно PASS у меня). Невакуумность `PosSemidef` над ℂ закреплена плантом с обеих сторон. Второй канал агента: numpy,
9 проверок, 400 экземпляров. Отчёт: `docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-05_GOAL058_WEIL_GRAM_MINUS_SHIFT.md`.

## 2026-09-05 (утро) — широкие ячейки m=43: кэши (43,320) и (43,344) готовы (MAX_DEGREE 900, 6.7 ч каждый); `p` измеримо, `ε` — нет

Probe 22 на (43,320):

| N | λ₁ | λ₂ | R(q) | ε | p | δ | T | δ/T |
|---|---|---|---|---|---|---|---|---|
| 260 | 5.848e-216 | 1.788e-206 | 2.283e-182 | 3.9e33 | 2.21e-8 | +1.05e-5 | 1.375e-3 | +0.0076 |
| 300 | 1.057e-219 | 5.308e-210 | 2.283e-182 | 2.2e37 | 1.04e-10 | +7.2e-7 | 1.192e-3 | +0.0006 |
| 320 | 3.741e-220 | 2.185e-210 | 2.283e-182 | 6.1e37 | 7.05e-12 | −1.9e-7 | 1.117e-3 | −0.0002 |

**Диагноз пола (записан сразу):** `R(q_N) = 2.283e-182` на всех трёх N до четырёх знаков — плато кэша, не энергия трала: усечение Лежандра при
`MAX_DEGREE = 900` даёт относительную ошибку коэффициентов ~1e-91 (в квадрате 1e-182), хотя хвост `|c_n|` спадает честно до 1e-113. Для `ε_∞(43)`
нужна относительная точность ≲ 1e-115: `MAX_DEGREE ≳ 1200`, dps ≥ 400, ~сутки счёта. **Направление измеримо и ведёт себя как на m = 13, 23:**
`p` = 2.2e-8 → 1.0e-10 → 7.1e-12 (N = 260 → 320), `δ/T → 0` (−0.0002 при N = 320): дно ≡ трал на третьем m. Оценка C3 `(R−λ₁)/(λ₂−λ₁)` полом
испорчена (1e24..1e28) — не сравнивать. Предсказание живого чата `P_WIDE43_PROJECTIVE_ERROR_LE_1E_7` 0.67 — на предзаявленной ячейке (43,344)
(юнит `q3-p22-43p`); на (43,320) уже `7e-12 ≤ 1e-7`. Правило для генератора (backlog): `MAX_DEGREE` подбирать по требуемой относительной точности
`≈ √λ₁(m,∞)`, не по спаду хвоста. DIAGNOSTIC.

**Предзаявленная ячейка (43,344) = 8m (`q3-p22-43p`, 706 с):** `λ₁ = 2.464e-220`, `λ₂ = 1.504e-210`, `p = 5.31e-11`, `δ = −5.1e-7`, `δ/T = −0.0005`; `R(q)` —
то же плато 2.283e-182 (пол). **Судьба `P_WIDE43_PROJECTIVE_ERROR_LE_1E_7` 0.67 (живой чат): CONFIRMED** (`5.3e-11 ≤ 1e-7`, FINITE_CELL). Заметка:
`p(344) = 5.3e-11 > p(320) = 7.1e-12` — как на (13,120) против (13,60) и (23,160) против (23,145): после насыщения `p` слегка растёт с N (усечённый
трал точнее полного на конечном окне? — странность, записана; прочтения: (A) хвост трала за насыщением несёт малую массу вне дна конечного окна,
(B) численный эффект точности на 1e-11). `λ₁(43,344) = 2.46e-220` ≈ скан 2.62e-220 при N=340 (разные dps) — согласуется. DIAGNOSTIC.

## 2026-09-05 (утро) — второй проход WEILPROOF из нового чата (`8e4f2329`, отдельный файл): арифметические пакеты — положительность доказана, кофинальный подъём опровергнут

**Судья (GPT-6 Astra, продолжение по прямому слову владельца, файл `PROSHKA_VERDICT_WEILPROOF_CONTINUATION_ARITHMETIC_PACKETS_AND_DENSITY_2026-09-05.md`,
593 строки; первый вердикт не перезаписан).** RESULT снова PARTIAL. Новое (PAPER): (S-NEG) `𝒮(g) ≤ −log2/(2√2)` на явном тесте из двух бампов на
расстоянии `log 2` — арифметическая поправка НЕ неотрицательна сама по себе (убит механизм «`𝒮 ≥ 0` отдельно»; остаётся совместное `𝒥 + 𝒮 ≥ d_A`).
(DIV) **точная сумма квадратов фон Мангольдта:** `Σ_n a_n^{(M)}|c_n|² − P_M(c) = Σ_{nd≤M} Λ(d)|c_{nd} − c_n/√d|² ≥ 0`, `a_n = log n + B(M/n)`,
`B(y) = Σ_{d≤y}Λ(d)/d` — только делимость и `Σ_{d|j}Λ(d) = log j`. (B) `B(y) ≤ log y + 4 log 2` элементарно (биномиальные коэффициенты, без PNT).
(PRIME) `P_M(c) ≤ (log M + 4 log 2)‖c‖²`. (MATCH) логарифмические пакеты: `φ_n(x) = η_M(x − log n + ½log M)`, `ε_M = 1/(16M⁴)` — носители не
пересекаются, prime-вклад формы на `V_M` равен ровно `P_M(c)`. **(PACKET-POS): `𝒬(g_c) ≥ ½‖g_c‖²` для всех `M ≥ 128` и всех комплексных `c`** — безусловная
положительность полной формы Вейля на явных M-мерных пространствах (`µ_M = 2 log M − c_A − 3 log 2 − …`), с сохранением полюсов, всех простых и
комплексных коэффициентов. **(REC-FAIL) — сильнейшая атака самого судьи:** эти пространства НЕ восстанавливают фиксированные тесты:
`dist(g, V_M) → ‖g‖` (мера носителей `≤ 1/(8M³)`), и (CLASS) закрывает весь класс пакетов радиуса `O(1/M)` с двусторонним исчерпанием окна.
§8: точное тождество для перекрывающихся пакетов (Gram `G`, остаток `E`) — знак не доказан; (OPEN-OVERLAP) — следующий бумажный вопрос.
Предсказания судьи на review: (DIV)+(MATCH) 0.97; (PACKET-POS) 0.88; (REC-FAIL)+(CLASS) 0.98. Lean-heads: `mangoldt_divisibility_energy_identity`,
`weil_log_integer_packet_lower_bound`, `narrow_log_integer_packets_no_cofinal_recovery`, `weil_arithmetic_remainder_has_negative_smooth_direction`.
**Мой второй канал:** (DIV) на случайных комплексных `c`, `M = 50, 200, 400` — относительная невязка 1e-16; (B) на `N ≤ 20000` — максимум
`B(N) − log N − 4 log 2 = −3.12` (запас; при N = 20000 разность `−0.58`). (PACKET-POS) и (S-NEG) численно не проверял (нужна реализация
формы на бампах; их доказательства элементарны и прочитаны). **Что это меняет.** Появился первый доказанный класс тестов с безусловной
положительностью формы Вейля вне классического диапазона — но класс «арифметически развязан» узостью пакетов и потому не плотен; цена
развязки — провал восстановления. Стена сдвинулась к (OPEN-OVERLAP): совместная знаковая оценка на геометрии, восстанавливающей тесты.
Это согласуется с XIDEV L4 (конечная редукция по простым при фиксированной гладкости): пакеты — крайний случай «гладкость = δ-узость».
DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-05 (утро) — полка: ранний Q3 уже делал арифметические сертификаты; «ошибка конуса» и Prime-препятствие = сегодняшние (S-NEG) и конус свёрточных квадратов

Владелец: «в первых версиях Q3 мы это делали: пакеты арифметики, сертификаты, считали на узлах днями; при формализации упёрлись в сертификаты, по конусу
не сходилось». Проверено по полке (`ask.sh`, `docs/GENEALOGY.md`, `ACTIVE/PSD_STEP33_MONITOR.md`, `ACTIVE/FAILED_STRATEGIES.yaml`, `docs/trackB/*`):
(1) **A-линия (2026-01-29)**: 25 Lean-файлов, T0/A1′/A2/A3/D3 — «локальная плотность на вспомогательном конусе», prime cap, сокращение простых.
(2) **Ошибка конуса (публикация 2026-03-10)** дословно: «the RH endgame must run through the positive-definite / convolution-square Weil cone, not
through the broad cone of all even nonnegative compactly supported tests» — проверяли положительность не на том конусе. Ровно это судья
зафиксировал в WEILPROOF §2 («конус тестов — свёрточные квадраты `f* * f`, не заменять всеми чётными функциями»). Кто и как нашёл — в
генеалогии не записано. (3) **Prime-препятствие (та же публикация):** `W_K(u) = â*_K(u) − Σ(2Λ(n)/√n)cos(uξ_n) ≥ 0` недостижимо в принципе —
Риман–Лебег против конечной суммы косинусов; «цель недостижима, не точность и не машины». Это тот же факт, что (S-NEG) и (NEG) судьи:
арифметическая часть отдельно не может быть неотрицательной; знак только в связке с архимедовой энергией. (4) **PSD-pd линия (2026-05-01,
1018 файлов, `Step33`)** — конечные сертификаты в `Matrix ι ι Rat` (`PSD_PenaltyCertificate.lean`), заморожена 25.06: не математическая стена, а
отсутствие сгенерированного потока `complete_collapsed_expression_coeff_stream`; блокеры монитора: «C1/C2 recert routes are blocked by
negative C on ker(Q)» (`:5564`: primary `−A−P` на `ker Q` — 13 отрицательных собственных значений; `A−P` на `ker Q` — min `+1.9e-4`, 0 отрицательных).
(5) **Track B E5p / LP-переформулировка (Cohn–Elkies dual witness, ATLAS_07)**: конус `C_K` пакетов эрмитовых квадратов с условиями `ker Q`, матрица
краевого дефекта `D_K = arch − zero_PSD + boundary − prime_edge`, цель `µ_K·G_K − E_edge,K ≥ 0` на `ker(Q_K)`; статус `GAP_EXACTLY_NAMED_IN_PROGRESS`
(`SAME_UNIT_ANALYTIC_MU_BRIDGE`), интервальный сертификат для `µ = (0.45, 0.51, 0.75)` на `K = 2, 3, 3.5`; dual witness не решён.
**Вывод для сегодняшнего фронта.** Старая линия и линия судьи — один объект: положительность на конусе свёрточных квадратов, где арифметика
одна не даёт знака, а конечный сертификат упирается в знак на ядре/пересечении. Новое сегодня: точный совместный леджер (9)/(DIV) (старая линия
оценивала три вклада порознь — судья в (5) показал, что так `b(L) → −∞`), доказанный конечный класс (PACKET-POS) и доказанный провал его
плотности. Что взять со старой полки: (a) LP/dual-witness как класс K8 для (OPEN-OVERLAP)/(GAP-GRAM) — дуальный сертификат положительности на
конусе пакетов (Cohn–Elkies), (b) интервальные PSD-сертификаты Track B на малых K как образец «finite certificate principle», (c) пилот
`Step33` как машину для конечных сертификатов, если судья выпишет конечную матрицу. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (утро) — Lean: `MangoldtDivisibilityEnergy.lean` KERNEL_GREEN (тождество (DIV) второго прохода), двенадцатый файл фронта

Opus-агент (16 мин), проверено мной: `lake env lean` EXIT 0 без вывода, `q3_check ok`, все 26 теорем/лемм на `[propext, Classical.choice, Quot.sound]`
(пространство имён `Q3.RouteB.MangoldtDivisibilityEnergy`), `sorry/admit/exact?/axiom` = 0. `mangoldt_divisibility_energy_identity` для ЛЮБОГО `M`
(гипотеза `M ≥ 2` не нужна) и любого `c : ℕ → ℂ`: `Σ_{n≤M} diagWeight M n·‖c n‖² − primeForm M c = energy M c ≥ 0`; плант `M = 2, c = (1, 1/√2)`:
энергия 0, `primeForm = log 2`, с удвоенным ребром `−log 2 < 0`. Сверх задания — цепочка §4 через Mathlib `Chebyshev.psi_le_const_mul_self`:
`B(N) ≤ log N + (log 4 + 4)` (константа 5.386 вместо `4 log 2 = 2.773` у судьи — его биномиальный ход ψ ≤ 4N log 2 в Mathlib отсутствует; шаг Лежандра
`Σ log j = Σ Λ(d)⌊N/d⌋` доказан в файле) и `primeForm M c ≤ (log M + log 4 + 4)‖c‖²`. Второй канал агента: numpy 1.4e-15; скан `N ≤ 3000` совместим с
`4 log 2`. Отчёт: `docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-05_GOAL058_MANGOLDT_DIVISIBILITY_ENERGY.md`.

## 2026-09-05 (день) — вердикт XIDEV (`2aa9dfc9`, blob `136aceb3`): PARTIAL; L1, L2, L4 доказаны (PAPER); L3 даёт точное знаковое представление (GS); остаток = (DOM)/(FM)

**Судья (GPT-6 Astra, 796 строк).** Класс `TRY_XIDEV_SIGNED_CANONICAL_ENERGY_AND_FINITE_PRIME_CERTIFICATES`.
L1 (доказано, PAPER): канонический тест `Φ(x) = 4E(h)(e^x)`, `h(u) = (π²u⁴ − (3/2)πu²)e^{−πu²}`, `E(h)(u) = √u Σ h(nu)`; **починка масштаба CCM (7.1): Mellin
печатного `E(h)` равен `ξ/4`, поэтому `FΦ = Ξ`**; `f₀ = Φ/‖Φ‖`, `Ff₀ = Ξ/A`; `Φ` чётна (Пуассон, `ĥ = h`, `h(0) = ∫h = 0`), строго положительна, спадает
как `e^{−(π/2)e^{2|x|}}` со всеми производными (явные константы (ENV)); (NULL) `Q(f₀) = 0` из явной формулы ([W] §2.1.1, класс Вейля допускает `f₀`
по (ENV)); (CAN-EQ) `𝒥(f₀) + 𝒮(f₀) = d_A` как явные сходящиеся интегралы, `C_{f₀}(t) = ∫Ξ²cos(yt)/∫Ξ²` по Парсевалю — моё прочтение подтверждено.
L1c: восстановление некомпактного `f₀` конечными Фурье-проекциями на диагонали `N = m` — отдельная лемма с бюджетом (компактное (REC) к `f₀`
напрямую неприменимо). **L2 (доказано): `f₀` — радикальный вектор: `B(f₀,v) = 0 ∀v ∈ X`, `Q(f₀ + αv) = |α|²Q(v)`** — сильнее нулевого значения
(контроль: `Q = |x₁|² − |x₂|²`, вектор (1,1) имеет нулевое значение, но ненулевое спаривание). Гессиан на отклонениях = сама форма Вейля.
**L3 (GS, доказано): «преобразование основного состояния» через положительный радикальный вектор:** для `r ∈ ℂ + C_c^∞`, `v = f₀r`,
`Q(f₀r) = ∫₀^∞ b(t)E_r(t)dt + Σ w_n E_r(log n)`, `E_r(t) = ∫f₀(x)f₀(x+t)|r(x+t) − r(x)|²dx ≥ 0`, `b(t) = k(t) − e^{t/2}` ЗНАКОВАЯ; нулей в правой части нет.
(NEG-MEASURE): на `I = [log 7/5, log 8/5]` (без простых степеней) `ν(I) ≤ −(43/168)log(8/7) < 0` — представляющая мера не положительна; открытое
неравенство (DOM): `Σw_nE_r(log n) + ∫b₊E_r ≥ ∫b₋E_r` для всех `r`. Плант: `Q* = diag(0,−1,1) = J* − d*I + S*` с PSD `J*, S*` и радикальным `e₁`, но
`Q*(e₂) = −1` — радикал ≠ минимум. **L4 (доказано):** плотный класс `𝓔_a` (суперэкспоненциальная огибающая с зависящими от `g` константами);
**поправка ко мне: «`Ξ²` конечного экспоненциального типа» — ЛОЖНО** (`log|Ξ(i(s−½))²| ≥ s log s − O(s)`); (CORR) `|C_g' − C_g/2| ≤ M_g e^{−t/2}e^{−2ae^t}`;
(SP) конечная знаковая сумма по простым с граничным членом `2Δ(T)P^{−1/2}C_g(T)` (не выбрасывать!), (TAIL-S) явный хвост `(M_g/a)(1+log P)P⁻¹e^{−2aP}`,
(TAIL-J), (CERT) двусторонний сертификат, (PCUT) явный cutoff `P(g,ε)`. **L5:** первое оставшееся неравенство (FM) — конечная маржа для всех
единичных `v ⊥ f₀` из `𝓔₁` при `P ≥ P(v,ε)`; условная лемма сборки: (FM) ⇒ W ⇒ RH через опубликованный критерий. Lean-граница: Mathlib имеет
Пуассона (`Real.tsum_eq_tsum_fourierIntegral`), Schwartz-Фурье, `completedRiemannZeta₀`; безопасное `ξ(s) = (1 + s(s−1)·completedRiemannZeta₀(s))/2`;
явная формула — PAPER-импорт, не аксиома. Судьбы: L1 0.75 CONFIRMED; L2 0.60 CONFIRMED; L3 0.20 NOT REALIZED (представление есть, знак нет);
L4 0.35 CONFIRMED; COMPLETE 0.03 REFUTED; PARTIAL 0.85 CONFIRMED; REFUTED 0.12 REFUTED. Четыре предсказания судьи на независимую проверку
(0.88/0.84/0.78/0.88) — агент-аудитор запущен. Route score 4; класс REPRESENTATION_PROGRESS.
**Мой второй канал.** (a) `d_A = γ + log 8π + π/2 − 4 = 1.372183419` — **в моих записях 04–05.09 стояло 1.372178: неверные цифры** (округление
неверно перенесено); замечание судьи о десятичных верно; полноточностный остаток −5.5e-11 был честным, печать — нет. (b) **Масштаб 4
подтверждён:** `∫4E(h)(e^x)e^{−izx}dx = Ξ(z)` при `z = 0, 1, 3` на 8 знаков (0.49712078, 0.48575743, 0.40316521). Ловушка инструмента: прямая сумма
`Σh(nu)` при малых `u` даёт мусор (первый прогон: −1.397 вместо 0.497); нужна чётность `E(h)(u) = E(h)(1/u)`. (c) (NEG-MEASURE): `∫_I b = −0.0739 ≤
−0.0342` — держится. (d) **(GS) подтверждена численно:** на сетке `dx = 0.0025` оценщик формы имеет смещение `−5.67e-4·H` (видно на `Q(f₀)`);
после его вычитания для трёх тестов `r` (с O(1) вариацией) `Q(f₀r)` и правая часть (GS) совпадают: 2.9e-4 / 2.4e-4, 9.96e-3 / 9.91e-3, 3.2e-3 / 3.1e-3
(4–15 %, уровень сетки); все три положительны. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-05 (день) — статья владельца 2025 («Operator Methods for the Weil Criterion: Q3», Zenodo 17527099): карточка и кроссволк агента

Агент (Opus, 22 мин; PAPER + NUMERIC двумя каналами квадратур): `docs/routeB_bus/AGENT_REPORT_2026-09-05_GOAL058_Q3_2025_PAPER_CROSSWALK.md`,
карточка `docs/routeB_bus/litreview/MALAMUTMANN2025_Q3_USAGE_CARD.md`. (1) Конус `W_K = C⁺_even([−K,K])` — Definition 12.1, Theorem 13.1(ii),
Theorem 13.4; **опровергнут собственным генератором статьи**: атом Theorem 6.2 на узле `ξ₂` даёт `Q = −1.55` при `t = 1e-4` и `−2707` при `1e-8`.
(2) Словарь: `L = 2πK` (`|ξ_n| ≤ K ⟺ n ≤ e^{2πK}`). (3) **T0 (нормализация) мёртв** (находка агента, крупнее A3): дигамма-плотность спарена не с той осью
и с обратным знаком; на трёх `s` до 8 знаков архимедов член судьи совпадает с `(1/2π)∫ĥ·[Re ψ − log π]`, а не с формой статьи (−3.4840 против +8.9514).
(4) Prime bound: узлы `ξ_n = log n/2π` и веса `Λ(n)/√n` совпадают с (DIV)/(PRIME) точно, но честный след в RKHS равен `2A_L = 86.93` при `K = 1`, а не
`ρ(1) = 0.0272`; гауссов демпфер Prop. 9.30 не выведен, при масштабе узлов статьи `ρ(1) = 1.2484 > 1`; снизу `‖T_P‖ ≥ w_max = log 7/√7 = 0.7355`
против потолка `c₀/4 ≈ 1/25` — нарушение в 18 раз. (5) A3 vs `𝒥`: `c₀(K)` — барьер, не долг `d_A`; аналогов `𝒥`, `𝒟`, полюса, `𝒮` в статье нет; пол символа
положителен (0.94–0.98), но насыщается на 1.40, роста `log(1+K)` нет; Theorem 8.16 из своих лемм даёт −135.38, не +0.1878. (6) Смешанная
оценка (Lemma 12.5 / Thm 12.6 / Thm 8.26) = независимые оценки трёх вкладов с развязанными шкалами `t_sym/t_rkhs`, что ломает тождество Рэлея
(Lemma 8.2); при `K = 1` `b(L) = −108.94`, простой вклад 86.93 против 0.04 (×2173). (7) Верификация статьи: 19 прогонов Vampire (410 мс суммарно),
один скрипт Z3 на тавтологию; Lean в статье нет; «no numerical tables» повторено ≥ 12 раз при `c₀(K)` из JSON во введении. (8) **Переиспользуемо:
словарь Фейер×тепло НЕ попадает в убитый класс (REC-FAIL)/(CLASS)** — равномерная сетка центров, фиксированная ширина, перекрывающиеся носители,
полное покрытие; A1′+A2 дают половину (OPEN-OVERLAP) — восстановление фиксированных тестов в `L²` и по `Q`; знака не дают; `G ≠ I`, (ARCH) больше
не поставляется, леджер `ℰ_{M,η}` считать заново. Не сделано: supplements Zenodo, мартовский `full/RH_Q3.pdf`, §10 MD₂,₃.
**Мои проверки:** `w_max = log 7/√7 = 0.7355` ✓; `2A_L` при `K = 1` (`e^{2π} ≈ 535`) — см. вывод выше ✓ порядок. Пункт (3) о T0 мной не проверен.
**Вывод.** Статья 2025 совпадает с сегодняшней линией по объектам (узлы, веса, конус после починки) и расходится по константам: её замыкание —
раздельные оценки, которые судья и ревизия марта 2026 признали недостижимыми. Что берём: словарь Фейер×тепло как плотную перекрывающуюся
геометрию для (OPEN-OVERLAP) — кандидат в следующий батч вместе с (DOM)/(FM). DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (день) — независимый аудит XIDEV (агент, из источников, без вывода судьи как посылки): все четыре предсказания судьи SURVIVE

`docs/routeB_bus/AGENT_REPORT_2026-09-05_GOAL058_XIDEV_INDEPENDENT_AUDIT.md`. (1) Масштаб и радикал (0.88): Mellin печатного `E(h)` = `ξ(s+½)/4` независимо;
`FΦ = Ξ` на 14 знаках в четырёх точках; (EF) пересобрана из CCM (3.10)–(3.11) и совпадает с [W] (1.1); множитель 4 — дефект печатной Lemma 7.1 у CCM;
бонус: `Q(f₀) = 2.1e-14` прямой геометрической формой. (2) (GS) и (NEG-MEASURE) (0.84): обе поляризации точны (sympy, остаток 0); (GS) выведена
независимо из (Q)+(RAD); численно `Q(v)` по (Q) и по (GS) на комплексном `r` сходятся на 1.5e-14 (мой канал на сетке дал 4–15 % после снятия
смещения — агент точнее); `∫_I b = −0.0739 ≤ −0.0342`, `1.4³ − 1.4 = 168/125` ровно. (3) Бюджет L1c (0.78): все константы пересчитаны, острые оценки
ниже печатных, `35/3 = 1 + 32/3` по членам, (ENV) с `A₀ = 23.91`, `A₁ = 325.4` проверена; не разобраны две оговорки судьи (кроссволк литеральных мод к
`Fin (2N+1)` у [F]; отсутствие утверждений о позитивности конечных матриц). (4) (SP)/(TAIL-S) (0.88): (SP) — точное тождество (`P = 2, 3`: 1e-14 с
граничным членом); ловушка: при `P ≤ 3` выброс граничного члена случайно уменьшает видимую ошибку. `d_A = 1.3721834192256656`; печатное 1.372178
— ошибка на +5.4e-6 (моя); `𝒥(f₀) = 0.5706415615`, `𝒮(f₀) = 0.8015418578` — мои печатные округления верны, сумма согласуется с `d_A` в ±5e-7 печатной
точности; остаток −5.5e-11 не подтверждён и не опровергнут (у агента +2e-14 при ошибке квадратуры ~1e-13). Судьбы предсказаний судьи: все четыре
CONFIRMED (второй канал: агент, PAPER + NUMERIC + sympy). DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (день) — Probe 25: словарь Фейер×тепло на буквальной матрице CCM — запас положительности умирает вместе с плотностью

Владелец: «делай». Скрипт `docs/routeB_bus/phase5_codex/overlap_dictionary.py` (атомы Thm 6.2 статьи 2025 в лог-переменной: шапка `Λ_B`·гауссиан
`ρ_t`, центры на равномерной сетке шага `Δ`, `B = 4√(2t)`; коэффициенты в базисе мод CCM; сжатие `λ_min(VᵀKV, VᵀV)` на буквальной полной матрице
`K_{13,13}` (27 мод); расстояния Ξ-строки `y` и гауссова теста до span V; double).

| Δ | t | M | λ_min(V) | dist(y,V) | dist(gauss,V) |
|---|---|---|---|---|---|
| L/6 | 0.002 | 6 | +1.17e-1 | 0.78 | 0.75 |
| L/6 | 0.02 | 6 | +7.8e-4 | 0.32 | 0.18 |
| L/10 | 0.005 | 10 | +3.3e-3 | 0.23 | 0.20 |
| L/10 | 0.02 | 10 | +1.1e-4 | 3.3e-2 | 2.2e-2 |
| L/16 | 0.005 | 16 | +1.6e-11 | 1.3e-2 | 4.5e-3 |
| L/24 | 0.02 | 24 | −3.9e-16 (0 в double) | 6.6e-7 | 7.6e-9 |
| L/40 | любое | 40 | G сингулярна (M > 27 мод) | 1e-15 | 1e-15 |

**Закон, который видно сразу и который тривиально доказывается:** для любого подпространства `V` `λ_min(K|V) ≤ R(P_V y)/‖P_V y‖² ≤ R(y) + 2‖K‖·d + ‖K‖d²`,
`d = dist(y, V)`, а `R(y)` (энергия Ξ-строки) = 8e-21 при m = 13 (1e-20..1e-78 на ячейках). **Плотность убивает запас по определению:** любой словарь,
приближающий Ξ-строку (или дно) на `d`, имеет запас `≲ 2‖K‖d`. Измерено: `d = 0.78 → 0.12`; `0.23 → 3e-3`; `3e-2 → 1e-4`; `1.3e-2 → 2e-11`; `7e-7 → 0`.
Судьбы: `P_NO_OVERLAP_REGIME` 0.60 CONFIRMED (нет `(Δ,t)` с `λ_min ≥ 1e-2` и `d ≤ 1e-2`); `P_MARGIN_DECAYS_WITH_WIDTH` 0.85 CONFIRMED (монотонно при
`Δ = L/6, L/10`; при `L/16` шум 1e-11); `P_NARROW_MARGIN_ORDER_ONE` 0.70 REFUTED как сказано (0.1 только при `t = 0.002`; при `t = 0.005` уже 0.014).
**Следствия.** (1) (OPEN-OVERLAP) в форме «плотная геометрия с равномерным запасом `≥ c > 0`» мертва как форма теоремы — не константами, а
неравенством выше: запас плотного семейства не превосходит `R(y) + O(d)`, а `R(y) → 0` сверхэкспоненциально. Живая форма только с нулевым
запасом: `λ_min(K|V) ≥ −o(1)`, т.е. (DOM)/(FM), т.е. знак на масштабе `λ₁`. (2) То же неравенство в одну строку опровергает замыкание статьи
2025 независимо от констант: «плотный конус Фейер×тепло» и «`λ_min ≥ ½c₀* > 0` равномерно» несовместимы, потому что плотный конус содержит
приближения Ξ-строки. (3) Для батча: не просить «знак с запасом на словаре»; просить (DOM) на взвешенных разностях и (FM) с cutoff, где
запас равен нулю по построению. m = 23, 43 считаются юнитами для той же таблицы (мод 47 и 87). DIAGNOSTIC_NEVER_A_PROOF.

**Probe 25, m = 23 и 43 (47 и 87 мод):** тот же закон. m=23: `(λ_min, dist(y,V))` = (7.6e-2, 0.86), (4.3e-2, 0.64), (1.5e-4, 9.7e-2), (1.6e-5, 1.3e-2), (1.3e-11, 3.9e-3),
(0, 1e-9). m=43: (8.4e-2, 0.93), (1.4e-2, 0.72), (1.3e-4, 0.21), (3.4e-5, 2.3e-2), (5.3e-6, 7.7e-3), (1.1e-8, 2.5e-3). На всех трёх m и всех 90 конфигурациях
**ни одного отрицательного `λ_min` вне double-нуля (−2e-15)**: конечная форма на словарях неотрицательна в пределах точности, а запас
падает вместе с расстоянием — `λ_min ≲ O(dist)`. Это численное содержание (FM) при нулевом запасе и одновременно смерть «запаса `≥ c`».

## 2026-09-05 (вечер, судья над DOMFM) — Probe 26: ядро (GS) — знаковый графовый лапласиан; знак `b` меняется в пластическом числе; символ на плоских волнах = сумма по нулям на 1e-13

**Форма ядра (моё, из (GS) раскрытием `|s(x+t) − s(x)|²`):** `D(s) = Q(f₀s) = ½∬ f₀(x)f₀(x′)ν(|x−x′|)|s(x) − s(x′)|² dx dx′`, `dν = b(t)dt + Σw_nδ_{log n}` —
графовый лапласиан со ЗНАКОВЫМ весом `f₀(x)f₀(x′)ν(|x−x′|)`. Непрерывная плотность `b(t) = √u(1/(u³−u) − 1)`, `u = e^t`: **`b > 0` ⇔ `u³ − u < 1` ⇔ `u < ρ = 1.324718`
(пластическое число, корень `u³ = u + 1`), `t₀ = log ρ = 0.28120`** (проверено: `b(t₀) = 2e-21`). Все атомы простых (`u = n ≥ 2`) сидят в отрицательной зоне
плотности. (DOM) в этих координатах: положительная короткодействующая часть (`|x−x′| < 0.281`) плюс атомы простых должны доминировать
отрицательную дальнодействующую непрерывную часть — для всех `s`.
**Символ на плоских волнах** `s = e^{iξx}`: `σ(ξ) = D(e^{iξx}) = ∫2(1 − cos ξt)C₀(t)dν(t)` (геометрическая сторона, `C₀` — автокорреляция `f₀` = Фурье-образ `Ξ²/∫Ξ²`)
против нулевой стороны `σ(ξ) = Σ_γ Ξ(γ−ξ)²/A²` (так как `F(f₀e^{iξx}) = Ξ(·−ξ)/A`; `A² = ∫Ξ²/2π`; 119 нулей до `γ ≈ 280`):

| ξ | σ (геометрия, лапласиан) | σ (нули) | отн. расхождение |
|---|---|---|---|
| 0.5 | 3.4485215e-6 | 3.4485215e-6 | 9e-13 |
| 2 | 1.9087739e-4 | 1.9087739e-4 | 2e-14 |
| 5 | 1.1653898e-2 | 1.1653898e-2 | 3e-16 |
| 10 | 0.34798825 | 0.34798825 | 8e-18 |
| 14.13 | 0.85250175 | 0.85250175 | 3e-18 |
| 20 | 1.1255521 | 1.1255521 | 2e-18 |

Явная формула на модулированных канонических тестах выполняется на 1e-13..1e-18 — второй канал на (GS) и на всю конструкцию `f₀`, теперь с
нулевой стороной. `σ(ξ) ≥ 0` и растёт с `ξ` (нет провала у `γ₁`). Судьбы: `P_SIGMA_NONNEG_ON_GRID` 0.95 CONFIRMED; `P_TWO_SIDES_AGREE_1E-6` 0.80 CONFIRMED
(на 7+ порядков лучше); `P_SIGMA_MIN_NEAR_GAMMA1` 0.5 REFUTED (монотонный рост). **Что это даёт стене.** Плоские волны — направления, где знак
известен из нулевой стороны при RH (сумма квадратов); геометрическая сторона даёт тот же знак без RH только через явную формулу. Открытое (DOM)
= положительность знакового лапласиана на всех `s`, не только на `e^{iξx}`. Кандидат-лемма для батча (уже у судьи): «символ» `σ(ξ) ≥ 0` ⟺ … нет:
модуляции не исчерпывают, но дают необходимое условие и точный тест каждой формулы. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-05 (вечер) — вердикт DOMFM (`002ad66e`, blob `d1a8c909`): PARTIAL; D1 доказана острее с стражами; абсолютный Шур убит для ВСЕХ положительных весов

**Судья (GPT-6 Astra, 686 строк).** Класс `TRY_DOMFM_ZERO_MARGIN_COUPLED_CERTIFICATES`. **D1.** (TRADE) `λ_min(K|V) ≤ R_K(p) ≤ R_K(y) + 2Md` (без `d²`; страж:
проекция `p ≠ 0`; `M` = операторная норма); (EIG-TRADE): для собственного `y` ошибка квадратична `(M+|λ|)d²/(1−d²)`; (FORM-TRADE)/(MARGIN-KILL): на семействе,
плотном в X-норме (`‖g‖²_X = ‖e^{|x|}g‖² + 𝒟(g)`), никакого равномерного `c > 0`: `|Q(v_j)|/‖v_j‖² ≤ C_Xδ_j²/(1−δ_j)²`; следствие `limsup λ_min(K_{m,m}) ≤ 0` (только
верхняя оценка). Плант против «голой L²-плотности»: `Q* = Σn²|x_n|²` с радикалом `e₀` и L²-плотным `V` с равномерным запасом — X-плотность (по форме)
обязательна. Историческая поправка: D1 не опровергает буквальное неравенство статьи 2025 напрямую (её функционал не отождествлён с `Q`), но
(LEGACY-PLANT) — явный атом `φ_B` на узле `ξ₂` (треугольник×гауссиан) даёт `F(φ_B) ≤ 2M*B − w* < 0` — опровергает положительность на широком конусе
как транскрибировано, без RH и без числовых таблиц. **D2.** (SECOND): `E_{1+αs} = |α|²E_s`, `Q(f₀(1+αs)) = |α|²D(s)`, `D(s) = Q(f₀s)` — точно квадратично; (KERNEL)/(DIAG):
ядро `d_ε(x)δ_x − J_ε(x,dy)` с обрезкой `ε`; **(UV-DIAG): сырая диагональ логарифмически расходится** `d_ε(x) = f₀(x)²log(1/ε) + O(1)` — поточечного
диагонального баланса без регуляризации нет; (UV-BUDGET) `|D − D_ε| ≤ (5/3)‖s'‖²_∞ε²`; (FOURIER): двухчастотное ядро `𝓜(η,ξ)`, не скалярный множитель
(вес `f₀(x)f₀(x+t)` не трансляционно-инвариантен). **(SCHUR-KILL): никакой положительный диагональный вес `q` не даёт абсолютного Шур-сертификата** —
`∫(d_ε − a_ε)dx = −4N₋ < 0` (DEFECT), а симметризация с `z + 1/z ≥ 2` требует `≥ 0`; явная оценка `≤ −(43/42)ℓ₀²log(8/7)`. Обязательный плант (SIGNED-PSD):
`2|s₁−s₂|² + 2|s₂−s₃|² − |s₁−s₃|² = |s₁−2s₂+s₃|² ≥ 0` — форма PSD при отрицательном ребре и нулевых строчных суммах: провал абсолютного Шура ≠ отрицательность.
**D3.** (REC-FORM): моды CCM восстанавливают фиксированные тесты в X-норме с бюджетом `√(mL + 14(L+2))·ε_m(g)`; (GRAM)/(COMP-GAP): сжатие даёт
`Z*KZ + eZ*Z ⪰ 0 ⟺ Z*ΓZ − (c_L−e)Z*Z − 2(Z*β)(Z*β)* ⪰ 0` — при неполном ранге Z это лишь неравенство на range Z (плант `diag(−1,1)`, `Z = (0,1)ᵀ`); D3.3:
на восстанавливающем семействе `W ⟺ ∃e_m → 0: Q ≥ −e_m‖v‖²` — словарь ничего нового не поставляет, меняет только обусловленность и цену.
Критика Probe 25: float-midpoints и 40001-точечные суммы; `−2e-15` не сертифицирует нулевой запас (согласен). **D4.** (ZG) — точная матричная цель;
(DOM) ⟺ W (через `g = f₀s`); (ENC)/(FM) — конечно-простая версия с явными односторонними бюджетами. Направление судьи: R1 — сцепленные знаковые
сертификаты по образцу (SIGNED-PSD), а не абсолютные значения по рёбрам; R2 — нижние сертификаты полной Грам-минус-сдвиг. Судьбы: D1 0.90 CONFIRMED
(с стражами); ядро 0.70 CONFIRMED; тест положительности 0.30 CONFIRMED (весь класс убит); D3 → (GAP-GRAM) 0.80 CONFIRMED на уровне семейства; PARTIAL 0.88
CONFIRMED. Четыре предсказания судьи на review 0.94/0.87/0.91/0.89 PENDING. Route score 4; FALSIFICATION_PROGRESS.
**Мой второй канал.** (SIGNED-PSD) — тождество проверено символьно (sympy, остаток 0). Массы знаковой меры с весом `C₀` (mpmath): отрицательная
`N₋ = ∫_{t₀}^∞ b₋C₀ = 0.083642` (сходится); атомы простых `Σw_nC₀(log n) = 0.037599` — **в 2.2 раза меньше отрицательной массы**; положительная
непрерывная часть расходится как `log(1/ε)`: 0.1747, 1.1587, 2.2941 при `ε = 0.1, 0.01, 0.001` (≈ +1.13 на декаду ≈ `(log 10)/2` — (UV-DIAG) судьи в
числах). Вывод: баланс (DOM) не может быть степенным/поточечным — его несёт короткодействующая часть через `E_s(t) = O(t²)`, ровно как говорит судья.
Lean-агент запущен на конечные головы (TRADE, EIG-TRADE, конечный Шур-запрет, SIGNED-PSD, COMP-GAP). DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

## 2026-09-05 (ночь) — Lean: `DomfmFiniteObstructions.lean` KERNEL_GREEN (конечные головы DOMFM), тринадцатый файл фронта

Opus-агент (25 мин), проверено мной: `lake env lean` EXIT 0 без вывода, `q3_check ok`, все 39 теорем на `[propext, Classical.choice, Quot.sound]`
(две «ошибки» в моём grep — имена теорем со словом `error`), `sorry/admit/exact?/axiom` = 0; пространство имён `Q3.RouteB.Domfm`, единственный
проектный импорт `WeilGramMinusShift.lean`. Доказано: (TRADE) `domfm_projected_rayleigh_le` с операторной нормой `‖Kop‖` и явным тождеством
коэффициентов (невакуумность доказана), поляризация `R(v) − R(u) = Re⟪v−u, T(v+u)⟫`, `‖v−u‖‖v+u‖ = 2d`, вариационное следствие; (EIG-TRADE) точное
тождество и оценка `(M+|λ|)d²/(1−d²)`; конечный запрет абсолютного Шура `domfm_no_positive_absolute_schur_weight` (из `Σ(d_i − a_i) < 0`, симметризация
и `z + 1/z ≥ 2`) плюс достаточность `domfm_absolute_schur_sufficient`; (SIGNED-PSD) тождество, лапласиан `!![1,−2,1; −2,4,−2; 1,−2,1]`, нулевые строчные
суммы, дефект `−4`, отсутствие веса и при этом неотрицательность формы; (COMP-GAP) `domfm_compressed_gram_minus_shift` с PSD-эквивалентностью и плантом
`diag(−1,1), Z = (0,1)ᵀ`. Поправка агента к моему заданию: сжатый сдвиг несёт `ZᴴZ`, не единица — добавлена изометрическая версия. Второй канал
агента: numpy, пять пунктов. Отчёт: `docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-05_GOAL058_DOMFM_FINITE_OBSTRUCTIONS.md`.

## 2026-09-05 (ночь, судья над COUPLED) — радикал формы Вейля бесконечномерен: `Q(f₀ * h) = 0` для всех `h`; следствие для (CSS)

Повод: владелец прислал «Reverse-Math»-скелет (P ⟺ X ⟺ W ⟺ RH) со строкой `ker L = ℝ·f₀`. Это неверно. Явная формула: `Q(g) = Σ_ρ conj(Fg(ρ̄))Fg(ρ)`-типа
(зерo-сторона), и `F(f₀ * h) = Ξ·ĥ/A` обращается в нуль на ВСЕХ нулях для любого гладкого быстро убывающего `h` ⇒ `Q(f₀ * h) = 0` безусловно. Радикал
(ядро) формы содержит бесконечномерное пространство `{f₀ * h}`; в координатах отклонений — `s_h = (f₀ * h)/f₀`, не константы. **Проверено численно
(сеточный оценщик, смещение `−4.07e-4·H` снято):** `Q(f₀ * h)` = −1.2e-5, −3.9e-6, −6.3e-6 для трёх разных `h` (гауссианы в 0 и 1.2, нечётный бамп) при
контроле `Q(f₀(1 + bump)) = +8.6e-5`. Это классический факт (Ξ-кратные тесты), но для (CSS) он даёт жёсткое ограничение: любая сумма квадратов
`Σ∫W_j|S_js|²`, равная `Q(f₀s)`, должна обращаться в нуль на всём семействе `s_h` — каждый стенсил `S_j` с `W_j > 0` обязан аннулировать все `s_h`.
Локальные явные стенсилы с фиксированными коэффициентами этого не могут (семейство `s_h` не «локально полиномиально»); значит либо стенсилы
нелокальны (строятся через свёртку с `f₀`), либо (CSS) в локальном классе невозможна — это ровно C3 батча COUPLED, и моя `P_C3_LOCAL_STENCIL_OBSTRUCTION
0.40` выглядит заниженной (не редактируется). Прочие поправки к скелету владельца: `Ff₀ = Ξ/A` (единичная нормировка), `FΦ = Ξ`; критерий Вейля —
на классе тестов, не «на всём L²»; вес для `s` — `f₀²dx`. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-05 (ночь) — аудит «с нуля» по слову владельца: что леса, что удалить, что упростить

Владелец: «подумай с первых принципов; что лишнее; что удалить; что упростить; можно ничего не менять». Ответ. (1) **Леса:** спектральная линия Route B
(матрицы CCM, дно, кривизна, вторая мода, широкие окна) довела до стены и дала её точную форму, но её объект не необходим (FULLCHAIN, DOMFM: крыша —
критерий Вейля, (DOM) ⟺ W). Она остаётся лабораторией чисел, не дорогой. (2) **Удалить/прекратить:** производство Lean-файлов по конечной
бухгалтерии судьи (последние шесть файлов ничего не открывают, но и к крыше не ведут) — существующие не трогаю (удаление только по слову
владельца, хранение бесплатно); одноразовые скрипты зондов не автоматизирую (числа в журнале). (3) **Упростить сейчас:** карта стены переписана
в одно текущее состояние вместо пятнадцати хронологических слоёв (история — в git этого файла и в журнале; копия старой версии в scratchpad).
(4) **Слабое допущение, названное вслух:** что цикл батчей сам произведёт механизм. Шесть батчей за 30 часов дали шесть честных PARTIAL с леммами
и одну стену. COUPLED — последний естественный батч (единственный неубитый механизм); при теореме о препятствии (вероятной из-за бесконечномерного
ядра) честное состояние: стена классическая, наш вклад — явный леджер, убийства с числами, канонический тест, 13 ядерных тождеств; это и есть
публикуемое. Дальше нужна новая идея, не упаковка. Решения о заморозке спектральной линии и о переходе к статье — за владельцем.

## 2026-09-05 (ночь) — вердикт COUPLED (`6b103bd1`): класс сцепленных знаковых сертификатов с конечными стенсилами УБИТ теоремой

RESULT `ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE`. Механизм убийства — не отрицательная мера `b₋`, а радикал: каждый сдвиг `f_q = U_q f₀`
лежит в радикале формы (TRANS-RAD, из инвариантности (Q) к сдвигу и `B(f₀,·)=0`); компактные обрезки `s_{q,R} = χ_R·f_q/f₀` имеют
`|D(s_{q,R})| ≤ C_X C_q² exp(−2a_q e^{2R}) → 0` (NULL-BUDGET); конечные сдвиги ненулевой интегрируемой функции линейно независимы
(Фурье + Вандермонд, INDEP). Итог (C3.4): любой неотрицательный конечно-стенсильный минорант `∫W|Ss|² ≤ D(s)` имеет `W = 0` п.в. — без ограничения
на диаметр и мощность стенсила и даже без условия нулевого среднего. Следствие C3.5: точное CSS на всём компактном классе невозможно, потому что
`D ≢ 0` (узкий положительный тест даёт `Q(g) ≥ e^{−1/2}log(1/ℓ) − c_A ≥ 1`). Строгая отрицательная маржа сертификата (CERTIFICATE-KILL)
`D(s_{q,R}) − A_S(s_{q,R}) ≤ −η/2`. Расширение на континуальные семейства стенсилов (C3.6). Контроль: неотрицательная нелокальная форма
`|∫g e^{−iωx}|²` с радикалом из сдвигов тоже не имеет CSS — убит класс сертификатов, не положительность. C1: расщепление длинного ребра на N
коротких стоит `N³` против доступной плотности `N` (CAP-KILL); УФ-бюджет `∫₀^δ b₊E_s = I_s δ²/4`, логарифмической расходимости в
используемой энергии нет. C2: (RECT) верно, но перенос DIV в канонические стенсилы даёт лишние веса `⌊M/d⌋` и знаконеопределённые
диагонали (DIV-POT); (DIV-PLANT): `Q(fχ_R) → 0`, а конечная DIV-энергия `≥ log2(1−1/√2)² = 0.0595 > 0`. C4: локальная экстракция второй
разности имеет остаток, не являющийся PSD (REMAINDER-KILL). **Поправка к запросу (мне):** `Q(f₀e^{iξx}) = A^{−2}Σ_z Ξ(z−ξ)²` с КОМПЛЕКСНЫМИ
квадратами для невещественных нулей; «безусловная неотрицательность символа» не лицензирована явной формулой — моя запись Probe 26 предполагала
вещественность нулей. Не убито: (DOM-OPEN) само; нелокальные факторизации (R1); cutoff-зависимые сертификаты с доказанным восстановлением (R2).
Route score 4. `forbidden_future_move: retry_local_stencils_by_increasing_their_finite_size_or_diameter`.

**Второй канал (наблюдатель, sympy/mpmath):** PATH для N=2,3,4, RECT, DIV-POT — тождества точные; `ρ³−ρ=1` даёт `t₀ = 0.2811996`, `b(t₀) = 0`;
`I = [log 1.4, log 1.6] = [0.33647, 0.47000] ⊂ (t₀, 2t₀)`; `min B₋ на I = 0.3028 ≥ 43/168 = 0.2560`; `a(h)h ≤ 0.7015 ≤ 4/3`;
`ℓ = 2.737e-5`, `e^{−1/2}log(1/ℓ) − c_A = 1.0000`; `c_A = 5.3721834`. Всё сошлось.

**Данные против наблюдателя:** P_C3 0.40 — событие произошло, оценка занижена (после Probe о бесконечномерном радикале я это уже
предвидел, но предсказание было заморожено); P_RESULT_PARTIAL 0.80 — опровергнуто, класс исключён, а не оставлен незакрытым; знак символа
плоских волн — предпосылка о вещественности нулей у меня прошла молча. Вывод дня: аудит «с нуля» (выше) подтверждён вердиктом: локальные
механизмы исчерпаны; следующий батч по этому объекту не пишется без нелокального инварианта.

## 2026-09-05 (утро 06.09 по часам) — независимый аудит C3 COUPLED: все шесть лемм SURVIVE

Свежий Opus-агент вывел четыре утверждения (TRANS-RAD, бюджет обрезки, INDEP, NO-MINORANT) из одного абзаца определений ДО чтения доказательств
(файл заморожен 10:49, отчёт 11:04) и получил тот же механизм: радикал → обрезка → Фату → Вандермонд. C3.1–C3.6 и положительный контроль — SURVIVE,
без GAP и FALSE; два косметических замечания (гладкость `f` не перечислена среди наследуемых фактов; формулировка C3.6 «W = 0 или стенсил тривиален»).
Скрытой положительности `Q` и вещественности нулей не использовано. Агент проверил и наследуемый вход другим каналом: `Q(f₀) = 1.8e-10` из сырых
определений, `Q(U_q f₀) = Q(f₀)` для q = 0.5, −1, 2, `B(U_q f₀, v) ≈ 1e-10` относительно. Мой второй канал по константам агента: `Ξ(0)/A = 0.87913467`,
`F̂(0) = 3.5449077`, `F̂(1) = 1.49165412`, `min a·2t·e^{1/2} = 1.64955` — все совпали. Граница доверия: лемма о домене `B(f₀,v) = 0 ∀v ∈ X` и
`C_X = |c_A| + 14` наследуются из XIDEV. Зарегистрированные судьёй предсказания P_COUPLED_TRANSLATED_RADICAL_AND_CUTOFF_SURVIVE 0.92,
P_COUPLED_FINITE_STENCIL_NO_GO_SURVIVES 0.90, P_COUPLED_SPLITTING_JACOBIAN_SURVIVES 0.90 (мой sympy: N² перед суммой, направление CAP-KILL сохранено),
P_COUPLED_RECTANGLE_DIV_REPAIR_SURVIVES 0.94 (мой sympy: RECT, DIV-POT точные; DIV-PLANT число 0.0595) — все события произошли на уровне
агент+наблюдатель. Отчёт: `docs/routeB_bus/AGENT_REPORT_2026-09-05_GOAL058_COUPLED_C3_INDEPENDENT_AUDIT.md`. Статус C3.4: PAPER, дважды проверен
(судья + независимый вывод), в Lean не формализован — и по ночному решению не формализуется, пока не появится механизм, которому это служит.

## 2026-09-05 (утро 06.09) — два дефекта инструментов, найдены по ходу ответа владельцу, починены первыми

1. `./ask.sh` печатал «ПОИСК НЕПОЛОН — semantic-index freshness validation failed» на каждый запрос: приёмник индекса от 03.09 (`source_commit 7e4c60d1`),
   корпус ушёл вперёд на ~40 коммитов (`SEMANTIC_INDEX_CORPUS_STALE`). Корень: перестройку индекса никто не дёргал после вечера 03.09; ask.sh по контракту
   только читает. Починка: `./orchestrator/spine.py --refresh --reason semantic-index-refresh` (3 мин 42 с), повторная валидация PASS.
   Правило себе: после каждого дня с десятком коммитов в `docs/` — перестройка индекса, иначе полка молчит и «у нас этого нет» снова становится догадкой.
2. Тот же прогон показал `TOOL_MANIFEST_INVALID: writer bind-request has no approval gate`: запись `bind-request` в `TOOLS.yaml` (моя, 03.09) имела
   `writes: true` при `approval: NONE`, что валидатор манифеста запрещает. Починка: `approval: EXACT_WRITE_SCOPE` (пишет ровно PROSHKA_QUEUE.md).

## 2026-09-05 (утро 06.09) — фильтр Уильямса по Broughan т. 3: чужого инструмента, видящего простые в форме, нет

Агент прошёл 11 глав; я проверил оглавление и два ключевых утверждения. Тождество `Φ_ours(x) = 2Φ_P(x/2)` и `H_0 = Ξ(·/2)/8` — верно (mpmath, 12 знаков);
поток де Брёйна–Ньюмана = `f₀·e^{tx²/4}`, простых не содержит. Единственный «кандидат» агента (Pólya–Jensen через «те же моменты») опровергнут
на уровне определения: (DOM) на полиномах зависит от автокорреляционных моментов с мерой ν, Йенсен — только от `γ_n`. Итог фильтра отрицательный, но
с внешней пользой: два независимых подтверждения нулевого запаса (Rodgers–Tao, Nicolas). Данные против агента: одно ложное «TRANSPORTABLE» из семи
карточек, поймано вторым каналом. Подробно: `docs/CHAT_DIGESTS.md`, отчёт `docs/routeB_bus/AGENT_REPORT_2026-09-05_WILLIAMS_FILTER_BROUGHAN_VOL3.md`.

## 2026-09-05 (день) — статья 1 написана целиком; проход новизны снял две «наши» новизны из трёх

По слову владельца «пиши публикацию, го» открыт план и написан полный черновик `paper_weil/` (14 стр., 4 рисунка из определений/кэшей, 24 источника,
компилируется). Конвейер плагина: рисунки → определения → теоремы → обсуждение → введение → аннотация. Проход новизны (Opus, 54 обращения, полные PDF)
и моя проверка тех же PDF (`pdftotext` + grep): канонический тест — Риман/CCM Lemma 7.1, лог-форма — Freedman 2606.29555; знаковое ядро — Suzuki
2606.09096 §2.5 и 2301.00421 §3.5, «screw ⟺ RH» — Krein–Langer/Suzuki. Ложный локатор агента: CCM (4.12) — это α_L(n), не константа; в статью не вошёл.
Что осталось нашим и стоит в заголовке: теорема о препятствии (C3.4) против нелокального миноранта Connes 2602.04022 Thm 7.1; подстановка g = f₀s с
явной плотностью и пластическим числом; бесконечномерный радикал на расширенном классе (против Suzuki §1 и Bombieri Lemma 10); компромисс запас–плотность;
запрет Шура; инварианты на f₀. Введение, §3, §4, §5 и аннотация переписаны с атрибуцией. Урок дня в память: «полка → литпоиск → новизна» до
формулировки заголовка; две из трёх наших «новинок» жили в печати с 2025–2026, и первая — с 1859.

## 2026-09-05 (день) — Lean: `NoFiniteStencilMinorant.lean` KERNEL_GREEN — ядро теоремы о препятствии формализовано без дзеты

Opus-агент за 17 мин написал 621 строку: `independence_of_translates` (Фурье-фаза определена в файле, непрерывность через `continuous_of_dominated`,
сдвиг через `integral_sub_left_eq_self`; вместо производных — выборка экспоненциального многочлена в k точках малого интервала + `Matrix.det_vandermonde`),
`stencil_energy_limit_eq_zero` (Фату для одного q), `no_positive_finite_stencil_minorant` (H1 бюджет + H2 минорант на семействе χ_R r_q ⇒ W = 0 п.в.),
`..._hypotheses_satisfiable` (модель: f = e^{−x²}, Q ≡ 0). Моя проверка: `lake env lean` EXIT 0, 5 × `[propext, Classical.choice, Quot.sound]`,
`scripts/q3_check.sh` — сперва ложный hole на слово «sorry»/«admitted» в докстринге (ловушка из памяти `q3-check-admitted-trap`, третий раз),
после правки докстринга — чисто. Гипотезы сильнее спецификации в плюс (не нужны 0 ≤ χ ≤ 1 и структура Q). Не формализовано: аналитический бюджет
(Lemma 5.1 статьи) — входит гипотезой H1. Статья: §9 и приложение B обновлены (13 файлов; ядро главной теоремы проверено ядром).
Отчёт агента: `docs/routeB_bus/AGENT_REPORT_2026-09-05_LEAN_NoFiniteStencilMinorant.md`. Рецензент-агент ещё работает.

## 2026-09-05 (день) — рецензент-агент, раунд 1: major revision, 24 находки; правки внесены

Свежий Opus (слепой к журналам) пересчитал всё проверяемое: форма основного состояния `b = a − 2cosh(t/2)` и коэффициент атомов `w_n` подтверждены
(остаток 1.3e-12; альтернативы мимо на 1e-2 и 5e-4); Lemma 5.1 во всех константах, Lemma 5.2, Theorem 5.3, Cor 5.4, контроль F̂(π/2)=0 — верны.
Две CRITICAL: (1) моя Prop 5.7 (запас–плотность) имела ложный свидетель (обрезка сдвига сходится к радикальному элементу) — переписана в корректную
и тривиальную форму: плотность в X + непрерывность Q + Q(f₀)=0 при ‖f₀‖_X>0; (2) Prop 5.8 (Шур) — |T| от распределения не определено, расходится
положительная часть, а мажорировать надо отрицательную — понижена до Remark без статуса теоремы, из аннотации и леджера убрана как теорема.
HIGH: (EF) применялась к некомпактному f₀ без обоснования — добавлено доказательство через обрезки: сходимость источника по C_X и нулевой стороны через
Σ|z|^{-2} и ‖e_R''‖₁ → 0; ложная скобка «сдвиговая инвариантность ⇒ радикал» заменена корректным аргументом (поляризация инвариантности + B(f₀,·)=0);
`λ₁ ≥ −o(λ₂)` RH-эквивалентность — фраза удалена (одного предложения мало); формула второго джета трала переименована из «exact» в численное наблюдение
с эвристическим выводом, подгонка описана честно (двухточечная 0.019893; МНК по 4 ячейкам (0.019891, 0.00540) — второй коэффициент к 13/(256π²) на 5 %);
§8/абстракт про Lean — согласованы с реальным состоянием; cleveref печатал все Proposition/Corollary/Example как «Theorem» — починено через `aliascnt`.
MEDIUM: доказательство Thm 3.2 — исправлен множитель (`Ξ(z) = 4∫Φ_P cos(2zu)`, `H₀ = Ξ(·/2)/8`); противоречивая фраза о положительности удалена;
константы оболочки `M₀ = 23.910, M₁ = 325.43` вычислены и добавлены, `c_χ = 2`; коэффициент УФ-массы `1.13` → `(ln10)/2 = 1.1513`; аннотация «одно
неравенство между атомами и отрицательной плотностью» → «три члена»; X определён конкретно, четыре слагаемых C_X выписаны (сумма |c_A|+11.54 ≤ |c_A|+14);
«радикал есть замыкание Ξ-кратных» → «содержит»; параграф «инварианты Ξ» удалён (формулы 𝒥, 𝒮 не были определены); Thm 5.3 переписана в общем виде
(любой f>0 в радикале функционала с бюджетом; Weil — следствие), как в Lean-файле; измеримая версия → Remark с Фубини. LOW: ρ → ρ_p, A_j → M_j, dν̃(t),
Q(f₀) ≈ 1e-15, «экспоненциально по m», таблица Probe 19 добавлена, Connes–Moscovici процитирован.
Не принято: ничего (все 24 найдены обоснованными; #1 переформулирован, не удалён). Отчёт: `docs/routeB_bus/AGENT_REPORT_2026-09-05_PAPER_REFEREE_ROUND1.md`.
Данные против наблюдателя: две «теоремы» в первом черновике были утверждениями без доказательств; сам бы я их пропустил. Правило: враждебный рецензент
до стиля — подтверждено практикой.

## 2026-09-05 (вечер) — рецензент раунд 2 (major revision, лёгкий) + стилевой проход слиты; статья v3, 17 стр.

Раунд 2 (свежий Opus, чеклист из 24 находок раунда 1): 14 YES, 8 PARTIAL, 2 NO; новых находок 16 (3 HIGH). Мой второй канал по двум HIGH:
(1) нулевая сторона расширения (EF) требовала `‖e_R''‖ → 0`, а оболочка была дана лишь для j ≤ 1 — константа `M₂ = 6011.8` (мой sympy/mpmath ДО
отчёта, совпала с числом рецензента 6011.82) и `|χ''| ≤ c'_χ = 8` внесены; выделена Lemma 3.3 (cutoff norms) — устраняет и видимую циркулярность
между Prop 3.4 и Lemma 5.1; (2) полюсный шаг в доказательстве Thm 4.1 был записан несимметрично (`2Re A₊(f₀)conj A₋(f₀|s|²)` вместо
`Re[conj A₊(f₀)A₋(f₀|s|²) + conj A₋(f₀)A₊(f₀|s|²)]`) — рецензент: расхождение 5.6e-3 против 6e-16 у симметричной формы; теорема верна, дисплей починен.
(3) «exact second-jet formula» во введении → «conjectural second-jet expansion»; «дзета сокращается тождественно» — убрано; App A «measured 0.005143»
→ МНК `0.00540`; `A_j` → `M_j` везде, `C_q² = 150 925/(2a_q)`; параграф «Envelope constants» переписан (был с многоточиями); §8 про Lean-файлы окон —
«companion computation», не утверждения статьи; X — пополнение, плотность по построению; строка (13,120) в таблице объяснена в подписи; ε_∞ с нормой;
0.03 % к Zhu убрано, 20 % — с явным предсказанием 10^{−219.5}; дисплеи в аннотации и §1 приведены к виду Thm 4.1; «cutoff property» → «cutoffs have
vanishing form value». Стилевой проход (humanizer-academic → sciwrite, по копии): 15 правок (1 AI-паттерн: «corroborate» → «support»; 14 ясность:
пассив → актив, разрезание 78- и 71-словных предложений, CCM определён, «cell» определён, «non-» закрыт), все слиты вручную поверх правок рецензента;
математика, числа, ссылки не тронуты (проверено агентом механически и мной сборкой). Отчёты: `docs/routeB_bus/AGENT_REPORT_2026-09-05_PAPER_REFEREE_ROUND2.md`,
`paper_weil/style_pass/STYLE_CHANGELOG.md`. Сборка чистая, 17 страниц. Дальше: третий (подтверждающий) раунд рецензента и вычитка владельца.

## 2026-09-05 (вечер) — вердикт PAPERCLEAN (`da9236c8`, 1336 строк): READY_AFTER_LISTED_FIXES; все P01–P13 применены; статья v4

Судья прочитал все tex-исходники v3, оба отчёта рецензента, стиль и новизну. 0 CRITICAL, 9 HIGH, 7 MEDIUM, 3 LOW, 1 WORDING — по корням, не по вхождениям.
Ядро SURVIVES: нормировка Римана/Φ_P, обрезки (с точными константами и R ≥ 0), радикал (после починки оболочки свёртки: a_H = (π/2)e^{−2H} по радиусу
носителя h, а не «константа × та же оболочка» — F01, моя ошибка), тождество (GS), обструкция конечных стенсилов, счётный SOS-запрет, отсутствие
X-запаса. NOT_ESTABLISHED и удалено из текста: «нет никакого SOS», «минорант Sonin нельзя локализовать» (у Connes ограниченный класс носителей;
нуль трансформы у него в i/2, не 2i — по визуальной проверке судьи), «форма индефинитна» (отрицательного направления мы не доказали). Приоритет:
плотность b(t) и атомы получаются дифференцированием винтовой функции Suzuki (1.3) — компонент prior art; §3.5 — это arXiv:2206.03682 (JLMS 108,
2023), а не 2301.00421 (мой второй канал: abs 2206.03682 — screw function, да). F08: матрицы CCM в базисе Фурье-мод (их (4.12), U_n на L²([0,L])),
не в пролатном — исправлено везде; F09: 1.35/1.33 — это R(q)/λ₁, рэлеевские отношения, не ‖ξ−q‖/√λ₁ (мой журнал 4665 подтверждает); F10: 1.7e-220
на 46 % ниже 10^{−219.5}, не на 20 %; F12: архимедова часть не «неограничена снизу» (D − c_A H ≥ −c_A H) — леджер п.1 переписан; F13: Newman/Nicolas
не дают теоремы о нулевом запасе для всех эквивалентов — обобщения сняты; F14: Lean H2 использует ENNReal.ofReal(Q) = положительную часть — уточнено.
Применено: 8 файлов заменены целиком (abstract, intro, setup, windows, ledger, disclosure, app_constants, app_lean), фрагменты в canonical/groundstate/
obstruction (P04a–d, P06a–e, P07a–f), bib (Suzuki2023Screw, LeidenDeclaration2026, Frank–Seiringer с DOI). Сборка EXIT 0, 16 стр., без неразрешённых
ссылок. Предсказания: 4 из 5 моих сбылись; HIGH ≤ 2 (0.55) опровергнуто — девять. Директива судьи: независимая проверка P04b–c и поляризованной
алгебры P06, затем сборка — сборка сделана; независимая проверка алгебры — следующий шаг. Данные против наблюдателя: оболочка свёртки (F01),
базис CCM (F08), рэлеевское отношение под именем ε_∞ (F09), «неограничена снизу» (F12) — четыре содержательные ошибки, которых два раунда
Opus-рецензента не увидели. Судья стоит выше рецензента-агента; это записать.

## 2026-09-05 (вечер) — независимая проверка патчей судьи P04b–c и P06 (директива PAPERCLEAN): всё CORRECT

Свежий Opus (только три tex-файла, без вердикта): Lemma 3.3 — три интеграла точно (E₁, Γ(1/4,·)), константы воспроизведены, квинтик-ступень
max|p'| = 15/8, max|p''| = 10/√3 (sympy), после сжатия 1.913 ≤ 2 и 6.012 ≤ 8; свёртка — нужен M_j, не AM_j, в тексте верно; Thm 4.1 — все четыре шага,
полюсный шаг доказан символически для произвольных комплексных s (не использует чётность |s|², только вещественность f₀), численно 1.85e-12;
плоские волны и Lemma 4.2 — верно. Предсказания судьи P_PAPERCLEAN_INDEPENDENT_GS_FACTORS_SURVIVE 0.97 и ..._CUTOFF_AND_CONVOLUTION_BOUNDS_SURVIVE 0.94 —
события произошли (агент+наблюдатель). Замечание: 32/3 в H¹-оценке слабо на e^{−1/2} — не ошибка. Директива судьи выполнена: сборка чистая, 16 стр.
Отчёт: `docs/routeB_bus/AGENT_REPORT_2026-09-05_PAPER_PATCHCHECK_JUDGE_P04_P06.md`. Статус статьи: v4, ждёт вычитки владельца и решения по arXiv.

## 2026-09-05 (ночь) — вечер штурма владельца (циркуль, спираль, окружность, радиусы, сгиб, дырка) + ответ судьи TRY_ADAPTIVE_CONTOUR_FORMALIZATION

Шесть частей штурма записаны в CHAT_DIGESTS с переводом на известные объекты: θ Римана–Зигеля, точки Грама и закон Грама (93.7 % на 600 нулях),
GUE-щели, произведение Адамара, преобразование Кэли, координата Ли (владелец пришёл к ней сам; λ_n посчитаны; λ₁ ≈ κ_Ξ объяснено как две суммы по нулям
с разными весами, разность ¼Σ1/(γ²(γ²+¼)) = 9.28e-6 совпала), функциональное уравнение как сгиб, тепловой поток и классификация Pólya–Schur/Borcea–Brändén,
Hilbert–Pólya/Berry–Keating, головоломка с монетой = инвариантность периметра = θ/N(T) против S(T). Судья формализовал сгиб: две абстрактные леммы,
один убитый класс (произвольная изоляция ⇒ вещественность; контрпример (1+16z²)cos z), интерфейс Руше на покрытии как условная достаточность, поставщик —
тот же same-family ZeroEscape Route B. Итог вечера: ни одна геометрическая картина не дала новый вход; все — координаты одной стены. Работ не запущено;
статья v4 ждёт вычитки владельца.

## 2026-09-06 (ночь) — Probe 27 (Руше на границе): предрегистрация ДО чисел

Объект: Q(D) = sup_{∂D} |Ξ/Ξ(0) − F_v/F_v(0)| / |F_v/F_v(0)| для трансформа донного вектора F_v(z) = 2sin(zL/2)Σ_n(−1)^n c_n/(z − 2πn/L) (FULL-коэффициенты,
c_0 = v_0, c_n = v_n/√2; проверка конвенции: F(x_k)/F(0) = (−1)^k c_k/c_0 = карточка) на прямоугольниках [0,T]×[h₁,h₂] в полосе вне оси; ячейки (13,13),
(13,60), (13,120). Вопрос: годится ли донный вектор конечного окна как модель для интерфейса Руше судьи (TRY_ADAPTIVE_CONTOUR_FORMALIZATION), и как
масштабируется запас 1 − Q. Предсказания (наблюдатель, заморожены): P_Q_LT1_WIDE_13_120_ALL_RECTS 0.70 — на (13,120) Q < 1 на всех пяти прямоугольниках;
P_Q_GT1_PROD_13_13_SOME 0.60 — на (13,13) хотя бы один прямоугольник даёт Q ≥ 1; P_Q_GROWS_WITH_HEIGHT 0.80 — Q растёт с Im z при фиксированном T.
ЕСЛИ_A (Q < 1 на широких ячейках, степенной запас): поставщик Руше виден количественно → форма оценки для батча судье. ЕСЛИ_B (Q ≥ 1 везде): донный вектор
не модель Руше при конечном m → класс убит. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-06 (ночь) — Probe 27, первая попытка: странность поймана и объяснена до чисел

Первая строка выдала `F(0.1)/F(0) = 0.99387` при `Ξ(0.1)/Ξ(0) = 0.99977` на ВСЕХ ячейках, включая (13,120), где совпадение на оси известно до 1e-9 → ошибка
в моём трансформе, не в данных. Корень: моды builder'а на `[0, L]`, а я писал центрированную формулу с `(−1)^n`; сдвиг окна на L/2 поглощает знак. Проверка
корня: без знака второй джет формулы даёт `kappa_full` карточки дословно. Исправлено, записано в CONVENTION_CARD; перезапуск.

## 2026-09-06 (ночь) — Probe 27, результат: интерфейс Руше на донных векторах работает до высоты T*(m), запас не зависит от Im z

Q(D) на прямоугольниках [0,T]×[h₁,h₂] (ячейки (13,13), (13,60), (13,120); F по исправленной формуле; ось: F(0.1)/F(0) = 0.99978 против Ξ 0.99977 —
разность 1.6e-5 = |α_G|·z² с α_G = −1.567e-3, сходится с Probe 19):
| ячейка | T=5 | T=15 | T=30 |
| (13,13)  | 0.073 | 1.022 ✗ | 82 ✗ |
| (13,60)  | 0.038 | 0.296 | 0.756 |
| (13,120) | 0.038 | 0.297 | 0.757 |
Q практически не зависит от высоты полосы (0.05–0.15 против 0.2–0.4: разница в третьем знаке) и растёт с T; на широких ячейках Q < 1 до T* ≈ 33–35, дальше
сертификат Руше исчезает. Судьбы предсказаний: P_Q_LT1_WIDE_13_120_ALL_RECTS 0.70 — CONFIRMED; P_Q_GT1_PROD_13_13_SOME 0.60 — CONFIRMED (T ≥ 15);
P_Q_GROWS_WITH_HEIGHT 0.80 — REFUTED (растёт с T, не с Im z). Прочтение: ошибка трансформа относительно Ξ есть архимедов множитель трала
(1 + a_m z²/m + …), поэтому Q ~ 1 при T² ~ m/a_m ≈ 13/0.02 → T ≈ 25–35 ✓. Ожидание: T*(m) ∝ √m ∝ λ — «конечное окно видит нули до высоты ∝ λ»
(Бомбьери 2000 о числе отрицательных собственных значений; тот же масштаб). Новые предсказания ДО прогона (23,160), (43,344):
P_TSTAR_SQRT_M 0.60 — T*(23)/T*(13) ∈ [1.2, 1.5] (√(23/13) = 1.33); P_TSTAR_LINEAR_M 0.25 — отношение ∈ [1.6, 1.9]; P_TSTAR_43 0.55 — T*(43) ∈ [50, 75].
ЕСЛИ √m: интерфейс Руше на донных векторах = сертификат безнулевости полосы до высоты ∝ λ, RH требует λ → ∞ с сохранением Q < 1 — та же стена в
координате высоты; ЕСЛИ быстрее √m: новый факт о трансформах, требующий объяснения. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-06 (ночь) — Probe 27b: Q(T) = 1 − exp(−a_m T²/m) — граница Руше на дальней стороне есть архимедов множитель трала; «T* ≈ 75» — артефакт float64

Скан T = 5…80 на (13,120), (23,160), (43,344): Q растёт монотонно к 1 и достигает 1.000 при T ≈ 75 на ВСЕХ трёх ячейках — подозрительно; причина: коэффициенты
вектора переданы через float64, а |F/F(0)| ~ |Ξ/Ξ(0)| ~ e^{−πT/4} падает ниже 1e-16 при T ≈ 47 → дальше F = шум и Q ≡ 1. До T ≈ 40 числа настоящие и
ложатся на закон архимедова множителя: Ξ/F ≈ exp(−a_m z²/m) ⇒ Q = 1 − exp(−a_m T²/m): (13, T=30) 0.757 против 0.748; (23, 30) 0.546 против 0.542;
(43, 30) 0.343 против 0.343; (43, 45) 0.611 против 0.611; (43, 60) 0.819 против 0.813. Значит: на дальней стороне Q < 1 всегда и стремится к 1 снизу —
сертификат формально жив при любом T, но его маржа e^{−a_m T²/m} → 0; при фиксированном m это НЕ даёт RH только потому, что провал сидит не на дальней
стороне, а у нижнего края полосы возле вещественных нулей F: трансформ трала k_λ имеет РОВНО нули Ξ (архимедов множитель безнулевой), а F донного вектора
отличается от него остатком √p ~ 7e-5, сдвигающим нули на δ_k ≈ остаток/|Ξ'(γ_k)|; сертификат на высоте h требует δ_k < h. Судьбы предсказаний 27b:
P_TSTAR_SQRT_M 0.60 — НЕ РЕАЛИЗОВАНО (пересечения нет; измеренный «T*» — артефакт точности; событие в [1.2,1.5] не наступило → REFUTED как поставлено);
P_TSTAR_LINEAR_M 0.25 — REFUTED; P_TSTAR_43 0.55 — REFUTED (артефакт). Данные против наблюдателя: гнал зонд через double после правила «arb до печати»
(третий раз за сутки, см. 04.09) — правило переносится в память как hard: коэффициенты только через mpf/arb-строку.
Probe 27c (запуск, предрегистрация): δ_k(m) = |zero_k(F) − γ_k| для k ≤ 12 на трёх ячейках, коэффициенты в полной точности; P_DELTA_LOGLIN 0.60 — log δ_k
линейно по γ_k (растёт как e^{πγ/4}/√p-масштаб); P_DELTA_DECREASES_IN_M 0.70 — δ_k(43) < δ_k(23) < δ_k(13) при всех k ≤ 8; P_DELTA_LT_0.05_TO_40 0.65 —
δ_k < 0.05 для всех γ_k ≤ 40 на (13,120) (согласуется с Q-максимумом на дальней стороне при h = 0.05).

## 2026-09-06 (ночь) — Probe 27c: нули трансформа донного вектора совпадают с нулями Ξ до 1e-17; объяснение — тождество утечки

Полная точность (dps 60, коэффициенты через строку arb). (13,120): δ_k = zero_k(F) − γ_k = −1.4e-17 … −5.6e-17 для k = 1…12 (линейно по γ_k: это ошибка
double в L = math.log(m), относительная 1e-18 — не математика); (23,160): +7e-17 … +2.8e-16 — тот же артефакт L. |F(γ_k)/F(0)| = 5e-20 … 3e-30 на (13,120):
F практически ОБНУЛЯЕТСЯ во всех нулях Ξ. Объяснение (не новое, но теперь измерено): λ₁ = Σ_z F_ξ(z)² (тождество окна, Groskin Thm 2.5 + CCM 5.9;
п. 5–6 PUBLICATION_PLAN) — донный вектор минимизирует именно сумму квадратов F по нулям, поэтому |F(γ_k)| ~ √λ₁·масштаб и δ_k ~ √λ₁/|F'(γ_k)| — за пределами
измеримого. Дальняя сторона при полной точности: (13,120) Q(50, 60, 80, 100) = 0.98079, 0.99670, 0.999965, 0.99999992 против модели 0.9782, 0.9960, 0.99994,
1.0000 — закон Q = 1 − e^{−a_mT²/m} держится до T = 100, пересечения единицы НЕТ (27b «T*≈75» окончательно артефакт). Судьбы 27c: P_DELTA_LOGLIN 0.60 —
REFUTED (δ на полу точности, роста нет); P_DELTA_DECREASES_IN_M 0.70 — NOT_MEASURABLE (пол); P_DELTA_LT_0.05_TO_40 0.65 — CONFIRMED тривиально.
Странность записана: (43,344) при dps 300 и 60 итерациях обратной итерации дало λ₁ = 9.24e-124 вместо сертифицированных 1.73e-220 — итерация не сошлась;
числа m = 43 в 27b/27c по дальней стороне всё же легли на закон (он зависит от вектора слабо), но ячейку надо пересчитать с большим числом итераций.
Процесс 27c был убит harness'ом до конца m = 43 (второй раз за сессию; см. память vahta/systemd-run) — длинные счёты только через `systemd-run --user`.
Прочтение фронта: сертификат Руше на донном векторе жив до высоты, где остаток R ~ √λ₁ сравнивается с |Ξ(t+ih)| ~ e^{−πt/4}: T_cert(m) ≈ (2/π)·ln(1/λ₁)
≈ (2/π)(4.5…5.1)·m·ln10 ≈ 3.3–3.7·m — ЛИНЕЙНО по m, не √m (моё утро-предсказание было о другой величине). Предрегистрация 27d (полоса h ∈ [0.01, 0.05],
T до 200): P_TCERT_13_IN_70_100 0.60; P_TCERT_23_IN_140_190 0.50; P_TCERT_LINEAR_IN_M 0.55 (T_cert(23)/T_cert(13) ∈ [1.6, 2.0]); P_NEAR_AXIS_Q_LT1_TO_TCERT 0.65.
ЕСЛИ линейно: окно m сертифицирует отсутствие невещественных нулей до высоты ≈ 3.5m — количественная форма «конечное окно видит нули до высоты ∝ m»
(сравнить с Бомбьери 2000 §8: отрицательные собственные значения ↔ нули вне прямой); RH ⟺ это верно при всех m — стена в координате высоты, но с ЯВНОЙ
константой; ЕСЛИ нет: остаток R не подчиняется масштабу √λ₁ и тождество утечки надо перечитать. DIAGNOSTIC_NEVER_A_PROOF.

## 2026-09-06 (ночь) — Probe 27d, m=13: T_cert(13) ∈ [140, 160): сертификат Руше донного вектора живёт до высоты ≈ 150 ≈ 11.5·m

Полоса h ∈ [0.01, 0.05]: Q = 0.466 (T=20), 0.920 (40), 0.9967 (60), 0.99997 (80), 1 − Q < 5e-9 (100–140, максимум на дальней стороне по закону
архимедова множителя), при T = 160 максимум переехал к оси: Q ≥ 1 в z = 151 + 0.01i рядом с γ₃₇ = 150.925 → T_cert(13) ∈ [140, 160). Предсказание
P_TCERT_13_IN_70_100 0.60 — REFUTED: сертификат живёт почти вдвое дольше грубой оценки «√λ₁ против e^{−πT/4}» (T = 86). Значит остаток R = F − Ξ·G
на вещественной оси много меньше своей глобальной нормы √λ₁: он сосредоточен не там (в мнимом направлении / вне полосы). Это новое количественное:
|F(γ_k)/F(0)| спадает медленнее Ξ (наклон ≈ 0.55 против π/4 = 0.785 на γ ∈ [14, 56]); пересечение масштабов ≈ 150. Предрегистрация для m = 23
(скан продлён до T = 440 отдельным юнитом): P_TCERT_23_IN_240_320 0.55 (линейно по m → 265; по ln(1/λ₁) → 285); P_TCERT_23_GT_200 0.80.
ЕСЛИ ∝ m: T_cert(m) ≈ 11.5·m — окно m сертифицирует полосу до высоты ≈ 11.5m (сравнить: число нулей до T ≈ (T/2π)log(T/2πe) ≈ 30 при T=150, а
размер окна N = 120 мод; при m=23: ≈ 60 нулей на 160 мод); ЕСЛИ ∝ ln(1/λ₁) ∝ m·log m: чуть быстрее линейного — различить на m = 43.

## 2026-09-06 (ночь) — вход «фазовый циркуль»: проверен числами, сведён к положительности Лагариаса (эквивалент RH); см. CHAT_DIGESTS

## 2026-09-06 (ночь) — Probe 27d, m=23: T_cert(23) ∈ [260, 280) — линейно по m

Полоса h ∈ [0.01, 0.05], скан T = 200…440 (юнит 2, вектор сохранён в `ground_23_160.json`): Q ≥ 1 впервые при T ∈ [260, 280). Предсказания:
P_TCERT_23_IN_240_320 0.55 — CONFIRMED; P_TCERT_23_GT_200 0.80 — CONFIRMED. Отношение T_cert(23)/T_cert(13) ≈ 270/150 = 1.8 при m-отношении 1.77
(линейный закон T_cert ≈ 11.6·m) и при ln(1/λ₁)-отношении 257/135 = 1.9 — линейный закон чуть лучше, различить окончательно может m = 43:
линейно → ≈ 495; по ln(1/λ₁) (λ₁ = 1.73e-220 → 506) → ≈ 560. Предрегистрация m = 43 (юнит 3, T = 300…700, вектор 300 итераций dps 320, сохраняется):
P_TCERT_43_IN_460_540 0.50; P_TCERT_43_GT_560 0.30; P_TCERT_43_LT_460 0.20. Прочтение (если линейно): донный вектор окна m сертифицирует отсутствие
невещественных нулей до высоты ≈ 11.6·m; число нулей дзеты до этой высоты ≈ (T/2π)ln(T/2πe) ≈ 30 (m=13), 60 (m=23) — примерно N/4 мод на нуль.

## 2026-09-06 (ночь) — Probe 27d, прочтение двух точек: T_cert = (4/π)·ln(h₁/R_ax), остаток на оси R_ax ≈ e^{−9.4·m} ≪ √λ₁

Механизм провала сертификата у оси: возле нуля γ отношение Ξ/F ≈ (z − γ)/(z − γ′), Q = |γ − γ′|/|z − γ′| ≥ 1 ⟺ сдвиг нуля δ(T) ≥ h₁ = 0.01. Сдвиг растёт как
δ(T) ≈ R_ax·e^{πT/4} (остаток R_ax делится на |Ξ′(γ)| ~ e^{−πT/4}); при T ≤ 56 он ниже пола точности (27c), при T_cert равен h₁. Отсюда ln(1/R_ax) =
πT_cert/4 + ln(1/h₁): m=13 → 122.4 (9.42/m); m=23 → 216.7 (9.42/m). Две точки дают ОДНУ константу: ln(1/R_ax) ≈ 9.42·m. Сравнение с утечкой: ln(1/λ₁) = 135,
257 → R_ax ≈ λ₁^{0.91}, λ₁^{0.84} — остаток донного трансформа на вещественной оси гораздо меньше √λ₁ (это и опровергло моё [70,100]). Предсказание для
m = 43 по этой константе: T_cert(43) ≈ (4/π)(9.42·43 − 4.6) ≈ 510 — внутри зарегистрированного [460, 540]. Линейность по m = линейность ln(1/R_ax) по m.
Это первый явный количественный закон об остатке донного вектора вне утечки; в статью (§6, диагностика) и в батч судье, когда придёт m = 43.

## 2026-09-06 (ночь) — вход «∂_y|Ξ|² ≥ 0»: проверен числами, сведён к монотонности Сондоу–Думитреску (эквивалент RH); объект W_y на нашей f₀; см. CHAT_DIGESTS

## 2026-09-06 (ночь) — вход «W_y > 0 / отрицательный хвост усечений»: проверен числами, все три утверждения верны; главный знак = RH; см. CHAT_DIGESTS

## 2026-09-06 (ночь) — Probe 27d, m=43: оба юнита дали негодный вектор; результат m=43 АННУЛИРОВАН, серия остановлена до пересчёта вектора

Юнит 1 (dps 320, 300 итераций обратной итерации, builder по умолчанию): λ₁(43,344) = 3.06e-20 вместо сертифицированных 1.73e-220 — итерация не сошлась/
разошлась (60 итераций ранее давали 9.24e-124); «T_cert(43) ∈ [40,60)» — артефакт негодного вектора, НЕ считается. Юнит 3 (тот же способ построения) остановлен
до вывода. Причина по памяти (`MAX_DEGREE` ↔ требуемая относительная точность ≈ √λ₁): сертифицированные бездны m=43 считались отдельными юнитами
(q3-sat43) с MAX_DEGREE 900; builder из edge_ledger_build без этого параметра не даёт нужной точности. Предсказания P_TCERT_43_* остаются PENDING (событие
не измерено). Числа 27b для m=43 на дальней стороне (T ≤ 60) сохраняют силу: вектор с λ₁ ≈ 1e-124 достаточен для Q при e^{−πT/4} ≫ 1e-62. Далее: либо найти
сохранённый сертифицированный вектор (43,344), либо пересчитать его отдельным юнитом с MAX_DEGREE 900 (часы) — только если различение 510/560 нужно судье.
Корень негодного вектора m=43 найден: сертифицированные бездны q3-sat43 считались при `ctx.dps = max(460, 2N+160)` = 848 и 6 итерациях; мои юниты брали dps 300–320 —
недостаточно для (43,344) (λ₁ ~ 1e-220 требует ≳ 450 знаков в матрице). Перезапуск юнита 43b: dps 850, 8 итераций, mpmath dps 260, вектор в JSON, скан T = 400…640.

## 2026-09-06 (ночь) — Probe 27d, m=43 (dps 850, вектор настоящий, λ₁ = 2.464e-220): T_cert(43) ∈ [520, 540). Серия закрыта.

Скан T = 400…540: провала нет до 500 (максимум на дальней стороне), при 520 максимум ушёл к оси (520 + 0.01i), при 540 Q ≥ 1 → T_cert(43) ∈ [520, 540).
Судьбы: P_TCERT_43_IN_460_540 0.50 — CONFIRMED; P_TCERT_43_GT_560 0.30 — REFUTED (закон ln(1/λ₁) → 560 не подтвердился); P_TCERT_43_LT_460 0.20 — REFUTED.
Три точки с учётом ширины бинов: ln(1/R_ax)/m ∈ [8.8, 10.0] (13), [9.08, 9.76] (23), [9.61, 9.97] (43) — общее окно [9.61, 9.76]: ОДНА константа
ln(1/R_ax) ≈ 9.7·m совместима со всеми тремя ячейками; T_cert/m ∈ [12.1, 12.6] на m = 43. Закон: остаток донного трансформа на вещественной оси
R_ax ≈ e^{−9.7m} ≈ λ₁^{0.83}; сертификат Руше окна m покрывает высоты ≈ 12m. Прочтение по фронту: это скорость same-family сходимости F_m → Ξ на оси
(поставщик N0/N1 Route B), измеренная впервые; вместе с нормальностью (Curvature–Vitali) такая сходимость на растущих отрезках даёт RH через крышу — т.е.
это атом FULLCHAIN с числом, не механизм. Серия Probe 27 закрыта; скрипт регистрируется в TOOLS.yaml (`rouche_tcert.py`) для воспроизведения.

## 2026-09-06 — аудит skill-файлов и цепи Codex по статье Provencher «Rethinking skills and prompts for GPT-6 Astra» (X, 04.09); применён по слову владельца

Статья прочитана через браузер владельца (WebFetch дал 402). Правила: короткие описания skill, корень = маршрутизатор, без рецептов; AGENTS.md без стопки
документов перед каждой правкой и без напоминаний «запусти тесты/спроси разрешения»; вместо запретов — разрешение на безопасные процедуры и определение
«где остановиться». Сделано (удаляемое — в архив, решение владельца): `archive/skills_gpt5_era_2026-09-06/` с README-таблицей причин — туда ушли
`.agents/skills/{q3-psdpd-step33-bootstrap, q3-step32-lean, routeb-conductor}`, `.claude/skills/routeb-conductor` (377 строк июльского транспорта,
противоречил v10), `skills/x-insider`, `docs/Aristotle_models_training/{SKILL.md, claude_code_skills.md}`. Сжато: `SESSION_ENTRY.md` 172 → ~45 строк
(одна команда, battle brief, таблица «триггер → раздел»), `AGENTS.md` без «прочитать полностью до любого действия» (токены валидатора сохранены:
CODEX_BOOTSTRAP_VALID), три `.codex/agents/*.toml` до 5–7 строк без чтения спящих мониторов, `CLAUDE.md`: два абзаца батчей → `docs/BATCH_PATTERNS.md`
с указателем. Реестры: `TOOLS.yaml` (запись RETIRED с архивными путями; инвентарь без `.agents/skills`) — MANIFEST PASS; `portability_manifest.py` без
архивных путей — CHECK PASS. Не тронуто: `docs/CODEX_CONTROL.md` (цепь Codex, bump версии — его дело по команде владельца), гейты ядра/аксиом/PX_RH_CLAIM,
`q3.lean.aristotle/KB/skills` (карантин, никем не грузится). `session_start.sh` по-прежнему exit 1 по двум старым расхождениям (запись 03.09 без полей
развилки; мигратор — прогнан сейчас).

## 2026-09-06 — аудит v2 по пакету Codex (срез 6140d6ad, до моих правок): взято 6 пунктов + KB-стаб; отвергнуто 3; всё удаляемое — в архив

Проверено мной: `q3_check.sh` действительно сам гонит `lake env lean` и считал `exact?` дырой — оба замечания Codex верны. Применено: (1) `q3_check.sh`:
`sorry|admit` — провал, `exact?` — предупреждение «перенеси найденную тактику в исходник»; (2) один локальный гейт `scripts/q3_check.sh <file>` вместо двойного
прогона (toml, SESSION_ENTRY); (3) `q3-researcher.toml`: право менять представление и строить доказательство, интегратор сохраняет утверждение, недоказанное не
называется доказанным; (4) CLAUDE.md, VOI-раздел: предсказания и ветки ЕСЛИ обязательны только перед дорогим шагом и в батчах, не после каждого зонда;
(5) четыре пункта рабочего контекста (цель / чтение / истинность / действия) — НЕ в AGENTS.md: валидатор `THIN_POINTER_CONTAINS_POLICY` (≤ 24 строк, запрещённые
слова политики) отверг 27-строчный вариант Codex — положены в `SESSION_ENTRY.md` (обе копии), AGENTS.md остался тонким указателем; (6) `KB/skills/AGENTS.md` →
5-строчный стаб, прежнее содержимое в `archive/skills_gpt5_era_2026-09-06/kb_skills_AGENTS.md`. Отвергнуто (правила владельца, не Codex): язык крыши/опор,
запись странного до объяснения, «таблица на сотнях окон прежде агента»; правка `CODEX_CONTROL.md` до v11 — отдельное решение, не пакетом. Валидаторы:
CODEX_BOOTSTRAP_VALID, MANIFEST PASS, `q3_check.sh` на NoFiniteStencilMinorant.lean — ok.
