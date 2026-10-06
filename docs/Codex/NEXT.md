# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~80 строк.
При закрытии ворот, фазы или вилки — сразу обновить «Дорожную карту» в том же коммите.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-10-06 · by: Codex Mac · baseline HEAD: 832ac341

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
Прежняя программа: Route B → Goal058, крыша `rh_of_real_zero_family_tendsto_centeredXi` (одна семья F: вещественные нули + F → Ξ).
Все звенья, статусы, последний доказанный результат и убитое — только в `docs/Codex/PAPER_CHAIN.md` (не дублировать здесь).
Коротко: закрыто на бумаге 8 из 14 (G2, G2b, hentire, G5 — Lean; G4 — статья CCM; hmode, hχ/hθ, selected-shell G3c — бумага);
ядро открыто: G1 (простота/чётность основного состояния) и G3 (tracking), плюс итоговая сборка; G3c и selected-shell crosswalk G4 проверены при HMODE/chi.

## Следующий шаг — полный CCM: рост отрицательного дна
После записанных тупиков source-transfer, direct localization и weak overlap выбран новый
условный потребитель на ТОЙ ЖЕ полной K_m, m=N, L=log m, исходный eventual schedule.
Активная ветка: полный CCM → SP → исключение off-critical zeros → RH; SP открыт.
1. Ответ10 и собственное усиление проверены: если есть ноль .5+delta+i gamma, delta>0, то
   lambda_min(K_m)≤−c m^delta/(log m)^(2delta) на каждой достаточно поздней ячейке.
   Это условная альтернатива, а не найденный ноль и не доказательство RH.
2. Достаточная открытая цель SP: для каждого eta>0 доказать
   lambda_min(K_m)≥−C_eta m^eta eventually. Старые G1/G3 этим не закрыты.
3. Ответ1 новой фазы проверен: causal A даёт равномерную оценку в норме прообраза,
   но carrier-wide возврат этой нормы убит верхней модой даже с D_arch.
   Для F=(I−R)Z, F=VM, Y=V*XV осталось оценить сверху
   D=M^-1[M,[M,Y]]M^-1: <f,Df>≤D_arch(f)+C_eta m^eta||f||² на полном V_m.
   Достаточно неограниченной подпоследовательности для каждого eta. Эта оценка OPEN.
   Ответ3 проверен: полный floor −cA−C sqrt(m)L³ exp(−.001(L/log L)^(1/3)), все моды и cross terms оплачены.
   Это выигрыш любой степени log, но exponent 1/2−o(1), не SP. Следующий шаг: signed Hilbert commutator против фактического diagonal slack.
4. Ответ4 проверен: на ker Lsrc (codim≤C m/L^5) floor −C L^10 log L; endpoint jets сохранены.
   При r≥2epsilon точный regular block положителен; остаётся actual Schur размерности≤C m/L^5.
   Ответ5 проверен: полный high-zero tail при T=mL² имеет norm≤3e6/sqrtL; старый jet-majorant убит.
   Endpoint-only блок точного Schur положителен; его coupling сохранён. Остался знак low off-line rows.
   Двусторонний sandwich даёт faithful Z(s)=L0(G_low+sI)^-1 L0*; Z(C_eta m^eta)≤I OPEN.
   Ответ6: fixed shifted-xi observation lift и gamma-neutralized positive kernel убиты в точной форме.
   Своя проверка: exceptional-only Hardy defect уже RH-equivalent; norm-transfer STALLED.
   Вопрос7: прямой signed relative-form estimate совместных d,h из одной Phi, с полным Schur coupling.
   Доказательства: `SHIFTED_XI_KERNEL_AUDIT_2026-10-06.md`, `HARDY_DEFECT_OWN_ATTEMPT_2026-10-06.md`.
Доказательства, один независимый проход и решение о смене фазы:
`../routeB_bus/source_observability_2026-09-28/NEGATIVE_BOTTOM_GROWTH_AUDIT_2026-10-06.md`.
Никаких предположений RH, positivity, polynomial gap или missing overlap.

## Прошка
По запросу владельца 06.10: конкретный U=min Rayleigh span{c(G),c(G'')} и нечётный secular sign
остаются OPEN. Для m=8 строго сертифицировано нечётное R<U; m=12,16 пока численные.
Конечный сертификат не опровергает хвост. Прошка дал явный нечётный upper envelope B_m,
e^(Cm/log m) B_m→0 для каждого C>0; сравнение U_m>B_m на неограниченной исходной семье OPEN.
Пакет, воспроизводимый probe и точный незакрытый шаг: `../routeB_bus/source_observability_2026-09-28/ODD_TRIAL_SIGN_2026-10-06.md`.
- Старый Missing T7 Lemma завершён **10/10**, новых вопросов туда нет. Нижний overlap не получен.
- Новый [Proof of CCM Growth](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ac54396-d878-83eb-ae29-35d2bdd2262b): **6/10 получен и проверен; 7/10 отправлен**: fixed-positive norm transfer STALLED; возврат к совместному signed d,h arithmetic estimate. SP OPEN. См. `SHIFTED_XI_KERNEL_AUDIT_2026-10-06.md` в той же bus-папке. Ждать ответ в том же чате, не пересылать.
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
- Сверка 06.10: мост projected trial→Ξ на |Im z|<1/2 уже записан условно на принятое PAPER HMODE; проверен source crosswalk, не свежая Lean-сборка. См. `../routeB_bus/source_observability_2026-09-28/CRITICAL_STRIP_PROJECTION_SOURCE_AUDIT_2026-10-06.md`; ground tracking G3 остаётся открыт.
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
