# STATUS: SOURCE_WRITTEN
```yaml
ARTIFACT_TYPE: PAPER_SOURCE_RECORD
JUDGE_VERDICT: false
DATE: 2026-09-20
AUTHOR: Proshka
BASE_HEAD: 6120768a1eef9ce6eef1b64c358b23b76d68948f
BRANCH: rh_clean
ACTION_SCOPE: OWNER_REQUESTED_PUBLICATION_OF_NAMED_PAPER_RESULT
SCOPE: ABSTRACT
VERIFIER: PAPER
PAPER_RESULT: CONDITIONAL_IMPLICATIONS_WITH_COMPLETE_PROOFS
NEW_PAPER_RESULT: QUANTITATIVE_SCHUR_FLOOR_AND_DIRECTIONAL_BUDGET
CONCRETE_CCM_COERCIVITY: NOT_PROVED
COFINAL_PROJECT_CERTIFICATE: NOT_PRODUCED
TRANSPORT_FINDING: SOURCE_LOCKED_REQUEST_BINDING_MISSING
PRODUCTION_THEOREM_TRANSACTION: HOLD
LEAN_PATHS: []
LEAN_CHECKED: false
EXPECTED_AXIOM_PROFILES: {}
CLOSES: []
OPENS: []
CATALOG_SUPPLIER_ADDED: false
ROUTE_PROMOTION: false
RH_CLAIM: false
BUS_010_POLICY: VOID
STATE_FILES_CHANGED: false
SOURCE_ATTACHMENT_SHA256: 71ac3564b8cabe6a5ff0596290dcba8d9a2327f5faf806c1c833c844e23624c8
PROTOCOL_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
SUPPLIER_CONTRACT_BLOB: b0d4ba335afca2a6cb38fb22d599bf3941e7cfe9
EXACT_CHECK_SCRIPT: docs/routeB_bus/proshka/ccm_directional_resolvent_2026-09-20/exact_checks.py
EXACT_CHECK_SCRIPT_BLOB: 8059d7f0c97801cfe22948038a5ca630076451eb
EXACT_CHECK_SCRIPT_SHA256: 2eb55a71e11a5f33dece0b259776e256243a05fa82f04d4c39284fc790037c39
REGISTRATION_UTC: 2026-09-20T10:59:29.181045+00:00
REGISTRATION_SHA256: b970e03665961c086e28611621c3123beaac4cd8c3a4e1681c67207f68e8ed22
EXACT_CHECK_STDOUT_SHA256: 845bdc879e7b5a3097692f730f9f3c9e06e2d6705c966c047c3feced5187c63f
EXACT_CHECK_EXIT_CODE: 0
EXACT_CHECK_GROUPS_PASSED: 13
VERIFICATION_HANDOFF:
  WORKDIR: REPOSITORY_ROOT
  COMMAND: uv run --no-project --with sympy==1.14.0 python docs/routeB_bus/proshka/ccm_directional_resolvent_2026-09-20/exact_checks.py
  EXPECTED_FINAL_LINE: ALL_CHECKS_PASSED; PROJECT_C_REMAINS_OPEN; LEAN_NOT_RUN
  CHANGES_IF_SUCCESSFUL: ALGEBRAIC_CONTROLS_REPRODUCED_ONLY
  KERNEL_GATE: NOT_RUN_NO_LEAN_SOURCE
NEXT_LOAD_BEARING_GAP: SOURCE_DEFINED_CCM_COMPRESSED_POSITIVITY_AND_WEIGHTED_RESIDUAL
GAP_NAME_IS: PRIOR_REVIEW_DIAGNOSTIC_NOT_CATALOG_DECLARATION
```

## 1. Что именно записано

Прямой запрос владельца: проверить доказательство и сразу сохранить результат
на GitHub. Этот файл публикует бумажный результат из приложенного
`PROSHKA_CCM_COERCIVITY_REPAIR_2026-09-20.md`, с самостоятельной повторной
проверкой и количественным продолжением его блочного разложения. Исходный
файл не редактировался; его SHA-256 указан выше. Старые зарегистрированные
предсказания не пересчитываются задним числом.

**Это не доказательство оценки C для конкретного проектного оператора.**
Сам оператор, его метрика, семейство параметров и потребитель не привязаны
байт-точным запросом production-фазы. Это транспортная граница, не утверждение,
что нужных определений нет в репозитории. Очередь и чужие OPEN-маркеры не
сканировались; другая задача не выбиралась. Публикация бумажного результата
не запускает Lean-транзакцию и не снимает эту границу.

`CLOSES/OPENS` пусты именно для **каталога проекта**. Ни один его поставщик
не объявляется закрытым. Новые выводы ниже относятся к абстрактной лемме.
В среде этого прохода отсутствуют исполняемые `lean` и `lake`; ядро не запускалось.

Источники: приложенный файл с указанным хешем; актуальные
`docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` и
`docs/routeB_bus/SUPPLIER_CONTRACT.md` с указанными blob. Брифинг и прошлые
сообщения не используются как доказательство конкретной положительности.

## 2. Объекты и кванторы

[ABSTRACT | PAPER] Пусть H — конечномерное комплексное гильбертово пространство,
W=W* — самосопряжённый оператор, ||v||=1. Скалярное произведение
сопряжённо-линейно по первому аргументу и линейно по второму.
Ортогональность, нормы и сопряжения относятся к одной и той же метрике.
При неортонормированном базисе матрица Грама не выбрасывается.

Положим

\[
\mu=\langle v,Wv\rangle,\qquad
P=I-|v\rangle\langle v|,\qquad
r=(W-\mu I)v,\qquad
B=\left.P(W-\mu I)P\right|_{v^\perp}.
\]

Тогда r перпендикулярен v. Все обратные операторы B ниже действуют на
v-перпендикулярном пространстве, не на H целиком.

Предположение C в этом конечномерном утверждении:

\[
B\succ0
\quad\Longleftrightarrow\quad
\exists G>0\ \forall y\perp v:\quad
\langle y,(W-\mu I)y\rangle\ge G\|y\|^2.
\]

Ни равномерная по всем параметрам положительная константа, ни конкретная
проектная C здесь не предполагаются доказанными.

## 3. Точная реконструкция нижнего состояния

[ABSTRACT | PAPER] **Теорема A.** При предположении B>0 существует единственное
число delta>=0, удовлетворяющее

\[
\delta=\langle r,(B+\delta I)^{-1}r\rangle.\tag{1}
\]

Для u=(B+delta I)^(-1)r справедливы

\[
\lambda_{\min}(W)=\mu-\delta,\qquad
\xi=\frac{v-u}{\sqrt{1+\|u\|^2}},\tag{2}
\]

нижнее собственное значение простое, и

\[
\sin\angle(v,\xi)
=\frac{\|u\|}{\sqrt{1+\|u\|^2}}
\le\frac{\eta}{\sqrt{1+\eta^2}},\qquad
\eta=\|B^{-1}r\|.\tag{3}
\]

### Доказательство

В разложении H=Cv плюс v-перпендикулярное пространство имеем

\[
W-\mu I=\begin{pmatrix}0&r^*\\r&B\end{pmatrix}.
\]

Функция f(t)=t-<r,(B+tI)^(-1)r> непрерывна при t>=0, и

\[
f'(t)=1+\|(B+tI)^{-1}r\|^2>0.
\]

Пусть s0=<r,B^(-1)r>. Тогда f(0)=-s0<=0. Из спектрального разложения B
следует (B+s0 I)^(-1)<=B^(-1), поэтому f(s0)>=0. Непрерывность и строгая
монотонность дают единственный корень delta в [0,s0]. При r=0 он равен нулю.

Для x=alpha v+y, y перпендикулярен v, раскрытие скобок даёт

\[
\begin{split}
\langle x,(W-\mu I+\delta I)x\rangle
={}&\langle y+\alpha u,(B+\delta I)(y+\alpha u)\rangle\\
&+|\alpha|^2\bigl(\delta-\langle r,(B+\delta I)^{-1}r\rangle\bigr).
\end{split}
\]

Последнее слагаемое равно нулю по (1). Следовательно,

\[
\boxed{\langle x,(W-(\mu-\delta)I)x\rangle
=\langle y+\alpha u,(B+\delta I)(y+\alpha u)\rangle\ge0.}\tag{4}
\]

Поскольку B+delta I положительно определён, равенство достигается ровно
при y=-alpha u. Ядро сдвинутого оператора одномерно и порождено v-u.
Это доказывает (2), нижний характер собственного значения и его простоту,
не предполагая заранее знания истинного нижнего состояния.

В собственном базисе B, с b_k>0,

\[
\|u\|^2=\sum_k\frac{|r_k|^2}{(b_k+\delta)^2}
\le\sum_k\frac{|r_k|^2}{b_k^2}=\|B^{-1}r\|^2.
\]

Так как u перпендикулярен v, формула угла следует из (2); функция
q/sqrt(1+q^2) возрастает при q>=0. Получено (3).

[ABSTRACT | PAPER] **Чётность.** Дополнительно пусть J — унитарная инволюция,
JW=WJ и Jv=v. Тогда JP=PJ, Jr=r и J коммутирует с B и его резольвентой
на v-перпендикулярном пространстве. Поэтому Ju=u и Jxi=xi.
Одна простота плюс коммутирование с J без выбора чётного кандидата
не выбирают знак чётности.

[ABSTRACT | PAPER] **Граница знакового вывода.** Тождество (4) не доказывает
свою предпосылку B>0 и не доказывает W>=0. Последнее требует mu-delta>=0.
Из delta<=s0 следует лишь нижняя оболочка lambda_min(W)>=mu-s0.
Если эта нижняя оболочка отрицательна, это не сертификат отрицательности W.

## 4. Количественный блочный сертификат: новый бумажный шаг

[ABSTRACT | PAPER] **Теорема B.** Разложим v-перпендикулярное пространство
на две ортогональные части и запишем

\[
B=\begin{pmatrix}A&C\\C^*&D\end{pmatrix},\quad
S=A-CD^{-1}C^*.
\]

Пусть независимо доказаны три оценки

\[
D\succeq dI,\quad S\succeq sI,\quad
\|D^{-1}C^*\|\le k,\qquad d,s>0,\quad k\ge0.\tag{5}
\]

Тогда для всех x в этом пространстве

\[
\boxed{\langle x,Bx\rangle\ge
G\|x\|^2,\qquad G=\frac{\min(s,d)}{(1+k)^2}>0.}\tag{6}
\]

Для r=(r_h,r_t) положим

\[
q=D^{-1}r_t,\quad p=r_h-Cq,\quad H_0=\|p\|/s.
\]

Направленная ошибка удовлетворяет

\[
\boxed{\|B^{-1}r\|\le E,
\qquad E^2=H_0^2+(\|q\|+kH_0)^2.}\tag{7}
\]

### Доказательство

Обозначим K=D^(-1)C*. Прямое раскрытие скобок даёт тождество Шура

\[
\langle(h,t),B(h,t)\rangle
=\langle t+Kh,D(t+Kh)\rangle+\langle h,Sh\rangle.
\]

При m=min(s,d) правая часть не меньше m(||h||^2+||t+Kh||^2).
Для z=(h,t+Kh) имеем (h,t)=z+(0,-Kh), поэтому

\[
\|(h,t)\|\le\|z\|+k\|h\|\le(1+k)\|z\|.
\]

Это доказывает (6), включая квантор по всем x.

Блочное решение B w=r имеет точный вид

\[
w_h=S^{-1}p,\qquad w_t=q-Kw_h.
\]

Действительно, второе блочное уравнение даёт w_t, а первое после подстановки
становится S w_h=p. Из S>=sI получаем ||w_h||<=H0 и
||w_t||<=||q||+kH0. Ортогональность блоков даёт (7).

**Что изменилось:** получены явные формулы для запаса и направленной ошибки
из трёх блочных оценок. Сохраняется сокращение в p=r_h-CD^(-1)r_t.
Мы не заменяем его заранее суммой норм отдельных слагаемых.

**Что не изменилось:** (5) ещё нужно доказать для настоящих проектных блоков.
Определить s,d через неизвестные наименьшие собственные значения и назвать
это независимым сертификатом нельзя. Это формулы для использования
сертификатов, а не способ получить их без анализа источника.

## 5. Проверяемые контрпримеры к чрезмерным выводам

[ABSTRACT | PAPER] **Худшая щель не обязательна для сближения.** При 0<eps<1

\[
W_\varepsilon=\begin{pmatrix}0&0&\varepsilon\\
0&\varepsilon^3&0\\\varepsilon&0&1\end{pmatrix},\quad v=e_1.
\]

Здесь mu=0, B=diag(eps^3,1), r_perp=(0,eps). Поэтому

\[
\|r\|/G=\varepsilon^{-2}\to\infty,\qquad
\|B^{-1}r\|=\varepsilon\to0.
\]

Корень (1) равен (sqrt(1+4eps^2)-1)/2, и (2) даёт xi->v.
При J=diag(1,-1,1) состояние чётно. Это модель, не проектный оператор.
Она опровергает обязательность малого отношения ||r||/G, а не достаточность.

[ABSTRACT | PAPER] **Малая невязка не доказывает C.** W=diag(0,1), v=e2,
mu=1 дают r=0, но на v-перпендикулярном пространстве B=-1. Для y=e1
точная верхняя граница U=<y,By>=-1<0. Кандидат не нижний.
При J=diag(-1,1) кандидат чётен, а истинное нижнее состояние нечётно.

[ABSTRACT | PAPER] **Произвольный сдвиг не даёт простоты.** Для
W=diag(2,1,1), v=e1 и сдвига mu0=0 сжатие равно I_2, но нижнее
собственное значение имеет кратность два. Если источник фиксирует mu0,
то при a=<v,Wv>-mu0 нужно учитывать B=B0-aI и r=r0-av.
Менять сдвиг без этой поправки нельзя.

[FINITE_CELL | PAPER] **Связь блоков нельзя выкидывать.** A=D=1, C=2 дают
положительные диагональные блоки, но S=-3. Для x=(1,-2) получаем
x* B x=-3. Контроль, который принимает такую матрицу только по A,D,
заведомо неисправен. Это не контрпример к проектной C.

## 6. Передача ошибки через преобразование

[ABSTRACT | PAPER] Пусть для каждого j заданы изометрическое вложение
U_j:H_j->L2([-L_j,L_j]), L_j>0, и

\[
(\mathcal F_j w)(z)=\int_{-L_j}^{L_j}(U_jw)(t)e^{-izt}\,dt.
\]

Для |Im z|<=sigma неравенство Коши--Буняковского даёт

\[
|\mathcal F_jw(z)|\le M_{\sigma,j}\|w\|,\qquad
M_{\sigma,j}=\begin{cases}
\sqrt{\sinh(2\sigma L_j)/\sigma},&\sigma>0,\\
\sqrt{2L_j},&\sigma=0.
\end{cases}
\]

Фаза xi_j выбрана по (2), так что <v_j,xi_j>>0. При theta=angle(v_j,xi_j)
имеем ||xi_j-v_j||^2=2(1-cos theta)<=2 sin^2 theta. Следовательно,
для ненулевых c_j, целевых T_j и любого компакта K в указанной полосе

\[
\boxed{\sup_K|c_j\mathcal F_j\xi_j-T_j|
\le\sqrt2|c_j|M_{\sigma,j}\eta_j+\tau_{j,K},}\tag{8}
\]

где tau_jK=sup_K|c_j F_j v_j-T_j|. Вместо eta_j можно использовать E_j
из (7). Это треугольное неравенство с явной константой, не бесплатный
перенос сходимости через растущее преобразование.

[COFINAL_FAMILY | CONDITIONAL] Для проектного применения нужны независимые
доказательства (5) и |c_j| M_sigma,j E_j->0, tau_jK->0 на согласованной
последовательности параметров для каждого требуемого компакта. Точная
сигнатура `FiniteGroundTransformToCCMTrialLocallyUniform`, нормировка
и отождествление объектов должны быть привязаны к исходнику.
Ни этот потребитель, ни конечный->бесконечный переход здесь не закрыты.

## 7. Регистрация и фактические проверки

Предсказания записаны **до исполнения** в `registration.json` в
2026-09-20T10:59:29.181045+00:00. Это новые P1--P5 данного прохода,
не изменение ставок прошлого артефакта.

| Предсказание | Фактическая проверка | Судьба |
|---|---|---|
| P1: реконструкция и квадратное тождество сохраняют знак/сопряжение | Рациональная комплексно-эрмитова матрица; точное собственное уравнение; полином по произвольным комплексным координатам | CONFIRMED |
| P2: ложный знак и потеря связи блоков отвергаются | Ненулевая невязка для v+u; U=-3 при пропущенном дополнении Шура | CONFIRMED |
| P3: направленная ошибка сходится при расходящемся грубом отношении | Символьное семейство eps, точные радикалы и пределы | CONFIRMED |
| P4: блочные формулы дают корректный контроль | Комплексное символьное тождество; рациональная нижняя оболочка G=4/9; направленный бюджет | CONFIRMED |
| P5: прежние чрезмерные импликации ложны | Нулевая невязка верхнего состояния; нечётный ground state; кратность два при произвольном сдвиге | CONFIRMED |

Исполнение: Python с SymPy 1.14.0, точная арифметика без floating-point
собственных значений. Завершилось с exit code 0; 13 групп проверок прошли.
Полный вывод находится в `exact_checks.stdout`, скрипт — в `exact_checks.py`.

**Символьные контроли не заменяют общие доказательства §§3--4 и не являются
Lean-проверкой.** Ни одна проверенная модель не выдана за ячейку Route B.
Намеренно неправильные варианты обнаружены, а не включены в доказательство.

## 8. Маршруты и эпистемическая граница

[ABSTRACT | PAPER] **R1 — направленная резольвента:** сохранить B^(-1)r,
не заменяя его худшей скалярной щелью. Стоимость алгебры мала;
диагностическая сила высока для выявления потерь от направления невязки.
Стоимость конкретной семейной оценки без определения B неизвестна.

[ABSTRACT | PAPER] **R2 — конечный блок и хвост:** доказать (5) независимо,
использовать (6)--(7). Алгебра мала; решающая сила высока, если уже есть
сертификаты хвоста и небольшого эффективного блока. Риск — спрятать исходную
трудность в неизвестной положительности S. Выбран R2 как конкретизация
положительного входа R1; численное масштабирование не назначено.

[COFINAL_FAMILY | CONDITIONAL] **DISCRIMINATOR:** для привязанного B нужна
нижняя оболочка L>0 на всём v-перпендикулярном пространстве либо точный
свидетель с верхней оболочкой U<0. Нулесодержащий интервал не решает вопрос.
Точный ненулевой нулевой вектор опровергает строгий запас, но не доказывает
отрицательности PSD. Для точного нуля требуются анализ ядра/факторизация,
а не обещание, что повышение точности обязательно решит знак.

```yaml
DOWNSTREAM_CONSUMER: FiniteGroundTransformToCCMTrialLocallyUniform
CONSUMER_SOURCE_STATUS: NAME_FROM_PRIOR_REVIEW_EXACT_SIGNATURE_NOT_BOUND
ACTUAL_CONSUMER_REQUIREMENT: SOURCE_CORRECT_NORMALIZED_LOCAL_UNIFORM_TRANSFORM_APPROXIMATION
ORIGINAL_REQUESTED_OBJECT: CONCRETE_C_AND_RESIDUAL_OVER_WORST_GAP_RATE
ORIGINAL_OBJECT_IS:
  CONCRETE_C_NECESSARY_FOR_EVERY_ROUTE: UNKNOWN
  WORST_GAP_RATE_NECESSARY: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - B_positive_and_weighted_directional_inverse_residual_tends_to_zero_plus_trial_error_imply_equation_8
  - independent_block_certificates_5_imply_floor_6_and_directional_budget_7
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: EXPLICIT_BLOCK_BUDGET_FOR_PREVIOUS_DIRECTIONAL_INTERFACE
MATHEMATICAL_NOVELTY_CLAIM: false
ROUTE_FAMILY_DEATH: false
PROJECT_THEOREM_REFUTED: false
REOPEN_TRIGGER:
  - byte_exact_request_binds_W_v_metric_shift_parameters_transform_and_consumer
  - source_bound_independent_certificates_for_D_S_and_D_inverse_C_adjoint
  - proof_of_consumer_weighted_cofinal_error_budget
```

Нет доказательства смерти маршрута. Опровергнуты только конкретные
абстрактные импликации из §5, не семейство проектных операторов.

## 9. Закрытие прохода и передача

**Уменьшилось:** бумажный интерфейс получил явные блочные формулы для G и E;
все шаги реконструкции, чётности и преобразования выписаны с предпосылками.
**Не уменьшилось:** число открытых поставщиков конкретной C. Это не
проектный PROOF_PROGRESS и не повод повышать статус Route B.

Нельзя повторять: вывод C из малой невязки; выбор чётности одной простотой;
подмену проектного W тестовой матрицей; утверждение обязательности ||r||/G;
превращение положительности дополнения Шура в доказанный факт по определению.

```yaml
iteration:
  target: audited_paper_directional_resolvent_and_block_certificate
  status: PROGRESS
  progress_class: REPRESENTATION_PROGRESS
  project_supplier_closure_count: 0
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SOURCE_DEFINED_CCM_COMPRESSED_POSITIVITY_AND_WEIGHTED_RESIDUAL
  invariant_learned: retain_source_metric_shift_coupling_and_transform_rate
  forbidden_future_move: publish_another_conditional_bridge_as_concrete_C
  next_decisive_test: source_bound_signed_compression_or_Schur_certificate
  route_score: 3
```

**Одна CODEX DIRECTIVE — привязать текущую C, не выбирать новую задачу.**
Подготовить один байт-точный `.txt`-запрос с commit, точными W/v/метрикой/сдвигом,
параметрами, преобразованием и сигнатурой потребителя. До нового имени
поставщика проверить каталог через `./ask.sh`. Для выбранного разложения
указать существующие доказательства (5) либо точное первое отсутствующее
неравенство; не предполагать их. Успех — все объекты разрешаются на одном pin
и бюджет (8) соответствует неизменённому потребителю. Неуспех —
`SOURCE_BINDING_MISSING` с конкретным отсутствующим полем.
Эта директива записана, не отправлена исполнителю; Lean-запуск не назначен.

**Квитанция записи.** Этот SOURCE RECORD и три файла проверок должны находиться
в одном коммите с префиксом `[Proshka]`. Его SHA сообщается в ответе владельцу
после подтверждённой записи: нельзя поместить само-хеширующий SHA внутрь
того же файла до создания коммита. Все пути находятся в
`docs/routeB_bus/proshka/ccm_directional_resolvent_2026-09-20/`.
Ни Lean, ни состояние маршрута, ни протокол, ни чужие вердикты не изменяются.

Воспроизведение из корня репозитория:

```bash
uv run --no-project --with sympy==1.14.0 python docs/routeB_bus/proshka/ccm_directional_resolvent_2026-09-20/exact_checks.py
```

В команде нет переменных или заполнителей. Успех воспроизводит только
алгебраические контроли; не меняет статус на LEAN_PROVED или на доказанную C.

Для контекста, не как импорт доказательства: метод Фешбаха--Шура с
уравнениями неподвижной точки для собственных значений и собственных функций
описан в G. Dusson, I. M. Sigal, B. Stamm, *The Feshbach-Schur map and
perturbation theory*, arXiv:2105.02058 (2021), DOI 10.4171/ECR/18-1/5.
Проверены библиографическая запись и аннотация первоисточника. Математические
выводы выше доказаны здесь; заявление об открытии нового метода не делается.
