# STATUS: TRY_ROUND10_EXACT_MOBIUS_PRIME_PACKETS_B

```yaml
STATUS: TRY_ROUND10_EXACT_MOBIUS_PRIME_PACKETS_B
OPERATIVE_CLASS: TRY_ROUND10_EXACT_MOBIUS_PRIME_PACKETS_B
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_CONSTRUCTION_AND_TESTS
DATE: 2026-11-06
REQUEST_COMMIT: 1c870b51b8342a8c9a4fa68e6b0f68fa9df1f6b2
REQUEST_BLOB: 0551784f7af091a4d8072d8d5e7bca2125bfd35b
SUMMARY_BLOB: df730a5d44e5aee76b02e9c1532e4970d593f942
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_R8_COMMIT: 70c4e6b097bc714689fb9226aeaea12a46127c95
INPUT_R8_BLOB: e0c22e09de31ce8c3ee37e8c53343477168b2063
INPUT_R9_COMMIT: b5fc098b7727bded490c4e46969d6379afa90307
INPUT_R9_BLOB: bc15928e8da77401e6fc15514cb6fc6f2c1932ee
OBSERVED_INBOX_HEAD: b5fc098b7727bded490c4e46969d6379afa90307
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND10_2026-11-06_B.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: TRUE_MOBIUS_CORE_BOUND_ON_AN_UNBOUNDED_SUBSET_OF_S
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: EXACT_EULER_PACKETIZATION_AND_DUAL_POSITIVE_MAJORANT
ROUTE_SCORE: 3
```

Ы. Отдельный freeze, не редактируется. Выбор сделан после чтения брифа, сводки, R8/R9 и первичного алгебраического анализа; ниже регистрируются проверки до законченного доказательства и вычислений. Полные локальные копии R8/R9 совпали с указанными Git blobs. Отчёт a180142f прочитан: измерена голова на S, но полное H на S не вычислялось; утверждение сводки о малости shoulder на S не импортируется.

<!-- FROZEN_R10_B_BEGIN -->
## S10-B: неизменная mu, точные prime-пакеты и цена их разъединения

[ABSTRACT / COFINAL_FAMILY | CONDITIONAL: целевой bound не предполагается.]

Сохраняются r_n(k)=(k mod n)/n, w_k=1/[k(k+1)], L=log N, K_N=ceil(N^(3/2)), R_N=1+sum_(2<=n<=N)mu(n)(1-log n/L)r_n, H_N=sum_(k<K_N)w_k R_N(k)^2 и настоящее S из R8. Один и тот же ряд mu используется для ВСЕХ N. Ни значения mu, ни mu*1=epsilon, ни исходная полная форма не изменяются.

Новый кандидат: для квадратсвободного P разбить каждый squarefree n единственным образом n=a*d, a|P, (d,P)=1. Внутри каждого d-пакета сложить ТОЧНО все члены mu(a)(1-log(ad)/L)r_(ad), ad<=N. Между пакетами оставить настоящие множители mu(d). Разрешено брать P=P_N с P_N<=N^(1/4), включая фиксированный P и растущее число обработанных простых. Пакетизация — перегруппировка, не изменение коэффициентов. Построить конечный Gram пакетов, его положительную диагональную часть и точный подписанный межпакетный остаток.

Основная попытка: оценить настоящий H_N, используя полную свёртку и согласованность префиксов. Если это не получится, проверить следующий ТОЧНО ОПРЕДЕЛЁННЫЙ класс методов: все положительные пакетно-разделённые квадратичные мажоранты этого Gram, справедливые для любых амплитуд пакетов. Внутрипакетные сокращения и произвольные веса разрешены; межпакетные подписанные взаимодействия в сертификате отсутствуют. Допускается произвольный совместный блок для постоянной строки и пакета d=1. Это лишь класс оценок, не все методы доказательства RH.

Проверяемая необходимая цена любой такой мажоранты на НАСТОЯЩЕМ векторе амплитуд mu(d) не меньше суммы норм настоящих d-пакетов. Искать строгую расходящуюся нижнюю огибающую этой цены, равномерно по P<=N^(1/4). При успехе это obstruction метода с неизменённой mu, а НЕ lower bound истинного H_N. Нельзя спутать эти две величины.

### Предсказания и судьи

P1. Точное разложение по n=a*d сохранит R_N построчно и все divisor-identities. R9-поправка должна отказать именно в mu*1=epsilon, а не в PSD.

P2. На строках k<d полный пакет имеет явный линейный профиль через phi(P)/P и sum_(p|P)log p/(p-1). Это должно дать ненулевую нижнюю цену даже после полного суммирования внутри пакета.

P3. Ожидается расходящаяся цена независимой оплаты: для фиксированного P порядка не меньше log N; при P<=N^(1/4) ожидается lower bound порядка log N/(1+log log N)^3 с явной универсальной константой. Это прогноз масштаба, не уже заявленная теорема. Проверить uniform squarefree-coprime counting, концы диапазонов и phi-bound; при провале не менять прогноз задним числом.

P4. Межпакетный остаток нельзя удалить из H_N. Новый объект должен дать точное H_N=D_N+J_N (либо с явно выделенным начальным пакетом); доказательство малости J_N+D_N не заменяется нижней ценой D_N. True-source bound может остаться OPEN.

P5. Скалярный отбор S не снимет obstruction, если нижняя цена доказана для каждого достаточно большого N. Для кривой проверяется её собственный exact periodization square; ordinary mu-словарь ей не приписывается.

Тесты после freeze: точные целочисленные проверки mu*1=epsilon и факторизации n=a*d; символические коэффициенты при log p в строках k<d; малые N=64,256,1024,4096 и squarefree P<=N^(1/4), дополнительно P=30 при N=10^6 только для подсчёта/профиля, без большого Gram. Плавающие нормы при двух точностях — только DIAG; успех или провал cofinal-теоремы решает PAPER-огибающая, не эта сетка. Отрицательный судья универсального шага: 2-by-2 Gram [[1,1],[1,1]] на векторе (1,-1); диагональная цена не равна норме суммы. Ни нули zeta, ни неизвестный знак A_m для построения не используются.

### K8A до проверки

DOWNSTREAM_CONSUMER: bounded actual H_N on an unbounded subset of S, then source-correct NB capture and RH.
ACTUAL_CONSUMER_REQUIREMENT: достаточно истинной (26) R8; packet-separable certificate не является обязательным.
ORIGINAL_REQUESTED_OBJECT: оценка для неизменной mu либо obstruction, сохраняющий точную mu, полную свёртку и coherence.
ORIGINAL_OBJECT_IS: UNKNOWN as necessary for RH; the tested separable certificate is NOT_NECESSARY.
KNOWN_WEAKER_INTERFACES: signed interpacket control, optimal NB coefficients, or another source-correct window lower bound with its proved receiver.
FAILURE_TYPE: UNRESOLVED before proof.
EPISTEMIC_STATUS: RESEARCH_DEBT for true H_N; no route-family death is assumed.
NOVELTY_AXIS: all internal prime-packet cancellations retained, actual coherent mu used as witness, uniform growing P allowed.
REOPEN_TRIGGER: a source estimate using signed interpacket coherence, or a defect in the proposed necessary-price lower bound.
<!-- FROZEN_R10_B_END -->
