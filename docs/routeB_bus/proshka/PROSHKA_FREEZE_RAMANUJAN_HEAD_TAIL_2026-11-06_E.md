# STATUS: TRY_RAMANUJAN_HEAD_TAIL_SOURCE_RETURN_E

```yaml
STATUS: TRY_RAMANUJAN_HEAD_TAIL_SOURCE_RETURN_E
OPERATIVE_CLASS: TRY_RAMANUJAN_HEAD_TAIL_SOURCE_RETURN_E
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_COMPLETED_PROOF_AND_TESTS
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_GO_JOINT_RAMANUJAN_HEAD_TAIL_CANCELLATION
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_D_COMMIT: 2bac098143d9e8968d4a0f16d700a3646906056e
INPUT_D_BLOB: 18e8cbeb850ec0b6fe5789eb96f2334b689dcd76
INPUT_GREEN_COMMIT: a337b335777c3912694fb058a68a019c47061ffe
INPUT_GREEN_BLOB: 692b10822320c76a8d2c9a82168bb5c35f124d4b
OBSERVED_INBOX_HEAD: 2bac098143d9e8968d4a0f16d700a3646906056e
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_RAMANUJAN_HEAD_TAIL_2026-11-06_E.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: TRUE_SOURCE_SIGNED_BALANCED_ENERGY_BOUND
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: EXACT_BOUNDARY_DIVISOR_COLLAPSE_AND_RAMANUJAN_BILINEAR_RETURN
ROUTE_SCORE: 3
```

Ы. Отдельный freeze; после коммита не редактируется. Предварительный аудит обнаружил возможные ошибки нормировки в D; они проверяются первыми, а не импортируются как доказанные. Старые закрытые файлы не изменяются. Никакие тесты этой спецификации ещё не выполнены.

<!-- FROZEN_HEAD_TAIL_E_BEGIN -->
## Неизменный источник и задача

[FINITE_CELL / COFINAL_FAMILY | CONDITIONAL для искомой оценки.]
Сохранить N>=3, L=log N, a_n=mu(n)log(N/n)/L (a_1=1), s_N=sum_(n<=N)a_n/n, q_1=1-s_N, q_n=a_n для n>=2. Истинный ток A_N(l)=sum_(n|l,n<=N)q_n; j_N(l)=1_(l=1)-A_N(l), d_N(l)=j_N(l)/l. Сохранить K(l,k)=min(l,k)*(1-|log((l+1)/(k+1))|/log 2)_+ и Z_N=d^*K d на 1<=l,k<=N^2. Голова l<=N, хвост l>N; полный cross-терм включает оба порядка. S — прежнее множество переходов настоящего линейного taper, не новый оптимизированный отбор.

Цель: точное полное c_q(l)c_r(k)-представление cross-терма и попытка совместной односторонней оценки полной Z_N. Отдельный bound для cross не выдавать за bound всей положительной формы. Не заменять фиксированный источник CRT-средним или независимыми амплитудами.

### Проверки и предсказания до тестов

P1. Коэффициент конечного Ramanujan-разложения divisor-свёртки должен содержать вес 1/d внутри суммы по кратным q. Проверить формулу D на N=2,l=1 и нормировку Green на одиночной координате l=k=2. При ошибке дать явную поправку в НОВОМ вердикте; D не редактировать.

P2. Опора kernel должна точно ограничить head-tail область полосой N<k<=2l<=2N. На этой полосе у k>N единственный делитель, превышающий N, — k; это должно дать полный tail-current через Lambda(k), mu(k) и s_N, без неизвестного divisor-tail. Границы целочисленного округления проверить отдельно.

P3. Ожидается точная конечная билинейная матрица в Ramanujan-координатах истинного A_N. Предыдущие h_N для одной усечённой Lambda могут не описывать полный A_N в хвосте. Нулевая частота, l=1 и вес 1/max(l,k) не должны исчезнуть.

P4. Попытаться извлечь новое совместное сокращение, сохраняя реальные mu. Никакой O(1) bound заранее не предполагается. Если останется та же арифметическая цена, назвать это отсутствием RH-sign progress, а не доказательством невозможности всех совместных методов.

P5. Проверить, может ли head-tail cross сам исправить произвольную энергию глубокой головы/дальнего хвоста. Судья — положительное блочное представление K и импульс вне полосы; отрицательный результат имеет только свой точный scope.

Конечные судьи после freeze: N=2,3,4,8,16,32 для точных log-prime векторов и всех l<=2N; N=8,16,32,64,128,256 для прямой билинейной суммы и независимой prefix/integral формы; 50 и 80 десятичных знаков при необходимости (DIAG, не ARB_INTERVAL). Обнуление логарифмического коэффициентного вектора — точный algebraic discriminator; small floating residual не сертификат. Большая cofinal сетка не запускается. Для нового нетривиального численного утверждения сначала отдельная регистрация.

### K8A

DOWNSTREAM_CONSUMER: RH через bounded source-correct NB subsequence и pinned Green receiver.
ACTUAL_CONSUMER_REQUIREMENT: ограниченность всей Z_N на неограниченной части S либо другой доказанно достаточный source-bound.
ORIGINAL_REQUESTED_OBJECT: joint Ramanujan head-tail cancellation с точной границей.
ORIGINAL_OBJECT_IS: UNKNOWN как необходимый механизм RH; само разложение не обязательно.
KNOWN_WEAKER_INTERFACES: полный signed Gram, optimal NB coefficients, source-correct prime-only/window receiver.
FAILURE_TYPE: UNRESOLVED_BEFORE_TESTS.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: точный полный boundary-current, не только конечная Lambda и не новое имя прежней эквивалентности.
REOPEN_TRIGGER: joint source inequality либо строгий дефект в импортированном возврате.
<!-- FROZEN_HEAD_TAIL_E_END -->
