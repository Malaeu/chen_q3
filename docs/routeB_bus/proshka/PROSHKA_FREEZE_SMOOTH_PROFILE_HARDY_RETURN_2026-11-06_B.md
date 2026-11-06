# STATUS: TRY_SMOOTH_PROFILE_HARDY_RETURN_B

```yaml
STATUS: TRY_SMOOTH_PROFILE_HARDY_RETURN_B
OPERATIVE_CLASS: TRY_SMOOTH_PROFILE_HARDY_RETURN_B
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_TESTS_AND_COMPLETED_PROOF
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_PROVE_RH_AFTER_MOBIUS_RECIPROCITY
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_VERDICT_COMMIT: aabf1a70584f4151a27f8d99a23d47e33da34b9a
INPUT_VERDICT_BLOB: f568cd803251872ae9f7a5c7f1058abf03d62170
OPTIMAL_DIAG_COMMIT: ec1e2e961e07899824890db7f5fe39a89f2aa795
SMOOTH_DIAG_COMMIT: cffc56a52e0cf415c51d3a1a03c026d623e3d50c
SMOOTH_REPORT_BLOB: e32f725326ec74c4269af613dc4f8ee81a9a564d
OBSERVED_INBOX_HEAD: aabf1a70584f4151a27f8d99a23d47e33da34b9a
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_SMOOTH_PROFILE_HARDY_RETURN_2026-11-06_B.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: SOURCE_SPECIFIC_CONTROL_OF_THE_FULL_NB_ERROR
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: DISCRETE_CHAIN_RULE_AND_WEIGHTED_ENERGY
ROUTE_SCORE: 3
```

Ы. Отдельный freeze, после записи не редактируется. Предварительная алгебра выполнена; приведённые ниже идентичности являются кандидатами до проверки знаков, скачков, концов и независимых конечных судей. Новые данные читаются как DIAG. У них профили переобучаются при каждом N, raw a_1=1 не равен автоматически P(1), и улучшение головы сопровождается ростом плеча. Это не cofinal-оценка.

<!-- FROZEN_HARDY_B_BEGIN -->
## S: вернуть дискретный trace через его настоящие скачки

Сохраняются r_n(k)=(k mod n)/n, w_k=1/[k(k+1)], R=1+sum_(n=2)^N a_n r_n, E=sum w_k|R(k)|^2. Сначала вещественные a_n; общую комплексную форму не утверждать без поляризации. Всегда raw a_1=1. Определены s=sum a_n/n, u=sum a_n log(n)/n, q_1=1-s, q_n=a_n для n>=2, b=1+(sum a_n-s)/2. Тогда sum q_n/n=0. F=sum(q_n/n)B_1(nx)+sin(2pi x)/pi с midpoint B_1. Старый точный возврат E=2b(1+u)-s-pi L_N(F) сохраняется.

Кандидат нового положительного объекта: I_N=int_0^1 F(x)^2/sin^2(pi x) dx. Использовать точную цепную формулу для функции с конечными скачками: jump(F^2)=2 F_mid jump(F), а не ложное правило с односторонним F. Производная F между скачками равна sum q_n+2cos(2pi x). Ожидаемый возврат — E=(pi^2/2)I_N-(1+u). Он должен быть доказан с нулевыми endpoint-платами и независимо проверен на n=2 и общих рациональных коэффициентах. Если неверен, записать FATAL/MISS и не ремонтировать прогноз задним числом.

Для гладких профилей a_n=mu(n)P(log(N/n)/log N), n>=2, P(0)=0, построить точное представление как signed superposition прежних линейных taper по меньшим префиксам. Не подменять signed superposition выпуклым средним. Оценить доступные полюсные/граничные члены для P в C^2 или P' абсолютно непрерывной. Истинная цель — source-derived upper bound для I_N либо другого полного receiver, не только малая unweighted Fourier-норма.

### Предсказания до проверок

P1. Midpoint Stieltjes-цепное правило даст точное weighted-energy равенство выше для каждого конечного вещественного набора коэффициентов. Рациональный aliasing останется совместим с этим: правило связывает sampler с той же F и её скачками, не с произвольным L2-входом.
P2. Профильная гладкость по log n не устраняет разрывы F по x. Граничная нормировка P(1) и raw a_1 должны быть оплачены явно. Signed superposition даст перенос известных линейных Fourier-bounds с константой через |P'(0)|+int|P''|, но не бесплатный NB-bound.
P3. Для фиксированного нормированного гладкого P часть weighted energy, удалённая от x=0,1, оценивается существующей L2-малостью. Неизвестность должна локализоваться в сжимающихся граничных слоях, если новый exact return подтвердится. Нельзя называть такую локализацию доказательством ограниченности слоя.
P4. Полиномы низкой степени, переоптимизированные при каждом N, пока не являются единым арифметическим поставщиком. Скалярная перенормировка объясняет часть finite-N выигрыша через exact Hilbert projection; это проверить без асимптотических догадок.
P5. Попытка доказать RH может остановиться на новом source-specific endpoint bound. В этом случае дать точные константы доказанной части и честно указать, получен ли новый RH-sign bound. Общий all-input запрет не объявлять запретом истинной F.

Судьи: N=2,3,4,8,16; отдельный rational random-pattern coefficient vector; log taper, P=x^2, P=2x-x^2, P=(3x-x^3)/2, и ненормированный P=2x. Проверять complete cotangent return, weighted integral с разбиением во всех rational jump-points, profile superposition и boundary coefficients. Десятичные сравнения при 40 и 70 знаках — DIAG, не интервальная сертификация. Алгебраические jumped-chain identities проверяются точно; любые near-zero значения получают analytic discriminator. Большой NB-grid не требуется.

### K8A

DOWNSTREAM_CONSUMER: источник-корректный NB capture, затем RH или буквальный A_m.
ACTUAL_CONSUMER_REQUIREMENT: достаточно bounded pointwise-zero residual subsequence; конкретная норма I_N не обязательна до доказательства exact return.
ORIGINAL_REQUESTED_OBJECT: доказательство RH.
ORIGINAL_OBJECT_IS: PROVED_NECESSARY_FOR_THE_STATED_GOAL.
KNOWN_WEAKER_INTERFACES: оптимальные NB-коэффициенты, true-core на S, прямой Gaussian receiver.
FAILURE_TYPE: UNRESOLVED before tests.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: источник-связанное midpoint chain-rule вместо недопустимого общего L2 sampling; quantitative smooth-profile transport и exact boundary bookkeeping.
REOPEN_TRIGGER: доказанный source-specific контроль сингулярно взвешенной энергии либо ошибка в candidate return.
<!-- FROZEN_HARDY_B_END -->
