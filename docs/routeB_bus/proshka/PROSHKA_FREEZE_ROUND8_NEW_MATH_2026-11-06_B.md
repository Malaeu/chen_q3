# STATUS: TRY_ROUND8_ADDITIVE_FREQUENCY_GRAM_B

```yaml
OPERATIVE_CLASS: TRY_ROUND8_ADDITIVE_FREQUENCY_GRAM_B
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_CONSTRUCTION
DATE: 2026-11-06
REQUEST_COMMIT: 2f75fac798d71500c9445dbeb6a8ee6e99b43f15
REQUEST_BLOB: 3f99134611845b12dfcfada03439e0cba1222bde
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
OBSERVED_INBOX_HEAD: 8a994500ffc9648f2f3e22561ee74a9d0c2e9eca
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND8_NEW_MATH_2026-11-06_B.md
PROVED_STEPS: []
RH_GAP: CRITICAL_NORM_CONTROL_OF_SOURCE_MATCHED_NB_RESIDUAL
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: ADDITIVE_SPECTRAL_DECOMPOSITION
ROUTE_SCORE: 3
RH_PROVED: false
NUMERICAL_TESTS_RUN: false
```

Ы. Отдельный freeze. Этот файл после коммита не редактируется. Метод выбран после чтения брифа, новых Limit 9 и R7 B и предварительного алгебраического разбора; зарегистрированные ниже проверки ещё не выполнены. Старые вердикты не меняются.

<!-- FROZEN_R8_B_BEGIN -->
## S8-B: положительный частотный Gram, нулевая мода и оплаченный хвост

[ABSTRACT / COFINAL_FAMILY | CONDITIONAL для искомой арифметической оценки.]

Неизменный словарь R6 C: r_n(k)=(k mod n)/n, k>=1, веса w_k=1/[k(k+1)]. Для N>=3, l=log N берём ровно a_n=mu(n)(1-log n/l), 1<=n<=N, и R_N(k)=1+sum_(n=2)^N a_n r_n(k). Это явный сглаженный кандидат, НЕ оптимальный e_N; его ошибка E_N=||R_N||^2 лишь мажорирует e_N.

Новый объект: разложить R_N в постоянную моду b_N и конечные аддитивные характеры exp(2*pi*i*alpha*k), alpha — сокращённые рациональные частоты со знаменателем <=N. Сгруппировать совпадающие частоты. Построить их точный положительный Gram / GCD covariance и точную взвешенную хвостовую матрицу. Звенья определяются целочисленным делением, mu и текущими коэффициентами; ни нули, ни psi-x, ни знак A_m не используются для выбора.

Основной масштаб хвостового среза K(N)=ceil(N^(3/2)). Кандидат конечной положительной цены:

    C_N = sum_(1<=k<K(N)) |R_N(k)|^2/[k(k+1)] + |b_N|^2/K(N).

Искомое трёхчастное представление: явно вычислимый finite-core, положительная по построению нулевая мода / GCD bulk и ТОЧНЫЙ signed remainder E_N-C_N. Проверить возможность безусловно оплатить последний как O(1/log^2 N), с явной константой. Это ещё не малость C_N: далее попытаться доказать C_N<=1/(4 log N) при всех поздних N либо предъявить точное незакрытое утверждение. Нельзя объявить полный раунд закрытым, если оплачен только дальний хвост.

Предсказания до тестов:
P1. Средняя за общий период энергия непостоянной части имеет точную PSD-запись через (gcd(n,m)^2-1)/(12nm) и Jordan-totient squares. Для сглаженных mu-коэффициентов ожидается верхняя граница <=2N/log^2 N без cancellation mu.
P2. Аддитивная separation alpha-beta>=1/N^2 и large sieve должны ограничить взвешенный tail covariance; связь постоянной моды с остальными надо оценивать отдельно, иначе теряется степень N. Ожидается |E_N-C_N|<=10/log^2 N для N>=3. Константа и область должны быть доказаны, а не подогнаны по числам.
P3. Для C_N малость не следует из PSD, периодического среднего или отдельной PNT-оценки. Проверить точный head R_N(k)=k*s_N-psi(k)/log N при k<=N; все степени простых сохраняются. Требуется попытка оценить совместный finite-core, не только назвать его.
P4. Универсальный all-coefficient large-sieve correction масштаба N^2 нельзя заменить o(N^2): детектор — близкие рациональные частоты 1/N и 1/(N-1). Это проверка точного класса частотных огибающих, не запрет специальной mu-компенсации и не запрет RH.
P5. Обычный residue/character источник не станет источником DH, DMV или изменённого Gamma-factor после переименования. Полный source-match и точный Gaussian/Gamma link должны быть сохранены. Контроль E/F3 использует собственный положительный antiperiodic square, не чужую zeta-Gamma.

Тесты: до каких-либо больших запусков проверить covariance рационально для 2<=n,m<=12 и собственный двухчастотный отрицательный контроль. Для проверки нормировок допускается N=3,...,10, точная периодизация хвоста с digamma и 80/120 знаками; это DIAG, не интервальный сертификат. Для попытки арифметической оценки допустим finite-core grid N=8,16,32,...,4096; ни один конечный grid не является PASS для eventual bound. Точки с почти нулевой разностью требуют точного тождества или интервального знака, не названия zero. При необходимости нового теста он регистрируется отдельно до запуска, freeze не редактируется.

K8A: DOWNSTREAM_CONSUMER=RH через source-matched e_N->0 или R7 fast receiver. ACTUAL_CONSUMER_REQUIREMENT=исчезновение оптимального e_N; скорость и конкретный Selberg-кандидат не обязательны. ORIGINAL_REQUESTED_OBJECT=новый объект с оплаченной критической ошибкой. ORIGINAL_OBJECT_IS=UNKNOWN для данного candidate, NOT_NECESSARY для любого фиксированного taper. KNOWN_WEAKER_INTERFACES=любые оптимизированные coefficients с e_N->0; bounded-head subsequence из Limit 9, если её цена доказана. FAILURE_TYPE до работы=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT. NOVELTY_AXIS=точная source-specific finite-core/constant-mode/frequency-tail decomposition, не новизна large sieve или NB-критерия. REOPEN_TRIGGER=доказанный signed arithmetic bound на finite-core либо принципиально иной source-matched supplier.
<!-- FROZEN_R8_B_END -->
