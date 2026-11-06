# STATUS: TRY_ROUND9_CORE_ON_S_B

```yaml
STATUS: TRY_ROUND9_CORE_ON_S_B
OPERATIVE_CLASS: TRY_ROUND9_CORE_ON_S_B
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_TESTS
DATE: 2026-11-06
REQUEST_COMMIT: 9d8a6d48a0efdeaea7987748d242a3844e91a6dc
REQUEST_BLOB: 2227c094d0cf36b7aa19b71f1eee68e80d1a330e
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_R8_COMMIT: 70c4e6b097bc714689fb9226aeaea12a46127c95
INPUT_R8_BLOB: e0c22e09de31ce8c3ee37e8c53343477168b2063
OBSERVED_INBOX_HEAD: 70c4e6b097bc714689fb9226aeaea12a46127c95
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND9_2026-11-06_B.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: BOUNDED_TRUE_MOBIUS_CORE_ON_UNBOUNDED_SUBSET_OF_S
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: SOURCE_MOMENT_NULLSPACE_AND_ENERGY_AUDIT
ROUTE_SCORE: 3
```

Ы. Отдельный freeze, после коммита не редактируется. Бриф и протокол получены через GitHub. Полная локальная копия R8 имеет ровно закреплённый Git blob. Папка R8_CERTIFICATE_AND_CORE при первом чтении недоступна (404); отсутствие отчёта не заменяется выдуманными числами. Метод выбран после предварительного анализа, до приведённых ниже проверок и построений.

<!-- FROZEN_R9_B_BEGIN -->
## S9-B: настоящее ядро на S и проверка достаточности скалярного отбора

[COFINAL_FAMILY | CONDITIONAL: нужная ограниченность не предполагается.]

Сохраняются буквально определения R8: r_n(k)=(k mod n)/n, a_n(X)=mu(n)(1-log(n)/log(X)), 1<=n<=X; R_X(k)=1+sum_(n>=2) a_n(X)r_n(k); s(X)=sum a_n(X)/n; b(X)=1+sum a_n(X)(1-1/n)/2; K_N=ceil(N^(3/2)); H_N=sum_(1<=k<K_N)|R_N(k)|^2/[k(k+1)]; S={N>=3:b(N)b(N+1)<=0}. Цель — (26) R8, не только новая положительная матрица.

Первичная попытка: вывести точное совместное уравнение энергии и скалярных мод при изменении log X; сохранить в нём все смешанные члены. Проверить, может ли малость b на S вместе с оплаченной дальней нормой и s=O(1/log X) контролировать H. Неполученный bound не заменять знаком положительного Gram.

Параллельный adversarial test этой попытки: рассмотреть методы, которые используют коэффициенты лишь через их модульный taper, squarefree support, b(X), s(X), конечный начальный блок и универсальные PSD/CRT/tail-тождества. Проверить, существуют ли конечные Dirichlet-полиномиальные поправки с двойными нулями при s=0 и s=1, невидимые одновременно b и s, но создающие большой core в настоящем словаре r_n. Возможная факторизация из нескольких обычных простых — кандидат, не принятая теорема. Поправки НЕ называются настоящей mu и НЕ заменяют источник zeta в доказательстве RH.

Если такой свидетель найден, граница запрета — только uniform inference из перечисленных ослабленных данных. Нельзя объявлять невозможной исходную (26), методы, использующие полный mu*1=epsilon, или весь NB-маршрут. Именно полное source-match должно быть указано как потерянное различие.

### Предсказания до проверок

P1. Для Y(t)=t R_(exp t) точная вторая производная энергии имеет положительный квадрат 2||Y'||^2 и подписанный импульсный prime/divisor член; скалярное b=0 само по себе последний член не обнуляет.
P2. Двойные Mellin-нули при 0 и 1 сохранят обе скалярные траектории b(X),s(X) после включения всей поправки; ниже её минимального индекса сохранятся все строки остатка.
P3. Можно усилить P2 до поправки на squarefree integers с ограниченными коэффициентами и core-энергией не меньше c N/log^2 N при явном c>0. Проверить точный квантор и сохранение N,N+1, а не только одного нуля b.
P4. Полная Möbius/divisor-идентичность не сохранится у ненулевого свидетеля; её нельзя молча перенести на фальшивый источник.
P5. Если прямой true-source bound не получится, допустим только узкий исход (c) с честным NO_NEW_RH_SIGN, либо частичный результат. Новый scalar criterion сам по себе не считается прогрессом.

### Проверки и фальсификаторы

Сначала PAPER-арифметика и точная рациональная проверка коэффициентов Dirichlet-полинома и его четырёх моментов. Затем малые целочисленные блоки для тождеств строк; плавающие логи при 60/90 знаках допустимы только как DIAG. Большая сетка H_N не планируется и не занимает cofinal-квантор. Для любого kill нужен строгий отрицательный upper witness для заявленного bound; большая положительная оценка сверху не является kill. Zero-consistent moment проверяется точным произведением/полиномом, а не дополнительными десятичными знаками.

### K8A до построения

DOWNSTREAM_CONSUMER: RH через centered NB capture и прежний literal CCM receiver.
ACTUAL_CONSUMER_REQUIREMENT: достаточно bounded true residual subsequence с поточечным нулевым пределом; допустимы другие source-correct approximants.
ORIGINAL_REQUESTED_OBJECT: (26) R8 для true Mobius taper на S.
ORIGINAL_OBJECT_IS: UNKNOWN как необходимое для RH.
KNOWN_WEAKER_INTERFACES: source-correct convex averages или оптимальные NB-коэффициенты; нужен собственный norm bound, не одно определение.
FAILURE_TYPE: NO_DERIVATION до выполнения попытки.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: точный энергетический аудит и арифметические направления, невидимые всему скалярному отбору, внутри исходного residue dictionary.
REOPEN_TRIGGER: новый совместный true-Mobius bound, чувствительный к полному divisor identity; либо ошибка в явном obstruction witness.
<!-- FROZEN_R9_B_END -->
