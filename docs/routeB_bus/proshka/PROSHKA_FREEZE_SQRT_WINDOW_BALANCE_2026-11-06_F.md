# STATUS: TRY_SQRT_WINDOW_BALANCE_F

```yaml
STATUS: TRY_SQRT_WINDOW_BALANCE_F
OPERATIVE_CLASS: TRY_SQRT_WINDOW_BALANCE_F
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_COMPLETED_PROOF_AND_TESTS
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_PROVE_SQRT_CANCELLATION_ON_N_HALF_TO_TWO_N
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_COMMIT: 6602052985df5a1b2e3ab876e6a459e6f92a18cd
INPUT_BLOB: e7d45ebbd49e8d060cc5368352e7b3f17b837e13
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_SQRT_WINDOW_BALANCE_2026-11-06_F.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: SOURCE_SPECIFIC_FIXED_ORIGIN_SQUARE_ROOT_OR_JOINT_ENERGY_BOUND
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: FIXED_PHASE_VERSUS_EXACT_CRT_VARIANCE
ROUTE_SCORE: 3
```

Ы. Неизменяемый freeze. Первичный алгебраический анализ выполнен, законченных доказательств и тестов этой попытки ещё нет.

Сохранить N>=3, L=log N, a_n=mu(n)log(N/n)/L, a_1=1, s_N=sum a_n/n, c_N=L*s_N, q_1=1-s_N, q_n=a_n для n>=2. A_N(k)=sum_(n|k,n<=N)q_n, j_N(k)=1_(k=1)-A_N(k). На рабочей полосе k>floor(N/2), k>=2, использовать сырой ток f_N(k)=L*j_N(k), не смешивать его с j_N.

Целевая версия: prefix/suffix суммы j_N на обеих половинах полосы имеют размер O(sqrt N) на неограниченной части настоящего S. Отдельно проверить более сильную версию с f_N вместо j_N. Одна малая итоговая сумма не подменяет все partial sums или квадратную энергию. Даже оплаченный cross не является всей Z_N.

Предсказания до проверок:
P1: знаки не равны просто prime/nonprime: proper prime powers отрицательны в Lambda-части; после N обязателен член -mu(k)log(k/N).
P2: proper prime powers можно оплатить явной универсальной константой times sqrt N; это не оплачивает первые степени или scalar drift c_N-1.
P3: точная периодическая CRT-ортогональность даёт square-root mean-square цену для блока усечённого тока, с константой, независимой от длины блока. Попробовать вывести её из настоящих beta_N(q), не независимых случайных знаков. Перенос среднего по фазе на конкретное начало floor(N/2) НЕ предполагается.
P4: root-scale bounds двух настоящих partial sums дают явный O(1) bound cross через Abel summation; попробовать получить и интегральный, более слабый sufficient interface. Никакой источник его верхней оценки заранее не принимается.
P5: проверка против смешения mean/fixed phase — тот же divisor dictionary с положительным taper вместо mu; этот контроль не является другим настоящим источником и убивает только generic norm-to-pointwise шаг, если применим.

Судьи после freeze: N=3,4,5,6,8; точные rational vectors in log primes для current и beta; полные периоды и длины H=1,floor(N/2),N,2N и 2N-floor(N/2), с проверкой CRT-second-moment. Малые численные сравнения 50/80 digits — только DIAG, не интервальный сертификат. Cofinal-прогон не требуется и не доказывает нужный квантор. Для near-zero использовать точные коэффициенты при логарифмах, а не допуск.

K8A: DOWNSTREAM_CONSUMER=bounded full Z_N then NB capture and RH; ACTUAL_CONSUMER_REQUIREMENT=joint signed full-energy bound, not necessarily pointwise sqrt; ORIGINAL_REQUESTED_OBJECT=source-specific sqrt balance; ORIGINAL_OBJECT_IS=UNKNOWN as necessary; KNOWN_WEAKER_INTERFACES=integrated prefix-energy product or direct source-correct full Gram estimate; FAILURE_TYPE=UNRESOLVED_BEFORE_PROOF; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=explicit actual-source phase variance and exact fixed-origin gap; REOPEN_TRIGGER=independent fixed-origin or joint-energy inequality.