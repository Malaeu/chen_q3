# STATUS: TRY_PAIRED_SCALE_DIVISOR_ESTIMATE_M

```yaml
OPERATIVE_CLASS: TRY_PAIRED_SCALE_DIVISOR_ESTIMATE_M
ARTIFACT_STATE: FROZEN_BEFORE_COMPLETED_PROOFS_AND_TESTS
DATE: 2026-11-07
AUTHORITY: OWNER_GO_PAIRED_SCALE_DIVISOR_ESTIMATE_BEFORE_ABSOLUTE_VALUES
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_PLAN_COMMIT: c3f80b9871ca022d307b27331a2753dbc386e97a
INPUT_PLAN_BLOB: 7e8920ceac98f25b2da19a968c026baf37c76b7f
INPUT_K_COMMIT: 06238eb5dd6d06887d9b088aca089fdb3c05b9cc
INPUT_K_BLOB: cd777de92a512c2bb1f5cbb1aedbc38fa83d8757
OBSERVED_INBOX_HEAD: c3f80b9871ca022d307b27331a2753dbc386e97a
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PAIRED_SCALE_DIVISOR_2026-11-07_M.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: INDEPENDENT_SIGNED_FULL_TWO_SCALE_BOUND
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: PAIRED_SCALE_FLOOR_KERNEL_BEFORE_MODULI
ROUTE_SCORE: 2
```

Ы. План L прочитан полностью; локальные bytes сверены с его Git blob и с K. Bootstrap и Pappus skill получены заново. Поиск PAIRED_SCALE не дал результата на индексируемой ветке; это не исчерпывающий аудит. Предварительная алгебра уже предложила периодический примитив и проверку большого делительного блока; законченных доказательств и тестов новой попытки до этого freeze нет. Прежний план L остаётся неизменным.

## Контракт зависимости до выбора поставщика

DOWNSTREAM_CONSUMER: критическая рекурсия полной Lambda-энергии A(X), затем energy-Mellin receiver K/J и RH.
ACTUAL_CONSUMER_REQUIREMENT: независимое уменьшение показателя полной энергии на всех больших dyadic X, либо другой полностью доказанный receiver.
ORIGINAL_REQUESTED_OBJECT: совместная делительная оценка X и 2X до модулей; реальная экономия степени.
ORIGINAL_OBJECT_IS: NOT_NECESSARY как метод доказательства RH.
KNOWN_WEAKER_INTERFACES: иной source-correct feedback, signed aggregation без поэлементного majorant, исходный NB subsequence receiver.
FAILURE_TYPE: UNRESOLVED_BEFORE_TESTS.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: стоимость точного двухмасштабного ядра на неизменённом источнике, не ещё одна запись RH-эквивалентности.

## Источник

Для dyadic X>=8, D=4X, сохранить

    a_1=-1; a_d=-mu(d)log d (d>=2);
    N_d(x)=floor(x/d)-floor(x/(2d));
    S(x)=sum_(x/2<n<=x)(Lambda(n)-1)=sum_(d<=D)a_d N_d(x), x in [X,4X];
    A(X)=X^(-2) integral_X^(2X) S(x)^2 dx;
    M_X(d,e)=integral_X^(2X)N_d N_e dx - (1/8)integral_(2X)^(4X)N_d N_e dx;
    A(X)-A(2X)/2=X^(-2) sum_(d,e<=D)a_d a_e M_X(d,e).

Все prime powers, a_1, оба масштаба, опора и fixed-origin кванторы остаются. TARGET: для каждого eta>0 upper bound C_eta X^eta(sqrt(A(2X))+1). При стартовом A=O(X) это ненормированная цена O(X^(5/2+eta)), но промежуточное X^(5/2) само по себе не является повторяемой рекурсией.

## Предсказания и дешёвые судьи

P1. Главный x^2/(4de) сокращается при 1/8 точно; исходный overlap и две формы счёта совпадут. Намеренно заменить 1/8 на 1/4: judge обязан обнаружить ненулевой рациональный дефект.

P2. r_d(x)=N_d(x)-x/(2d) имеет нулевое среднее на 2d и ограниченный периодический примитив порядка d. Его точное использование должно оплатить блок d,e<=U с ценой O(X U^2 log^C(2U)); при U<=sqrt(X) ожидается O(X^2 log^C X), а не X^3. Успех только для этого блока не объявлять успехом всей формы.

P3. Полный периодический главный член r_d r_e должен выражаться через gcd и иметь суммарную цену O(X^2 log^C X). Остаток неполных периодов сохранять ТОЧНО; его нельзя считать средним.

P4. Для d,e>2X первая энергия не видит ни одного кратного, поэтому соответствующий блок M отрицательно полуопределён. Отбрасывать его как модуль запрещено. Проверить большой активный диапазон X<d,e<=4X/3: там число кратных мало и M имеет явную формулу. Возможен настоящий source-свидетель кубической цены для termwise positive/absolute оплаты после pairing. Если он подтвердится, KILL только этого способа оплаты, не совместной суммы.

P5. Попробовать совместно удержать все смешанные и большие делители. TARGET не предполагается. Если получены лишь paid subblocks, явно указать отсутствие общего выигрыша и не принимать запись остатка target-minus-paid за арифметическую оценку.

Тесты: X=8,16,32, все d,e<=4X, рациональная арифметика для M, независимые overlap/count/primitive вычисления. Formal log-prime coefficients для source-return. Covariance/primitive судья на 1<=d,e<=12, exact endpoints. Большой активный slab проверять на той же сетке; его cofinal lower envelope доказывать аналитически. Floating DIAG для проверки итоговых неравенств допускается отдельно с явным указанием, что это не ARB. Новых источниковых asymptotic claims по сетке не делать.

Сохранить оригинальные P1–P3 плана L и оценить их судьбу отдельно. Никакой большой численной сетки. Не переписывать этот freeze. DISCRIMINATOR: exact rational/log-coefficient equality for finite claims; strict lower/upper envelopes for cofinal assertions; Mellin pole cannot be erased by change of notation.
