# STATUS: TRY_BLOCK_B_MULTISCALE_REPAIR_C

```yaml
STATUS: TRY_BLOCK_B_MULTISCALE_REPAIR_C
OPERATIVE_CLASS: TRY_BLOCK_B_MULTISCALE_REPAIR_C
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_COMPLETED_PROOF_AND_TESTS
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_PROVE_RH_CONTINUATION
REQUEST_COMMIT: 8e2e29a866600c16cf38127ff5325ac97dc2880e
REQUEST_BLOB: ea960a415d74beb2c332d6851b43e18cb93716d0
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_COMMIT: 2cb305016f3f935fa5d9332ba8f9b3c1b0a25d95
INPUT_BLOB: 9eccae44e4e1a69e8b6eaa2343c2493784f17ecd
OBSERVED_INBOX_HEAD: 2cb305016f3f935fa5d9332ba8f9b3c1b0a25d95
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_BLOCK_B_MULTISCALE_2026-11-06_C.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: TRUE_SOURCE_MULTISCALE_ENERGY_BOUND_ON_S
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: MULTISCALE_BLOCKING_WITH_DETERMINISTIC_PHASE_AVERAGING
ROUTE_SCORE: 3
```

Ы. Отдельный freeze; после коммита не редактируется. Метод выбран после предварительного алгебраического анализа. Завершённые доказательства, численные и точные тесты ниже ещё не проведены. Полная локальная копия входа содержит 45014 байт и совпадает с INPUT_BLOB. Старый запрет относится к одной ширине h при снятии частотного среза; его нельзя переносить на следующие растущие блоки без доказательства.

<!-- FROZEN_MULTISCALE_C_BEGIN -->
## S: сохранить источник, изменить только способ оценки обратного сдвига

[ABSTRACT / FINITE_CELL / COFINAL_FAMILY | CONDITIONAL: будущие оценки не предполагаются.]

Сохраняются исходные r_n(k)=(k mod n)/n, w_k=1/[k(k+1)], a_1=1, a_n=mu(n)log(N/n)/log N, s=sum a_n/n, q_1=1-s, q_n=a_n при n>=2. Всегда sum q_n/n=0. Сохраняются R_N, E_N, J_N и настоящее множество S из входных источников. Ни один мёбиусов коэффициент и ни одна простая степень не меняются.

Положим A_N(l)=sum_(n|l,n<=N)q_n, d_l=(1_(l=1)-A_N(l))/l, y_j=sum_(l>=j)d_l. Входной PAPER даёт E_N=sum_j|y_j|^2. Его количественные оценки будут проверены непосредственно там, где используются.

Для 1<=t<2 и b>=0 определить m_b(t)=floor(2^b t), I_b(t)={m_b,...,m_(b+1)-1}, v_l=1_{1,...,l}. Старт m_0=1; все положительные целые покрыты ровно один раз. Определить

    V_b(t)=sum_(l in I_b(t)) d_l v_l,
    D_N(t)=sum_(b>=0)||V_b(t)||_2^2,
    Dbar_N=integral_1^2 D_N(t) dt.

Проверить, существует ли универсальная all-input оценка ||sum_b V_b||^2 <= C sum_b||V_b||^2 с явной C<=16, не зависящей от N, числа блоков и текущих коэффициентов. В отличие от прошлого раунда, ширина блока растёт с l. Если это проходит, проверить обратное сравнение Dbar_N<=16 E_N: фазовое усреднение должно оплатить выбор dyadic endpoints, а не считать их бесплатными.

Новый конечный объект — средняя сумма первых B положительных блоковых квадратов. Усреднение здесь детерминированное: при конечном B интегранд постоянен на конечной dyadic-сетке t, поэтому это конечный PSD Gram. Полный remainder — сумма всех следующих квадратов, а подписанный межблочный член в E_N отдельно сохраняется. Предполагаемый хвост для настоящего источника: Dbar_N-Dbar_(N,B) <= C_tail Q_N^2/2^B, Q_N=sum|q_n|, с явной абсолютной константой.

Основная арифметическая попытка: использовать на l<=N точное d_l=(s-Lambda(l)/log N)/l и полную усечённую divisor-свёртку далее, чтобы получить ограниченность Dbar_N на неограниченной части S. Существование такой оценки НЕ предполагается. Одно двустороннее сравнение Dbar_N с E_N не считается новой RH-оценкой. Если остановка останется здесь, результат должен явно сообщить PARTIAL / FULL_RH_ACCEPTANCE_NOT_COMPLETE, а не объявить доказанным один из исходов брифа.

### Предсказания до проверок

P1. Универсальная блоковая upper-оценка с C<=16 существует: растущие масштабы дают геометрическое убывание углов между блоками. Это конструктивный ремонт, не новый fixed-width kill.
P2. Обратное сравнение после усреднения по t имеет константу <=16. Для одного фиксированного dyadic разбиения обратная all-input оценка может не существовать; проверить явным единичным импульсом y у границы.
P3. Полная цена D_N(t) конечна при каждом фиксированном N; хвост допускает явную оценку O(Q_N^2/2^B), без перебора lcm(1,...,N).
P4. В true-source формулах все внутренние сокращения и исходная mu*1=epsilon сохраняются. R9-counterarray ломается в первой изменённой divisor-координате. Для DMV старый integer-floor/Mellin bridge не является его собственным источником.
P5. Generic block geometry и оплаченный хвост сами по себе не дадут source-specific boundedness; отдельно проверить доступный безусловный бюджет и не выдавать рост upper bound за опровержение ограниченности.

Тесты: точная рациональная проверка finite Green-матриц при T=8,16,32 и dyadic фазах; тест единичного импульса y при j=2^b для b=1,...,6; настоящие N=3,8,16,32,64 для проверки harmonic/difference/dyadic равенств при 50 и 80 знаках. Это DIAG нормировок, не cofinal-сертификат. Любой нуль, согласующийся с floating point, различать точной полиномиальной/рациональной идентичностью, а не ещё одной точностью. Новые source-specific гипотезы не объявлять проверенными конечной сеткой.

### K8A

DOWNSTREAM_CONSUMER: RH через исходный NB bounded-pointwise-zero receiver.
ACTUAL_CONSUMER_REQUIREMENT: истинная ограниченная подпоследовательность E_N на S достаточна; более общие нормированные NB-приближения допустимы.
ORIGINAL_REQUESTED_OBJECT: доказательство RH либо ближайший закрытый шаг и точный gap.
ORIGINAL_OBJECT_IS: PROVED_NECESSARY_FOR_RH_GOAL; конкретная multiscale-репрезентация NOT_NECESSARY.
KNOWN_WEAKER_INTERFACES: источник-определённые signed estimates, оптимальное NB-приближение, прямой Gaussian/Weil receiver.
FAILURE_TYPE: UNRESOLVED_BEFORE_PROOF.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: bounded positive replacement for the previously divergent fixed-width certificate, with explicit phase-averaging and tail cost; no claim of historical priority for dyadic blocking.
REOPEN_TRIGGER: a quantitative true-Mobius estimate of the resulting finite multiscale core, or a flaw in the proposed block comparison.
<!-- FROZEN_MULTISCALE_C_END -->
