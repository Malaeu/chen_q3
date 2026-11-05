# STATUS: TRY_ROUND7_NB_WINDOW_COUPLING_B

```yaml
OPERATIVE_CLASS: TRY_ROUND7_NB_WINDOW_COUPLING_B
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_CONSTRUCTION
DATE: 2026-11-06
REQUEST_COMMIT: 195366c6a61cd1fc457b0a302e58b33b1936528e
REQUEST_BLOB: e43e2bb5430b266b8c52eb489d7b882a261c17a9
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_R6_C_COMMIT: 0005623ec3a2b476019899562b50c0854a602dfb
INPUT_R6_C_BLOB: 83004738a32926d80030b52bbae4655ee221dba0
INPUT_R6_B_COMMIT: 888b808094dcc5d8d53686c466f79487ffb1e05f
INPUT_R6_B_BLOB: 33de3e38276671101b701d895509e81d09c0f2e5
OBSERVED_INBOX_HEAD: 0005623ec3a2b476019899562b50c0854a602dfb
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND7_NB_WINDOW_COUPLING_2026-11-06_B.md
PROVED_STEPS: []
RH_GAP: QUANTITATIVE_CENTERED_NB_CAPTURE_AND_FINITE_WINDOW_TRANSFER
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: SCALE_AUDIT_AND_RECEIVER_MATCHING
ROUTE_SCORE: 3
RH_PROVED: false
NUMERICAL_TESTS_RUN: false
```

Ы. Это отдельный freeze; после записи он не редактируется. Прочитаны бриф, R6 C (C1)–(C32), R6 B §7–8 и addendum C. Настоящие A_m, G_m, K_m, все prime powers, полюсы и Gamma остаются прежними. Содержание предыдущих доказательств импортируется как PAPER, не как независимо проверенные теоремы.

<!-- FROZEN_R7_B_BEGIN -->
## S7-B — две разные цены и два явно раздельных consumer

[ABSTRACT / COFINAL_FAMILY | CONDITIONAL: искомые bounds не предполагаются.]

1. Основной кандидат сопряжения: N(m)=m, L=log m. Основной тестируемый порог имеет вид e_N<=c/L с фиксированной c>0. Вариант N(m)=ceil(exp(L^3)) допускается только как отдельно названное сопряжение для условной обратной стрелки, не как задняя правка N=m.

2. Сначала установить точное отношение e_N из R6 C к d_N^2: e_N — центрированный остаточный словарь, d_N^2 — минимум по всем Dirichlet polynomials длины N. Проверить Mellin-изометрию, условие A_N(1)=0, хвост x>1 и цену центрирования. Ошибку конкретного V_N обозначать отдельно E_N(V_N); не заменять ею infimum.

3. Главный consumer брифа — полный finite-window floor на всех K_m. Для него попытаться ослабить m^(-6), оптимизируя и затем улучшая (C20), с явными константами. Отдельно проверить непосредственно fixed-Gaussian receiver RG §6: его спектральная Gaussian-убыль может допустить e_N=O(1/L), даже если полный floor таким конечным тестом ещё не получен. Успех на одном Gaussian не выдавать за finite-cell оценку на всех K_m. Cofinal implication через RH также не выдавать за pointwise finite bridge.

4. Проверить точное соответствие показателей: квадрат NB-нормы, сама NB-норма, окно длины L и реально использованное расстояние между двумя физическими пакетами. R6 receiver использовал расстояние L/2. Отдельный near-edge receiver с расстоянием L-o(L) допустим только с заново оплаченными cutoff/projection/moment errors. Его показатель не приписывать старому receiver.

5. Все ссылочные скорости Burnol, Balazard–de Roton, Bettin–Conrey–Farmer, Maier–Rassias проверяются по первичным текстам и поиску corrections/errata. Цель — доказать новую количественную стрелку, не объявить классический NB-критерий новым доказательством.

### Предсказания, зарегистрированные после чтения входов, до построения/тестов

P1. e_N равен минимуму Mellin-ошибки с одним линейным ограничением A_N(1)=0; d_N^2<=e_N<=K d_N^2 с явной абсолютной K. Равенство e_N=d_N^2 вообще не ожидается.

P2. Порог m^(-6) чрезмерен для polylog-floor: непосредственная оптимизация R6 C даст хотя бы e_N<=1/(m log m), с полилогарифмической ценой. Оптимальность этой степени заранее НЕ предполагается.

P3. Для фиксированного Gaussian-отклика e_N log m<=c должно давать равномерный нижний бюджет за счёт Gaussian-подавления высоких ординат. Для всего несглаженного cosine-carrier такой вывод не предполагается.

P4. Рост N^(2a) из Maier–Rassias относится к конкретному V_N, а не к оптимальному e_N, который не превосходит 1. Поэтому прямое отождествление этого роста с e_N или с неизменным integer-Gram после изменения Gamma должно провалиться. Нужно сохранить собственный источник plant.

P5. Равенство log N=L не означает равенства Hilbert-пространств: fractional-part dictionary имеет Mellin-tail. Проверить support и boundary до любого утверждения об изометрии с буквальным окном.

P6. Если finite Gaussian bridge проходит, N=m и скорость O(1/log N) потребуют только точно названных дополнительных гипотез BCF для обратного направления. Квазиполилогарифмическое сопряжение exp(L^3) может пройти уже из более слабой RH-условной скорости Balazard–de Roton. Ни один такой условный supplier не является безусловным доказательством RH.

### Предварительные конечные фальсификаторы

Точные проверки: N=1,2; constraint A(1)=0; planted quartet a=1/3 и gamma=7,100; проверка размерности/нормы и точных Mellin-коэффициентов. Сначала аналитика, затем при необходимости обычный SymPy/Fraction для алгебры.

Если понадобятся численные проверки: N,m in {2,3,4,8,16,32,64}; 80 и 120 десятичных знаков; остаточный Gram суммировать с доказанным хвостом (не обрезать молча); сравнивать e_N,d_N^2,E_N(V_N), e_N log m и e_N m log m. PASS только по нижней интервальной огибающей требуемой разности >=0; KILL только по верхней <0. Decimal agreement без интервального хвоста — DIAG. Ни одна finite-grid не доказывает cofinal rate. Для нулесогласованного результата discriminator — точное линейное constraint либо ненулевой Mellin/Laplace residue.

### K8A перед фиксацией требований

DOWNSTREAM_CONSUMER: RH через исходный literal-window Gaussian export.
ACTUAL_CONSUMER_REQUIREMENT: достаточен cofinal subpolynomial lower bound одного заранее заданного Gaussian-направления; полный K_m floor сильнее по форме.
ORIGINAL_REQUESTED_OBJECT: оптимальное finite NB-to-whole-window сопряжение с polylog defect.
ORIGINAL_OBJECT_IS: UNKNOWN как необходимый для RH; существование конкретного оптимального сопряжения не предполагается.
KNOWN_WEAKER_INTERFACES: Gaussian finite bridge плюс cofinal residue rate => RH; одно лишь e_N->0 не засчитывать новым результатом.
FAILURE_TYPE: NO_DERIVATION на момент freeze.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: quantitative threshold, exact centering cost, correct exponent correspondence.
REOPEN_TRIGGER: явная новая оценка либо строгий свидетель против точно названного universal bridge, без расширения запрета на настоящую zeta.
<!-- FROZEN_R7_B_END -->
