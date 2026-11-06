# STATUS: TRY_BLOCK_B_UNIT_SHIFT_GREEN_B

```yaml
STATUS: TRY_BLOCK_B_UNIT_SHIFT_GREEN_B
OPERATIVE_CLASS: TRY_BLOCK_B_UNIT_SHIFT_GREEN_B
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_CONSTRUCTION_AND_TESTS
DATE: 2026-11-06
REQUEST_COMMIT: caeaac024b05054e6a625bdea8b3f929ee665ac8
REQUEST_BLOB: ea960a415d74beb2c332d6851b43e18cb93716d0
DICTIONARY_REF: 089f59e5
DICTIONARY_BLOB: 8462d827e01dd83fef22f750936f3d84ad238e1d
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_COMMIT: b227cf636cbf33e482177b05d4e151b02b5a6cd8
INPUT_BLOB: ebb4994e7adb3aff745c5e9feb7c8dda71ea0842
OBSERVED_INBOX_HEAD: b227cf636cbf33e482177b05d4e151b02b5a6cd8
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_BLOCK_B_SHIFT_2026-11-06_B.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: SIGNED_UNIT_SHIFT_INVERSE_ENERGY_FOR_THE_TRUE_SOURCE
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: DISCRETE_GREEN_FUNCTION_AND_SOURCE_COHERENT_BLOCK_TEST
ROUTE_SCORE: 3
```

Ы. Отдельный freeze; после записи не редактируется. Прочитаны бриф, словарь и источник b227cf63. Метод выбран после предварительного алгебраического анализа. Проверки и завершённые доказательства ниже ещё не проведены. Числа прежних DIAG не становятся посылками.

<!-- FROZEN_SHIFT_B_BEGIN -->
## S: сдвиг на единицу в точной дискретной энергии

Сохраняются обычная mu, a_1=1, a_n=mu(n)log(N/n)/log N для 2<=n<=N, s_N=sum a_n/n, q_1=1-s_N, q_n=a_n. Никакой коэффициент, prime power, исходная NB-норма E_N, слой J_N или множество S не меняется. Всегда sum q_n/n=0.

Кандидат: A_q(l)=sum_(n|l,n<=N)q_n, d_l=[1_(l=1)-A_q(l)]/l и хвостовой примитив y_j=sum_(l>=j)d_l. Проверить точный возврат E_N=sum_(j>=1)|y_j|^2 через sine-isometry b227cf63, включая условную сходимость, midpoint и boundary at infinity. Предполагаемый конечный Green-Gram имеет элементы min(j,k); он является положительным Gram начальных отрезков обычной целой решётки. Прямая цель — новая совместная оценка на настоящем векторе d, не независимая оплата его модулей.

Если прямой bound не получен, проверяется ТОЛЬКО следующий класс: для фиксированного N делить индексы l на последовательные блоки одинаковой целой длины h=h(N), разрешить любую положительную квадратичную оценку внутри блока, но потребовать block-diagonal majorization всего конечного Green-Gram для всех входных амплитуд и затем переход к бесконечному cutoff. h может зависеть от N и настоящей арифметики, но не от cutoff. В оценке цены подставляется исходный неизменённый d_l. Методы со знаковыми межблочными членами, растущими по l блоками, особым точным хвостовым суммированием или без all-input требования этим классом не охватываются.

Предрегистрированные прогнозы:
P1. Полная NB-норма равна квадрату l2-нормы хвостового примитива; здесь не будет дополнительного полюсного вычитания. Проверить нулевой свободный вектор и одно r_2 до общей теоремы.
P2. A_q периодична со средним ноль; на l<=N полная mu-свёртка даёт A_q(l)=1_(l=1)+Lambda(l)/log N-s_N. Это точное место integer shift и всех prime powers. R9-контрмассив провалит именно эту идентичность.
P3. Для любого простого N/2<p<N, не делящего h, суммы A_q на последовательных h-блоках имеют ненулевую периодическую дисперсию. Тогда сумма точных положительных энергий блоков растёт как положительная константа times log(cutoff), хотя энергия полной подписанной суммы конечна. Это ожидаемое препятствие локальной положительной оплате; не утверждение о росте истинной E_N.
P4. В указанном классе необходимые длины h содержат произведение простых из (N/2,N). При использовании PNT только для интерпретации масштаба это экспоненциально по N; сам отрицательный свидетель должен быть конечным и аналитическим, без PNT и RH.
P5. Goldston–Montgomery и Bogomolny–Keating не импортировать как безусловную стрелку к RH; проверить первичные формулировки и условия. Локальные вычеты сами по себе не оплачивают обратный сдвиг.

Проверки после freeze: точная целочисленная mu-свёртка; N=4,8,12 и h=1,2,3,5, а также h кратная полному периоду; две десятичные точности для гармонического возврата и малых норм (только DIAG). Положительный/отрицательный операторный судья: Green-Gram min(j,k) и вектор (1,-1); нельзя выдавать большую раздельную цену за нижний bound нормы суммы. DISCRIMINATOR нулевой дисперсии — точный Fourier-коэффициент на конечной циклической группе, не близость float к нулю.

K8A: DOWNSTREAM_CONSUMER=bounded true E_N on an unbounded subset of S, then source-correct NB capture and RH. ACTUAL_CONSUMER_REQUIREMENT=any proved source-specific sufficient bound. ORIGINAL_REQUESTED_OBJECT=RH or a concrete obstruction. ORIGINAL_OBJECT_IS=UNKNOWN for this particular endpoint criterion as necessary for RH. TESTED_LOCAL_MAJORANT_IS=NOT_NECESSARY. KNOWN_WEAKER_INTERFACES=signed all-scale coupling, the full R8 Gram, normalized profile averaging, or a direct Weil receiver. FAILURE_TYPE=UNRESOLVED before tests. EPISTEMIC_STATUS=RESEARCH_DEBT. NOVELTY_AXIS=source-coherent unit-shift inverse and exact local residue obstruction, not a new classical RH equivalence. REOPEN_TRIGGER=new signed Green-energy estimate or a defect in the claimed local-block lower price.
<!-- FROZEN_SHIFT_B_END -->
