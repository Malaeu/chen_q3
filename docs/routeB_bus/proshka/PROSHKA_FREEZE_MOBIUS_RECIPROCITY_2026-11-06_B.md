# STATUS: TRY_SOURCE_EXACT_MOBIUS_RECIPROCITY_B

```yaml
STATUS: TRY_SOURCE_EXACT_MOBIUS_RECIPROCITY_B
OPERATIVE_CLASS: TRY_SOURCE_EXACT_MOBIUS_RECIPROCITY_B
ARTIFACT_STATE: SPEC_FROZEN_BEFORE_CONSTRUCTION_AND_TESTS
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_PROVE_RH_REQUEST_AFTER_R10
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_R8_COMMIT: 70c4e6b097bc714689fb9226aeaea12a46127c95
INPUT_R8_BLOB: e0c22e09de31ce8c3ee37e8c53343477168b2063
INPUT_R9_COMMIT: b5fc098b7727bded490c4e46969d6379afa90307
INPUT_R9_BLOB: bc15928e8da77401e6fc15514cb6fc6f2c1932ee
INPUT_R10_COMMIT: 4a496c5c5984ee47e01746ef84c7971a6d11cd0f
INPUT_R10_BLOB: c6d3c4da9cda6b3ef98d08d5f58f6f35cc038c29
SUMMARY_REF: rh_clean_1c870b51
SUMMARY_BLOB: df730a5d44e5aee76b02e9c1532e4970d593f942
LITERATURE_REF: rh_clean_15398196
LITERATURE_BLOB: 3c69a4d7f54507c4aeee385d1879f1457214ee8d
OBSERVED_INBOX_HEAD: 0ee656bb9e02e7dc2f67966cb976043b030ed269
WRITE_BRANCH: proshka_inbox_2026-10-31
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_MOBIUS_RECIPROCITY_2026-11-06_B.md
RH_PROVED: false
PROVED_STEPS: []
RH_GAP: SOURCE_SPECIFIC_SIGNED_RECIPROCITY_BOUND
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: EXACT_RECIPROCITY_AND_FULL_GCD_COUPLING
ROUTE_SCORE: 3
```

Ы. Отдельный freeze; после записи не редактируется. Метод выбран после чтения закреплённого обзора, первичных формул и предварительного алгебраического анализа. Завершённые доказательства и вычислительные проверки ниже ещё не проведены. Обзор — источник указателей, не разрешение импортировать его ASSESSMENT как THEOREM.

<!-- FROZEN_RECIPROCITY_B_BEGIN -->
## S: полный подписанный Gram, без разъединения пакетов

Сохраняются обычная mu, все её префиксы, mu*1=epsilon, r_n(k)=(k mod n)/n, w_k=1/[k(k+1)], L=log N и a_n=mu(n)log(N/n)/L. Полный остаток R_N=1+sum_(n=2)^N a_n r_n, E_N=sum w_k |R_N(k)|^2. s_N=sum_(n<=N)a_n/n, b_N=1+(sum a_n-s_N)/2, S={N>=3:b_N b_(N+1)<=0}; это ровно R8, не новый отбор.

Введём центрированные коэффициенты q_1=1-s_N, q_n=a_n для 2<=n<=N. Тогда sum q_n/n=0. Положительный объект — полный Gram функций rho_n(x)={1/(n x)} в L2(0,infinity), включая все перекрёстные элементы, с последующим точным возвратом к L2(0,1). На конечной стадии применять сумму Васьунина в соглашении

    V(h/k)=sum_(r=1)^(k-1) {r h/k} cot(pi r/k), gcd(h,k)=1,
    c0(h/k)=-sum_(r=1)^(k-1) (r/k)cot(pi r h/k).

При общих h,k сначала делить на gcd; коэффициент масштабирования должен остаться. Источник формул — Bettin–Conrey, arXiv:1111.0931v2, (13),(14), Theorem 4, с проверкой страниц и знаков. Буквальные расходящиеся значения g на рациональных числах не импортировать вместо конечной V.

Попытка: точно сложить элементарные члены полной квадратичной формы, оценить оставшийся элементарный член на S из настоящих divisor-identities, затем применить полную reciprocity/Euclid recursion к подписанной котангенсной части. В gcd-разложении сохранить совместную mu(h)mu(k), общие множители и taper на обоих индексах. Искомый новый вход — доказанная односторонняя оценка этой совместной части, достаточная для bounded E_N на неограниченной части S. Одно переписывание такого входа не объявлять доказательством RH или новым знаковым результатом.

### Предрегистрация

P1. Предварительная алгебра предсказывает точное удаление большого элементарного рангового члена при sum q_n/n=0; после смешивания с целью ожидается E_N=1+2 b_N u_N-pi T_N, где u_N=sum a_n log n/n, а T_N — полный gcd-взвешенный Vasyunin sum. Знак и gcd-множитель проверить независимо.

P2. Из mu*1=epsilon и mu*log=-Lambda ожидается безусловный явный постоянный bound на |u_N| (цель <=40 для N>=3), следовательно элементарная поправка на S имеет размер O(1/log N). Ни RH, ни cancellation M(x) на sqrt-scale для этого не допускаются.

P3. Полное gcd-разложение снимает знаки общих делителей, но оставляет настоящие совместные веса mu(a)mu(b) при (a,b)=1. Предположение, что modular inversion сохраняет эти веса, проверяется до его использования. Точный 2-by-2 или малый целочисленный falsifier предпочтительнее большого прогона.

P4. Нормировки литературных g,V,c0 обязаны пройти тест h/k=1/3,2/3,2/7 и noncoprime pair 2,4. У буквального ряда sum_l(1-2{l h/k})/l ожидается ненулевой средний дрейф на рациональных; не считать его без определения конечной частью/Фурье-значением.

P5. Главная знаковая оценка не предсказывается как доказанная. Если reciprocity даёт только эквивалентную открытую сумму, отметить NO_NEW_RH_BOUND; не выдавать вычислимость каждого коэффициента за контроль суммы. Самодуальные подсадки могут сохранять ordinary NB Gram и reciprocity, но обязаны отказать на точном Gamma/completion link.

Проверки после freeze: точные divisor- и gcd-идентичности на N=3,4,8,16,32; finite cotangent Gram против независимо суммированной периодической residue-нормы при 50 и 80 десятичных знаках, пары 1..12 с кратностями gcd; signed decomposition для N=3,8,16,32,64; reciprocity recursion на малых coprime rationals. Никакая decimal near-zero не считается сертификатом. Доказательства констант PAPER; большие N и настоящие нули не вычислять ради ритуала.

### Consumer contract

DOWNSTREAM_CONSUMER: RH через source-correct centered NB capture; также прежний literal A_m receiver.
ACTUAL_CONSUMER_REQUIREMENT: достаточно bounded pointwise-zero residual subsequence, не обязательно 1/log N и не обязательно именно S.
ORIGINAL_REQUESTED_OBJECT: доказательство RH, при незавершении — точный доказанный шаг и минимальный gap.
ORIGINAL_OBJECT_IS: PROVED_NECESSARY для RH как цели; выбранный reciprocity supplier UNKNOWN как необходимый.
KNOWN_WEAKER_INTERFACES: optimal NB capture, coherent convex averages, direct signed Gaussian lower bound с доказанными стрелками.
FAILURE_TYPE: UNRESOLVED до проверки.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: оплаченная элементарная часть и точная gcd-подписанная reciprocity на неизменной mu; историческая новизна самой reciprocity не предполагается.
REOPEN_TRIGGER: новый source-specific lower bound совместной котангенсной формы, либо ошибка в source-normalization или доказанных оценках.
<!-- FROZEN_RECIPROCITY_B_END -->
