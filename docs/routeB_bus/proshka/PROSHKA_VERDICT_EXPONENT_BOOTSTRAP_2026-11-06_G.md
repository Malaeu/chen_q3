# STATUS: TRY_EXPONENT_BOOTSTRAP_CONTRACT_G

```yaml
STATUS: TRY_EXPONENT_BOOTSTRAP_CONTRACT_G
OPERATIVE_CLASS: TRY_EXPONENT_BOOTSTRAP_CONTRACT_G
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_THETA_TO_F_THETA_FIXED_POINT_HALF
SPEC_FREEZE_COMMIT: 8f3eed8c10a136b4614bd5f21d6436ec6a25f18d
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_EXPONENT_BOOTSTRAP_2026-11-06_G.md
SPEC_CHANGED_AFTER_FREEZE: false
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_F_COMMIT: ed480327be4c37df57519cc5c06d4d7ecc3090e0
INPUT_F_BLOB: 642e3d6e6842a18ad04d7d11049404e356823413
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_EXPONENT_BOOTSTRAP_2026-11-06_G.md
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
ANSWER: VALID_CONDITIONAL_BOOTSTRAP_NOT_AN_ARITHMETIC_IMPROVEMENT
PROVED_STEPS:
  - {id: FINITE_ITERATION_PER_EPSILON_CLOSURE, scope: ABSTRACT, verifier: PAPER}
  - {id: GLOBAL_PSI_EXPONENT_LIMIT_EXCLUDES_RIGHT_ZEROS, scope: COFINAL_FAMILY, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: ALL_DYADIC_WINDOWS_RETURN_TO_GLOBAL_ERROR, scope: ABSTRACT, verifier: PAPER}
  - {id: NONLINEAR_ENVELOPE_IMPLIES_AFFINE_EXPONENT_CONTRACTION, scope: ABSTRACT, verifier: PAPER, type: IMPLICATION_ONLY}
RH_GAP: NO_SOURCE_DERIVATION_OF_AN_EXPONENT_IMPROVEMENT_WITH_A_PROVED_START
MINIMAL_MISSING_IDENTITY: "For some fixed 0<q<1, prove H(theta)=>H(1/2+q*(theta-1/2)) for every 1/2<theta<=1, with H defined in section 1. This is a sufficient proposed method, not a newly proved arithmetic estimate."
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PROGRESS_SCOPE: QUANTIFIER_CONTRACT_ONLY_NOT_NEW_NUMBER_THEORY
RH_SIGN_PROGRESS: NONE
KILLS: []
DOES_NOT_KILL: [RH, EXPONENT_BOOTSTRAP, SOURCE_SPECIFIC_PHASE_CONTROL, BALANCED_GREEN_METHOD]
DISCRIMINATOR: "A nonzero Mellin pole at beta>1/2 must block a genuine exponent improvement below beta; contraction of notation or a phase average is insufficient."
REOPEN_TRIGGER: SOURCE_EXACT_SELF_IMPROVEMENT_WITH_UNCHANGED_DOMAIN_AND_AN_ACCESSIBLE_START
CLOSES: [LOGICAL_ITERATION_AND_CONSTANTS_AUDIT]
OPENS: []
COGNITIVE_OPERATOR: QUANTIFIER_AUDIT_AND_BOOTSTRAP
ROUTE_SCORE: 3
NUMERICAL_TESTS: NOT_RUN
EXACT_TESTS: RATIONAL_RECURRENCE_FOR_N_ZERO_THROUGH_EIGHT
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
```

Ы. **Да: если доказать настоящий повторяемый шаг улучшения показателя с притяжением к 1/2, RH следует.** Бесконечное вычисление не требуется: для каждого заданного epsilon или предполагаемого правого нуля хватает конечного числа шагов. Но существование неподвижной точки само по себе ничего не доказывает. В этой записи проверена логика схемы; арифметическое улучшение показателя НЕ получено.

## 1. Какой именно показатель улучшаем

[ABSTRACT / COFINAL_FAMILY | PAPER для определения и начальной оценки.]

Во избежание подмены объекта положим

    D(x)=psi(x)-x,  psi(x)=sum_(n<=x) Lambda(n),
    H(theta): forall epsilon>0 exists C>0, X0>=2:
              forall real x>=X0, |D(x)|<=C*x^(theta+epsilon).

theta здесь — показатель роста ошибки, не функция Чебышёва vartheta и не показатель среднего по фазам. Все prime powers входят в Lambda.

Начало H(1) безусловно: Lambda(n)<=log n, поэтому |D(x)|<=x(log x+1), а log x+1<=C_epsilon*x^epsilon. Даже PNT для этого старта не требуется.

THEOREM T1: NIST DLMF 25.16.4 утверждает H(1/2) <=> RH. Проверена текущая HTML-формулировка и квантор «for every epsilon>0». Доказательство нужного прямого направления дано в §3. THEOREM T2: DLMF 25.4.3–25.4.4 — функциональное уравнение и точное определение xi. Никакого утверждения о простоте нулей не используется. Указанная на странице 25.16 поправка к обозначению гармонических чисел относится к другой формуле.

```text
https://dlmf.nist.gov/25.16#E4
https://dlmf.nist.gov/25.4#E3
https://dlmf.nist.gov/25.4#E4
```

Вход F прочитан по точному commit/blob из YAML, включая его границу: доказано среднее по всем периодическим сдвигам, а не bound заданной фазы. Это inherited PAPER, не новый аудит всей прежней цепочки.

## 2. Теорема замыкания bootstrap

[ABSTRACT | PAPER: условная импликация; арифметическая посылка ниже CONDITIONAL.]

Пусть theta_0=1 и доказано одно правило

    H(theta) => H(f(theta)),  1/2<theta<=1,

где итерации theta_(n+1)=f(theta_n) остаются в [1/2,1] и стремятся к 1/2. Тогда H(1/2), следовательно RH.

Доказательство. Конечной индукцией H(theta_n) верно для каждого целого n. Для заданного epsilon>0 выбираем КОНЕЧНОЕ n с theta_n-1/2<epsilon/2. Применяем H(theta_n) с потерей epsilon/2. Получаем для всех достаточно больших x:

    |D(x)|<=C_(n,epsilon)*x^(theta_n+epsilon/2)
            <=C_(n,epsilon)*x^(1/2+epsilon).

Это H(1/2). Константа и начальный порог могут зависеть от n и epsilon и расти сколь угодно быстро; они лишь должны быть конечны. Их равномерность по n НЕ нужна. Порядок кванторов:

    epsilon -> finite n -> C_(n,epsilon), X_(n,epsilon)
            -> ALL x>=X_(n,epsilon).

Нельзя вместо этого фиксировать x и посылать n в бесконечность: пороги X_(n,epsilon) могут превысить этот x. QED.

Простой достаточный контракт:

    f(theta)=1/2+q*(theta-1/2),  fixed 0<q<1.

Тогда theta_n=1/2+q^n/2. При q=1/2 получаем

    1 -> 3/4 -> 5/8 -> 9/16 -> 17/32 -> ...,
    theta_n=1/2+2^(-n-1).

Это ИЛЛЮСТРАТИВНАЯ искомая рекурсия, не доказанная оценка для настоящей psi. Равномерное геометрическое сжатие не обязательно: достаточно доказанной сходимости итераций. Например, непрерывность f на [1/2,1], f(1/2)=1/2 и 1/2<=f(theta)<theta при theta>1/2 обеспечивают её: убывающий предел обязан быть неподвижной точкой, а выше 1/2 таких точек нет.

## 3. Почему конечного числа шагов достаточно против любого нуля

[COFINAL_FAMILY | PAPER: импликация из H(theta), не новая zero-free область.]

При Re s>1 Euler product и интегрирование по частям дают

    -zeta'(s)/zeta(s) = s/(s-1)
                        + s*integral_1^infinity D(x)x^(-s-1)dx.

Если H(theta) выполнено, интеграл справа голоморфен при Re s>theta. На каждом компактном подмножестве берётся epsilon меньше расстояния до границы; абсолютная сходимость и её локальная равномерность следуют из определения H(theta).

Тождество мероморфно продолжается из Re s>1. Поэтому в Re s>theta нет нуля zeta: его логарифмическая производная имела бы полюс с ненулевым целым вычетом. Полюс s=1 уже явно выделен и не является нулём.

Пусть предположен нуль rho с beta=Re rho>1/2. Выбираем конечное n так, чтобы theta_n<beta. Тогда H(theta_n) запрещает этот нуль. Все правые нули исключены; стандартное xi(s)=xi(1-s) исключает и левые. Не нужно предполагать, что supremum действительных частей нулей достигается.

Важное различие: результат итерации — оценки x^(1/2+epsilon) ДЛЯ КАЖДОГО epsilon, а не O(sqrt x) с одной константой. Функция sqrt(x)*log x удовлетворяет первым и не удовлетворяет второму. Для RH достаточно первых.

## 4. Где bootstrap может оказаться пустым

[ABSTRACT | PAPER для контрпримеров и логических границ.]

Неподвижная точка не означает притяжение: f(theta)=theta тоже фиксирует 1/2, но не улучшает ничего.

Нужен доступный старт. Правило, доказанное лишь при theta<1, не запускается из H(1). Из качественной PNT D(x)=o(x) не следует H(theta_0) для какой-либо фиксированной theta_0<1: функция x/log x — прямой логический контрпример этой импликации. Нельзя выдавать логарифмическую экономию за фиксированный выигрыш степени.

Нужно контролировать потери. Если получается только

    theta_(n+1)=1/2+q*(theta_n-1/2)+eta

с одним НЕУСТРАНИМЫМ eta>0, предел равен 1/2+eta/(1-q), а не 1/2. При q=1/2, eta=1/100 это 13/25. Напротив, сколь угодно малая потеря, разрешённая заново на каждом конечном применении и корректно включённая в H(theta), не мешает доказательству §2. Конечные степени log x также поглощаются epsilon.

Нужно сохранять область и объект. Улучшение среднего по сдвигам нельзя подавать следующему шагу как улучшение фиксированного окна. Улучшение только cross X_N не является оценкой всей Z_N. Убывающие неограниченные множества допустимых N могут иметь пустое пересечение: например, S_n={N>=n}. Нельзя без receiver или диагонального выбора переносить по таким множествам бесконечную итерацию.

## 5. Точный возврат от окон и граница предыдущего F

[ABSTRACT | PAPER.]

Для реальных x>=2 положим

    W(x)=psi(x)-psi(x/2)-x/2=D(x)-D(x/2).

Если при некотором a>0 выполнено |W(x)|<=C*x^a для ВСЕХ x>=X0, телескопирование даёт

    D(x)=D(x/2^J)+sum_(j=0)^(J-1)W(x/2^j),
    |D(x)|<=B0+C*x^a/(1-2^(-a)),

где J выбран так, что X0<=x/2^J<2X0, а B0 — конечный максимум |D| на этом фиксированном компакте. Поэтому глобальные оценки W и D имеют один epsilon-показатель. Это законный оконный интерфейс для §2. Он требует всех нужных масштабов, не одной неограниченной S.

Но фактический f_N из F не равен 1-Lambda. На его head f_N(k)=c_N-Lambda(k), а после N добавляется -mu(k)log(k/N). Нельзя молча заменить c_N на 1 или удалить хвост. Чтобы применять §2 к этому объекту, нужны отдельная source-exact стрелка к D и доказанное улучшение той же фиксированной нормы.

F даёт для его периодических сумм S_(N,H)(t) лишь

    mean_t |S_(N,H)(t)|^2 <= 7N/2.

Для заданной фазы t0 точно

    |S_(N,H)(t0)|^2=V_(N,H)+Delta_(N,H)(t0).

Пример того, какой НОВЫЙ estimate мог бы давать желаемую рекурсию: из допустимой входной theta-оценки вывести односторонний bound

    Delta_(N,H)(t0) <= C_(theta,epsilon)*N^(theta+1/2+epsilon)

на всех требуемых фиксированных окнах. Тогда извлечение корня даёт показатель theta/2+1/4 (с epsilon-потерей). Сам этот bound не доказан; обычная ортогональность усредняет Delta в ноль, но не даёт его верхней оценки в t0. Даже доказанный локальный шаг ещё обязан иметь receiver для всей цели RH.

## 6. Один явный шаблон настоящей самоподтягивающейся оценки

[ABSTRACT | PAPER для импликации; source-bound ниже CONDITIONAL.]

Определим B(X)=1+sup_(1<=x<=X)|D(x)|. Если из арифметики удалось бы получить для каждого eta>0

    B(X)^2 <= C_eta * [X^(1/2+eta) B(2X)+X^(1+eta)]

при всех достаточно больших X, то H(theta) давало бы H(theta/2+1/4). Действительно, при H(theta) имеем B(2X)<=C_(theta,delta)X^(theta+delta). Подставляем, извлекаем корень и выбираем eta,delta сколь угодно малыми. Для theta>=1/2 второй член не ухудшает показатель. Старт H(1) и §2 завершили бы RH.

Эта формула НЕ получена и не объявляется слабой известной леммой. Это спецификация нужного нового неравенства, показывающая, где в реальной оценке должна появиться степень 1/2. Доказать лишь другой вид записи того же неизвестного максимума недостаточно.

## 7. Отрицательный контроль, предсказания и остаточная задача

[ABSTRACT | PAPER для контроля; будущая арифметическая лемма CONDITIONAL.]

Явный тест против универсального bootstrap без source-арифметики:

    D_beta,gamma(x)=x^beta*cos(gamma*log x),
    1/2<beta<1, gamma!=0.

У него H(beta) верно. Но H(f(beta)) ложно для каждого f(beta)<beta: выбрать epsilon<beta-f(beta) и x_j=exp(2*pi*j/|gamma|). Значит простое наличие гладкости, колебаний или Mellin-представления не даёт contraction. В полном источнике аналогичный дискриминатор — несокращённый полюс логарифмической производной в правом нуле.

Это не ещё один изменённый источник настоящей zeta. Для DMV, DH и planted quartet потенциальный source-return должен сохранять их собственный правый полюс; арифметический шаг ниже его beta там обязан отказать. Для self-dual plants Q*xi нельзя отбросить Q'/Q или объявить их completion стандартной xi. У counterarray R9 нарушена mu*1=epsilon, поэтому он не проходит source-идентичности настоящей psi. Собственный положительный контроль кривой из прежних pins, 2cosh((log 3)(s-1/2)), имеет нули с Re s=1/2 непосредственно; ordinary mu и psi ему не навязываются. Новая арифметическая лемма, которую можно было бы полностью проверить на этих мирах, здесь ещё не построена. Доказанная логическая импликация намеренно не различает миры; различать должен её отсутствующий поставщик.

P1 HIT: §2, без uniform-in-iteration констант. P2 HIT: притяжение существенно. P3 HIT: epsilon-endpoint достаточен, O(sqrt x) не выведено. P4 HIT: область F не стала глобальной fixed-phase областью.

Точная рациональная рекурсия проверена для n=0,...,8; результат совпал с 1/2+2^(-n-1). Проверен fixed-loss предел 13/25. Это контроль алгебры, не эксперимент над zeta и не сертификат RH. Теорема индукции охватывает все конечные n независимо от этой проверки.

Два направления продолжения: (A) source-specific оценка фазового дефекта с нужным новым показателем и полным receiver — различающая сила высокая, аналитическая стоимость высокая; (B) прямое самоподтягивающееся неравенство для глобальной ошибки, например §6, — различающая сила высокая, стоимость очень высокая. Ни один поставщик пока не доказан. Численный почти ноль не различает их истинность; нужен строгий signed bound на всей заявленной области.

K8A: DOWNSTREAM_CONSUMER=RH; ACTUAL_CONSUMER_REQUIREMENT=H(1/2) либо другой доказанный source-receiver; ORIGINAL_REQUESTED_OBJECT=повторяемое улучшение theta; ORIGINAL_OBJECT_IS=NOT_NECESSARY как метод; KNOWN_WEAKER_INTERFACES=любая доказанная последовательность допустимых глобальных показателей, сходящаяся к 1/2; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=точный контракт, не новая оценка простых; REOPEN_TRIGGER=source-derived exponent gain с доступным стартом.

```yaml
iteration:
  target: GENUINE_SOURCE_EXPONENT_CONTRACTION
  status: OPEN
  cognitive_operator_used: QUANTIFIER_AUDIT_AND_BOOTSTRAP
  new_gap_name: SAME_SOURCE_SAME_DOMAIN_IMPROVEMENT_STARTING_FROM_ONE
  invariant_learned: FINITE_ITERATION_PER_EPSILON_SUFFICES_WITH_NONUNIFORM_CONSTANTS
  forbidden_future_move: FIXED_POINT_OR_PHASE_MEAN_AS_PROOF_OF_ATTRACTION_FOR_THE_TRUE_SOURCE
  next_decisive_test: DERIVE_AND_AUDIT_THE_FIRST_ACTUAL_EXPONENT_GAIN
  route_score: 3
```

Вердикт: логическая схема владельца корректна после указанных уточнений. Арифметический шаг отсутствует; RH не доказана. Freeze не менялся. Записаны только freeze и этот новый verdict под docs/routeB_bus/proshka/; commit и blob финальной записи сообщаются после удалённого readback. Историческая новизна bootstrap или Mellin-аргумента не заявляется. PAPER, без Lean, Arb и независимого аналитического аудита.
