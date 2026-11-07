# STATUS: TRY_BACKWARD_BOOTSTRAP_DESIGN_H

```yaml
STATUS: TRY_BACKWARD_BOOTSTRAP_DESIGN_H
OPERATIVE_CLASS: TRY_BACKWARD_BOOTSTRAP_DESIGN_H
DATE: 2026-11-07
AUTHORITY: OWNER_REQUEST_BACKWARD_DECOMPOSITION_FROM_EXPONENT_IMPROVEMENT
SPEC_FREEZE_COMMIT: 5c21d42ff6f0a6ce41f7a6079aa13da5210ef0dc
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_BACKWARD_BOOTSTRAP_DESIGN_2026-11-07_H.md
SPEC_CHANGED_AFTER_FREEZE: false
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_G_COMMIT: 6a1119c4eaa27c539db6d5acf115a84bc0c2cc8c
INPUT_G_BLOB: 10e8c1d53654b14a70199fdfbadaff43fb4fb6b1
INPUT_F_COMMIT: ed480327be4c37df57519cc5c06d4d7ecc3090e0
INPUT_F_BLOB: 642e3d6e6842a18ad04d7d11049404e356823413
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_BACKWARD_BOOTSTRAP_DESIGN_2026-11-07_H.md
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
ANSWER: DEPENDENCY_DESIGN_WITH_EXACT_SOURCE_MATCH_NOT_AN_ARITHMETIC_BOUND
PROVED_STEPS:
  - {id: GENERAL_P_VERSUS_R_FEEDBACK_CONTRACT, scope: ABSTRACT, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: QUOTED_QUADRATIC_TEMPLATE_EQUIVALENT_TO_RH, scope: COFINAL_FAMILY, verifier: PAPER, type: EQUIVALENCE_ONLY}
  - {id: EXACT_CENTERING_AWARE_DYADIC_VARIANCE_RETURN, scope: FINITE_CELL, verifier: PAPER}
  - {id: JOINT_RESIDUAL_BOUND_IMPLIES_REPEATED_EXPONENT_GAIN, scope: COFINAL_FAMILY, verifier: PAPER, type: IMPLICATION_ONLY}
RH_GAP: SOURCE_DERIVED_ONE_SIDED_BOUND_FOR_THE_JOINT_FIXED_PHASE_AND_CENTERING_RESIDUAL
MINIMAL_MISSING_IDENTITY: "For every eta>0, Rjoint_N <= C_eta*(N^(1/2+eta)*B(2N)+N^(1+eta)) for all sufficiently large integers N; Rjoint is (6). Proposed sufficient interface only; not proved."
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PROGRESS_SCOPE: BACKWARD_DEPENDENCY_CONTRACT_NOT_NEW_NUMBER_THEORY
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: [CORRECTED_SAME_OBJECT_RULE, EXACT_CENTERING_AWARE_MATCH_TO_PREVIOUS_VARIANCE]
OPENS: []
DOES_NOT_KILL: [RH, EXPONENT_BOOTSTRAP, BOUNDED_NB_SUBSEQUENCES, OTHER_SOURCE_CORRECT_RECEIVERS]
DISCRIMINATOR: A proved source-specific exponent gain must fail for a genuine right-half-plane pole; small averages or chosen recurrences do not test this.
REOPEN_TRIGGER: An independent estimate of the joint residual, or a genuinely weaker quantitative interface with a complete return.
COGNITIVE_OPERATOR: BACKWARD_DEPENDENCY_DESIGN
ROUTE_SCORE: 3
NUMERICAL_TESTS: NOT_RUN
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
```

Ы. **Идея — проектировать доказательство от результата назад: нужный вывод → достаточная оценка → её точные зависимости → арифметическая лемма.** Но сам выбор желаемой оценки ничего не доказывает. Ниже отделены доказанные переходы от отсутствующего поставщика оценки. Нового выигрыша в распределении простых здесь нет.

## 1. Что сохранять при декомпозиции

[ABSTRACT | PAPER: логический контракт.]

Поправка к прежней формулировке «нельзя менять объект»: менять представление и вспомогательный объект МОЖНО. Нужен доказанный количественный возврат к выбранной исходной цели, с сохранением области, кванторов и цены ошибок. Точное равенство не обязательно: достаточны корректные односторонние оценки.

Например, переход к среднему по фазам допустим как промежуточный шаг, но для оценки фиксированной фазы требуется отдельная теорема. Аналогично, ограниченность NB-остатков на неограниченной подпоследовательности может дать RH через свой receiver; она не является оценкой ошибки psi на каждом большом X.

Неподвижная точка нужна только для выбранной итерационной архитектуры. Прямое доказательство требуемого знака или другого достаточного утверждения не обязано иметь никакой итерации. Bootstrap — кандидат метода, не новая обязательная предпосылка RH.

## 2. Сначала вычислить, какого неравенства достаточно

[ABSTRACT | PAPER: условная теорема.]

Пусть

    D(x)=psi(x)-x,
    B(X)=1+sup_(1<=x<=X)|D(x)|,
    H(theta): for every epsilon>0, B(X)=O_epsilon(X^(theta+epsilon)).

Фиксируем p>r>=0 и lambda>=1. Предположим, что для каждого eta>0 доказано при всех достаточно больших X

    B(X)^p <= C_eta *
       [X^((p-r)/2+eta)*B(lambda*X)^r + X^(p/2+eta)].       (1)

Тогда для theta>=1/2

    H(theta) => H(1/2+(r/p)*(theta-1/2)).                   (2)

Доказательство: подставить B(lambda*X)=O_delta(X^(theta+delta)) в (1). После корня степени p показатели равны

    (p-r)/(2p)+(r/p)*theta+(eta+r*delta)/p,
    1/2+eta/p.

Для любого заданного выходного epsilon выбираем положительные eta,delta достаточно малыми. Это (2). Константы и пороги могут зависеть от этих параметров и каждого конечного номера итерации. При r=0 получается прямой endpoint-bound; при 0<r<p — сжатие с коэффициентом r/p.

Предложенный ранее шаблон имеет p=2, r=1, lambda=2. Поэтому неподвижная точка 1/2 не угадана: она задаётся балансом степеней.

**Тест потерь.** Если вместо X^((p-r)/2+eta) возникает X^((p-r)/2+delta0+eta) с фиксированной delta0>0, терминальный показатель сдвигается на delta0/(p-r). При p=2,r=1 эта цена равна delta0. Поэтому положительная потеря степени в обратном переходе может разрушить именно нужный endpoint. Конечная степень log X поглощается произвольно малым epsilon; фиксированная степень X — нет.

Если справа дополнительно стоит kappa*B(X)^p с постоянной 0<=kappa<1, её можно перенести влево. Коэффициент kappa=1 не даёт такого замыкания. Ни (1), ни подобный коэффициент поглощения для настоящего источника здесь не доказаны.

### Сила исходного шаблона

[COFINAL_FAMILY | PAPER: эквивалентность, не арифметический прогресс.]

Для настоящей psi семейство неравенств

    B(X)^2 <= C_eta * [X^(1/2+eta)*B(2X)+X^(1+eta)]         (3)

для всех eta>0 эквивалентно RH.

Прямая стрелка: H(1) следует из Lambda(n)<=log n. Итерация (2) даёт theta_j=1/2+2^(-j-1). Для каждого epsilon достаточно конечного j, затем оценки H(theta_j) с оставшимся epsilon-запасом. Получается H(1/2), а значит RH.

Обратная стрелка: RH даёт B(X)=O_eta(X^(1/2+eta/2)); следовательно B(X)^2=O_eta(X^(1+eta)), чего уже достаточно для (3). Использована классическая эквивалентность DLMF 25.16.4. Таким образом (3) — удобная точка сборки доказательства, но не заведомо более слабая задача.

## 3. Конкретная сборка из наших исходных формул

[FINITE_CELL | PAPER для тождеств; bound V ниже — inherited PAPER F.]

Чтобы не требовать прямого сравнения прежней Z_N с B(N)^2, используем точный оконный интерфейс. Для N>=3 положим

    h=floor(N/2), H=N-h,
    W_N=psi(N)-psi(h)-H=D(N)-D(h).                         (4)

Если |W_N|=O(N^a) для ВСЕХ достаточно больших целых N и a>0, то телескопирование по N,floor(N/2),floor(N/4),... даёт |D(N)|=O(N^a). Действительно, сумма степенных бюджетов не больше N^a/(1-2^(-a)); конечный начальный остаток ограничен. Для вещественного x, psi(x)=psi(floor x), а |x-floor x|<1. Значит тот же показатель возвращается к B(X).

Теперь сохраняем НАСТОЯЩИЙ источник F:

    L=log N,
    a_n=mu(n)*log(N/n)/L, 1<=n<=N, a_1=1,
    s_N=sum a_n/n, c_N=L*s_N,
    q_1=1-s_N, q_n=a_n (n>=2),
    A_N(k)=sum_(n|k,n<=N)q_n,
    f_N(k)=-L*A_N(k),
    S_N(t)=sum_(v=1)^H f_N(t+v).

На h<k<=N, где k>=2, точная divisor-свёртка даёт f_N(k)=c_N-Lambda(k). Поэтому

    S_N(h)=H*c_N-[psi(N)-psi(h)],
    g_N=H*(c_N-1),
    W_N=g_N-S_N(h).                                       (5)

Это конкретное место арифметики обычных целых: sum_(d|k)mu(d)=1_(k=1) и sum_(d|k)mu(d)log d=-Lambda(k). Все proper prime powers сохранены. Мёбиусова добавка для k>N здесь не удалена из источника: она не входит в выбранное окно (4). Не утверждается, что (4) равно прежнему head-tail cross.

Пусть P_N=lcm(1,...,N). Из F для той же длины H и ТОГО ЖЕ периодического тока имеем

    V_N=(1/P_N)sum_(t=1)^P_N S_N(t)^2 <= 7N/2.

Все числа действительные. Определим полностью вычислимый подписанный остаток

    Delta_N=S_N(h)^2-V_N,
    Rjoint_N=Delta_N-2*g_N*S_N(h)+g_N^2.                    (6)

Тогда ТОЧНО

    W_N^2=V_N+Rjoint_N.                                    (7)

В (7) три содержательные части: явно заданный оконный объект W_N; положительная вычислимая форма V_N с известной верхней границей; точный совместный фазово-центровочный остаток Rjoint_N. Это декомпозиция, а не оценка последнего члена.

**Нельзя выкинуть центрирование.** Из старого |c_N|<5 не следует полезная малость g_N=H(c_N-1): такая оплата даёт лишь O(N), а квадрат — O(N^2). Раздельное взятие модулей у Delta_N, -2*g_N*S_N(h), g_N^2 может уничтожить нужное сокращение. Предлагается оценивать их совместно, а не превращать точное сокращение в три независимых требования.

## 4. Точная арифметическая лемма, которая замкнула бы эту сборку

[COFINAL_FAMILY | CONDITIONAL для посылки; PAPER для импликации.]

Один достаточный кандидат:

    For every eta>0 there exist C_eta,N_eta such that
    for EVERY integer N>=N_eta,
    Rjoint_N <= C_eta *
       [N^(1/2+eta)*B(2N)+N^(1+eta)].                      (8)

(8) НЕ ДОКАЗАНО. По (7) и V_N<=7N/2 оно влечёт такую же оценку для W_N^2. При H(theta) подстановка B(2N)=O_delta(N^(theta+delta)) даёт

    W_N=O_epsilon(N^(theta/2+1/4+epsilon)).

Телескопирование (4) возвращает H(theta/2+1/4). Начало H(1) доступно; конечная итерация для каждого epsilon даёт RH.

Здесь использовано конкретное уже доказанное среднее, но НЕ объявлено, что оно контролирует нужную фазу. Новое недостающее утверждение — (8), причём со всеми большими N, не только с некоторыми N из S.

**Честная граница.** Так как Rjoint_N=W_N^2-V_N, новая запись не уменьшает арифметическую трудность автоматически. Она показывает точное место, куда должна войти независимая оценка. Если дальнейшее «доказательство (8)» использует уже желаемый bound W_N, оно круговое.

## 5. Что из наработок действительно подходит

[FINITE_CELL / COFINAL_FAMILY | PAPER для сопоставления контрактов; прежние теоремы — inherited PAPER.]

| Вход | Что поставляет | Чего не поставляет |
|---|---|---|
| G: bootstrap | Конечную итерацию при каждом epsilon и Mellin-выход в RH | Ни одного фактического улучшения theta |
| F: периодическая дисперсия | Положительную часть V_N<=7N/2 в (7), при любой длине H | Фиксированную фазу h и совместный остаток (6) |
| Точные divisor-формулы F | Равенство (5) с настоящей c_N | Малость c_N-1 или фазового остатка |
| Green/NB-ветка, закреплённая в G/F | Другой receiver: bounded source-correct subsequence => RH | Не автоматически same-scale bound для B(X) или окно (4) |

Следовательно не нужно пытаться вставить КАЖДУЮ прежнюю лемму в новую схему. Нужны только леммы, закрывающие один из указанных переходов. Ограниченность на S и оценка при всех больших N — две разные допустимые архитектуры; у каждой должен быть собственный законченный возврат.

## 6. Как выбирать следующую декомпозицию

[ABSTRACT | PAPER: рабочий контракт, не утверждение о наличии поставщика.]

Для каждого кандидата фиксировать: точный вход; точный выход; необходимый диапазон; потери норм и степеней; роль арифметики; и прямое следствие для конечной цели.

Порядок работы:

1. Зафиксировать конечный receiver: здесь H(1/2), либо прежний bounded-NB receiver.
2. Назвать достаточную улучшающую оценку и проверить её итерацию ДО попытки её доказать.
3. Разложить её на точные зависимости: return, положительная оплаченная часть, подписанный остаток, допустимые границы.
4. Подставить лишь те доказанные результаты, у которых совпали нормы и кванторы.
5. Работать над одним отсутствующим арифметическим неравенством; если декомпозиция не позволяет оценить ничего нового, сменить её, а не переименовать остаток.

«Уперлись в стену — применяем» означает этот анализ зависимостей, а НЕ автоматическое право написать (1) или извлечь квадратный корень из желаемой правой части. Новый объект оправдан тем, что делает хотя бы одну отсутствующую зависимость доказуемой.

## 7. Сильнейшая атака, контроли и статус

[ABSTRACT | PAPER для логических тестов; полной новой source-леммы для проверки нет.]

Для модели B(X)=X^beta с beta>1/2 условие (3) нарушается при любом 0<eta<beta-1/2: левая степень 2beta больше обеих правых степеней. Поэтому доказательство шаблона из одной положительности, монотонности и полиномиального роста заведомо недостаточно. Это тест общего аргумента, не другая настоящая psi и не KILL данного маршрута.

В source-контролях DMV требует собственного generalized-integer источника, DH — собственных коэффициентов и completion; обычные divisor/Mellin-формулы им не приписываются. Для Q*xi дополнительный local factor не удаляется. R9-контрмассив не сохраняет точную mu-свёртку в (5). Кривая над F3 проходит свой прежний периодизационный receiver, но не обязана иметь наш ordinary-mu ток. Завершённой новой арифметической леммы (8) пока нет, поэтому полная проверка этой леммы на всех мирах НЕ заявляется. Чистая логика bootstrap намеренно универсальна; различать источники должен отсутствующий арифметический шаг.

Два направления: A — прямая совместная оценка (6), высокая различающая сила и высокая аналитическая цена; B — сохранить NB/S-область и искать достаточное улучшение её нормы с отдельным доказанным возвратом, также высокая цена. Никакой ранее доказанной необходимости именно (3) как метода нет; его эквивалентная сила не делает конкретную технику обязательной.

Прогнозы freeze: P1 HIT — доказаны обе стрелки для (3). P2 HIT — (1)-(2) и потеря delta0/(p-r). P3 HIT — точная c_N-поправка в (5). P4 HIT — (6)-(7), без upper bound остатка. P5 HIT — телескопирование требует всех нужных окон. Эти отметки относятся к аналитическим проверкам контрактов; численного теста распределения простых не было.

K8A: DOWNSTREAM_CONSUMER=RH; ACTUAL_CONSUMER_REQUIREMENT=H(1/2) для выбранного пути или иной законченный receiver; ORIGINAL_REQUESTED_OBJECT=обратная декомпозиция доказательства; ORIGINAL_OBJECT_IS=NOT_NECESSARY как конкретный метод; KNOWN_WEAKER_INTERFACES=другие сходящиеся правила улучшения либо исходный NB/S receiver; FAILURE_TYPE=NO_DERIVATION для (8); EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=точная сборка с учётом центрирования, не новая оценка простых.

```yaml
iteration:
  target: SOURCE_DERIVED_EXPONENT_GAIN
  status: OPEN
  cognitive_operator_used: BACKWARD_DEPENDENCY_DESIGN
  new_gap_name: JOINT_FIXED_PHASE_AND_CENTERING_UPPER_BOUND
  invariant_learned: CHANGE_REPRESENTATIONS_ONLY_WITH_A_QUANTITATIVE_RETURN
  forbidden_future_move: TREAT_A_CHOSEN_NONLINEAR_ENVELOPE_AS_A_PROVED_REDUCTION_IN_DIFFICULTY
  next_decisive_test: DERIVE_AN_INDEPENDENT_ONE_SIDED_ESTIMATE_OF_RJOINT_NOT_W_N_RENAMED
  route_score: 3
```

## 8. Источники и доставка

G и F прочитаны в текущем контексте и сверены по bytes: локальные файлы имеют соответственно 20606 и 39496 bytes; Git blobs совпадают с YAML. G получен через GitHub, F дополнительно прочитан из смонтированного полного файла. Bootstrap получен заново с rh_clean. Импортированные результаты — PAPER, без нового независимого аудита.

THEOREM, внешний факт: NIST DLMF 25.16.4, именно квантор «для каждого epsilon>0», проверен в текущем HTML. Пометка erratum на странице относится к обозначению гармонических чисел в другой части. Внешний источник используется только для RH <=> H(1/2), не для оценки (8).

```text
https://dlmf.nist.gov/25.16#E4
G: docs/routeB_bus/proshka/PROSHKA_VERDICT_EXPONENT_BOOTSTRAP_2026-11-06_G.md
F: docs/routeB_bus/proshka/PROSHKA_VERDICT_SQRT_WINDOW_BALANCE_2026-11-06_F.md
```

Записываются только отдельный freeze и этот новый файл в указанную inbox-ветку. Старые verdicts не меняются. Commit/blob финальной записи сообщаются после readback. Это контракт исследования и доказанные условные переходы, не доказательство RH. Lean, Arb, новые численные тесты и независимый аналитический аудит не выполнены.
