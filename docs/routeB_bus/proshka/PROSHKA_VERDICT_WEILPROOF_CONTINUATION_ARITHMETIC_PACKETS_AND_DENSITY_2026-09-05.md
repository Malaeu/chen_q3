# STATUS: TRY_WEIL_COUPLED_ARITHMETIC_OVERLAP
```yaml
OPERATIVE_CLASS: TRY_WEIL_COUPLED_ARITHMETIC_OVERLAP
PRIMARY_COUNT: 1
RESULT: PARTIAL_PROOF_WITH_PRECISE_REMAINDER
RELATED_REQUEST_ID: REQ-2026-09-04-WEILPROOF
BOUNDARY_ID: GOAL058_DIRECT_WEIL_SOURCE_PROOF_CONSTRUCTION
ARTIFACT_ROLE: OWNER_DIRECT_PAPER_RESEARCH_CONTINUATION
AUTOMATED_REQUEST_ADMISSION: NOT_CLAIMED
NEW_REQUEST_ID_INVENTED: false
CODEX_BINDING_VERIFIED: false
PREVIOUS_EXPECTED_VERDICT_OVERWRITTEN: false
BASE_VERDICT:
  COMMIT: b8b0dc95584907078745bbb5576503268065b1e2
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DIRECT_WEIL_SOURCE_PROOF_2026-09-04.md
  GIT_BLOB: a3fb1622e6792f353a51faa5100185f44da0d511
  READ_IN_FULL_THIS_CONTINUATION: true
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PREWRITE_BRANCH_HEAD_OBSERVED: 158ef1160118e5c2c7f916d97dc7320538b03f4d
CLOSES: []
OPENS: []
CANONICAL_RH_SUPPLIER_COUNT_DELTA: 0
NEW_LOCAL_RESULTS:
  - signed_arithmetic_remainder_has_a_strictly_negative_smooth_direction
  - exact_von_Mangoldt_divisibility_square_identity
  - logarithmic_prime_operator_bound_on_exact_arithmetic_packets
  - full_Weil_lower_bound_for_every_complex_coefficient_vector_on_those_packets
  - quantitative_failure_of_cofinal_fixed_test_recovery
  - exact_near_resonance_and_Gram_terms_for_overlapping_packet_repair
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
INDEPENDENT_PROOF_REVIEW: PENDING
NOVELTY_IN_LITERATURE: NOT_CLAIMED
RH_PROVED: false
W_PROVED: false
C_PROVED: false
F_FOR_LITERAL_CCM_PROVED: false
FINITE_CCM_MATRIX_REPLACED: false
LEAN_SOURCE_WRITTEN: false
LEAN_KERNEL_RUN: false
NUMERICAL_RUN: false
ARISTOTLE_SUBMISSION: false
QUEUE_OR_SHARED_STATE_WRITE: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
SCOPED_KILLS:
  - CODE: KILL_ARITHMETIC_REMAINDER_NONNEGATIVE
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    KILL_EVIDENCE_KIND: STRICT_NEGATIVE_UPPER_BOUND
    EVIDENCE: THIS_DOCUMENT_SECTION_2_EQUATION_S_NEG
    REPAIRED_STATEMENT: retain_the_coupling_between_J_and_S
  - CODE: KILL_NARROW_ARITHMETIC_PACKET_COFINAL_RECOVERY
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    KILL_EVIDENCE_KIND: STRICT_NEGATIVE_UPPER_BOUND_ON_RECOVERY_MARGIN
    EVIDENCE: THIS_DOCUMENT_SECTION_7_EQUATIONS_REC_FAIL_AND_MARGIN
    REPAIRED_STATEMENT: change_the_packet_geometry_and_control_all_new_cross_terms
K8A:
  DOWNSTREAM_CONSUMER: Weil_criterion_on_all_complex_smooth_compact_tests
  ACTUAL_CONSUMER_REQUIREMENT: nonnegative_full_Weil_form_on_every_such_test
  ORIGINAL_REQUESTED_OBJECT: complete_independent_proof_of_W_or_a_sufficient_vanishing_lower_error
  ORIGINAL_OBJECT_IS: PROVED_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - fixed_test_dependent_lower_errors_tending_to_zero_for_each_test
    - all_vector_finite_lower_bounds_plus_same_family_fixed_test_form_recovery
  FAILED_MECHANISM: exact_divisibility_packets_plus_cofinal_density
  FAILURE_TYPE: INCOMPATIBILITY
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: multiplicative_divisibility_energy_with_explicit_support_coverage_audit
  REOPEN_TRIGGER: prove_the_signed_overlap_bound_and_actual_fixed_test_recovery_in_section_8
DISCRIMINATOR:
  SIGN: rigorous_one_sided_bound_on_the_joint_Weil_margin
  COVERAGE: L2_distance_of_one_fixed_nonzero_smooth_test_to_the_same_cofinal_spaces
  ZERO_CONSISTENT_SIGN: INCONCLUSIVE
```

## 0. Результат и границы

Ы. Выполнен новый бумажный проход по самой положительности, а не по рейтингу маршрутов. Полного доказательства RH этот проход не дал. Он дал безусловную положительность полной исходной формы на явных M-мерных пространствах для всех M >= 128, а затем точное опровержение попытки получить из этих пространств кофинальное восстановление тестов. Также опровергнута положительность арифметической поправки самой по себе.

Это новые выводы данного прохода, не заявление о приоритете в литературе. Все доказательства ниже имеют verifier PAPER. Независимая проверка и Lean-формализация не выполнены. Уменьшение канонического списка RH-поставщиков не заявляется.

Предыдущий вердикт сохраняется. Новый текст не является повторной адъюдикацией его request lock и не удостоверяет Codex binding. Другие задачи из очереди не выбирались.

Источники:

[S1] Connes–Consani–Moscovici, Zeta Spectral Triples, arXiv:2511.22755v1, формулы (3.5)–(3.11), Proposition 3.2. В этой сессии прочитан первичный HTML с формулами.

[S5] Connes–Consani, Spectral Triples and Zeta-Cycles, arXiv:2106.01715v1, страница 5, (1.1)–(1.2) и следующий абзац: положительность QW_lambda для всех lambda влечёт RH. Формула и абзац проверены по изображению страницы PDF.

[V0] Предыдущий вердикт, закреплённый в header. Его §§1–2 и §5 используются только после прямой перепроверки алгебры ниже. Его fixed-test Fourier recovery и literal-CCM identity не являются предпосылками новых лемм.

## 1. Исходная полная форма: знаки сохранены

[ABSTRACT][PAPER; определения S1 и повторный прямой вывод]

Для f in C_c^infinity((0,infinity); C) положим g(x)=f(exp x). Тогда du/u=dx, инволюция переходит в g*(x)=conj(g(-x)), а мультипликативная свёртка — в аддитивную. Норма сохраняется. Работаем со всеми комплексными g, без ограничения чётностью.

Обозначим

\[
H=\|g\|_2^2,\qquad
C_g(t)=\Re\int\overline{g(x)}g(x+t)\,dx,
\qquad D_g(t)=2H-2C_g(t)=\|g(\cdot+t)-g\|_2^2,
\]

\[
a(t)=\frac{e^{-t/2}}{1-e^{-2t}},\qquad
c_A=\gamma+\log(8\pi)+\frac\pi2,
\qquad A_\pm(g)=\int g(x)e^{\pm x/2}\,dx.
\]

Полная форма из S1 равна

\[
\boxed{
\mathcal Q(g)=\mathcal D(g)-c_AH+
2\Re(A_+(g)\overline{A_-(g)})-
2\sum_{d\ge2}\frac{\Lambda(d)}{\sqrt d}C_g(\log d),
\quad \mathcal D(g)=\int_0^\infty a(t)D_g(t)\,dt.}
\tag{Q}
\]

Здесь Lambda(d)=log p для d=p^k, иначе 0. Для каждого компактного теста сумма конечна. Если ширина носителя g не превосходит L, слагаемые с log d > L равны нулю.

Проверка константы: исходный архимедов интеграл есть

\[
-(\log(4\pi)+\gamma)H-
2\int_0^\infty a(t)(C_g(t)-e^{-t/2}H)\,dt.
\]

Подстановка C_g=H-D_g/2 даёт (Q), поскольку

\[
\int_0^\infty a(t)(1-e^{-t/2})\,dt
=2\int_0^1\frac{du}{(1+u)(1+u^2)}
=\tfrac12\log2+\tfrac\pi4.
\]

Все интегралы сходятся: для гладкого компактного g имеем D_g(t)=O(t^2) у нуля, а a(t)=O(1/t); на бесконечности a экспоненциально убывает.

Для арифметического разложения положим

\[
\Delta(t)=\sum_{2\le d\le e^t}\Lambda(d)-(e^t-1),\quad
k(t)=a(t)-e^{-t/2}=\frac{e^{-5t/2}}{1-e^{-2t}},\quad d_A=c_A-4,
\]

\[
\mathcal J(g)=\int_0^\infty k(t)D_g(t)\,dt,\qquad
\mathcal S(g)=-2\int_0^\infty C_g(t)e^{-t/2}\,d\Delta(t).
\]

Тогда

\[
\boxed{\mathcal Q(g)=\mathcal J(g)-d_AH+\mathcal S(g).}
\tag{ARITH}
\]

Доказательство: полюсный член равен

\[
2\int_0^\infty C_g(t)(e^{t/2}+e^{-t/2})\,dt.
\]

Вычитание непрерывной части prime-меры оставляет 2 integral C_g(t)e^{-t/2}dt. Это равно 4H - integral e^{-t/2}D_g(t)dt. Получаем (ARITH). Эквивалентная формула, нужная далее:

\[
\boxed{\mathcal S(g)=2\int_0^\infty C_g(t)e^{t/2}\,dt
-2\sum_{d\ge2}\frac{\Lambda(d)}{\sqrt d}C_g(\log d).}
\tag{S}
\]

Таким образом, знак арифметической поправки нельзя выбирать по желанию.

## 2. Первая попытка закрыть знак: S >= 0 неверно для настоящих простых

Лемма 1. [ABSTRACT][PAPER; новый здесь явный контрпример]

Существует g in C_c^infinity(R; C), ||g||_2=1, для которого

\[
\boxed{\mathcal S(g)\le-\frac{\log2}{2\sqrt2}<0.}
\tag{S-NEG}
\]

Доказательство. Возьмём delta=1/256 и любую вещественную неотрицательную гладкую eta с носителем внутри (-delta,delta), нормированную в L2. Положим b=log2 и

\[
g(x)=\frac{\eta(x+b/2)+\eta(x-b/2)}{\sqrt2}.
\]

Пакеты не пересекаются, поэтому H=1. При положительном t автокорреляция может быть ненулевой только на

\[
[0,2\delta]\ \cup\ [b-2\delta,b+2\delta].
\]

В точке t=b она равна 1/2. Между b+2delta и log3 есть положительный промежуток. Поэтому единственный ненулевой prime-вклад в (S) равен log2/sqrt2, включая все простые степени, а не только выбранный вручную член.

По Коши–Буняковскому |C_g(t)| <= 1. Следовательно,

\[
2\int_0^\infty C_g(t)e^{t/2}\,dt
\le12\delta\sqrt2 e^\delta
\le\frac{3\sqrt2}{32}
\le\frac{\log2}{2\sqrt2}.
\]

Здесь использованы e^delta < 2 и log2 > 2/3 > 3/8. Подстановка в (S) доказывает (S-NEG). □

Этот результат не опровергает Q >= 0. Он опровергает только механизм, который объявляет S неотрицательным отдельным слагаемым. На данном тесте именно энергия J должна оплатить и d_A, и отрицательную S. Замена цели совместным неравенством J+S >= d_A H сохраняется.

## 3. Ремонт через арифметику: точная сумма квадратов

Лемма 2. [FINITE_CELL][PAPER; новая здесь конечная факторизация]

Для M >= 2 и всех c=(c_1,...,c_M) in C^M определим

\[
B(y)=\sum_{2\le d\le y}\frac{\Lambda(d)}d,
\quad a_n^{(M)}=\log n+B(M/n),
\]

\[
P_M(c)=2\Re\sum_{\substack{n\ge1,d\ge2\\nd\le M}}
\frac{\Lambda(d)}{\sqrt d}\overline{c_n}c_{nd}.
\]

Тогда

\[
\boxed{
\sum_{n=1}^M a_n^{(M)}|c_n|^2-P_M(c)
=\sum_{\substack{n\ge1,d\ge2\\nd\le M}}
\Lambda(d)\left|c_{nd}-\frac{c_n}{\sqrt d}\right|^2\ge0.}
\tag{DIV}
\]

Доказательство. Раскроем квадрат. Член с |c_n|^2 даёт B(M/n). Для члена с |c_{nd}|^2 положим j=nd и воспользуемся

\[
\sum_{d\mid j}\Lambda(d)=\log j.
\]

Последнее тождество следует из разложения j=product p^{v_p(j)}: каждый p вносит v_p(j) log p. Смешанный член равен -P_M(c). □

Факторизация использует только делимость и буквальные веса фон Мангольдта. Положительность Q не предполагается.

Калибровочный отрицательный plant. При M=2, c=(1,1/sqrt2) правая часть (DIV) равна нулю. Если незаконно удвоить только prime-edge, сохранив диагональ a_n, значение левой части станет -log2 < 0. Поэтому checker, который проверяет только Hermitian-симметрию, это тождество не сертифицирует.

## 4. Явная логарифмическая верхняя граница prime-оператора

Лемма 3. [ABSTRACT][PAPER; элементарная оценка без PNT и RH]

Для всех y >= 1 выполнено

\[
B(y)\le\log y+4\log2.
\tag{B}
\]

Доказательство. Обозначим psi(N)=sum_{d<=N} Lambda(d). Для целого m >= 1 показатель p в binomial(2m,m) равен сумме

\[
\sum_{r\ge1}\left(\left\lfloor\frac{2m}{p^r}\right\rfloor
-2\left\lfloor\frac m{p^r}\right\rfloor\right).
\]

Каждое слагаемое неотрицательно; для m < p^r <= 2m оно равно 1. Поэтому

\[
\psi(2m)-\psi(m)\le\log\binom{2m}{m}\le2m\log2.
\]

Суммирование по двоичным масштабам и округление N вверх до ближайшей степени 2 дают psi(N) <= 4N log2.

Далее по тождеству из предыдущей леммы

\[
\log(N!)=\sum_{d\le N}\Lambda(d)\lfloor N/d\rfloor
\ge N B(N)-\psi(N).
\]

Следовательно, B(N) <= logN + 4log2. Для вещественного y берём N=floor y; случай N=1 тривиален. □

Из (DIV) и (B) для каждого комплексного c немедленно следует

\[
\boxed{P_M(c)\le(\log M+4\log2)\sum_{n=1}^M|c_n|^2.}
\tag{PRIME}
\]

Это оценка всех направлений конкретного арифметического оператора. Следующий раздел доказывает, где именно он совпадает с исходным prime-вкладом Q.

## 5. Точный перенос в исходную форму: логарифмические пакеты

Лемма 4. [FINITE_CELL][PAPER; exact source-form realization]

Пусть M >= 2,

\[
\epsilon_M=\frac1{16M^4},\qquad
x_n=\log n-\tfrac12\log M,\quad 1\le n\le M.
\]

Возьмём любую eta_M in C_c^infinity((-epsilon_M,epsilon_M); C) с нормой 1. Определим

\[
\phi_n(x)=\eta_M(x-x_n),\qquad
V_M=\operatorname{span}_{\mathbb C}\{\phi_1,\ldots,\phi_M\},
\qquad g_c=\sum_{n=1}^M c_n\phi_n.
\]

Тогда

\[
\|g_c\|_2^2=\sum_n|c_n|^2,\qquad
2\sum_{d\ge2}\frac{\Lambda(d)}{\sqrt d}C_{g_c}(\log d)=P_M(c).
\tag{MATCH}
\]

Доказательство. Расстояние между соседними центрами равно log(1+1/n) >= 1/(n+1) >= 1/M. Поэтому носители разных phi_n не пересекаются и Gram-матрица равна I.

Положим R_eta(s)=integral conj(eta(x)) eta(x+s) dx. Она равна нулю при |s| >= 2epsilon_M, а R_eta(0)=1. Имеем точное равенство

\[
\int\overline{g_c(x)}g_c(x+\log d)dx
=\sum_{n,k\le M}\overline{c_n}c_k R_\eta(\log(dn/k)).
\]

Если dn != k, целочисленность даёт

\[
|\log(dn/k)|\ge\log(1+1/M)>1/(2M)>2\epsilon_M.
\]

Если dn=k, корреляция равна 1. Остаются ровно рёбра n -> nd из (DIV). Этот аргумент охватывает все d >= 2, в том числе d > M: для них совпадений нет. □

Это реализация в полной аналитической форме Q, а НЕ утверждение, что V_M есть весь Fourier-mode span CCM. Конечная матрица CCM не переопределялась.

## 6. Новая безусловная нижняя оценка полной формы на всех V_M

Теорема 5. [COFINAL_FAMILY][PAPER]

Для всех целых M >= 128, всех допустимых eta_M и всех комплексных c:

\[
\boxed{\mathcal Q(g_c)\ge\tfrac12\|g_c\|_2^2.}
\tag{PACKET-POS}
\]

Более точно для всех M >= 2:

\[
\mathcal Q(g_c)\ge\mu_M\|g_c\|_2^2,
\]

\[
\mu_M=2\log M-c_A-3\log2-\frac1{8M}
-\frac{e^{\epsilon_M}}{16M^{5/2}}.
\tag{LOWER}
\]

Доказательство.

Архимедова часть. При 2epsilon_M <= t <= 1/(4M) ни один сдвинутый пакет не пересекается ни с самим собой, ни с другим пакетом. Поэтому C_{g_c}(t)=0 и D_{g_c}(t)=2H на всём этом отрезке. На остальной полуоси D >= 0. Используем

\[
2a(t)\ge\frac{e^{-t/2}}t\ge\frac1t-\frac12.
\]

Получаем

\[
\mathcal D(g_c)\ge
\left[\log\frac{1/(4M)}{2\epsilon_M}-\frac1{8M}\right]H
=\left[3\log M+\log2-\frac1{8M}\right]H.
\tag{ARCH}
\]

Полюсный член. Пусть E_M — объединение носителей пакетов. Тогда |E_M| <= 2M epsilon_M, а на E_M выполнено |x| <= (logM)/2 + epsilon_M. Запишем

\[
C=\int g_c(x)\cosh(x/2)dx,\qquad S=\int g_c(x)\sinh(x/2)dx.
\]

Полюсный член равен 2|C|^2-2|S|^2. По Коши–Буняковскому и sinh^2(x/2) <= e^{|x|}/4,

\[
2|S|^2\le2H\int_{E_M}\sinh^2(x/2)dx
\le\epsilon_M M^{3/2}e^{\epsilon_M}H.
\tag{POLE}
\]

Простые. По (MATCH) и (PRIME) их вычитаемый вклад не превосходит (logM+4log2)H.

Складываем (ARCH), -c_AH, (POLE) и отрицательную верхнюю границу prime-вклада. Это доказывает (LOWER), причём все переходы имеют нужное для нижней оценки направление.

Для M >= 128 имеем 2logM >= 14log2. Элементарные границы gamma < 1 и pi < 4 дают c_A < 3+5log2. Следовательно,

\[
2\log M-c_A-3\log2>6\log2-3>1.
\]

Две оставшиеся потери в (LOWER) в сумме меньше 1/4: e^{epsilon_M}<2, M>=2 достаточно для этой грубой оценки. Итак mu_M > 3/4 > 1/2. □

Нижняя граница доказана, а не измерена. Сохранены полюсы, вся prime-сумма, комплексные коэффициенты и L2-норма. Однако она относится к V_M, не ко всем тестам соответствующего окна.

## 7. Сильнейшая атака: кофинальное восстановление не просто не доказано — оно ложно

Лемма 6. [COFINAL_FAMILY][PAPER]

Для каждого фиксированного ненулевого g in C_c^infinity(R; C):

\[
\boxed{
\operatorname{dist}_{L^2}(g,V_M)^2
\ge\|g\|_2^2-\frac{\|g\|_\infty^2}{8M^3},
\qquad
\operatorname{dist}_{L^2}(g,V_M)\longrightarrow\|g\|_2>0.}
\tag{REC-FAIL}
\]

Доказательство. Каждый h in V_M равен нулю вне E_M, причём |E_M| <= 2M epsilon_M=1/(8M^3). Поэтому

\[
\|g-h\|_2^2\ge\int_{E_M^c}|g|^2
\ge\|g\|_2^2-|E_M|\|g\|_\infty^2.
\]

Верхняя граница расстояния ||g||_2 получается выбором h=0. □

Строго отрицательный discriminator для попытки восстановления:

\[
\mathfrak m_M(g):=\tfrac12\|g\|_2^2-
\operatorname{dist}_{L^2}(g,V_M)^2
\le-\tfrac12\|g\|_2^2+\frac{\|g\|_\infty^2}{8M^3}<0
\tag{MARGIN}
\]

при всех достаточно больших M. Это верхняя отрицательная граница, не ошибка достаточного критерия.

Усиление, закрывающее класс аналогичных починок. Пусть M_j -> infinity, R_j -> infinity, M_j/R_j -> infinity. Центры равны log(n/R_j), 1<=n<=M_j. Пусть общий полурадиус носителя delta_j <= C/M_j с фиксированным C. Для каждого фиксированного K>0 объединение носителей E_j удовлетворяет

\[
|E_j\cap[-K,K]|\le
2\delta_j\bigl(R_j e^{K+\delta_j}+1\bigr)\longrightarrow0.
\tag{CLASS}
\]

Действительно, пересекать [-K,K] могут только центры с n <= R_j exp(K+delta_j). Число таких пакетов не превосходит указанной скобки. Теперь повторяем доказательство (REC-FAIL) для g с носителем в [-K,K]. Оно даёт dist(g,V_j) -> ||g||_2.

Таким образом, любая семья этого точно указанного класса, обеспечивающая арифметическую развязку посредством общего малого радиуса O(1/M_j), не восстанавливает фиксированные тесты при двустороннем исчерпании окна. Это НЕ доказательство невозможности иных форм пакетов, переменных ширин, смешанных масштабов или контролируемого перекрытия. Линейные комбинации из разных V_j также не объявляются положительными: их смешанные Q-члены здесь не контролируются.

## 8. Попытка ремонта: все новые члены выписаны, но их знак не доказан

[FINITE_CELL][PAPER; точное тождество для ремонта]

Разрешим eta иметь общий полурадиус delta > 0 без условия разделения и положим x_n=log(n/R), ||eta||_2=1. Тогда

\[
G_{nk}=R_\eta(\log(n/k)),\qquad
\|g_c\|_2^2=c^*Gc.
\]

Матрица G положительно полуопределена по определению Gram; её обратимость не предполагается.

Полный prime-вклад имеет вид

\[
P(g_c)=P_M(c)+\mathcal E_{M,\eta}(c),
\]

\[
\mathcal E_{M,\eta}(c)=
2\Re\sum_{2\le d\le M e^{2\delta}}\frac{\Lambda(d)}{\sqrt d}
\sum_{\substack{n,k\le M\\k\ne dn}}
\overline{c_n}c_k R_\eta(\log(dn/k)).
\tag{OVERLAP}
\]

Доказательство — та же полная корреляционная сумма из §5, но теперь несовпадающие dn и k нельзя выбросить. Верхний cutoff следует из носителя R_eta. Слагаемые с k=dn дают P_M, остальные дают (OVERLAP).

Пусть F_M(c) обозначает правую сумму квадратов в (DIV), а P02(g)=2Re(A_+ conjugate(A_-)). Тогда

\[
\boxed{
\mathcal Q(g_c)=F_M(c)+\mathcal D(g_c)+P02(g_c)
-\sum_{n=1}^M a_n^{(M)}|c_n|^2
-\mathcal E_{M,\eta}(c)-c_Ac^*Gc.}
\tag{REPAIRED-IDENTITY}
\]

Это точный ремонт, не доказательство положительности. Для получения W по такой семье нужно одновременно доказать восстановление каждого фиксированного теста в L2 и по Q, а также нижнюю оценку

\[
F_M(c)+\mathcal D(g_c)+P02(g_c)
-\sum_n a_n^{(M)}|c_n|^2-\mathcal E_{M,\eta}(c)
\ge(c_A-e_M)c^*Gc
\quad\forall c,\qquad e_M\downarrow0
\tag{OPEN-OVERLAP}
\]

в смысле e_M>=0 и e_M->0; монотонность e_M не требуется. Такая оценка в этом документе НЕ доказана. Также не построена уже плотная семья с этим бюджетом. Отождествлять c*c с c*Gc после расширения пакетов запрещено. Прежняя оценка (ARCH) при перекрытии больше не поставляется.

Первое остающееся неравенство на исходном, не изменённом тестовом классе по-прежнему равно

\[
\exists L_j\to\infty,\ r_j\ge0,\ r_j\to0,\quad
\forall g\in C_c^\infty((-L_j/2,L_j/2);\mathbb C):
\]

\[
\boxed{
\int_0^\infty\frac{e^{-5t/2}}{1-e^{-2t}}D_g(t)dt
+2\int_0^{L_j}\Delta(t)e^{-t/2}
\left(C'_g(t)-\tfrac12C_g(t)\right)dt
\ge(d_A-r_j)\|g\|_2^2.}
\tag{OPEN-W}
\]

Интегрирование по частям между (S) и (OPEN-W) законно: Delta(0)=0, C_g(L_j)=0, все скачки Delta сохранены.

Если (OPEN-W) будет выведено независимо, каждый фиксированный тест помещается в окна при больших j. Тогда Q(g)>=-r_j||g||^2 и предел даёт Q(g)>=0. Критерий S5 завершает RH. Здесь не хватает именно доказательства (OPEN-W), а не финального предельного перехода.

## 9. Две допустимые репрезентации и один следующий проверяемый вопрос

[COFINAL_FAMILY][CONDITIONAL]

R1: сохранить арифметическую сумму квадратов, но использовать перекрывающиеся либо переменно-ширинные пакеты. Проверяемые объекты — полный Gram G, полный остаток E в (OVERLAP), архимедовы и полюсные смешанные члены. Их совместная нижняя оценка должна достигать (OPEN-OVERLAP), а та же семья должна восстанавливать тесты. Оценка kill-power 9/10, стоимости 8/10 — экспертная, не экспериментальная.

R2: остаться в буквальном полном Fourier-mode пространстве CCM и работать с Gamma-c_L I-2 beta beta* из V0. Плюс: V0 содержит отдельное fixed-test recovery доказательство, подлежащее независимой проверке. Минус: нижний frame-bound Gamma >= (c_L-e_M)I+2 beta beta* не поставлен; факторизация (DIV) сама его не доказывает. Оценка kill-power 9/10, стоимости 9/10 — экспертная.

Один следующий бумажный вопрос: существует ли оценка полного знакового (OVERLAP), совместная с архимедовым и полюсным вкладом, на явно восстанавливающей тесты геометрии? До её вывода не строить численный generator и не формализовать очередной conditional composer.

Это не запуск Codex, не разрешение численного эксперимента и не новый binding в очередь.

## 10. Проверки, предсказания и эпистемика

[ABSTRACT][PAPER]

Проверены внутри вывода: комплексные коэффициенты; все простые степени; точный prime cutoff; полюсный отрицательный член; L2-мера; знаки верхних и нижних оценок; единый кофинальный объект; неудача восстановления. Нулевое численное значение нигде не использовано.

Алгебраические находки этого прохода не выдаются за blind predictions. Отдельного вероятностного прекоммита перед их первоначальным выводом не было; задним числом он не создаётся. Для будущего независимого review регистрируются:

```yaml
P_PACKET_DIVISOR_IDENTITY_SURVIVES_REVIEW:
  probability: 0.97
  event: DIV_and_MATCH_need_no_change_of_statement_or_prime_weights
  fate: PENDING
P_PACKET_FULL_LOWER_BOUND_SURVIVES_REVIEW:
  probability: 0.88
  event: PACKET_POS_holds_as_written_for_M_at_least_128_and_all_complex_vectors
  fate: PENDING
P_PACKET_COFINAL_RECOVERY_OBSTRUCTION_SURVIVES_REVIEW:
  probability: 0.98
  event: REC_FAIL_and_CLASS_hold_under_exactly_the_displayed_hypotheses
  fate: PENDING
PRIOR_V0_PREDICTIONS:
  P_WEILPROOF_FIXED_TEST_BUDGET_SURVIVES_INDEPENDENT_CHECK: PENDING_NOT_TESTED_HERE
  P_WEILPROOF_LITERAL_GRAM_IDENTITY_SURVIVES_SOURCE_CHECK: PENDING_NOT_TESTED_HERE
```

K8A: downstream неизменен — W на полном комплексном гладком компактном классе. Положительность узких пакетов не является необходимым входом: она была выбранным механизмом. Контрпримеры убивают только две точные theorem shapes из header. Полный Weil-маршрут не признан мёртвым. Для него остаётся RESEARCH_DEBT с reopen trigger (OPEN-W) либо совместным решением (OPEN-OVERLAP) и восстановления тестов. Отсутствие такого доказательства не используется как свидетельство математической невозможности.

Что стало точнее: (i) S не может поставляться как отдельная положительная поправка; (ii) делимость действительно даёт source-specific сумму квадратов и логарифмический prime-cap; (iii) цена точной арифметической развязки в данном классе — доказанный провал кофинального восстановления.

Что не стало меньше: канонический аналитический supplier (OPEN-W) не закрыт. Сам по себе новый finite-positive класс не является прогрессом до RH. Прогресс этого прохода — доказанные локальные оценки и точное исключение конкретного ложного подъёма.

Основной cognitive operator: REPRESENTATION_SHIFT. Progress class: FALSIFICATION_PROGRESS_WITH_LOCAL_PAPER_THEOREMS. Route score: 4 для диагностики механизма, не процент готовности RH.

Memory entry: сохранять prime–arch–pole cross terms и Gram-норму при любом расширении класса; запрещено вновь объявлять общие пакеты с радиусом O(1/M), двусторонним исчерпанием и одной клеткой на шаг источником fixed-test density без опровержения оценки (CLASS).

## 11. Минимальные theorem heads и проверка записи

[ABSTRACT][PAPER; предлагаемые имена, не существующие Lean declarations]

1. mangoldt_divisibility_energy_identity: конечное тождество (DIV) для каждого M и каждого комплексного вектора.
2. weil_log_integer_packet_lower_bound: теорема (PACKET-POS) с точными eta, epsilon_M, центрами, мерой и исходной формой.
3. narrow_log_integer_packets_no_cofinal_recovery: (REC-FAIL) и обобщение (CLASS).
4. weil_arithmetic_remainder_has_negative_smooth_direction: существование свидетеля (S-NEG).

Ни одного Lean-файла не написано. Следовательно, нет заявления о компиляции, новых аксиомах или kernel-certified theorem. Из публикаций импортированы определения и критерий, не готовая глобальная положительность.

Запись: один новый Markdown в docs/routeB_bus/proshka на rh_clean. Старый EXPECTED_VERDICT_PATH, queue, phase key, shared state, Lean и файлы других агентов не изменяются. Commit SHA и blob сообщаются в квитанции GitHub после записи; собственный commit SHA не вписывается рекурсивно в этот документ. Проверка записи — readback, совпадение пути, branch, первого статуса и Git blob. Она подтверждает доставку текста, не математическую истинность. Для документационного изменения Lean gate и axiom profile неприменимы; независимый PAPER-review остаётся PENDING.
