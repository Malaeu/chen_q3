# STATUS: TRY_CCM_INFINITE_WINDOW_WITH_ZERO_CLASSICAL_TRACE
```yaml
OPERATIVE_CLASS: TRY_CCM_INFINITE_WINDOW_WITH_ZERO_CLASSICAL_TRACE
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_INFINITE_WINDOW_REQUEST
SOURCE_REPOSITORY: Malaeu/chen_q3
SOURCE_BRANCH: rh_clean
SOURCE_COMMIT: 36ebe0d61a2ba1bad73afd81523301d5ee510c22
SOURCE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_HADAMARD_CCM_2026-11-02.md
SOURCE_SHA256: 62ced796e863365c3229e6005c6c7a1588f1ea31f35f5d1c35cf057e8010cbc4
SOURCE_GIT_BLOB: a7eafd0292479e0d5822dd48764bba4a463a4203
SOURCE_BYTES: 44947
SOURCE_LF_LINES: 689
SOURCE_HASH_CHECK: LOCAL_BYTES_MATCH_REMOTE_GIT_BLOB
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
FULL_EVEN_FORM_CLOSED_SEMIBOUNDED: PROVED_PAPER
COMPACT_RESOLVENT_AND_BOTTOM_ATTAINMENT: PROVED_PAPER
BOTTOM_NONINCREASING_IN_L: PROVED_PAPER
FIXED_L_GALERKIN_LIMIT: PROVED_PAPER
NORMALIZED_EIGENFUNCTION_L_INFINITY_BOUND: PROVED_PAPER
BOUNDARY_CONTINUITY_AND_ZERO_CLASSICAL_TRACE: PROVED_USING_PUBLISHED_BOUNDARY_THEOREM
BOTTOM_LOCALLY_LIPSCHITZ: PROVED_PAPER
NEW_ATOM_FIRST_ORDER_EFFECT: O_EPSILON_OVER_LOG_ONE_OVER_EPSILON
FORMULA_4_5_FOR_EVERY_FULL_MINIMIZER: NOT_ESTABLISHED
FORMULA_5_3_WITH_CLASSICAL_DERIVATIVES_AT_EVERY_THRESHOLD: NOT_ESTABLISHED
FORMULA_4_5_WITH_EXPLICIT_EXTRA_REGULARITY: PROVED_PAPER
NONZERO_FINITE_N_TRACE_KICK_IMPORTED_TO_N_INFINITY: NOT_ALLOWED
SIMPLE_BOTTOM_ASSUMED: false
N_INFINITY_IS_OWNER_REQUESTED_DOMAIN_ENLARGEMENT: true
LITERAL_SOURCE_PRIME_POWERS_POLES_ARCH_TAIL: PRESERVED
RH_ASSUMED: false
RH_PROVED: false
VERIFIER: PAPER
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
EXACT_LOCAL_SYMBOLIC_GROUPS_PASSED: 6
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: FULL_WINDOW_ATTAINMENT_MONOTONICITY_AND_BOUNDARY_ESTIMATES
```

## 0. Результат без подмены требуемого утверждения

**[ABSTRACT | PAPER.]** Для каждого фиксированного `L>0` нижняя грань полной чётной формы Вейля достигается. При увеличении окна она не возрастает. Более того, она локально Lipschitz по L и потому имеет неположительную производную почти всюду.

Для каждого единичного чётного собственного вектора полного оператора, в частности для любого минимизатора, доказаны ограниченность, непрерывность нулевого продолжения и оценка
\[
 |f(x)|\le D_L(\lambda)\,
 \left|\log\min\left\{\frac{L/2-|x|}{L},\frac1{10}\right\}\right|^{-1/2}.
\tag{0.1}
\]
Конечная константа `D_L(lambda)` выписана в §4 через lambda и фиксированные исходные величины. В частности, для **непрерывного представителя**:
\[
 \boxed{|f_\infty(L/2)|^2=|f_\infty(-L/2)|^2=0.}
\tag{0.2}
\]
Это не навязанное условие Дирихле: нулевой след выведен из полного eigen-equation с настоящими prime-shifts и полюсом.

**Граница выполнения запроса.** Формулы (4.5) и (5.3) закреплённого источника были доказаны для конечного N; (5.3) дополнительно предполагала простой нижний уровень. Я не установил их классическую версию для **каждого** полного минимизатора и каждого L. Ни закрытость формы, ни опубликованная краевая оценка не дают сами по себе внутреннюю `W^{1,1}`-регулярность, дифференцируемость всех нужных корреляций или существование двух классических производных в каждом пороге. Ниже доказаны точный условный перенос (4.5) и безусловная оценка входящего атома `o(|L-log n|)`.

Это не утверждение, что eigenfunction-specific (4.5) ложна. Опровергнуты только два общих shortcuts: непрерывность обычного следа в форме и ограниченность дилатационной производной относительно форменной нормы. Оба опровержения используют буквальную форму. Не установлена невозможность более сильной теоремы регулярности на собственных функциях.

## 1. Source lock и внешние входы

**S1, прочитан:** указанный в header HADAMARD_CCM на `36ebe0d`, §§2–6, особенно полный источник (3.4), (4.4)–(4.5), (5.1)–(5.3) и guards кратности. Локальные 44947 байт имеют указанный SHA-256 и Git blob; последний совпал с GitHub. В S1 прямо сказано, что внутренняя производная в (4.5) — производная конечного тригонометрического полинома.

**E1, первичный опубликованный результат:** V. Hernández-Santamaría, L. F. López Ríos, A. Saldaña, *Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the logarithmic Laplacian*, DCDS 45 (2025), 1–36; arXiv:2401.18033v2 (3 July 2024), Theorem 1.1, §4 и Appendix A. Для ограниченного слабого решения `L_Delta u=g` с нулевым внешним условием и ограниченным g на интервале он даёт непрерывность и верхнюю границу `O(|log d|^(-1/2))`. PDF прочитан; страницы 2–3 визуально проверены screenshot. Попытка screenshot страницы 22 вернула Cache miss; её текст доказательства был прочитан. Ни существование предела нормированного следа, ни формула формы Адамара из E1 не импортируются.

- https://arxiv.org/pdf/2401.18033
- https://doi.org/10.3934/dcds.2024084

**E2, первичный источник семейства:** Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Propositions 3.3–3.4 и Theorem 3.6. Прочитан HTML. Там уже установлены полузамкнутая снизу реализация, Fourier-core и дискретный спектр при фиксированном окне. Ниже достижение минимума и компактность дополнительно доказаны непосредственно в нормировке S1. Использование E2 для core не означает формальной верификации.

- https://arxiv.org/html/2511.22755v1

Поисковая выдача также показала rStation Paper 67 с заявленной формулой нормированного следа для Weil-оператора. Полный текст получить не удалось; этот результат НЕ использован как supplier, рецензия или доказательство. Поиск не заменяет чтение и проверку.

Протокол получен с `rh_clean`, включая конец. Управляющая задача — прямая команда владельца. Никакой другой запрос не выбирался из очереди. Все новые доказательства ниже — PAPER; отдельного проверяющего и Lean нет.

## 2. Полная форма: область, достижение и точный Galerkin-предел

### Теорема 1. Закрытая полная чётная реализация

**[ABSTRACT | PAPER; literal source.]** Обозначим `b=L/2`, `I_L=(-b,b)` и продолжим все функции нулём. Положим
\[
 j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad
 c_*=\gamma+\log(8\pi)+\pi/2,\quad
 \omega_n=\frac{\Lambda(n)}{\sqrt n},\quad a_n=\log n,
\]
\[
 p_L(x)=\sqrt2\cosh(x/2)\mathbf1_{I_L}(x),\qquad
 S_L=\sum_{a_n<L}\omega_n.
\]
Атом на `a_n=L` можно включить: его корреляция равна нулю. В дальнейших оценках удобно придерживаться строгого `<`.

Определим
\[
 \mathcal A[f]=\int_0^\infty j(s)\|f-T_sf\|_2^2\,ds,
\quad Q_f(s)=2\operatorname{Re}\int\overline{f(x)}f(x+s)dx,
\]
\[
 \mathcal D_L^E=\{f\in L^2_{\rm even}(\mathbb R):
 \operatorname{supp}f\subset[-b,b],\ \mathcal A[f]<\infty\}.
\]
На этой области полная форма равна
\[
 \boxed{\mathfrak k_L[f]=\mathcal A[f]-c_*\|f\|_2^2
       -\sum_{a_n<L}\omega_nQ_f(a_n)+|\langle p_L,f\rangle|^2.}
\tag{2.1}
\]
Нечётный полюс нулевой по чётности, не вследствие удаления из полной формы. Интеграл по архимедовым сдвигам остаётся от 0 до infinity. Все простые степени внутри окна присутствуют.

При Fourier-конвенции S1:
\[
 \mathcal A[f]=\frac1{2\pi}\int a(t)|\widehat f(t)|^2dt,
 \quad a(t)=2\int_0^\infty j(s)(1-\cos ts)ds.
\]
Причём
\[
 \boxed{\tfrac12\log(1+4t^2)\le a(t)
 \le\tfrac12\log(1+4t^2)+4.}
\tag{2.2}
\]
Действительно, `1/(2s)<=1/(1-exp(-2s))<=1+1/(2s)`. Применение
`int_0^infinity exp(-s/2)(1-cos ts) ds/s = (1/2)log(1+4t²)`
даёт нижнюю границу и логарифмическую часть верхней; оставшийся интеграл не больше 4.

Следовательно, `D_L^E` — замкнутая область логарифмической Fourier-энергии. Оператор каждой сжатой трансляции имеет L²-норму не больше единицы, а полюс ограничен и ранга один. Поэтому (2.1) — замкнутая, плотно определённая, ограниченная снизу форма:
\[
 \mathfrak k_L[f]\ge\mathcal A[f]-C_L\|f\|_2^2,
 \qquad C_L=c_*+2S_L.
\tag{2.3}
\]

### Теорема 2. Компактность и достижение минимума

**[ABSTRACT | PAPER; every fixed L>0.]** Вложение `D_L^E -> L²(I_L)` компактно. Поэтому
\[
 \lambda_0^\infty(L)=\inf_{f\in\mathcal D_L^E,\ \|f\|_2=1}\mathfrak k_L[f]
\]
конечно и достигается. Соответствующий оператор имеет компактную резольвенту.

**Доказательство.** Для множества с ограниченными `||f||²+A[f]` имеем из (2.2)
\[
 \frac1{2\pi}\int_{|t|>R}|\widehat f(t)|^2dt
 \le\frac{\mathcal A[f]}{\tfrac12\log(1+4R^2)}.
\tag{2.4}
\]
Все функции имеют одну ограниченную поддержку. Для пространственного сдвига h частоты `|t|<=R` дают цену `h²R²||f||²`, остальные — не больше четырёх хвостов (2.4). Сначала выбираем R, затем h. Получаем равномерную непрерывность сдвигов и tightness; критерий компактности L² даёт компактное вложение.

У единичной минимизирующей последовательности архимедова энергия ограничена по (2.3). Выделим сильно L²-сходящуюся подпоследовательность к единичному чётному f той же поддержки. Полузамкнутость снизу A и непрерывность ограниченных prime/pole частей дают `k[f]<=liminf k[f_j]`. Значит f — минимизатор. Поляризация его вариации даёт полный слабый eigen-equation
\[
 \mathfrak k_L(f,g)=\lambda_0^\infty(L)\langle f,g\rangle
 \quad(g\in\mathcal D_L^E).
\tag{2.5}
\]
В частности, f принадлежит операторной области. Компактная резольвента следует из компактного форменного вложения. Простота не использовалась. ∎

### Теорема 3. Связь с теми же конечными блоками

**[COFINAL_FAMILY | PAPER; limit N->infinity at fixed L, not a diagonal interchange.]**
\[
 \boxed{\lambda_{N,0}(L)\downarrow\lambda_0^\infty(L).}
\tag{2.6}
\]
Конечные вещественные чётные Fourier-полиномы образуют core по E2, Proposition 3.4. Чётная проекция сохраняет core, поскольку отражение коммутирует с формой. Min–max и core-приближение минимизатора доказывают (2.6).

Нормированные конечные минимизаторы имеют подпоследовательности, сходящиеся в L² к полным минимизаторам. Более того, вдоль такой подпоследовательности ограниченная часть формы сходится, а `k[f_N]->lambda_0^infinity`; поэтому сходятся архимедовы энергии и получается сходимость в форменной норме.

**Это не сходимость граничных значений или производных по L.** Их непрерывность в этой норме не предполагается и ниже опровергается для общего класса.

## 3. Монотонность по настоящей поддержке

### Теорема 4. Нижняя грань не возрастает

**[ABSTRACT | PAPER; all 0<L1<L2.]**
\[
 \boxed{\lambda_0^\infty(L_2)\le\lambda_0^\infty(L_1).}
\tag{3.1}
\]
**Доказательство.** При нулевом продолжении `D_(L1)^E subset D_(L2)^E`. Для каждого старого f значение полной глобальной формы буквально то же. Новые арифметические сдвиги не встречают его поддержку; полюс и архимедов хвост неизменны. Следовательно, инфимум берётся по большему множеству. ∎

Здесь вложены **полные физические области**, а не конечные носители с меняющимся периодом. Это ровно запрошенный переход к N=infinity. Из (3.1) не следует неотрицательность уровней и не следует RH.

## 4. Ограниченность eigenfunction и настоящий граничный след

### Лемма 5. Полный eigen-equation даёт явный L-infinity бюджет

**[ABSTRACT | PAPER; any normalized real even eigenfunction.]** Положим
\[
 g=\lambda+C_L\ge0,\qquad
 P_L=\|p_L\|_2\|p_L\|_\infty
 =\sqrt{L+2\sinh(L/2)}\,\sqrt2\cosh(L/4),
\]
\[
 \boxed{U_L(\lambda)=\tfrac12e^g+P_L\frac{e^g-1}{g},}
\tag{4.1}
\]
где последний множитель равен 1 при g=0. Тогда `||f||_infinity<=U_L(lambda)`.

**Доказательство с полной prime-частью.** Определим положительную jump-форму
\[
 \mathcal J_L[f]=\mathcal A[f]+\sum_{a_n<L}\omega_n\|f-T_{a_n}f\|_2^2.
\]
Её оператор `J_L` — killed restriction на I_L симметричного Lévy-оператора с полным символом
\[
 a(t)+2\sum_{a_n<L}\omega_n(1-\cos(a_nt))\ge a(t).
\]
На чётном секторе
\[
 K_L=J_L-C_L I+p_L\otimes p_L,\quad
 J_Lf+\langle p_L,f\rangle p_L=gf.
\tag{4.2}
\]
Отсюда g>=0. Полугруппа J_L положительна, является L-infinity contraction и доминируется полной convolution-полугруппой. Последнее можно получить без предположения о положительности K_L: сначала отсечь сингулярность j при s=0, раскрыть экспоненту положительного jump-kernel с запрещёнными внешними путями, затем перейти по монотонной сходимости форм. Удаление путей только уменьшает положительное ядро.

Плотность полной полугруппы в момент 1 имеет L²-норму не больше
\[
 \left[\frac1{2\pi}\int e^{-2a(t)}dt\right]^{1/2}
 \le\left[\frac1{2\pi}\int\frac{dt}{1+4t^2}\right]^{1/2}=\frac12.
\]
По Young и domination: `||exp(-J_L)||_(2->infinity)<=1/2`.

Из (4.2) в L² точно
\[
 f=e^g e^{-J_L}f-\langle p_L,f\rangle
           \int_0^1e^{sg}e^{-sJ_L}p_L\,ds.
\tag{4.3}
\]
Обе части справа ограничены. Используем `|<p_L,f>|<=||p_L||₂` и L-infinity contraction для второго члена. Получается (4.1). Положительность собственного вектора или полной полугруппы K_L не предполагалась. ∎

### Теорема 6. Граничный след равен нулю; цена через lambda

**[ABSTRACT | PAPER; source reduction plus imported E1.]** Для единичного чётного eigenfunction с eigenvalue lambda существует единственный непрерывный нулевой представитель. Он удовлетворяет (0.1) со следующей конечной ценой.

Пусть
\[
 r_0(s)=j(s)-\frac{\mathbf1_{(0,1)}(s)}{2s},\qquad
 R_0=\int_0^\infty|r_0(s)|ds<\infty,
\]
\[
 R_L=4R_0+\log_+L+\gamma,
\]
\[
 V_L(\lambda)=2\big[(|\lambda+c_*|+2S_L+R_L)U_L(\lambda)+P_L\big].
\tag{4.4}
\]
Возьмём фиксированную константу `C_bd` в boundary theorem E1 для единичного интервала, в нормировке
`sup |u|/sqrt(ell(d)) <= C_bd (||u||∞+||L_Delta u||∞)`.
Тогда допустимо
\[
 \boxed{D_L(\lambda)=C_{bd}
 \big[(1+2|\log L|)U_L(\lambda)+V_L(\lambda)\big].}
\tag{4.5-new}
\]
Здесь и далее `(4.5-new)` не является переименованием исходного (4.5).

**Доказательство.** Обозначим архимедов оператор через A. В одном измерении
\[
 L_\Delta u(x)=\int_0^1\frac{2u(x)-u(x+s)-u(x-s)}s ds
 -\int_1^\infty\frac{u(x+s)+u(x-s)}s ds-2\gamma u(x).
\]
На I_L при нулевом продолжении
\[
 A=\tfrac12L_\Delta+\mathcal R_L,
 \qquad \|\mathcal R_L\|_{\infty\to\infty}\le R_L.
\tag{4.6}
\]
Действительно, разность содержит интегрируемое ядро r0 с ценой 4R0, дальнюю интегральную часть с ценой log_+L и скаляр gamma. Около нуля `j(s)=1/(2s)+1/4+O(s)`, что оправдывает интегрируемость r0. Области форм совпадают, так как эта разность ограничена также в L² на фиксированном окне.

Из полного eigen-equation
\[
 L_\Delta f=2\left[(\lambda+c_*)f
 +\sum_{a_n<L}\omega_n(T_{a_n}f+T_{-a_n}f)
 -\langle p_L,f\rangle p_L-\mathcal R_Lf\right]
 \quad\hbox{в }I_L.
\tag{4.7}
\]
Все сдвиги здесь нулевые вне окна. По Лемме 5 правая часть ограничена и её L-infinity норма не больше V_L(lambda). Проверены ВСЕ предпосылки E1: f принадлежит пространству формы logarithmic Laplacian, f bounded, forcing bounded, interval имеет exterior sphere condition, внешнее условие нулевое. Никакого maximum principle для полного signed Weil-оператора не требуется.

Для контроля зависимости от L положим `u(y)=f(Ly)` на I_1. Масштабирование даёт
\[
 L_\Delta u(y)=(L_\Delta f)(Ly)+2\log L\,u(y).
\]
Применение E1 на одном фиксированном I_1 даёт (0.1), (4.5-new). Нормовая зависимость константы линейна по `||u||∞+||forcing||∞`: это следует из барьерного доказательства E1; эквивалентно — из теоремы о замкнутом графике на пространстве ограниченных слабых решений. Для полноты это пространство полно в указанной graph-норме: разности удовлетворяют `E_Delta[v]=int v g`, а bounded lower-order terms дают сходимость в форменной норме при равномерной сходимости v,g.

E1 даёт непрерывность на всей R. Вне I_L f=0, поэтому оба граничных предела равны нулю. Это доказывает (0.2). ∎

**[ABSTRACT | PAPER; useful quantitative consequence.]** При `0<delta<L/10`:
\[
 \int_{b-\delta}^b|f|^2\le
 \frac{D_L(\lambda)^2\delta}{\log(L/\delta)},
 \qquad
 |Q_f(L-\delta)|\le
 \frac{2D_L(\lambda)^2\delta}{\log(L/\delta)}.
\tag{4.8}
\]
Для первой оценки интегрируем (0.1), используя возрастание ell. Для второй обе точки перекрытия находятся в крайних полосках ширины delta; длина перекрытия равна delta. Следовательно `Q_f'(L^-)=0` как односторонняя производная в самой конечной точке.

Константы U,V,D локально равномерны по L и по eigenvalues в ограниченном интервале. Для нижнего уровня на любом компактном интервале `0<L_-<=L<=L_+` такая ограниченность eigenvalues следует из (2.3) и одного фиксированного гладкого теста, поддержанного в I_(L_-).

**Что не следует.** Оценка не утверждает существования предела
\[
 \tau_\pm(f)=\lim_{d\downarrow0}\sqrt{\log(L/d)}f(\pm(b-d)).
\tag{4.9}
\]
Она даёт лишь ограниченность limsup квадрата этого выражения. В частности, она НЕ даёт `|tau|²<=C lambda`, не обращается в ноль при lambda=0 и не предотвращает пересечение нулевого уровня.

## 5. Реальное следствие для вариации поддержки

### Теорема 7. Локальная Lipschitz-регулярность нижнего уровня

**[ABSTRACT | PAPER; full source.]** Функция `lambda_0^infinity` локально Lipschitz на `(0,infinity)`. Поэтому её производная существует почти всюду и не положительна.

**Доказательство.** Работаем в одном компактном диапазоне длин. По §4 нормированные ground functions имеют общие L-infinity и logarithmic-boundary bounds. Возьмём `L2=L1+epsilon`, bottom f на большем окне, и разрежем его физически:
\[
 u=f\mathbf1_{I_{L1}},\qquad v=f-u.
\]
Обе функции чётны и принадлежат форменной области большего окна. Последнее следует из ограниченности f: дополнительная энергия на разрезе не хуже интеграла logarithmic distance, который конечен. Множитель `mathbf1_I` не постулируется bounded на произвольной форменной области; используется именно bounded f.

По слабому eigen-equation:
\[
 \mathfrak k[u]-\lambda(L2)\|u\|_2^2=-\mathfrak k(u,v).
\]
Так как u допустим на старом окне,
\[
 0\le\lambda(L1)-\lambda(L2)
 \le\frac{-\mathfrak k(u,v)}{\|u\|_2^2}
 \le\frac{|\mathfrak k(u,v)|}{\|u\|_2^2}.
\tag{5.1-new}
\]
Масса v равна `O(epsilon/log(1/epsilon))`, поэтому знаменатель не меньше 1/2 при малом epsilon.

Оценим смешанный источник. Диагональный скаляр зануляется из-за непересекающихся поддержек. Полюс и каждый конечный prime-shift дают `O(epsilon/sqrt(log(1/epsilon)))`, поскольку одна переменная лежит в collar, а другая ограничена; на компактном диапазоне L число и сумма весов атомов ограничены.

Остаётся arch. В координате расстояния до одного из новых краёв пусть `delta=epsilon/2`, collar-точка `0<y<delta`, старая точка `delta<x<L2`. Сингулярность не хуже `C/(x-y)`. Для `delta<x<2delta` двойной интеграл `1/(x-y)` равен `2delta log2`; два boundary factors дают `O(1/log(1/delta))`. Для `2delta<x<L2/10` используем
\[
 \int_{2\delta}^{L2/10}\frac{dx}{x\sqrt{\log(L2/x)}}
 \le2\sqrt{\log(L2/\delta)},
\quad
 \int_0^\delta\frac{dy}{\sqrt{\log(L2/y)}}
 \le\frac\delta{\sqrt{\log(L2/\delta)}}.
\]
Произведение имеет порядок O(delta). Остальная часть ядра и вклад противоположного конца отделены от диагонали и стоят O(delta). Итого `|k(u,v)|<=C epsilon`. Подставляем в (5.1-new). Для немалых шагов достаточно разбить их на малые; константы локально равномерны. ∎

Этот аргумент не использует eigenfunction derivative, отсутствующий в текущем пакете, и не подменяет полную форму jump-частью.

### Теорема 8. Входящий prime-power атом не даёт первого порядка на полных minima

**[ABSTRACT | PAPER; literal source plus explicitly identified comparator.]** Фиксируем `a=log n>0`. Пусть `lambda(L)` — полный bottom, а `lambda^omit(L)` — вспомогательный bottom той же формы с удалённым только одним членом `-omega_n Q_f(a)`. Эта вспомогательная форма используется исключительно для измерения вклада данного атома; целевая CCM-форма не меняется.

При `L<=a` эти значения совпадают. При `L=a+epsilon`, epsilon>0,
\[
 \boxed{|\lambda(L)-\lambda^{omit}(L)|
 \le C_a\omega_n\frac\epsilon{\log(a/\epsilon)}=o(\epsilon).}
\tag{5.2-new}
\]
**Доказательство.** У обеих форм §2–4 применимы с соответствующим конечным S. На компактном диапазоне возле a их единичные минимизаторы имеют общий boundary bound. В момент L=a+epsilon две части сдвинутой поддержки перекрываются лишь в крайних слоях ширины epsilon. По (4.8), `|Q_f(a)|<=C epsilon/log(a/epsilon)` для каждого из этих двух минимизаторов. Две Rayleigh-подстановки, одна в каждом направлении, доказывают (5.2-new). ∎

Таким образом, **прямой вклад рождения атома в первый порядок полного нижнего уровня равен нулю**. Это более аккуратное утверждение, чем постулировать существование `lambda'_+(a)` и `lambda'_-(a)`.

Если у omit-семейства в a есть обычная производная, то у полного bottom есть та же производная: слева формы равны, справа разность o(epsilon). Тогда исходное (5.3) становится
\[
 \lambda'(a+)-\lambda'(a-)=0=-2\omega_n|f_a(a/2)|^2.
\tag{5.3-conditional}
\]
Но локальная Lipschitz-регулярность не гарантирует обычную производную в каждом заранее заданном a. При кратности также остаются возможные eigenbranch изломы. Они не являются рождением нового атома.

## 6. Почему конечномерное доказательство нельзя просто продолжить

### Лемма 9. В форменной норме нет обычного непрерывного endpoint trace

**[ABSTRACT | PAPER; literal form, general trials, NOT eigenfunctions.]** Зафиксируем L. Для малой epsilon возьмём две единичные по высоте крайние прямоугольные полоски:
\[
 g_\epsilon=\mathbf1_{[b-\epsilon,b]}+
             \mathbf1_{[-b,-b+\epsilon]}.
\]
Имеем односторонний след `g_epsilon(b^-)=1`, но
\[
 \|g_\epsilon\|_2^2+\mathcal A[g_\epsilon]
 =O_L(\epsilon\log(1/\epsilon))\longrightarrow0.
\tag{6.1-new}
\]
Действительно, для одной полоски длины epsilon квадрат нормы shift-difference равен `2 min(s,epsilon)`. Для суммы двух полосок используем квадрат треугольного неравенства. После интегрирования j(s)~1/(2s) это даёт указанную цену. Ограниченные prime/pole terms также стремятся к нулю.

После L²-нормировки след имеет квадрат `1/(2epsilon)`, тогда как полная энергия по модулю не больше `O_L(1+log(1/epsilon))`. Это запрещает линейный energy-to-endpoint bound на всей области формы, но НЕ опровергает eigenfunction-specific estimate: в §4 для eigenfunctions как раз выведен нулевой след.

В конечном Fourier-базисе тот же дефект виден из
\[
 \|dd^T\|=\|d\|_2^2=2N+1.
\tag{6.2-new}
\]
Поэтому rank-one оператор скачка (5.2) из S1 не имеет ограниченного операторного предела при N->infinity. Форменная сходимость eigenvectors не позволяет автоматически передать его ожидание.

### Лемма 10. Между атомами дилатационная производная тоже не bounded form perturbation

**[ABSTRACT | PAPER; exact literal-source trial family.]** Возьмём
`log2<L<log3`. Это настоящая ячейка, содержащая ровно атом n=2. Выберем вещественную чётную `eta in C_c^infinity(I_L)` с
\[
 C_\eta(a)=\int\eta(x)\eta(x+a)dx>0,
 \qquad a=\log2.
\]
Нормируем `f_T(x)=eta(x)cos(Tx)` в L². Обозначим
`c_eta=2 C_eta(a)/||eta||₂²>0`. Тогда при T->infinity
\[
 Q_{f_T}'(a)=-c_\eta T\sin(Ta)+O(1),
 \quad 1+\mathcal A[f_T]=O(\log(T+2)).
\tag{6.3-new}
\]
Первая формула — раскрытие произведения косинусов; быстро осциллирующий второй интеграл оценивается повторным интегрированием по частям. Вторая следует из (2.2) и двух сдвинутых Schwartz-преобразований eta.

В исходной frozen-coefficient dilation derivative вклад атома равен
`(omega_2 a/L)Q_f'(a)`. Архимедов член ограничен независимо от T: интегрируем `int sj Q'` по частям, оставляя граничное значение `-1` у нуля и `int(sj)' Q`, где `(sj)'` интегрируем. Полюсный член также ограничен.

Выбирая последовательности `sin(Ta)=+1` и `sin(Ta)=-1`, получаем
\[
 \sup_{f\ne0}\frac{|\partial_L\mathfrak k[f_{L,c}]|}
 {\|f\|_2^2+\mathcal A[f]}=\infty.
\tag{6.4-new}
\]
Здесь берутся гладкие, компактно поддержанные, чётные trials; это не произвольная другая матрица. Следовательно, нельзя автоматически применить стандартную common-form C1 perturbation theorem, опираясь лишь на форменную норму.

**Точный scope:** (6.1-new) и (6.4-new) не являются контрпримерами к дифференцируемости выбранного полного eigenbranch. Они опровергают предлагаемые общие механизмы передачи конечномерной формулы без дополнительной регулярности на eigenspaces.

## 7. Что от (4.5) уже можно доказать, и что ещё отсутствует

### Теорема 11. Строго условный перенос исходной физической формулы

**[ABSTRACT | CONDITIONAL for regularity; PAPER implication.]** Пусть L не является входом prime-power атома, `lambda_0^infinity` дифференцируема в L и некоторый единичный минимизатор f дополнительно принадлежит `W^{1,1}(I_L)`. Тогда (4.5) S1 верна для этого f, с внутренней слабой производной и его непрерывным следом. По §4 последний равен нулю, так что
\[
 \boxed{\lambda'(L)=\frac{a_f^2+a_fb_f}{L}
 +\frac2L\int_0^L sj(s)A_f(s)ds
 +\frac2L\sum_{a_n<L}\omega_na_nA_f(a_n),}
\tag{7.1-new}
\]
\[
 a_f=\langle\sqrt2\cosh(x/2),f\rangle,\quad
 b_f=\langle x\sqrt2\sinh(x/2),f\rangle,\quad
 A_f(s)=\int_{-b}^{b-s}f(x)f'(x+s)dx.
\]

**Доказательство.** Bounded f и `f' in L¹` дают непрерывную корреляционную производную и правило Лейбница
`Q_f'=2A_f-2f(b-s)f(b)`. Нулевой след убирает последний член. Рассмотрим нормированный dilation-trial на окне L+h, полученный из одного зафиксированного f. Дифференцирование его полной энергии законно: архимедова часть интегрируема после множителя s, prime-сумма конечна, pole-часть гладка. Вычисление S1 даёт ровно правую часть (4.5).

Минимальность даёт `lambda(L+h)<=k[trial_(L+h)]`, с равенством при h=0. Деление на h>0 и h<0, затем дифференцируемость lambda, дают равенство производных. Никакая производная eigenvector или единый spectral gap не нужны. ∎

Если существуют только односторонние производные, тот же довод даёт
`lambda'_+(L)<=D_L(f)<=lambda'_-(L)` для значения frozen-trial derivative. Он НЕ даёт автоматически равенство с произвольно выбранным f при кратности.

**Первый точно неоплаченный переход:** доказать для настоящих полных минимизаторов достаточную корреляционную/внутреннюю регулярность, разрешающую этот перенос в каждой нужной точке, либо получить полноценную support-variation theorem другим методом. E1 даёт logarithmic continuity и boundary decay; это не теорема `f in W^{1,1}` и не теорема о C1-зависимости eigenspace по L. Простота полного нижнего уровня тоже здесь не установлена.

### Контроль: нулевой обычный след не означает нулевую скорость уровня

**[ABSTRACT | PAPER; principal-model control, NOT replacement CCM.]** Для сжатия `T=log|D|=(1/2)L_Delta` на интервал длины L дилатация даёт точно
\[
 \lambda_j(T;L)=\lambda_j(T;1)-\log L.
\tag{7.2-new}
\]
По той же boundary theorem его bounded eigenfunctions имеют нулевой обычный след. Однако производная уровня равна `-1/L`, а не нулю. Поэтому нельзя из `f(b)=0` удалить всю правую часть (4.5) или заключить отсутствие геометрического дрейфа. Для полной CCM все внутренние/source terms должны оставаться; возможная более чистая boundary formula потребует нормированного логарифмического следа, не ordinary evaluation.

## 8. Два допустимых продолжения и точный discriminator

**[ABSTRACT | CONDITIONAL; research map, not new proof.]**

| Представление | Что именно закрывает | Сила / цена | Что обязано быть оплачено |
|---|---|---|---|
| Корреляционная регулярность полных eigenspaces | Буквальную интегральную (4.5), если её все значения и вариационные пределы существуют | Высокая / высокая аналитическая | Q'_f(log n), архимедов предел, кратность; не переносить ограниченность из конечного N |
| Физические collars и нормированный logarithmic trace | Подлинный support derivative без обязательного W1,1; правильную первую граничную скорость | Высокая / высокая | Существование tau, весь бесконечный complementary Schur response, uniform remainders и crossing guards |

Три моста проверены: closed-form compactness (работает), logarithmic Dirichlet boundary regularity (работает после bounded-forcing reduction), finite-matrix Hadamard/common-form C1 transfer (не работает автоматически, (6.4-new)). Vanishing identity имеется для ordinary endpoint trace и first-order activation, а не для полной производной.

**DISCRIMINATOR:** отличить `f(b)=0` от ненулевого или несуществующего предела `sqrt(log(1/d)) f(b-d)`. Одного значения нуль на границе недостаточно для расчёта полного support drift. Проверка должна также воспроизводить точный модельный закон (7.2-new), а не ошибочный нулевой наклон.

**Единственная следующая CODEX DIRECTIVE:** независимо проверить доказательства §4–5, затем получить source-faithful support-variation theorem для полного even eigenspace через collars с настоящим нормированным logarithmic trace. Допустим результат с явным первым неоплаченным пределом; недопустимо назвать E1 доказательством существования trace limit или удалить бесконечное дополнение. No RH or route-state promotion.

## 9. Consumer-first ledger и closeout

**[ABSTRACT | PAPER/CONDITIONAL as marked above.]**

- DOWNSTREAM_CONSUMER: запрошенная полная оконная вариация; NOESCAPE/RH — дальнейшие цели, не вывод текущего доказательства.
- ACTUAL_CONSUMER_REQUIREMENT: достижение + domain monotonicity + корректная regularity-controlled первая вариация.
- ORIGINAL_REQUESTED_OBJECT: finite-N (4.5), (5.3) на каждом full minimizer и оценка его endpoint value.
- ORIGINAL_OBJECT_IS: UNKNOWN для универсального классического переноса; finite-rank operator-norm limit NOT_AVAILABLE; ordinary trace estimate proved as zero.
- KNOWN_WEAKER_INTERFACES: weak eigen-equation (2.5); locally Lipschitz nonincreasing bottom; o(epsilon) cost нового атома; conditional (7.1-new).
- FAILURE_TYPE: NO_DERIVATION для полного классического переноса; COUNTEREXAMPLE только для trace-continuity/common-form derivative shortcuts.
- EPISTEMIC_STATUS: RESEARCH_DEBT для eigenfunction shape regularity. Никакая смерть CCM/RH не утверждается.
- NOVELTY_AXIS: FULL_WINDOW_CLOSED_FORM_AND_LOGARITHMIC_BOUNDARY_REPAIR.
- REOPEN_TRIGGER: исходниковая eigenfunction/correlation regularity либо доказанный normalized-trace support law.

Что закрыто: attainment, monotonicity, finite-N value limit, L-infinity bound и нулевой классический след; на компактных L получена Lipschitz-оценка и оплачена first-order activation error. Что не закрыто: классическая (4.5) на всех minima, дифференцируемость в каждом пороге, простота, нормированный trace limit и его полный shape law.

Нельзя повторять: принимать endpoint evaluation за bounded functional в логарифмической форме; выводить C1-семейство из finite-N derivative; объявлять lambda'=0 из f(b)=0; считать собственный вектор положительным без доказательства для signed полного оператора.

Предсказания для шести локальных символьных тестов зарегистрированы **после аналитического вывода, до исполнения кода**: principal coefficient 1/2; heat constant 1/2; pole norm и rho1; rank-one norm 2N+1; epsilon/log first-order suppression; знак cut/collar identity. Все шесть подтверждены. Они не названы предварительными прогнозами всего исследования и не проверяют аналитические теоремы.

Результат не является полным выполнением исходного конъюнктивного запроса. Это точная положительная часть и отдельное указание на оставшийся переход, без выдачи необходимой регулярности за доказанную. RH, T и прежняя source-positive bound не установлены.

## Appendix A. Исполненные точные локальные проверки

Следующий код проверяет только указанные константы и алгебру. Он не является Lean/Arb-сертификатом. Отдельный reviewer не запускался.

```python
#!/usr/bin/env python3
"""Exact local checks for the infinite-window CCM derivation.

Run:
  uv run --with sympy PROSHKA_INFINITE_WINDOW_CHECKS_2026-11-02.py

These checks validate constants and algebra, not the boundary-regularity
import, the compactness proof, or an RH assertion.
"""
import sympy as s


def main() -> None:
    z, L, x, a = s.symbols('z L x a', positive=True)
    j = s.exp(-z/2)/(1-s.exp(-2*z))
    assert s.limit(z*j, z, 0, dir='+') == s.Rational(1, 2)
    assert s.limit(j-1/(2*z), z, 0, dir='+') == s.Rational(1, 4)
    print('PASS 1: exact logarithmic principal kernel and integrable remainder')

    t = s.symbols('t', real=True)
    heat_square = s.integrate(1/(1+4*t*t), (t, -s.oo, s.oo))/(2*s.pi)
    assert heat_square == s.Rational(1, 4)
    print('PASS 2: time-one whole-line L2 kernel bound equals 1/2')

    p_squared_mass = s.integrate(2*s.cosh(x/2)**2, (x, -L/2, L/2))
    assert s.simplify(p_squared_mass-L-2*s.sinh(L/2)) == 0
    rho1 = 2*s.log(2)+s.polygamma(0, s.Rational(1,2))-s.EulerGamma
    assert s.simplify(rho1+2*s.EulerGamma) == 0
    print('PASS 3: even pole norm and one-dimensional logarithmic-Laplacian constant')

    for N in range(0, 9):
        d = s.Matrix([1]+[s.sqrt(2)]*N)
        assert (d.T*d)[0] == 2*N+1
        assert s.simplify((d*d.T*d)[0]-(2*N+1)) == 0
    print('PASS 4: finite endpoint rank-one norm grows as 2N+1; no bounded infinite limit')

    eps = s.symbols('eps', positive=True)
    assert s.limit((eps/s.log(L/eps))/eps, eps, 0, dir='+') == 0
    assert s.limit(s.sqrt(1/s.log(L/eps)), eps, 0, dir='+') == 0
    print('PASS 5: zero endpoint trace and o(epsilon) newly activated atom budget')

    A, B, C, lam, u2, v2 = s.symbols('A B C lam u2 v2', real=True)
    # q[u]=A, q[u,v]=B, q[v]=C; stationarity tested with u.
    stationary_B = lam*u2-A
    assert s.expand(A-lam*u2+stationary_B) == 0
    print('PASS 6: exact cut-and-collar eigen-equation balance')
    print('ALL 6 LOCAL SYMBOLIC GROUPS PASSED; NO RH OR ANALYTIC AUDIT CLAIM')


if __name__ == '__main__':
    main()
```

Исполненный вывод:
```text
PASS 1: exact logarithmic principal kernel and integrable remainder
PASS 2: time-one whole-line L2 kernel bound equals 1/2
PASS 3: even pole norm and one-dimensional logarithmic-Laplacian constant
PASS 4: finite endpoint rank-one norm grows as 2N+1; no bounded infinite limit
PASS 5: zero endpoint trace and o(epsilon) newly activated atom budget
PASS 6: exact cut-and-collar eigen-equation balance
ALL 6 LOCAL SYMBOLIC GROUPS PASSED; NO RH OR ANALYTIC AUDIT CLAIM
```
