# STATUS: TRY_GOAL058_SOURCE_MATCHED_ADJOINT_GREEN

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_MATCHED_ADJOINT_GREEN
OUTCOME: OPEN_ADJOINT_GREEN_MIX
REQUEST_ID: REQ-2026-09-25-ADJOINT-GREEN-MIX
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_PREFIX_MIXED_TERM_ADJOINT_GREEN
SOURCE_COMMIT_REQUESTED: 56ce8d82
SOURCE_COMMIT: 56ce8d8299fc14e6993663e20fda1ccdeb2a7467
PREDECESSOR: REQ-2026-09-25-COUPLED-DEFECT-SIGN
PREDECESSOR_VERDICT_SHA256_VERIFIED: d4ff0e570e53cfc51ed9311e4228725a7840e03a5ddf0e3889a0910f522c2818
PREDECESSOR_GIT_BLOB_VERIFIED: c9c1f79b9cba5453fdb26197280432c716a71a34
BOOTSTRAP_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
GENERAL_GREEN_IDENTITY: PROVED_BELOW
DIRICHLET_GREEN_SIGNS: BOTH_MINUS_AS_IN_REQUEST
DIRICHLET_INVERTIBILITY_AT_SELECTED_ENERGIES: NOT_ASSUMED_NOT_CERTIFIED
SOURCE_MATCHED_ROBIN_SOLVABILITY: UNIQUE_FOR_EACH_SELECTED_CELL_AND_EVERY_COMPLEX_FORCING
SOURCE_MATCHED_ROBIN_RESONANCE: EXCLUDED_BY_EXACT_SOURCE_IDENTITY
TWO_ENERGY_TAIL_SECANT: EXACT_POSITIVE_FACTOR_BETWEEN_ZERO_AND_ONE_THIRD
FULL_QUARTIC_BOUNDARY_REPRESENTATION: PROVED_BELOW
ONE_SIDED_FULL_MARGIN: NOT_ESTABLISHED
SIGN_OF_TAU: NOT_ESTABLISHED
SCHUR_FLOOR: OPEN
SOURCE_FAMILY_CHANGED: false
SOURCE_SPLICE: 5m_UNCHANGED
PREFIX_ENDPOINT: 6m_minus_1_UNCHANGED
RH_ASSUMED: false
PROLATE_6PI_GAP_USED: false
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: ADJOINT_SOLVABILITY_AND_TAIL_SECANT_ONLY_NOT_THE_TAU_SIGN
ROUTE_SCORE: 3
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_ADJOINT_GREEN_MIX.** Предложенная **Dirichlet Green-формула** имеет правильные знаки и индексы, но её разрешимость нельзя получать из одной записи обратной матрицы. Для двух настоящих выбранных энергий удаётся сделать сильнее: поставить **правую границу, согласованную с точным источниковым хвостом**, и доказать существование и единственность сопряжённого решения **для каждого выбранного m и любого комплексного forcing**. Резонанс этого исправленного блока исключается точным тождеством, без спектрального зазора.

Кроме того, разность двух исправленных блоков имеет точно известное направление: она равна минус положительной разности энергий, умноженной на `I` плюс положительную поправку ранга один. **Но знак отклика на настоящий forcing и полный margin относительно B(m) не доказаны.** Ни SIGN_BOUND, ни ADJOINT_PATH_KILL здесь не следуют.

## 1. Источник и область

**[COFINAL_FAMILY | PAPER]** Короткий pin разрешён GitHub в `56ce8d8299fc14e6993663e20fda1ccdeb2a7467`. У локального приложения предшествующего вердикта проверены **36 834 байта**, SHA-256 и Git blob; оба хеша совпали с запросом и файлом на этом pin. Независимый аудит принимает хвостовой бюджет, но не одностороннее сравнение. fileciteturn30file0L3-L6 fileciteturn31file0L2-L5 fileciteturn33file0L2-L2

Сохраняются один P и
\[
m=J_P+j+2,\quad m=N_j,\quad L=\log m,\quad
s_n=\tfrac12-2\pi in/L,\quad -m\le n\le m.
\]
Далее **N=6m-1** — только конец уже принятого Ferrers-prefix, не Fourier-cutoff. Источниковая склейка остаётся в `5m`, с якорем `5m-1`. Сохраняются K_j, U_j, q_j, z_j, rho_m, S_m, полный W02–WR–Prime и Q6. Бюджет B(m) предшественника не передоказывается и не уменьшается.

Пишем G_m=4 pi^2 m^2. Чтобы не смешать вектор d с диагональю рекурсии, последнюю обозначаем d_k^{rec}. Источниковая рекурсия:
\[
(J_m P)_k=\ell_kP_{k-1}+d_k^{\rm rec}P_k+u_kP_{k+1},
\]
\[
\begin{aligned}
\ell_k&=-G_m\frac{(2k-1)(2k)}{(4k-3)(4k-1)},\\
d_k^{\rm rec}&=2k(2k+1)+G_m\frac{4k(2k+1)-1}{(4k-1)(4k+3)},\\
u_k&=-G_m\frac{(2k+1)(2k+2)}{(4k+3)(4k+5)}.
\end{aligned}
\tag{1}
\]
В частности, ell_1=-2G_m/3, u_0=-2G_m/15; все ell_k при k>=1 и u_k при k>=0 ненулевые и отрицательные. Это именно source crosswalk со сдвигом **E=Lambda+G_m**, не иной Jacobi-оператор. Формулы согласуются с DLMF 30.8.3–30.8.4; асимптотика DLMF при фиксированном параметре не используется. fileciteturn35file0L2-L2 citeturn117979view0

Для i=0,4 обозначим E_i=E_{i,m},
\[
P_k^i=\mathcal P_k(E_i,m),\qquad P_0^i=1,
\qquad a^{(i)}_{m,k}=a^{(i)}_{m,0}P_k^i.
\]
Это те же два выбранных источниковых решения: Lambda_0<Lambda_4<20 и E_0<E_4. Здесь индекс `4` обозначает прежнюю физическую моду, а её even-carrier индекс равен 2. Никакой численной нижней границы для E_4-E_0 не импортируется. fileciteturn37file0L2-L2 fileciteturn38file0L2-L2

## 2. Общий Green-терм и настоящая проблема Dirichlet-границ

**[ABSTRACT | PAPER]** При обычном билинейном суммировании правильная транспонированная рекурсия имеет вид
\[
u_{k-1}\phi_{k-1}+(d_k^{\rm rec}-E)\phi_k
+\ell_{k+1}\phi_{k+1}=h_k,\qquad 1\le k\le N.
\tag{2}
\]
В ней стоят **u_{k-1} и ell_{k+1}**, а не коэффициенты исходной строки с тем же k. Для вещественного выбранного P комплексные h и phi разрешены; сопрягать h в сумме не надо.

Вычитание двух конечных сумм даёт
\[
\boxed{
\sum_{k=1}^N P_k(E)h_k
=u_0P_1(E)\phi_0-\ell_1P_0(E)\phi_1
+\ell_{N+1}P_N(E)\phi_{N+1}
-u_NP_{N+1}(E)\phi_N.
}
\tag{G}
\]
Доказательство — точное сокращение слагаемых с парами индексов `(k,k+1)` внутри диапазона. Остаются только четыре выписанных крайних члена. Поэтому при phi_0=phi_{N+1}=0 формула запроса верна буквально:
\[
\sum_{k=1}^N P_k(E)h_k
=-\ell_1\phi_1P_0(E)-u_N\phi_NP_{N+1}(E).
\tag{GD}
\]
Минусы здесь — алгебраические знаки; поскольку ell_1 и u_N отрицательны, это не утверждение об отрицательности значений правой части.

**[FINITE_CELL | PAPER]** Пусть A_N(E)=J_m|_{1:N}-EI — блок с двумя Dirichlet-границами. Зададим второе решение Q_0(E)=0, Q_1(E)=1 и продолжим той же рекурсией при k>=1. Тогда
\[
\det A_N(E)=(-1)^N\left(\prod_{k=1}^Nu_k\right)Q_{N+1}(E).
\tag{3}
\]
Если Q_{N+1}(E) не равен нулю, Dirichlet-задача однозначно разрешима. Если равен нулю, её необходимое и достаточное условие совместности:
\[
\boxed{\sum_{k=1}^N Q_k(E)h_k=0.}
\tag{4}
\]
Причина: ядро A_N(E) одномерно, порождено Q|_{1:N}; условие (4) — конечномерная альтернатива для A_N(E)^T. При совместности Green-выражение (GD) не зависит от выбора решения.

Значения (3) при настоящих E_0,E_4 здесь **не объявляются ненулевыми**. Однако для рабочего Green-переноса этот отдельный вопрос можно обойти без потери исходниковости — следующим точным выбором правой границы.

## 3. Источниковая Robin-граница: существование для всей семьи

### 3.1. Граница берётся из уже выбранной строки

**[COFINAL_FAMILY | PAPER]** Пусть t_i=P_{N+1}^i/P_N^i. Это отношение существует. Действительно,
\[
N=(5m-1)+m,
\]
а точная склейка, ненулевой якорь и положительность канонического хвоста дают
\[
P_N^i\ne0,\qquad
 t_i=
\frac{\operatorname{tailRow}_{i,5m}(m+1)}
     {\operatorname{tailRow}_{i,5m}(m)}
=\operatorname{rightTailLimit}(m,\Lambda_i,6m),
\qquad 0<t_i\le\tfrac12.
\tag{5}
\]
Это чтение того же хвоста дальше его исходной склейки; **склейка не переносится в 6m**. Использованы точные поля `tail_splice`, `splice_anchor_ne_zero` и положительность tail supplier, а не повтор предыдущего error budget. fileciteturn37file0L2-L2 fileciteturn36file0L2-L2

Для сопряжённого решения ставим
\[
\boxed{
\phi_0^i=0,\qquad
\phi_{N+1}^i=\frac{u_N}{\ell_{N+1}}t_i\phi_N^i
=\frac{4N+1}{4N+5}t_i\phi_N^i.
}
\tag{RB}
\]
Коэффициент `(4N+1)/(4N+5)` обязателен: это **сопряжённая**, а не исходная рекурсия. Условие phi_{N+1}=t_i phi_N без этого множителя вообще не сокращает правый Green-терм.

Определим конечный блок
\[
B_i=J_m|_{1:N}-E_iI+u_Nt_i e_Ne_N^T.
\tag{6}
\]
Уравнение B_i^T phi^i=h равносильно (2) с границами (RB). Подстановка в (G) точно уничтожает **два правых Jacobi-граничных члена вместе**:
\[
\boxed{\sum_{k=1}^N P_k^i h_k=-\ell_1\phi_1^i.}
\tag{7}
\]
Это не уничтожение правого физического края окна, не зануление Prime и не смена CCM-матрицы.

### 3.2. Обратимость доказана, а не предположена

**[COFINAL_FAMILY | PAPER]** Для каждого выбранного m>=2 и i=0,4 имеем
\[
\boxed{\forall h\in\mathbb C^N\quad\exists!\phi^i\in\mathbb C^N:
B_i^T\phi^i=h.}
\tag{8}
\]
Доказательство не использует положительность J_m, K_j или W. Положим p^i=(P_1^i,...,P_N^i)^T. По исходной рекурсии и (5)
\[
B_i p^i=-\ell_1e_1,
\tag{9}
\]
поскольку P_0^i=1. Если B_i^T v=0, то
\[
0=(p^i)^TB_i^Tv=-\ell_1v_1,
\]
следовательно v_1=0. Первая строка транспонированного блока даёт ell_2 v_2=0, следующая — ell_3 v_3=0, и так до N. Значит v=0. Конечномерность даёт (8).

Дополнительная точная проверка через крайний кофактор:
\[
\boxed{
\det B_i\,P_N^i=(-1)^N\prod_{k=1}^N\ell_k\ne0.
}
\tag{10}
\]
Это следует из (9) после умножения на adj(B_i) и взятия N-й компоненты. Формула (10) не является оценкой нормы обратной матрицы. **Резонанс исключён; uniform conditioning и знак отклика ею не доказаны.**

## 4. Разность двух правых границ: её знак действительно установлен

**[COFINAL_FAMILY | PAPER]** Этот дополнительный результат нужен, потому что B_0 и B_4 различаются не только сдвигом энергии.

Положим
\[
\Delta E=E_4-E_0>0,\qquad \mu_k=\frac1{4k+1},\qquad
\mu_ku_k=\mu_{k+1}\ell_{k+1}.
\]
Веса mu — вспомогательные коэффициенты дискретного Wronskian; евклидова норма CCM-строки не меняется. Для r>=0 зададим
\[
y_i(r)=\frac{P_{N+r}^i}{P_N^i}.
\]
На источниковом хвосте y_i(0)=1, 0<y_i(r)<=2^{-r}. Определим
\[
\boxed{
\vartheta_m=\sum_{r\ge1}\frac{\mu_{N+r}}{\mu_N}y_0(r)y_4(r),
\qquad 0<\vartheta_m<\frac13.
}
\tag{11}
\]
Верхняя граница следует из mu_{N+r}<mu_N и суммы `sum_{r>=1}4^{-r}=1/3`; здесь оценивается **двухэнергетический хвостовой отклик**, а не заново Ferrers-prefix error.

Вычитая две взвешенные рекурсии на k=N+1,...,M, получаем
\[
\Delta E\sum_{k=N+1}^{M}\mu_k
\frac{P_k^0}{P_N^0}\frac{P_k^4}{P_N^4}
=W_M-\mu_Nu_N(t_4-t_0).
\]
Здесь
\[
W_M=\mu_Mu_M\left(
\frac{P_M^0P_{M+1}^4}{P_N^0P_N^4}
-\frac{P_M^4P_{M+1}^0}{P_N^4P_N^0}\right).
\]
Геометрическое убывание даёт W_M->0. Значит
\[
\boxed{u_N(t_4-t_0)=-\Delta E\,\vartheta_m,}
\qquad
\boxed{B_4-B_0=-\Delta E\,M_m,\quad
M_m=I+\vartheta_m e_Ne_N^T.}
\tag{12}
\]
В частности, t_4>t_0. Утверждение (12) точное для всей выбранной семьи. Ни fixed-frequency asymptotic, ни prolate 6pi gap не использованы.

Для одного и того же h положим phi^i=B_i^{-T}h. Из (12)
\[
\phi^0-\phi^4=-\Delta E\,B_0^{-T}M_mB_4^{-T}h.
\tag{13}
\]
Таким образом,
\[
\boxed{
\sum_{k=1}^N(P_k^0-P_k^4)h_k
=\ell_1\Delta E\,e_1^TB_0^{-T}M_mB_4^{-T}h.
}
\tag{14}
\]
**Положительность M_m не означает положительности этого отклика.** В выражении стоят две разные обратные матрицы и конкретный forcing; знаковое свойство их произведения не постулируется. Игнорирование зависимости t_i от E_i потеряло бы слагаемое vartheta_m e_Ne_N^T.

## 5. Настоящий forcing и его когерентные нижние края

### 5.1. Ни Mellin-сопряжение, ни Q6 не исчезают

**[FINITE_CELL | PAPER]** Берём ровно
\[
F_{nk}=\frac{m^{1/4}}{\sqrt L}\mathcal M_{m,k}(s_n),
\quad 1\le k\le N,\qquad x=Fc,
\]
\[
c_k=\kappa_m(-1)^k(P_k^0-P_k^4),\qquad
 g_n=(K_jd)_n,
\]
\[
\boxed{
h_k=(-1)^k\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}\overline{\mathcal M_{m,k}(s_n)}\,g_n.
}
\tag{15}
\]
Здесь kappa_m — прежний вещественный множитель (16), его знак не подставляется по догадке. Матрица K_j — полный source `ccmWeilTauN1`, включая отдельную диагональную ветвь и все prime powers. fileciteturn32file0L2-L2 fileciteturn34file0L2-L2 fileciteturn39file0L2-L2

Для ясности фиксируем граничный член Q6 в самом d:
\[
d_n=\left(1+\frac{\omega_n^2-15/4}{16\pi m}\right)b_n^G
-\frac{G'(L/2)}{8\pi m\sqrt L},\qquad
\omega_n=2\pi n/L,
\tag{16}
\]
где b_n^G=coeff(T_mG)(n). **Знак граничного слагаемого в d — минус**; плюс стоял в остатке `a-d`.

Поскольку G вещественна и чётна, d_n=d_{-n} принадлежит R. Полные CCM-формулы дают K_j(-n,-n')=K_j(n,n') и вещественность всех элементов. Поэтому g_n=g_{-n} принадлежит R. Наконец, M_{m,k}(s_{-n})=overline(M_{m,k}(s_n)), откуда **h_k принадлежит R** и выбранные Robin-решения тоже вещественны. Это точное следствие симметрии данного forcing, **не замена комплексных моментов модулями и не ограничение класса y в q_j^perp**.

### 5.2. Явный ступенчатый вес вместо независимых фаз

**[FINITE_CELL | PAPER]** Переставляя только конечные суммы и интеграл, получаем
\[
\boxed{
h_k=\int_{1/m}^{1}(-1)^kP_{2k}(t)\,\mathscr H_m(t)\,dt,
}
\tag{17}
\]
\[
\boxed{
\mathscr H_m(t)=\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}g_n t^{\overline{s_n}-1}
\sum_{1\le r\le mt}r^{-\overline{s_n}}.
}
\tag{18}
\]
Это вещественный, но **не доказанно знакопостоянный** вес. Здесь P_{2k}(t) — обычный Legendre-полином, а не recurrence-полином P_k^i.

Продолжим вес нулём левее 1/m. Для 1<=r<m обозначим его скачок справа минус слева в a_r=r/m через `[H]_{a_r}`. Пусть
\[
\Sigma_g=\sum_{n=-m}^{m}g_n.
\]
Тогда
\[
\boxed{
[\mathscr H_m]_{a_r}=\frac{m^{3/4}}{r\sqrt L}\Sigma_g,
\qquad
[\mathscr H_m']_{a_r}=-\frac{m^{7/4}}{2r^2\sqrt L}\Sigma_g.
}
\tag{19}
\]
Доказательство первого равенства использует буквально
\[
r^{-\overline{s_n}}(r/m)^{\overline{s_n}}=m^{-1/2}.
\]
Во втором равенстве дополнительно использовано `sum_n omega_n g_n=0`, следующее из чётности g. При r=m интервал нового Mellin-слагаемого вырожден; соответствующий исходниковый поток содержит множитель `1-r^2/m^2=0`.

Следовательно, все эти скачки имеют **один и тот же источниковый множитель Sigma_g**, а не независимые случайные фазы. **Sigma_g не объявляется нулём и его знак здесь не доказан.**

Точный контроль связи с прежним (20)–(21): для полной выбранной безразмерной функции Phi_{i,m}, после спаривания (21) с сопряжённой Mellin-сеткой и g, нижний forcing **до общего минуса в (20)** равен
\[
\boxed{
\frac{m^{7/4}}{\sqrt L}\Sigma_g
\sum_{r=1}^{m-1}\frac{1-r^2/m^2}{r^2}
\left[\frac r m\Phi'_{i,m}(r/m)+\frac12\Phi_{i,m}(r/m)\right].
}
\tag{20}
\]
Этот вывод — точное конечное суммирование, не усреднение фаз. Само (20) относится к **полной** Phi_{i,m}; обрезанный Legendre-полином не объявляется решением однородного ODE. Верхний дискретный дефект prefix сохраняется через t_i и правые члены (G). Исходниковое ODE и нулевой поток не означают нулевых значений на концах. fileciteturn34file0L2-L2 fileciteturn37file0L2-L2

## 6. Смешанный член перенесён; остальные части не отброшены

**[FINITE_CELL | PAPER]** Обозначим
\[
\beta_m=e_1^TB_0^{-T}M_mB_4^{-T}h,\qquad D_m=d^*K_jd.
\]
Из (14) и настоящего (MIX) следует
\[
\boxed{\mathcal C_m=2\kappa_m\ell_1\Delta E\,\beta_m-2D_m.}
\tag{21}
\]
При исходных данных beta_m вещественна. Никакой знак beta_m из существования обратных матриц не выведен.

Пусть w=x-d, X=||x||_2, Y=||Pi x||_2, Pi=Pi_{U_j}, theta=tr_{U_j}K_j. На принятом хвосте Y>eta_m определим
\[
\mathscr A_m=w^*K_jw-D_m-X^2\theta
+\frac{X^2}{Y^2}x^*\Pi K_j\Pi x.
\]
Тогда полная величина предшественника равна
\[
\boxed{T(m)=\mathscr A_m+2\kappa_m\ell_1\Delta E\,\beta_m.}
\tag{22}
\]
В частности, знания знака одного MIX недостаточно: w^*K_jw, D_m и plane-коррекция остаются в (22).

### Весь квартет можно перенести тем же Green-оператором

**[FINITE_CELL | PAPER]** Чтобы следующий тест не выдал знак одного смешанного члена за знак всей формы, введём **полностью заданный сопряжённый forcing всей квартетной формы**:
\[
g^\sharp=Y^2(K_jx-\theta x)+X^2\Pi K_j\Pi x,
\qquad
h_k^\sharp=(-1)^k(F^*g^\sharp)_k.
\tag{23}
\]
Зависимость от x=Fc сохранена; это не независимый поставщик нужного знака. По определению квартетной формы (17) предшественника
\[
x^*g^\sharp=\mathcal Q_m(c).
\]
Решим две уже доказанно разрешимые задачи:
\[
\boxed{B_4^T\psi^\sharp=h^\sharp,\qquad
B_0^T\chi^\sharp=M_m\psi^\sharp.}
\tag{24}
\]
Применение (14) даёт
\[
\boxed{\mathcal Q_m(c)=\kappa_m\ell_1\Delta E\,\chi_1^\sharp,
\qquad T(m)=\frac{\kappa_m\ell_1\Delta E\,\chi_1^\sharp}{Y^2}.}
\tag{25}
\]
Фактор 2 здесь **отсутствует**: он относился только к MIX. Это точный перенос всей квартетной формы в одну граничную компоненту двух последовательно решаемых source-matched adjoint-задач.

Равенство (25) не поставляет знак chi_1^sharp. Оно показывает точно, **какого** одностороннего источникового утверждения ещё нет. Область (24) полностью фиксирована:
\[
\begin{gathered}
m=J_P+j+2,\quad 1\le k\le N=6m-1,\quad -m\le n,n'\le m,\\
1\le r\le m\quad\text{в неполных моментах};\qquad r<m\quad\text{в нижнем forcing},
\end{gathered}
\]
с истинными хвостовыми отношениями выбранных энергий в (RB).

**Важный предохранитель.** Для h^sharp сохраняется вещественность конечных коэффициентов, но g^sharp не обязательно вещественна и чётна по n: гарантировано лишь `g^sharp_{-n}=conj(g^sharp_n)`. Поэтому в ступенчатом весе (18) с g=g^sharp нужно сохранять **два** вещественных момента
\[
\Sigma_0^\sharp=\sum_n g_n^\sharp,\qquad
\Sigma_1^\sharp=\sum_n(\overline{s_n}-1)g_n^\sharp.
\]
Его скачки равны
\[
[\mathscr H_m^\sharp]_{a_r}=\frac{m^{3/4}}{r\sqrt L}\Sigma_0^\sharp,
\qquad
[(\mathscr H_m^\sharp)']_{a_r}=\frac{m^{7/4}}{r^2\sqrt L}\Sigma_1^\sharp.
\tag{26}
\]
Нельзя автоматически перенести упрощение `Sigma_1=-Sigma_0/2` из исходного g=Kd на полный g^sharp. Парный нижний forcing при этом содержит
\[
\frac{m^{7/4}}{\sqrt L}
\sum_{r=1}^{m-1}\frac{1-r^2/m^2}{r^2}
\left[\Sigma_0^\sharp\frac r m\Phi'_{i,m}(r/m)
-\Sigma_1^\sharp\Phi_{i,m}(r/m)\right],
\tag{27}
\]
опять до общего минуса исходного ODE. Так сохраняется нижняя граница при переносе **полной**, а не только смешанной формы.

## 7. Первый недоказанный односторонний знак и полный ledger

**[COFINAL_FAMILY | PAPER]** Принятый сертификат остаётся
\[
\mathfrak L_m=T(m)+\mathcal R(m),\qquad |\mathcal R(m)|\le B(m),
\qquad \tau_j=-\mathfrak L_m/\rho_m^2.
\]
Первое недоказанное утверждение после выполненного Green-переноса — **односторонняя оценка действительной граничной компоненты chi_1^sharp из (24) с настоящим forcing (23), (26)–(27)**:
\[
\boxed{
\kappa_m\ell_1\Delta E\,\chi_1^\sharp>Y^2B(m)
\quad\text{на доказанно неограниченных выбранных индексах},
}
\tag{28-}
\]
либо
\[
\boxed{
\kappa_m\ell_1\Delta E\,\chi_1^\sharp<-Y^2B(m)
\quad\text{на всём выбранном хвосте}.
}
\tag{28+}
\]
Не заявляется ни одно из этих неравенств. Не заявляется и противоположное утверждение, будто margin невозможен или интервал обязательно содержит ноль.

Это не повтор прежнего (18) без работы: **обе сопряжённые задачи теперь доказанно разрешимы на всей семье**, их разность удерживает точный положительный хвостовой секант (11)–(12), а неоплаченный знак относится к конкретному граничному отклику на раскрытый forcing. Но сама знаковая трудность не исчезла.

Почему текущие входы её не закрывают: положительность M_m не даёт знака `B_0^{-T} M_m B_4^{-T} h^sharp`; обратимость не даёт односторонней оценки этой компоненты; поля рекурсии и tail splice не оценивают совместные знаки ступенчатого forcing и его source-resolvent response. Оценка hmode и геометрический tail budget не применяются повторно как мнимый поставщик (28). Доказательства невозможности такого знакового supplier здесь нет.

**[FINITE_CELL | PAPER]** Все перенесённые значения K_j и все корреляции ошибок остаются полными. Равенство (25) меняет только конечное Ferrers-суммирование **после** сложения W02–WR–Prime. Оно не отождествляет J_m с CCM-матрицей.

| Часть | Что сохранено |
|---|---|
| **W02 и WR** | В g=Kd и g^sharp используется весь K_j. В глобальной записи ошибок сохраняется интеграл W02, диагональный член `-(gamma+log(4pi)) Omega(0)/2` и вычитание Omega(0) в числителе WR. Нормировки ошибок не объявляются единичными. |
| **Q6 и физические края** | d вычисляется по (16). Оба скачка конечного Fourier-синтеза остаются. Правое Robin-сокращение в (7) относится к индексу Ferrers-рекурсии и не удаляет ни один физический край. |
| **Все prime powers** | Конечная матрица содержит все `2<=nu<=m`. При использовании глобальных ошибок остаются все `nu>=2`, включая `nu>m`, через ту же полную корреляцию (15) предшественника. Ни одна из возвращённых частей не объявляется нулевой отдельно. |
| **Нижний Mellin-forcing** | Индексы `r=1,...,m-1`, точная фаза `m^{-1/2}` и source-значения/производные сохранены в (20), (26)–(27). Вырожденный r=m учитывается своим нулевым потоком, не заменой остальных краёв нулём. |

Этот ledger опирается на полное source-crosswalk предшественника и его аудит; Green-алгебра не требует новых бесконечных сумм в W. Единственная новая бесконечная сумма — положительный Jacobi-tail pairing (11), для которого сходимость и граница доказаны отдельно. fileciteturn32file0L2-L2 fileciteturn33file0L2-L2 fileciteturn39file0L2-L2

Если (28-) выполнено, то
\[
\tau_j\le-\frac{\kappa_m\ell_1\Delta E\,\chi_1^\sharp/Y^2-B(m)}{\rho_m^2}<0.
\]
Если (28+) выполнено eventually, то
\[
\tau_j\ge-\frac{\kappa_m\ell_1\Delta E\,\chi_1^\sharp/Y^2+B(m)}{\rho_m^2}>0.
\]
Это только направления принятого сертификата, **не доказанные знаковые исходы**. Schur-floor не закрывается ни одним формальным Green-переносом.

## 8. Контрпроверки и сильнейшее возражение

**[ABSTRACT | PAPER]** Проверка одной строки N=1 даёт
\[
P_1h_1=u_0P_1\phi_0+\ell_2P_1\phi_2
-\ell_1P_0\phi_1-u_1P_2\phi_1,
\]
что совпадает с (G). При двух Dirichlet-границах и E=d_1^{rec}, h_1!=0 уравнение решения не имеет: это контроль детектора резонанса, **не контрпример к выбранной CCM-семье**. При согласованной границе B=-ell_1/P_1, и (10) снова точна.

Снятие множителя `u_N/ell_{N+1}` из (RB) оставляет ненулевой в общем случае правый член
\[
(\ell_{N+1}-u_N)t_iP_N^i\phi_N^i.
\]
Снятие зависимости t_i от энергии теряет положительный rank-one член vartheta_m в (12). Оба ошибочных переноса отвергнуты бумажной алгеброй.

**Сильнейшее возражение:** «Robin-граница выбрана через P, значит обратимость или знак зашиты в определение». Обратимость не зашита: отношение (5) уже независимо дано источниковым хвостом, не определяется через h или желаемый margin; (9)–(10) доказывают разрешимость. Однако **считать знак следствием такой обратимости действительно было бы кругом**. Он оставлен ровно в (28), где не поставлен никакой односторонний supplier.

Второе существенное возражение: перенос всей формы в (25) не делает forcing проще автоматически — он зависит от настоящего x и plane-коррекции. Это верно. Вывод здесь не «доказательство знака», а закрытый cofinal вопрос разрешимости и точная source-граница оставшегося знака.

## 9. Один следующий дискриминирующий PAPER-тест

**`TEST_SOURCE_MATCHED_ROBIN_COUPLED_BOUNDARY_MARGIN`**

На тех же выбранных m построить **односторонний аналитический сертификат именно для chi_1^sharp в (24)**, с forcing (23), (26)–(27), и проверить произведение `kappa_m ell_1 DeltaE chi_1^sharp` относительно `+/-Y^2 B(m)`. При использовании двухэнергетического resolvent identity требуется точный M_m из (11), а не I. Положительный собственный хвостовой фактор не заменяет знака остального отклика.

Успех теста — (28-) на явно доказанной неограниченной выбранной подпоследовательности либо (28+) на всём выбранном хвосте, с положительным указанным запасом и сохранённым полным ledger. Если источник даёт лишь модуль или ненулевой determinant, тест не выполнен. При неудаче нужно назвать конкретное source-парное forcing/граничное слагаемое из (24), (26)–(27), чей односторонний остаток не оплачен. Числовая сетка, Lean и runtime этим не разрешаются.

Две репрезентации того же объекта, не две директивы:

| Репрезентация | Решающее действие / стоимость | Риск |
|---|---|---|
| **Выбрана: source-matched Robin и двухэнергетический ответ (24).** | Один boundary margin даёт вывод для всей семьи. Две трёхдиагональные задачи размерности 6m-1; их cofinal разрешимость уже доказана. | Знак источникового forcing-response, а не резонанс; нельзя потерять энергетическую поправку правой границы. |
| **Альтернатива: обратная задача Коши для adjoint.** | Положить phi_N=phi_{N+1}=0 и определить phi_{k-1} из (2) при k=N,...,1; u_{k-1}!=0, поэтому решение есть при любом E. Green-ответ равен `(E-d_0^{rec}) phi_0-ell_1 phi_1`. На энергию достаточно одного конечного прохода без inverse и без хвостового отношения. | Большие взаимные сокращения двух левых ответов; одно существование по рекурсии также не даёт знака. |

Стоимость здесь — структура математического расчёта, не обещание времени выполнения. Альтернативная граница не меняет q, z или источник; она меняет только вспомогательный способ вычислить тот же pairing.

## 10. Closeout и зависимости

**[COFINAL_FAMILY | PAPER]** Закрыто новое утверждение с кванторами: для всех выбранных m>=2, обеих E_i и всех h из C^N существует единственное adjoint-решение с (RB). Дополнительно доказаны точный двухэнергетический секант с 0<vartheta_m<1/3 и правильный полный boundary-перенос (25). **Не закрыты** знак MIX, margin всей квартетной формы, первый скалярный знак tau_j и Schur-floor.

Регистрации перед проверками: ставка о двух минусах в Dirichlet Green-формуле подтверждена; отдельно заявленная ставка о снятии резонанса точным источниковым хвостом подтверждена (8)–(10). Знаковая ставка на tau не регистрировалась. Положительный хвостовой секант и формулы скачков — дополнительно выведенные результаты, не задним числом объявленные прогнозы. Новое PAPER-доказательство ещё не проходило независимую проверку.

```yaml
DOWNSTREAM_CONSUMER: first_scalar_sign_gate_for_unchanged_cellwise_complement
ACTUAL_CONSUMER_REQUIREMENT: one_sided_full_source_margin_not_merely_MIX_sign
ORIGINAL_REQUESTED_OBJECT: adjoint_Green_transfer_with_correct_solvability_and_boundaries
ORIGINAL_OBJECT_IS: UNKNOWN
QUALIFICATION: this_method_is_not_proved_necessary_for_the_scalar_gate
DIRICHLET_INVERSE_AS_PREREQUISITE: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - source_matched_Robin_solution_preserves_exact_pairing_without_Dirichlet_invertibility
  - terminal_Cauchy_adjoint_solution_preserves_exact_pairing_without_any_spectral_inverse
  - any_separate_valid_full_source_margin_can_decide_tau_without_this_representation
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
MINIMAL_MISSING_ESTIMATE: one_sided_selected_full_forcing_boundary_response_in_24_to_28
DISCRIMINATOR: TEST_SOURCE_MATCHED_ROBIN_COUPLED_BOUNDARY_MARGIN
REOPEN_TRIGGER: full_source_boundary_response_bound_separating_28_or_an_exact_zero_identity
KILLED_THEOREM_SHAPE: NONE
ADJOINT_PATH_DEAD: false
NOVELTY_AXIS: source_matched_nonresonance_plus_positive_tail_secant_plus_coherent_forcing_boundary
COGNITIVE_OPERATOR_USED: DUALIZE
MEMORY_ENTRY:
  target: selected_Ferrers_prefix_MIX_adjoint_Green
  status: OPEN
  closed_quantifier: unique_source_matched_adjoint_solution_for_each_selected_cell_and_all_complex_forcings
  invariant_learned: energy_dependent_Robin_boundary_contributes_a_positive_secant_factor
  forbidden_future_move: infer_forcing_response_sign_from_invertibility_or_drop_Robin_energy_dependence
  next_decisive_test: TEST_SOURCE_MATCHED_ROBIN_COUPLED_BOUNDARY_MARGIN
```

**Единственный исход: OPEN_ADJOINT_GREEN_MIX.** Резонанс рабочего source-matched блока не препятствует переносу; односторонний полный знак пока не доказан. Выполнены чтение источников, бумажные выводы, локальная проверка хешей и создание этого Markdown. Математические численные/символьные прогоны, Lean, проектный runtime, записи в репозитории и RH claim отсутствуют.
