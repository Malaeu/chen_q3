# STATUS: TRY_CCM_PHI_LIMIT_FOUR_THIRDS_AND_FINITE_COUNT

```yaml
OPERATIVE_CLASS: TRY_CCM_PHI_LIMIT_FOUR_THIRDS_AND_FINITE_COUNT
REQUEST: LITERAL_CCM_PHI_LIMIT_2026_11_04
AUTHORITY: DIRECT_OWNER_REQUEST_IN_CHAT
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
DATE: 2026-11-04
BASE: rh_clean@c539c195
INBOX_INPUT: proshka_inbox_2026-10-31@07a242c1
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
CARRIER: EVEN_PHYSICAL_L2_COSINES_N_EQ_m_L_EQ_log_m
VERIFIER: PAPER
SCOPE: [ABSTRACT, FINITE_CELL, COFINAL_FAMILY]
TRACE_FIXED_c1_SHAPE: REFUTED
FROBENIUS_FIXED_d1_SHAPE: REFUTED
TRACE_REPAIRED: "t=1-[c*(1+log L)+b]/L+O((1+log L)^2/L^2)"
OFFDIAGONAL: UNCONDITIONAL_O_m_LOG_m
v_INFINITY: 4/3
PHI_INFINITY: 8/3
SIMPLE_ON_LINE_ASYMPTOTIC_LOWER: 2/3
DISTINCT_ASYMPTOTIC_LOWER: 5/6
BEATS_0_6725_WITH_THIS_SCORE: false
COFINAL_TAIL: INHERITED_DENSITY_BOUND_PAID
FINITE_TAIL: NEW_MODE_RESOLVED_WHOLE_ZERO_TAIL
FINITE_m: 300
FINITE_SIGMA: log_300_PLUS_1_OVER_5
FINITE_N_UPPER: 185
FINITE_TRACE_LOWER: 895.9
FINITE_FROBENIUS_SQUARED_UPPER: 5481
FINITE_NUCLEAR_TAIL_UPPER: 12.5
FINITE_SIMPLE_ON_LINE_LOWER: 14
FINITE_DISTINCT_LOWER: 100
INTERVAL_BACKEND: mpmath.iv_1.3.0
INTERVAL_REPLAYS_DPS: [45, 65]
INTERVAL_CLASS: MP_IV_NOT_ARB_NOT_LEAN
ARB_INTERVAL_EXECUTED: false
LEAN_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
INDEPENDENT_BACKEND_AUDIT: NOT_PERFORMED
FINITE_ZERO_LIST_USED: false
RH_LH_HL_PAIR_CORRELATION_ASSUMED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
CLOSES: [LEADING_NORMALIZED_SECOND_MOMENT_OF_LITERAL_CCM]
CONSUMER_REQUIRED_NEW_SUPPLIERS: []
OPTIONAL_OPEN: LIMIT_OF_SUBLEADING_ETA_m
REOPEN_TRIGGER: "Audit failure in Lemmas 2-5, source normalization, or finite interval gates; optional eta-limit only for a sharper expansion."
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CCM_PHI_LIMIT_2026-11-04.md
```

Ы. **Ведущий момент закрывается без стены близнецов: для буквального чётного CCM получается \(v_\infty=4/3\), \(\Phi_m\to8/3\), а после уже оплаченного плотностного хвоста — доли \(2/3-o(1)\) простых на линии и \(5/6-o(1)\) различных.** Здесь дан PAPER-вывод, не заявление о независимом аудите или Lean-проверке.

В постановке действительно две ловушки: постоянных \(c_1,d_1\) в предложенных разложениях нет. Их место занимают члены с \(\log L/L\). Кроме того, асимптотический хвост не надо насильно использовать при \(m=300\): отдельный модовый envelope даёт там конечный результат. Без положительного списка нулей получены интервальные входы для **не менее 14 простых нулей на линии и 100 различных** ниже исходного \(T_{300}\). Бэкенд — **mpmath.iv, не Arb и не Lean**; код и аналитические остатки включены ниже. Повтор при другой точности не называется независимым аудитом.

## 0. Source lock, импорты и границы

**[FINITE_CELL | PAPER; проверка источников.]** Прочитаны через GitHub connector:

- `PROSHKA_SYSTEM_PROMPT_v2.md`, `rh_clean`, blob из YAML.
- `docs/routeB_bus/proshka/PROSHKA_VERDICT_RANK_TRACE_CCM_2026-11-04.md`, `eada41db`, blob `b0337bb10193b2498e6c35997a49237174c84a2c`: определения A, R, физического базиса и точный rank–trace transfer.
- `docs/routeB_bus/proshka/PROSHKA_VERDICT_ZERO_DENSITY_TAIL_Q3_DIAGNOSIS_2026-11-04.md`, `07a242c1`, blob `29647418b82ade2eca870a6d68592c1bf9c51859`: унаследованный cofinal nuclear-tail budget и его оплата в score.
- `docs/routeB_bus/second_moment_2026-11-04/RESULT.md`, `c539c195`, blob `e0a53b2a60fae7e1f560530396d2fddcddd2d440`: диагностические моменты и разложение. CSV-пакет целиком не переаудирован; вместо этого m300 пересчитан из аналитических формул, без исходных массивов и без нулевого census.

**[ABSTRACT | PAPER; внешние THEOREM-импорты.]**

P1. Montgomery–Vaughan, *Hilbert's inequality*, JLMS (2) 8 (1974), 73–82, Theorem 1, (1.3): для различных по модулю 1 узлов \(x_n\), \(0<\delta_n\le\min_{k\ne n}\|x_n-x_k\|\),
\[
 \left|\sum_{n\ne k}a_n\overline{a_k}\csc\pi(x_n-x_k)\right|
 \le\frac32\sum_n\frac{|a_n|^2}{\delta_n}.                 \tag{0.1}
\]
Прочитаны и просмотрены скриншотами первые две страницы оригинальной статьи. Это безусловная геометрическая теорема, не гипотеза о простых.

P2. Классическая количественная PNT: \(\vartheta(x)=x+O_A(x/\log^A x)\) для каждого фиксированного A. Для вывода ведущей диагонали достаточно PNT; указанная стандартная безусловная скорость нужна лишь для удобной константы второго порядка в (4.1). Внешняя проверка достаточной более сильной оценки: Johnston–Yang, arXiv:2204.01980v2. Современная плотность/проверка RH до высоты в доказательство ниже не импортируется.

P3. Rosser, Theorem 19, в точной записи Faber–Kadiri, *New bounds for psi(x)*, Theorem 1.5: при \(t\ge2\),
\[
 |N(t)-M(t)|\le R(t),\quad
 M(t)=\frac{t}{2\pi}\left(\log\frac{t}{2\pi}-1\right)+\frac78,
\quad R(t)=.137\log t+.443\log\log t+1.588.                 \tag{0.2}
\]
Это счёт **всех** нулей с кратностями. Взята только Theorem 1.5, НЕ соседняя Theorem 1.3 о вычисленной RH-высоте. Формула прочитана в PDF-тексте; попытка screenshot этой страницы вернула cache miss. Отдельное доказательство оригинальной теоремы Rosser здесь не воспроизводится.

P4. Сравнение с 0.6725: проверено заявление абстракта Alpöge–Furman, arXiv:2608.13637, о Montgomery–Taylor window; полный внешний вывод этого процента здесь не аудирован и не используется как supplier.

```text
https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf
https://arxiv.org/abs/2204.01980v2
https://www.cs.uleth.ca/~kadiri/articles/New-Bounds-for-Psi-Math-Comp-Faber-Sept2013.pdf
https://arxiv.org/abs/2608.13637
https://arxiv.org/abs/2609.02882
```

## 1. Объект и исправленный ответ о следе

**[COFINAL_FAMILY | PAPER.]** Всюду \(m\to\infty\) по целым, \(L=\log m\), \(h=1+\log L\),
\[
 \omega_j=2\pi j/L,\quad \Omega=\omega_m,\quad
 \kappa=1+ch/L,\quad T=\kappa\Omega,\quad 0<c<1,
 \quad\sigma=L+b,\quad b=1/\gamma_*>0.                  \tag{1.1}
\]
В запросе \(c=1/4\). Размер чётного пространства — \(m+1\); \(N(T)\) — число верхних нулей, а не размер матрицы. Нули на высоте T полностью относятся к хвосту.

Исходный базис на \(I=[-L/2,L/2]\):
\[
 \phi_j(x)=d_j(-1)^j L^{-1/2}\cos(\omega_jx),\quad
 d_0=1,\quad d_j=\sqrt2\ (j>0).
\]
Обозначим \(c_n=\Lambda(n)/\sqrt n\), \(R_u=S_u+S_{-u}\), где сдвиги обрезаны фактическим I. В матрицах ниже R означает физическое сжатие. Сохраняем точное исходное разложение
\[
 A=H+P-B,\quad P=vv^*,\quad B=\sum_{2\le n\le m}c_nR_{\log n},
\quad v_j=\frac{\sqrt2d_j\sinh(L/4)}{\sqrt L(\omega_j^2+1/4)}. \tag{1.2}
\]
Все простые степени включены. При \(n=m\) перекрытие нулевой меры, поэтому его вклад точно нулевой.

Ниже доказано
\[
 \operatorname{tr}A=m(L-h)+O(\sqrt m\,L+L^2).             \tag{1.3}
\]
Из (0.2)
\[
 N(T)=\frac{\kappa m}{L}(L-h+\log\kappa)+O(L).
\]
Следовательно,
\[
 t_m=\frac{L}{L+b}\frac{L-h}{\kappa(L-h+\log\kappa)}
       +O(L^2/\sqrt m)
 =1-\frac{ch+b}{L}+O(h^2/L^2).                          \tag{1.4}
\]
Таким образом, \(L(t_m-1)=-c\log L-c-b+o(1)\to-\infty\). **Не существует постоянной \(c_1\), удовлетворяющей форме запроса.** Это не отсутствие найденного коэффициента, а несовместимость указанной формы с cutoff.

При m300: L=5.703782..., kappa=1.120145..., исходниковый главный след \(m(L-h)=888.795878...\), точный пересчёт даёт 895.996435.... Если только для объяснения диагностической таблицы поставить её \(b\approx0.07074775\), рациональное выражение (1.4) даёт **0.84928**, измерено **0.84789**. Для окончательной конечной оценки ниже применяется независимо доказанное \(b=1/5\), а не первая ордината из таблицы.

## 2. Gamma: точная положительная краевая поправка, а не пропуск Gamma

**Лемма 1. [FINITE_CELL / COFINAL_FAMILY | PAPER.]** Положим
\[
 q(t)=\Re\psi(1/4+it/2)-\log\pi,\quad
 D=\operatorname{diag}(q(\omega_j)),\quad a_r=2r+1/2.
\]
Тогда для каждого m
\[
 H=D+K,\qquad
 K_{jk}=\frac{2d_jd_k}{L}\sum_{r\ge0}
 \frac{a_r^2(1-e^{-a_rL})}{(a_r^2+\omega_j^2)(a_r^2+\omega_k^2)}.
                                                               \tag{2.1}
\]
В частности \(K\succeq0\), \(\operatorname{tr}K=O(L)\), \(\|H\|=O(L)\).

**Доказательство.** Раскладываем исходный \(j(u)=e^{-u/2}/(1-e^{-2u})\) в \(\sum_{r\ge0}e^{-a_ru}\). Прямое интегрирование перекрытий даёт при \(j\ne k\)
\[
 R(u)_{jk}=-\frac{2d_jd_k}{L}
 \frac{\omega_j\sin(\omega_ju)-\omega_k\sin(\omega_ku)}
      {\omega_j^2-\omega_k^2},                            \tag{2.2}
\]
а при \(j=k>0\)
\[
 R(u)_{jj}=2(1-u/L)\cos(\omega_ju)
                  -\frac{2\sin(\omega_ju)}{L\omega_j};
\quad R(u)_{00}=2(1-u/L).
\]
Используем \(\omega_jL=2\pi j\) и
\(
 \int_0^Le^{-au}\sin(\omega_ju)du
 =\omega_j(1-e^{-aL})/(a^2+\omega_j^2).
\)
Диагональное вычисление включает интеграл u>=L. После вычитания периодического символа q получается (2.1). Каждое слагаемое — положительный rank-one Gram.

Для \(w\ge0\), сравнением суммы с интегралом для одногорбой функции,
\(
 \sum_r a_r^2/(a_r^2+w^2)^2\ll(1+w)^{-1}.
\)
Поэтому \(K_{jj}\ll[L(1+\omega_j)]^{-1}\); суммирование даёт O(L). Также \(\|K\|\le\operatorname{tr}K\). Никакой положительности A отсюда не следует.

Из \(q(t)=\log(t/(2\pi))+O(t^{-2})\) при t>=1, отдельно обрабатывая O(L) низких мод и применяя суммирование к \(\log(j/L)\), получаем
\[
 \operatorname{tr}H=m(L-h)+O(L^2),
\quad \|H\|_F^2=m[(L-h)^2+1]+O(L^2).                    \tag{2.3}
\]
Для второго равенства \(2|\operatorname{tr}DK|+\operatorname{tr}K^2=O(L^2)\). Все Gamma-константы и прямоугольный край сохранены.

Кроме того, равномерно по p<=m и log2<=u<L,
\[
 \operatorname{tr}R_p(u)=(1-u/L)[1+D_p(2\pi u/L)]
                   -\frac1\pi\sum_{j=1}^p\frac{\sin(2\pi ju/L)}j
                   =O(L).                              \tag{2.4}
\]
Здесь \(D_p\) — Dirichlet kernel; у u=L множитель L-u снимает граничную особенность. Использованы \(|D_p(2\pi x)|\le1/|\sin\pi x|\) и равномерная ограниченность суммы sin(j theta)/j. PNT/Chebyshev дают \(\sum c_n=O(\sqrt m)\). Поэтому \(\operatorname{tr}B=O(\sqrt m L)\), а \(\operatorname{tr}P\le L+2\sinh(L/2)=O(\sqrt m+L)\). Это доказывает (1.3).

## 3. Вся внедиагональ: один Hilbert-bound вместо пар простых

**Лемма 2. [FINITE_CELL | PAPER.]** Введём конечные, явно вычислимые величины
\[
 d=2m+1,\quad Q=\sum c_n^2(1-\log n/L),\quad S_0=\sum c_n^2,
\]
\[
 C_0=\sum|c_n|,\quad
 W=\sum(n+1)c_n^2(L-\log n),\quad
 C_\times=\sum_{n,k\ge2,\ nk\le m}|c_nc_k|,
\]
\[
 \beta_m=\frac2{\pi^2}(\log(2m+1)+2),\qquad
 b_L=1+\frac{L}{4\log2}.
\]
Тогда для **сжатого чётного** B из (1.2)
\[
 \boxed{|\|B\|_F^2-dQ|
 \le\frac32W+b_LC_\times+(8+4\beta_m)C_0^2=:E_B.}         \tag{3.1}
\]
Для диагонали по арифметическим атомам
\[
 \mathcal D=\sum_n c_n^2\operatorname{tr}(R_n^2),\qquad
 |\mathcal D-dQ|\le(b_L+8+4\beta_m)S_0=:E_D.               \tag{3.2}
\]
Значит, точная внедиагональ
\[
 \mathcal O_m=\sum_{n\ne k}c_nc_k\operatorname{tr}(R_nR_k)
\quad\text{удовлетворяет}\quad |\mathcal O_m|\le E_B+E_D. \tag{3.3}
\]

**Доказательство с оплатой проекции.** Пусть Pi — полный Fourier projector |j|<=m на круге длины L, J — отражение, \(\Pi_E=(1+J)\Pi/2\). Используем несжатый обрезанный оператор \(\mathcal B=\sum c_n(S_{u_n}+S_{-u_n})\), \(u_n=\log n\).

В полном комплексном базисе точное разложение энергии:
\[
 \operatorname{tr}(\Pi\mathcal B^2\Pi)
 =\frac2L\sum_{n,k}c_nc_k
 \{(L-\max(u_n,u_k))D_m(2\pi(u_n-u_k)/L)
 +(L-u_n-u_k)_+D_m(2\pi(u_n+u_k)/L)\}.                  \tag{3.4}
\]
В первой части диагональ равна 2dQ. Для её внедиагонали пишем
\(
 L-\max(u_n,u_k)=\int_0^L1_{u_n\le s}1_{u_k\le s}ds.
\)
Узлы \(x_n=\log n/L\) различны на круге; даже с круговым зазором можно взять
\[
 \delta_n=\frac1{(n+1)L}.                               \tag{3.5}
\]
Обычный зазор следует из log(1+1/n)>=1/(n+1); круговой зазор не меньше log2/L. Из (0.1) и
\(D_m(2\pi x)=\sin(\pi d x)\csc(\pi x)\)
получаем для каждого префикса
\[
 \left|\sum_{n\ne k}c_nc_kD_m(2\pi(x_n-x_k))\right|
 \le\tfrac32 L\sum_n(n+1)c_n^2.
\]
Интегрирование по s и переход к половине полного trace дают именно \(\frac32W\), не предположение об исчезновении корреляций.

Вторая часть (3.4) существует только при nk<=m. При w=log(nk),
\[
 |(1-w/L)D_m(2\pi w/L)|\le b_L\quad(2\log2\le w<L).
\]
На w=L множитель равен нулю. Это даёт \(b_LC_\times\) после половинного trace.

**Цена чётности.** \(\mathcal B\) коммутирует с J, поэтому
\[
 \operatorname{tr}(\Pi_E\mathcal B^2\Pi_E)
 =\tfrac12\operatorname{tr}(\Pi\mathcal B^2\Pi)
 +\tfrac12\operatorname{tr}(\Pi J\mathcal B^2\Pi).
\]
Каждое произведение двух обрезанных сдвигов — ещё один сдвиг на интервале. Его отражённый trace — интеграл
\(
 L^{-1}\int_KD_m(2\pi(2x+a)/L)dx.
\)
Примитив и \(|\sum_{j\le m}\sin(j\theta)/j|\le1+\pi\) дают абсолютную оценку <4. Четыре ориентации сдвигов и множитель 1/2 дают цену <=8 C_0^2. Чётный блок не отождествляется со всем Fourier-блоком.

**Цена повторного сжатия.** Для индикатора любого интервала K его Fourier-коэффициенты удовлетворяют \(|\widehat{1_K}(r)|\le1/(\pi|r|)\), r!=0. Поэтому
\[
 \|(1-\Pi)1_K\Pi\|_F^2
 \le\frac2{\pi^2}\left(\sum_{r=1}^{d}\frac1r+
                              d\sum_{r>d}\frac1{r^2}\right)
 \le\beta_m.
\]
Обрезанный сдвиг есть индикатор, умноженный на периодический сдвиг, сохраняющий Pi. Треугольное неравенство даёт
\[
 \|(1-\Pi)\mathcal B\Pi\|_F^2\le4\beta_mC_0^2.
\]
Из паритета утечка чётного блока не больше этой. Тождество
\[
 \|\Pi_E\mathcal B\Pi_E\|_F^2
 =\operatorname{tr}(\Pi_E\mathcal B^2\Pi_E)
      -\|(1-\Pi_E)\mathcal B\Pi_E\|_F^2
\]
оплачивает последний член (3.1). Применение того же расчёта к одному атому и суммирование его квадрата даёт (3.2). Все края, wrap-around и потеря при сжатии перечислены. □

**Следствие. [COFINAL_FAMILY | PAPER.]** Для фактических c_n=Lambda(n)/sqrt(n),
\[
 S_0=O(L^2),\ C_0=O(\sqrt m),\ W=O(mL),\
 C_\times=O(\sqrt m L),\quad E_D=O(L^3).
\]
Например, W<=2L sum Lambda(n)(L-log n)=O(mL); для C_cross применяем \(\sum_{k\le x}\Lambda(k)/\sqrt k=O(\sqrt x)\) и \(\sum_{n\le m}\Lambda(n)/n=O(L)\). Следовательно,
\[
 \boxed{\mathcal O_m=O(mL)=o(mL^2).}                    \tag{3.6}
\]
Это безусловный двусторонний envelope всей знаковой суммы. **HL, RH, LH и F(alpha) при alpha>1 здесь не нужны.** Близость lambda_eff к 1 сама ничего не доказывала; доказательство даёт конкретный круговой Hilbert-bound вместе с ценой проекции.

## 4. Диагональ простых, смешанные члены и главный Frobenius

**Лемма 3. [COFINAL_FAMILY | PAPER.]** Существует конечная арифметическая константа
\[
 C_\Lambda=\lim_{x\to\infty}
 \left(\sum_{n\le x}\frac{\Lambda(n)^2}{n}-\frac12\log^2x\right).
\]
Количественная PNT и частичное суммирование дают
\[
 \sum_{n\le x}\Lambda(n)^2=x\log x-x+O_A(x/\log^A x),
\quad Q=L^2/6+C_\Lambda+O(1/L).
\]
Высшие степени простых дают в первой сумме \(O(\sqrt x\log^3x)\), а не выбрасываются. Для второго равенства используем
\(
 Q=L^{-1}\int_0^L\sum_{n\le e^u}\Lambda(n)^2/n\,du.
\)
По (3.2)
\[
 \boxed{\mathcal D=mL^2/3+2C_\Lambda m+O(m/L+L^3).}       \tag{4.1}
\]
Таким образом, ведущий арифметический коэффициент **1/3** вычислен через PNT.

Полюс и смешанные члены также оплачены. Имеем
\[
 \|P\|_F^2=O(m),\quad |\operatorname{tr}(HP)|=O(\sqrt m L),
 \quad |\operatorname{tr}(PB)|=O(m).                     \tag{4.2}
\]
Последняя оценка следует из \(\|B\|\le2C_0\) и \(\operatorname{tr}P=O(\sqrt m)\).

Для Gamma×prime пишем H=D+K. q(omega_j) монотонно возрастает: это видно из ряда digamma. Его величина и полная вариация O(L). Abel summation с (2.4) даёт \(|\operatorname{tr}(DR_u)|=O(L^2)\). Кроме того \(|\operatorname{tr}(KB)|\le\operatorname{tr}K\,\|B\|\). Поэтому
\[
 |\operatorname{tr}(HB)|=O(\sqrt m L^2).                 \tag{4.3}
\]
Все эти члены меньше mL; их знаки не подменены положительностью.

Совместив (2.3), (3.6), (4.1)–(4.3), получаем
\[
 \boxed{\|A\|_F^2=m[(L-h)^2+1]+mL^2/3+O(mL).}           \tag{4.4}
\]
В частности, \(\|A\|_F^2\sim(4/3)mL^2\). Это вывод для исходной физической матрицы, не для surrogate Gabor-окна.

## 5. Предел Phi и точная граница второго порядка

**Теорема 4. [COFINAL_FAMILY | PAPER.]** Из (1.4), (4.4) и N(T)~m:
\[
 \boxed{v_m\longrightarrow4/3,\qquad\Phi_m=4t_m-v_m\longrightarrow8/3.} \tag{5.1}
\]
Унаследованный хвост \(O_c(L^7/h^2)\) из `07a242c1`, вместе с его уже доказанной оплатой в score, даёт
\[
 \boxed{\frac{s_1(T_m)}{N(T_m)}\ge\frac23-o(1),\qquad
        \frac{N_d(T_m)}{N(T_m)}\ge\frac56-o(1).}          \tag{5.2}
\]
Это безусловное PAPER-следствие названных теорем и вывода выше. Новое утверждение RH не делается. Наличие фиксированных внелинейных нулей совместимо с (5.2).

Чтобы не скрыть остаток второго порядка, определим **ровно**
\[
 \eta_m=\frac1{mL}\sum_{n\ne k\le m}
 \frac{\Lambda(n)\Lambda(k)}{\sqrt{nk}}\operatorname{tr}(R_nR_k).
                                                               \tag{5.3}
\]
Доказано eta_m=O(1), но существование её предела не доказано. Более точная запись:
\[
 v_m=\frac43+
 \frac{-\frac{2+4c}{3}h-\frac83b+\eta_m}{L}+o(1/L).       \tag{5.4}
\]
При c=1/4:
\[
 v_m=\frac43+\frac{-h-\frac83b+\eta_m}{L}+o(1/L),
\qquad L(v_m-4/3)=-\log L+O(1)\to-\infty.               \tag{5.5}
\]
**Постоянного d1 в предложенной форме также нет.** Точный неоценённый коэффициент после удаления обязательного логарифма — eta_m. Ведущая доля его предела не требует. Утверждать, что для этого дополнительного предела *необходима* HL, было бы необоснованно: здесь доказана лишь достаточность безусловного O(1) для основного consumer.

Любопытная особенность именно c=1/4: логарифмические поправки в Phi взаимно уничтожаются:
\[
 \boxed{\Phi_m=\frac83-\frac{\frac43b+\eta_m}{L}+o(1/L).} \tag{5.6}
\]
Это не разрешает выбросить eta_m и не является новой положительностью остатка.

При m300 вклад H² составляет лишь 2954.816..., а его будущий масштаб mL² — 9759.94...; поэтому v около 0.90 не противоречит пределу 4/3. В конечной ячейке существенно также взаимное погашение pole² и pole×prime. Эти члены включены в пересчёт.

Сравнение с 0.6725: **2/3 < 0.6725**. Буквальный равномерный CCM-score из запроса этого числа не превосходит. Более сильный score/веса/спектральная поправка были бы другим доказательством; вся Route B этим не убита.

## 6. Конечный хвост: не терять 300 разных знаменателей

**Лемма 5. [FINITE_CELL | PAPER.]** Для m>=2, T>Omega, каждого верхнего нуля z=gamma+i eta, |eta|<1/2, gamma>=T, точная evaluation-колонка даёт
\[
 2\|e(z)\|^2\le w_m(\gamma),\qquad
 w_m(t)=\frac{8\cosh^2(L/4)}{L}(t^2+1/4)
              \sum_{j=0}^{m}\frac{d_j^2}{(t^2-\omega_j^2)^2}. \tag{6.1}
\]
Использованы \(|\sin(zL/2)|^2\le\cosh^2(L/4)\),
\(|z^2-\omega_j^2|^2\ge(\gamma^2-\omega_j^2)^2\). Оба знака высоты и все кратности оплачены. Функция w_m положительна и строго убывает при t>Omega.

Пусть |N(t)-M(t)|<=R_*(t) при t>=T, R_* неубывает. Stieltjes-интегрирование с N(T-) даёт
\[
 \boxed{\|R_T\|_1\le
  \int_T^\infty w_m(t)\frac{\log(t/(2\pi))}{2\pi}\,dt
  +2w_m(T)R_*(T)+\int_T^\infty w_m(t)R_*'(t)\,dt.}       \tag{6.2}
\]
Это не предполагает знака R_T. Два граничных платежа возникают соответственно из -w(T)(N(T-)-M(T)) и интегрирования |w'| R_*.

В m300 отношение Rosser R(t)/log t убывает для t>=T, а в T оно <0.539. Поэтому можно взять **R_*(t)=(11/20)log t**. По (6.2), обозначая два интеграла I и J=integral w(t)/t dt,
\[
 E=I+1.1\log T\,w(T)+.55J <12.5.                       \tag{6.3}
\]
Интервальные результаты:

```text
T                 in [370.17962509312907, 370.17962509312909]
I                 in [11.74924099800072, 11.74924099800073]
J                 in [0.02403850930194, 0.02403850930196]
w(T)              in [0.09840433433268, 0.09840433433269]
E                 in [12.40262047483016, 12.40262047483017]
M(T)+.55 log T     in [185.35961182594357,185.35961182594358]
```

Отсюда N(T)<=185 без использования фактического census 183. Старый worst-mode envelope около 1843.93 здесь действительно бесполезен; это было свойство его грубой цены, а не настоящего хвоста. Новый конечный envelope не заменяет cofinal density argument: асимптотическая и конечная задачи оплачены разными допустимыми оценками.

### 6.1. Без списка нулей: gamma_* = 5

**[FINITE_CELL | PAPER.]** Из стандартного theta–Mellin представления
\[
 \xi(s)=\tfrac12+\frac{s(s-1)}4\int_1^\infty
 (\Theta(x)-1)(x^{s/2}+x^{(1-s)/2})\frac{dx}{x}
\]
на прямоугольнике 0<=Re s<=1, |Im s|<=5 имеем |s(s-1)|<=26 и
\(
 \Theta(x)-1\le2e^{-\pi x}/(1-e^{-3\pi}).
\)
Поэтому
\[
 |\xi(s)-1/2|\le\frac{26e^{-\pi}}{\pi(1-e^{-3\pi})}
 <0.358<1/2.
\]
Нулей в этом прямоугольнике нет. Значит, **sigma=log(300)+1/5** — доказанный sampling cap, без первой ординаты из таблицы.

### 6.2. Конечный перенос с явными числами

**[FINITE_CELL | PAPER; вычислительная реализация MP_IV, не ARB_INTERVAL.]** Для интервалов a>=a_-, q=||A||²_F<=q_+, E>=||R_T||_1 и N<=N_+ используем унаследованную точную формулу
\[
 F_-=4a_-/\sigma-4E/\sigma-(\sqrt{q_+}/\sigma+E/\sigma)^2,
\]
\[
 s_1\ge\max(0,\lceil F_--2N_+\rceil),\qquad
 N_d\ge\max(0,\lceil(F_--N_+)/2\rceil).                  \tag{6.4}
\]
Независимый от исходных массивов пересчёт из (1.2), (2.1), (2.2) дал

```text
tr A       in [895.9964353161231271713828631355508,
               895.9964353161231271713828631355526]
||A||²_F   in [5479.9598641188123929632168652553415,
               5479.9598641188123929632168652553566]
```

Берём намеренно грубые рациональные входы a_-=895.9, q_+=5481, E=12.5, N_+=185. Тогда
\[
 F_->383.69377706,\quad F_--370>13.69377706,
\quad(F_--185)/2>99.34688853.
\]
Итак,
\[
 \boxed{s_1(T_{300})\ge14,\quad N_d(T_{300})\ge100.}       \tag{6.5}
\]
Соответствующие безопасные доли — не меньше 14/185 и 100/185. Это не неоплаченные 0.49 и 0.75 из DIAG, не утверждение, что все 183 диагностических нуля на линии, и не перенос конечного m на бесконечность.

**Уровень проверки.** (6.5) — PAPER-вывод с воспроизводимой интервальной реализацией `mpmath.iv`. Аналитические хвосты, специальные функции и положительные ряды ограничены явно в приложении. Arb установить не удалось из-за DNS-недоступности PyPI; Arb/Lean не запускались. Независимый Arb replay и независимый аналитический аудит остаются gate, прежде чем повышать статус в репозитории. Ни увеличение точности, ни совпадение с Codex-числами не подменяют этот gate.

## 7. Дискриминаторы и сильнейшая атака

**[ABSTRACT | PAPER.]** Самая опасная ошибка была бы посчитать (3.4) и забыть leakage либо просто разделить полный trace пополам. Оба члена явно оплачены в (3.1). Вторая опасность — применить zeta-tail/census к другому источнику. Это запрещено контрактом (6.1)–(6.4), а не последующим clipping результата к 1.

**Двойной нулевой атом.** Для M=2uu*, ||u||=1, N=2 получаем Phi=4. Формула даёт s1>=0, Nd>=1: кратный нуль не превращается в два простых. Для одного простого атома M=uu* score равен 3 и N=1, то есть обе границы равны 1.

**Внелинейный блок.** Для допустимого bad-block с собственными значениями x>=0 и -y<=0,
\(
 4x-x^2-4y-y^2\le4.
\)
Одна верхняя пара имеет N>=2, поэтому её одинокий simple lower bound <=0. В пределе y=0 этот же предел сохраняется: нуль-согласованность не выдаётся за отсутствие bad-block. DISCRIMINATOR — отрицательная инерция полного source-matched head или точная дивизорная проверка, не два момента.

**DH.** Его Gamma, коэффициенты, полоса и счёт иные. Ни PNT-диагональ (4.1), ни (0.2), ни zeta-density tail к DH не импортируются. Формула (6.4) универсальна только после оплаты его собственной полосы, density/census и sampling cap. Число 0.36 остаётся неоплаченным DIAG-score, а не новым DH-сертификатом. Новый DH-census здесь не запускался.

**Подсадка.** Фиксированный квартет с |beta-1/2|=a<1/2 меняет source-form на конечную сумму evaluation-блоков нормы O(m^a), а N — на O(1). Его квадрат и смешанный с A вклад — o(mL²). Поэтому тот же ведущий предел совместим с подсадкой: доля её плохих нулей стремится к нулю. В конечной ячейке все planted-blocks оплачиваются в head/tail по фактическим высотам; пересчитанный zeta-бюджет не объявляется plant-бюджетом.

**F_a=xi(s+a)xi(s-a).** Унаследованный density discriminator сохраняется: положительная доля сдвинутых нулей находится на фиксированном отступе от 1/2, несовместимом с использованной zeta-density. Меняются также Gamma, полюсы и арифметические веса (множитель 2cosh(a log n)). Следовательно, supplier (4.1) с коэффициентом 1/3 отсутствует. Нельзя приписать этому миру (5.2).

**Удвоенный арифметический атом n=2.** Фиксированная добавка к B не меняет ведущий mL²-момент. Поэтому именно moment asymptotics не различает такую подделку. Но она меняет полную исходную Weil-форму: старый нулевой divisor и старый tail нельзя оставить автоматически. DISCRIMINATOR — точное равенство новой формы её полной нулевой сумме с Gamma/pole terms. Пока matching completion/divisor не предъявлены, никакой zero-count bound в этом мире не выдаётся. Это сознательный fail-closed, а не скрытая универсальная гарантия из PNT.

## 8. Прогнозы, границы KILL и dependency contract

**[COFINAL_FAMILY / FINITE_CELL | PAPER; мета-учёт, не новые численные теоремы.]**

| Прогноз до ответа | Судьба |
|---|---|
| Mythos W1: t->1 с постоянной c1/L, c1<0 | t->1 подтверждён; буквальная форма постоянной c1 опровергнута (1.4). Объяснение 0.85 дано без fit. |
| W2: внедиагональ o(sigma²N) безусловно | Подтверждён PAPER: (3.3)–(3.6). |
| W3: v∞ in [1,4/3] | Подтверждён на правом конце: ровно 4/3, не путь к доле 1. |
| W4: доля строго выше 0.6725 | Для данного Phi-score опровергнут: предел нижней границы 2/3. Другие усиления не исключены. |
| W5: положительная сертифицируемая доля при m300 | PAPER + MP_IV gates положительны: 14 и 100. Arb/Lean gate ещё не выполнен. |

Собственные прогнозы, зарегистрированные в живом ходе до тестов: отсутствие постоянной c1; v∞=4/3; Hilbert-обход вместо HL; неэффективность **старого** конечного envelope. Все подтверждены в указанных границах. После обнаружения нового модового envelope, до интервального теста зарегистрированы E<12.5 и положительная конечная граница: оба подтверждены. Это не ретроактивная замена прогноза о старом envelope. Первый запуск кода остановился на отсутствии `iv.sinh`; замена на точные exp-формулы исправила API-вызов, не математическое утверждение. Прогоны 45 и 65 dps — проверка реализации/точности, не два независимых аудита.

```yaml
DEPENDENCY_CONTRACT:
  DOWNSTREAM_CONSUMER: RANK_TRACE_ZERO_PROPORTION_IN_LITERAL_CCM
  ACTUAL_CONSUMER_REQUIREMENT: "limsup v_m<=4/3, t_m->1, paid head-tail transfer"
  ORIGINAL_REQUESTED_OBJECT: "fixed c1,d1 expansions and an alpha>1 correlation verdict"
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES: "(3.1)+(4.1)+(4.2)+(4.3) => v_m->4/3"
  FAILURE_TYPE: INCOMPATIBILITY_FOR_FIXED_COEFFICIENT_SHAPES_ONLY
  EPISTEMIC_STATUS: PAPER_RESULT_PENDING_INDEPENDENT_AUDIT
  NOVELTY_AXIS: "literal even carrier: cyclic Hilbert + reflection/leakage budgets; mode-resolved finite tail"
SCOPED_KILLS:
  - KILL_SCOPE: THEOREM_SHAPE
    TARGET: FIXED_c1_OVER_L
    EVIDENCE: "(1.4): L(t-1)=-c log L+O(1) -> -infinity"
    EVIDENCE_KIND: PROVED_ASYMPTOTIC_INCOMPATIBILITY
  - KILL_SCOPE: THEOREM_SHAPE
    TARGET: FIXED_d1_OVER_L
    EVIDENCE: "(5.5): L(v-4/3)=-log L+O(1) -> -infinity"
    EVIDENCE_KIND: PROVED_ASYMPTOTIC_INCOMPATIBILITY
KILL_ROUTE_FAMILY: false
OPTIONAL_JUMP_TARGET:
  NAME: SUBLEADING_ETA_LIMIT
  MINIMAL_MISSING_IDENTITY: "eta_m=eta_infinity+o(1) for eta_m defined in (5.3)"
  REQUIRED_FOR_MAIN_PROPORTION: false
  STATUS: RESEARCH_DEBT
  REOPEN_TRIGGER: "a joint estimate strictly sharper than O(mL), or a source-locked limit identity"
```

Направление KILL корректно: для любого предложенного фиксированного коэффициента верхняя оценка соответствующего масштабированного остатка имеет вид -c log L+C (либо -log L+C), отрицательна при достаточно большом L и не может быть O(1/L). Отказ достаточного условия нигде не назван отрицанием consumer.

Две кандидатные перепараметризации **только для необязательного eta-limit**: (i) csc/Hilbert quadratic form префиксов вместе с точной leakage, высокая kill-power при умеренной PAPER-цене — проверяет совместное сокращение, не отдельные пары; (ii) граничный оператор обрезанных сдвигов в координате y=L-log n, средняя цена, высокая kill-power для предложенной константы — выделяет короткое перекрытие и проверяет, является ли O(mL) артефактом Minkowski. Ни один не назначен новым обязательным supplier. Три bridge-попытки в этом ответе уже конкретны: точное Fourier/shift-представление (3.4), Gamma rank-one identity (2.1), Stieltjes tail certificate (6.2).

## 9. Один следующий target для Codex

**[FINITE_CELL | PAPER; verification handoff.]** Независимо проверить этот PAPER-вывод, затем воспроизвести **те же восемь конечных gates** из приложения в Arb/python-flint, без чтения списка нулей и без изменения source matrix. Приоритет аудита: (3.4), круговой зазор (3.5), parity term, leakage; затем (2.1) и коэффициент 8 в (6.1).

Успех: независимое подтверждение (3.1), (3.2), (4.4) и m300 gates. Неуспех: `CCM_PHI_AUDIT_COUNTEREXAMPLE` с точным равенством/индексом/интервалом; состояние Route B не повышать автоматически. Отсутствие Arb само по себе не является математическим опровержением.

Для точного replay приложенного кода (это **не** подмена независимого Arb gate):

```bash
# WORKDIR: <repo root>. Replace <repo root> by the directory containing docs/routeB_bus.
# Extract the one fenced Python block from this verdict into /tmp/ccm_phi_check.py.
uv run --with mpmath==1.3.0 /tmp/ccm_phi_check.py --m 300 --dps 65 --json /tmp/ccm_phi_m300.json
```

Новых Lean-файлов нет; axiom profile неприменим. Результат `lake` не заявляется. Записывается только указанный в YAML Markdown; commit SHA и проверенный blob возвращаются в сообщении доставки. Route-state файлы не изменяются.

**Meta closeout.** Закрыт ведущий второй момент для всей cofinal семьи, а не одна ячейка. Убиты две неверные формы разложения, не Route B. Запрещён следующий повтор: выдавать 2-v вместо 4t-v-2 на конечном m либо платить все моды крайним знаменателем. Основной consumer больше не ждёт eta-limit. Самый дешёвый следующий меняющий решение тест — независимая проверка четырёх геометрических переходов в Лемме 2, затем Arb replay конечных gates.

## Приложение A. Аналитические остатки для воспроизводимого интервала

**[FINITE_CELL | PAPER.]** Следующий код не интегрирует Gamma численной квадратурой. Для \(z=1/4+i\omega/2\) вычисляет digamma и trigamma после сдвига на 32 через Euler–Maclaurin с K=12. Если Z=z+32,
\[
 \psi(Z)=\log Z-\frac1{2Z}-\sum_{k=1}^{K}\frac{B_{2k}}{2kZ^{2k}}+r,
 \quad |r|\le\frac{|B_{2K}|}{2K(\Re Z)^{2K}},
\]
\[
 \psi'(Z)=\frac1Z+\frac1{2Z^2}+\sum_{k=1}^{K}\frac{B_{2k}}{Z^{2k+1}}+r_1,
 \quad |r_1|\le\frac{|B_{2K}|}{(\Re Z)^{2K+1}}.
\]
Эти bounds следуют из интегрального остатка с периодическим B_2K и \(|B_{2K}(x)|\le|B_{2K}|\). Реальная и мнимая части расширяются независимо на соответствующий радиус. Рекуррентные сдвиги возвращают исходный z.

Для (2.1) используется
\[
 f(w)=\sum_r\frac1{a_r^2+w^2}=\frac{\Im\psi(1/4+iw/2)}{2w},
\quad f(0)=\psi'(1/4)/4,
\]
\[
 \sum_r\frac{a_r^2}{(a_r^2+w^2)^2}
 =\frac{\Im\psi(1/4+iw/2)}{4w}+\frac18\Re\psi'(1/4+iw/2).
\]
Смешанный индекс получается разделённой разностью w² f(w). Экспоненциальная часть суммы обрывается при r=6; её остаток по модулю <=
\(
 e^{-(2R+1/2)L}/[(2R+1/2)^2(1-e^{-2L})].
\)

Интегралы I,J в (6.3) считаются положительными рядами. Положим x_j=(omega_j/T)², r=kappa^-2, C=8cosh²(L/4)/L, ell=log(T/(2pi)), b0=1/(4T²). Тогда
\[
 I=\frac C{2\pi T}\sum_jd_j^2\sum_{k\ge0}(k+1)x_j^k
 \left[\frac{\ell}{2k+1}+\frac1{(2k+1)^2}
 +b_0\left(\frac{\ell}{2k+3}+\frac1{(2k+3)^2}\right)\right],
\]
\[
 J=\frac C{T^2}\sum_jd_j^2\sum_{k\ge0}(k+1)x_j^k
 \left[\frac1{2k+2}+\frac{b_0}{2k+4}\right].
\]
После K=256 остаток геометрической массы точно
\(
 G_K=r^K[(K+1)/(1-r)+r/(1-r)^2].
\)
Для внутренних сумм I,J достаточно верхних bounds соответственно d(ell+1)(1+b0)G_K и d(1+b0)G_K. Это положительные upper envelopes, не оценка ошибки по разности двух точностей.

## Приложение B. Полный replay-код

```python
#!/usr/bin/env python3
"""Literal even CCM source moments and whole-zero-tail interval enclosure.
Uses mpmath.iv (not Arb/Lean). No zeta-zero list and no RH input.
All source formulas and analytic remainder bounds are in the verdict.
"""
from fractions import Fraction
import argparse, json, time, math
import mpmath as mp


def bernoulli(n):
    a=[Fraction(0)]*(n+1)
    for m in range(n+1):
        a[m]=Fraction(1,m+1)
        for j in range(m,0,-1):
            a[j-1]=j*(a[j-1]-a[j])
    return a[0]


def run(m=300,dps=45):
    iv=mp.iv; iv.dps=dps
    start=time.monotonic()
    def rat(q): return iv.mpf(q.numerator)/q.denominator
    B=[rat(bernoulli(2*k)) for k in range(1,13)]
    sym=iv.mpf([-1,1])
    def psi_pair(z):
        # Euler--Maclaurin at Re(z+32)>=32.25; explicit periodic-Bernoulli remainders.
        M=32; K=12; Z=z+M
        p=iv.log(Z)-1/(2*Z)
        t=1/Z+1/(2*Z*Z)
        for k,b in enumerate(B,1):
            p-=b/(2*k*Z**(2*k))
            t+=b/Z**(2*k+1)
        r=abs(B[-1])/(2*K*(Z.real)**(2*K))
        r1=abs(B[-1])/(Z.real)**(2*K+1)
        p+=iv.mpc(sym*r,sym*r)
        t+=iv.mpc(sym*r1,sym*r1)
        for n in range(M):
            p-=1/(z+n)
            t+=1/(z+n)**2
        return p,t
    L=iv.log(m); pi=iv.pi
    omega=[2*pi*j/L for j in range(m+1)]
    om2=[w*w for w in omega]
    d=[iv.mpf(1)]+[iv.sqrt(2)]*m
    logpi=iv.log(pi)
    q=[]; f=[]; sd=[]
    for j,w in enumerate(omega):
        ps,pt=psi_pair(iv.mpc(iv.mpf(1)/4,w/2))
        q.append(ps.real-logpi)
        if j:
            f.append(ps.imag/(2*w))
            sd.append(ps.imag/(4*w)+pt.real/8)
        else:
            f.append(pt.real/4);sd.append(pt.real/4)
    sieve=[True]*(m+1);sieve[0]=sieve[1]=False
    for p in range(2,math.isqrt(m)+1):
        if sieve[p]:
            for n in range(p*p,m+1,p):sieve[n]=False
    atoms={}
    for p in range(2,m+1):
        if sieve[p]:
            n=p; lp=iv.log(p)
            while n<=m:
                atoms[n]=lp
                n*=p
    atomlist=[(n,lp/iv.sqrt(n),iv.log(n)) for n,lp in sorted(atoms.items()) if n<m]
    S=[]; V=[]
    for j,w in enumerate(omega):
        s=iv.mpf(0);v=iv.mpf(0)
        for n,c,u in atomlist:
            s+=c*iv.sin(w*u)
            v+=c*(1-u/L)*iv.cos(w*u)
        S.append(s);V.append(v)
    pole=[iv.sqrt(2)*dj*((iv.exp(L/4)-iv.exp(-L/4))/2)/(iv.sqrt(L)*(ww+iv.mpf(1)/4)) for dj,ww in zip(d,om2)]
    R=6
    aa=[iv.mpf(2*r)+iv.mpf(1)/2 for r in range(R)]
    expweights=[a*a*iv.exp(-a*L) for a in aa]
    inv=[[1/(a*a+ww) for ww in om2] for a in aa]
    aaR=iv.mpf(2*R)+iv.mpf(1)/2
    etail=iv.exp(-aaR*L)/(aaR**2*(1-iv.exp(-2*L)))
    trace=iv.mpf(0);frob=iv.mpf(0)
    decomp={k:iv.mpf(0) for k in ["H2","P2","B2","HP","HB","PB"]}
    for j in range(m+1):
        for k in range(j+1):
            if j==k:
                sjk=sd[j]
                bjk=2*V[j] if j==0 else 2*V[j]-2*S[j]/(L*omega[j])
            else:
                sjk=(om2[j]*f[j]-om2[k]*f[k])/(om2[j]-om2[k])
                bjk=-2*d[j]*d[k]/L*(omega[j]*S[j]-omega[k]*S[k])/(om2[j]-om2[k])
            ejk=sum((ew*ivv[j]*ivv[k] for ew,ivv in zip(expweights,inv)),iv.mpf(0))+iv.mpf([0,1])*etail
            hjk=2*d[j]*d[k]/L*(sjk-ejk)+(q[j] if j==k else 0)
            a=hjk+pole[j]*pole[k]-bjk
            if j==k:trace+=a
            weight=(1 if j==k else 2)
            frob+=weight*a*a
            pp=pole[j]*pole[k]
            for key,value in [("H2",hjk*hjk),("P2",pp*pp),("B2",bjk*bjk),("HP",2*hjk*pp),("HB",-2*hjk*bjk),("PB",-2*pp*bjk)]:
                decomp[key]+=weight*value
        if j%50==0 or j==m:
            elapsed=time.monotonic()-start
            eta=elapsed*(m-j)/(j+1)
            print(f'matrix [{"#"*int(30*(j+1)/(m+1)):<30}] {j+1}/{m+1} ETA {eta:.1f}s',flush=True)
    h=1+iv.log(L);kap=1+h/(4*L);T=kap*2*pi*m/L
    C=8*((iv.exp(L/4)+iv.exp(-L/4))/2)**2/L; b=iv.mpf(1)/(4*T*T)
    xs=[ww/(T*T) for ww in om2]
    ell=iv.log(T/(2*pi));powers=[iv.mpf(1)]*(m+1)
    SI=iv.mpf(0);SJ=iv.mpf(0);K=256
    for k in range(K):
        mass=powers[0]+2*sum(powers[1:],iv.mpf(0))
        SI+=(k+1)*mass*(ell/(2*k+1)+1/iv.mpf(2*k+1)**2+b*(ell/(2*k+3)+1/iv.mpf(2*k+3)**2))
        SJ+=(k+1)*mass*(1/iv.mpf(2*k+2)+b/iv.mpf(2*k+4))
        powers=[p*x for p,x in zip(powers,xs)]
    r=1/(kap*kap)
    gtail=r**K*((K+1)/(1-r)+r/(1-r)**2)
    SI+=iv.mpf([0,1])*(2*m+1)*(ell+1)*(1+b)*gtail
    SJ+=iv.mpf([0,1])*(2*m+1)*(1+b)*gtail
    I=C/(2*pi*T)*SI;J=C/(T*T)*SJ
    wT=C/(T*T)*(1+b)*sum((dj*dj/(1-x)**2 for dj,x in zip(d,xs)),iv.mpf(0))
    err_coeff=iv.mpf(11)/20
    E=I+2*err_coeff*iv.log(T)*wT+err_coeff*J
    M=T/(2*pi)*(iv.log(T/(2*pi))-1)+iv.mpf(7)/8
    Nup_real=M+err_coeff*iv.log(T)
    count_ratio=iv.mpf(137)/1000+iv.mpf(443)/1000*iv.log(iv.log(T))/iv.log(T)+iv.mpf(1588)/1000/iv.log(T)
    sig=L+iv.mpf(1)/5
    # Use fixed, deliberately loose rational gates, not diagnostic midpoints.
    a_low=iv.mpf(8959)/10; q_high=iv.mpf(5481); Ehigh=iv.mpf(25)/2; Nup=185
    Flo=4*a_low/sig-4*Ehigh/sig-(iv.sqrt(q_high)/sig+Ehigh/sig)**2
    zerofree_error=26*iv.exp(-pi)/(pi*(1-iv.exp(-3*pi)))
    result={
      'm':m,'dps':dps,'backend':'mpmath.iv; NOT_ARB; NOT_LEAN',
      'trace':str(trace),'frob_sq':str(frob),'T':str(T),'I':str(I),'J':str(J),'wT':str(wT),
      'tail_E':str(E),'N_upper_real':str(Nup_real),'Rosser_R_over_log':str(count_ratio),
      'zero_free_gamma5_error':str(zerofree_error),'safe_score_lower':str(Flo),
      'simple_count_real_lower':str(Flo-2*Nup),'distinct_count_real_lower':str((Flo-Nup)/2),
      'gates':{
        'trace_ge_895_9':bool(trace>a_low),'frob_sq_le_5481':bool(frob<q_high),
        'tail_le_12_5':bool(E<Ehigh),'N_le_185':bool(Nup_real<186),
        'R_le_0_55_log':bool(count_ratio<err_coeff),'zero_free_gamma5':bool(zerofree_error<iv.mpf(1)/2),
        'simple_count_ge_14':bool(Flo-2*Nup>13),'distinct_count_ge_100':bool((Flo-Nup)/2>99)},
      'decomposition':{k:str(v) for k,v in decomp.items()},
      'mpmath_version':mp.__version__,'seconds':time.monotonic()-start}
    print(json.dumps(result,ensure_ascii=False,indent=2))
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--m',type=int,default=300);p.add_argument('--dps',type=int,default=45);p.add_argument('--json')
    args=p.parse_args();result=run(args.m,args.dps)
    if args.json:
        with open(args.json,'w') as f:json.dump(result,f,indent=2)
    if args.m==300 and not all(result['gates'].values()):raise SystemExit('FAILED GATE')

```

## Приложение C. Итог выполненных проверок

**[FINITE_CELL | PAPER; MP_IV arithmetic, not ARB_INTERVAL.]** На 45 и 65 dps все восемь gates истинны. На 65 dps source-разложение воспроизведено как

```text
H2   = 2954.816214459969943...
P2   =  527.462671577506660...
B2   = 2936.598450855467828...
2HP  = -162.725928513365243...
-2HB =  114.690915434211033...
-2PB = -890.882459694977829...
```

Это согласуется с pinned Codex decomposition; B2 включает и диагональ, и внедиагональ. Никаких eigensystems, новых нулевых census или предположения PSD не использовано. Установка python-flint не состоялась; эти запуски не называются Arb-сертификатами.

```yaml
iteration:
  target: LEADING_NORMALIZED_SECOND_MOMENT_OF_LITERAL_CCM
  status: PROGRESS
  failed_strategy: WORST_MODE_FINITE_TAIL_BUDGET
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: EXACT_EVEN_PROJECTION_AND_ALL_BOUNDARY_PAYMENTS
  forbidden_future_move: DROP_PARITY_LEAKAGE_OR_USE_RAW_2_MINUS_v_AT_FINITE_m
  next_decisive_test: INDEPENDENT_LEMMA_2_AUDIT_THEN_ARB_m300_REPLAY
route_score: 5
RH_claim: NOT_MADE
```
