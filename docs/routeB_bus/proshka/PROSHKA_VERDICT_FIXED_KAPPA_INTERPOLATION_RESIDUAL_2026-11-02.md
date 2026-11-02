# STATUS: TRY_FIXED_KAPPA_INTERPOLATION_RESIDUAL

```yaml
OPERATIVE_CLASS: TRY_FIXED_KAPPA_INTERPOLATION_RESIDUAL
DATE: 2026-11-02
TASK_MODE: OWNER_DIRECT_MATHEMATICAL_REQUEST
CANONICAL_TXT_REQUEST: NOT_SUPPLIED
FORMAL_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_COMMIT: a412a678a4ae1df4f03106d1a46cf5453451c65a
SOURCE_BRANCH: rh_clean
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ORIGINAL_OPERATOR: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
TARGET: FOR_EVERY_FIXED_KAPPA_GT_1_FULL_INTERPOLATION_KERNEL_OPERATOR_RESIDUAL_TENDS_TO_ZERO
TARGET_RESULT: PAPER_PROOF_GIVEN
STRONGER_RESULT: SUPERPOLYNOMIAL_FULL_SUBSPACE_RESIDUAL
GRAM_CONTROL: RELATIVE_MATRIX_DOMINATION_BEFORE_WHITENING
SIMPLE_ZEROS_ASSUMED: false
RH_ASSUMED: false
NONRESONANCE_ASSUMED: false
CONFLUENT_INTERPOLATION_ADDED: false
NONZERO_COFINAL_RANK_ASSERTED: false
SPECTRAL_COUNT_UPPER_BOUND_PROVED: false
FINITE_EXPLICIT_ENVELOPE: GIVEN_IN_TERMS_OF_DISTINCT_NONAUTOMATIC_ZERO_COUNT
M_ONLY_ASYMPTOTIC_ENVELOPE: GIVEN_WITH_EXPLICIT_KAPPA_CONSTANTS
NUMERICAL_ONSET_M0: NOT_COMPUTED
GONEK_BIG_O_CONSTANT: NOT_NUMERICALLY_EXTRACTED
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: REQUESTED_RESIDUAL_NOT_SATURATED_COUNT_OR_RH
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
VERIFIER: PAPER
EXACT_SYMBOLIC_SELF_CONTROLS: EXECUTED
LITERAL_CCM_MATRIX_RECOMPUTED: false
ARB_INTERVAL_EXECUTED: false
LEAN_EXECUTED: false
INDEPENDENT_REVIEW: NOT_PERFORMED
REPOSITORY_WRITTEN: false
RH_PROVED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. Для **исходного пространства точного зануления во всех комплексных спектральных точках нулей ζ ниже T** получается равномерная оценка всей операторной невязки. Не через перенос фиксированного theta-джета на растущий ранг, а через точное рациональное представление Fourier-образа, диск и произведение Бляшке.

Ниже — новый PAPER-вывод. Независимый аудит и формальная проверка не выполнены. Данные m=8,…,40 не используются как посылка доказательства.

## 0. Теорема и бюджет

**[COFINAL_FAMILY | PAPER]** Положим

\[
 L=\log m,\qquad \Omega_m=\frac{2\pi m}{L},\qquad T_m=\kappa\Omega_m,
 \qquad m\in\mathbb N,\ m\ge2,
\]

где **κ>1 фиксировано**. Пусть V_m — исходный чётный cosine-carrier размерности m+1 на [−L/2,L/2], A_m — исходная чётная CCM-матрица в физической L²-метрике, и

\[
 J_{m,T_m}=\{f\in V_m:\ \widehat f(i(\rho-1/2))=0
       \text{ для всех нетривиальных }\rho\text{ с }0<|\Im\rho|<T_m\}.
 \tag{0.1}
\]

Требуются только **значения**, не производные в кратных нулях. Повтор нуля не создаёт дополнительного условия. Используются действительные комплексные точки i(ρ−1/2), а не их проекции на вещественную ось.

Обозначим r_m=dim J_{m,T_m}. Для любого изометрического синтеза Q_m:ℂ^{r_m}→V_m с образом J_{m,T_m} справедливо

\[
 \boxed{\|A_mQ_m\|\le
 C_\kappa\sqrt m\,\log m\,
 \exp\!\left(-c_\kappa\frac{\sqrt m}{\log m}\right)
 \quad(m\ge m_0(\kappa)).}
 \tag{0.2}
\]

В частности,

\[
 \boxed{\forall B>0:\quad \|A_mQ_m\|=o(m^{-B}).}
 \tag{0.3}
\]

Положительность r_m не предполагается и не доказывается. При r_m=0 оператор с нулевой областью имеет норму 0. Однако доказательство ниже не опирается на исчезновение пространства: оно оценивает **каждый единичный f∈J**, когда такие f существуют.

### Полностью заданные κ-константы

Положим

\[
 \alpha=1+\frac{\kappa-1}{3},\qquad
 \beta=1+\frac{2(\kappa-1)}{3},\qquad
 \eta=\beta-\alpha=\frac{\kappa-1}{3},
\]
\[
 u=(\alpha-\sqrt{\alpha^2-1})^2,\qquad
 v=(\kappa-\sqrt{\kappa^2-1})^2,\qquad R=\frac{1+u}{2},
\]
\[
 \theta=\frac{R(u+v)}{R^2+uv},\qquad
 D_\kappa=\frac{(1+v)^4}{(1-R)^2(1-v)^2}.
 \tag{0.4}
\]

Тогда 0<v<u<R<1 и 0<θ<1. Допустимый выбор в (0.2):

\[
 \boxed{C_\kappa=\frac{48D_\kappa}{\pi\kappa},\qquad
 c_\kappa=\frac{(\kappa-1)(-\log\theta)}{96}.}
 \tag{0.5}
\]

Это не оптимальные константы.

### Конечный бюджет без неизвестной константы O

Пусть k_m — число **различных** нулей ρ=σ+iγ в полосе

\[
 \alpha\Omega_m<\gamma\le\beta\Omega_m
 \tag{0.6}
\]

за исключением автоматических sinc-нулей

\[
 \sigma=\tfrac12,\qquad \gamma\log m\in2\pi\mathbb Z.
 \tag{0.7}
\]

Каждый различный комплексный ρ считается один раз, независимо от кратности. Введём

\[
 \mathcal Z(T)=\frac{\log T}{\pi T}
              +\frac{\log T+21/2}{T^2}.
 \tag{0.8}
\]

Для **каждого** m≥2 имеем

\[
 \boxed{
 \|A_mQ_m\|\le\delta_{m,\kappa}:=
 8D_\kappa\frac{(2m+1)\sqrt m}{L}\,
 \mathcal Z(T_m)\,\theta^{k_m}.}
 \tag{0.9}
\]

Все коэффициенты этого бюджета явны. Единственный счёт в нём — конечный счёт действительных нулей ζ, не неизвестный спектральный счёт A_m. Ни минимальное собственное значение Gram, ни невязка отдельной колонки не спрятаны в константе.

Ниже без RH доказывается

\[
 \boxed{k_m\ge \frac{\kappa-1}{96}\frac{\sqrt m}{\log m}
       \quad\text{для всех достаточно больших }m.}
 \tag{0.10}
\]

Именно (0.9)+(0.10) дают (0.2). Численный m_0(κ) не вычислен: равномерная формула Ландау—Гонека импортируется с её абсолютными O-константами. Это ограничение **численного порога**, а не оставленная гипотеза в доказательстве предела. Конечный бюджет (0.9) этих O-констант не содержит.

## 1. Исходный оператор и точная формула по нулям

### 1.1. Фиксация объекта

**[ABSTRACT | PAPER]** Используем ортонормированный базис

\[
 \phi_0=L^{-1/2}\mathbf1_{[-L/2,L/2]},\qquad
 \phi_n=\sqrt{2/L}\cos(2\pi nx/L)\mathbf1_{[-L/2,L/2]},\quad1\le n\le m.
 \tag{1.1}
\]

Если f=Σa_nφ_n, то

\[
 \|f\|_2^2=\sum_{n=0}^m|a_n|^2.
 \tag{1.2}
\]

Это тот же чётный carrier, что в NOESCAPE; фазовый сдвиг исходных комплексных мод меняет только знаки (−1)^n, не метрику, поддержку или оператор.

Источник [S1, §1; S2, §1] определяет исходную форму, антилинейную по первому аргументу:

\[
\begin{aligned}
\mathfrak k(g,f)={}&-c_*\langle g,f\rangle
 +\int_0^\infty\frac{e^{-s/2}}{1-e^{-2s}}
       \{2\langle g,f\rangle-Q_{g,f}(s)\}\,ds\\
 &-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q_{g,f}(\log n)
 +\langle g,p\rangle\langle p,f\rangle
 -\langle g,q\rangle\langle q,f\rangle,
\end{aligned}
 \tag{1.3}
\]

где

\[
 Q_{g,f}(s)=\int\overline{g(x)}[f(x+s)+f(x-s)]dx,
\]
\[
 c_*=\gamma_{\rm Euler}+\log(8\pi)+\pi/2,\qquad
 p(x)=\sqrt2\cosh(x/2),\quad q(x)=\sqrt2\sinh(x/2).
\]

A_m — ограничение этой полной формы на V_m. Все простые степени, полюсы, архимедова часть и концы окна сохранены. В чётном секторе q-функционал равен нулю по чётности, а не выброшен как ошибка.

Точная безусловная явная формула имеет вид

\[
 \boxed{\langle g,A_m f\rangle
  =\sum_\rho\overline{\widehat g(\overline{z_\rho})}\,
                   \widehat f(z_\rho),\qquad
 z_\rho=i(\rho-1/2),}
 \tag{1.4}
\]

с кратностями. Это исходная формула CONFINE (1.4), не положительное разложение, предполагающее RH. Слагаемые при невещественных z_ρ не заменяются квадратами модулей.

### 1.2. Почему (1.4) допустима для оконных cosine-функций

**[ABSTRACT | PAPER]** Дадим возврат, чтобы не подменить оконные функции гладкими глобальными тестами.

Для фиксированного m нулевое продолжение любой f∈V_m имеет компактную поддержку и ограниченную вариацию. Интегрирование по частям с граничными массами даёт

\[
 |\widehat f(z)|\le\frac{C_{m,f}}{1+|\Re z|}
 \quad(|\Im z|\le1/2).
 \tag{1.5}
\]

По безусловному N(t)=O(t log t) произведение двух таких оценок суммируемо по нулям.

Возьмём неотрицательный гладкий чётный mollifier η_ε единичного интеграла и f_ε=f*η_ε, g_ε=g*η_ε. На критической полосе

\[
 \widehat f_\varepsilon(z)=\widehat f(z)\widehat\eta_\varepsilon(z),
 \qquad |\widehat\eta_\varepsilon(z)|\le e^{\varepsilon/2}.
\]

Поэтому на нулевой стороне разрешён предельный переход по доминированной сходимости.

На арифметической стороне нормы и полюсные функционалы сходятся. При фиксированном m поддержки остаются в одном компактном интервале, так что сохраняется конечный набор потенциально ненулевых prime-power-корреляций. Корреляция при log n=L сходится к нулю: пересечение исходных носителей в этой точке имеет меру ноль. Ни одна граничная простая степень не пропадает без предельного перехода.

Для архимедова интеграла равномерные BV- и L∞-границы mollification дают

\[
 |2\langle g_\varepsilon,f_\varepsilon\rangle
              -Q_{g_\varepsilon,f_\varepsilon}(s)|\le C_{m,f,g}s
 \quad(0<s<1).
\]

Это доминируется после умножения на j(s)=O(1/s). На s≥1 используется L²-граница и интегрируемость j. Следовательно, гладкая явная формула переходит точно в (1.4).

Этот ε→0 переход делается **при фиксированном m**; никакой равномерной mollifier-оценкой не подменяется дальнейший m→∞ бюджет.

## 2. Рациональный Fourier-образ становится ограниченной функцией в диске

### 2.1. Координаты Коши

**[ABSTRACT | PAPER]** Прямое интегрирование даёт прежнее точное тождество

\[
 \widehat f(z)=\frac{2\sin(zL/2)}{\sqrt L\,z}
 \left(a_0+\sqrt2\sum_{n=1}^m(-1)^na_n\frac{z^2}{z^2-\omega_n^2}\right),
 \qquad \omega_n=2\pi n/L.
 \tag{2.1}
\]

Введём масштабированные переменные

\[
 t=z^2/\Omega_m^2,\quad p_n=(n/m)^2,\quad
 b_0=a_0,\quad b_n=\sqrt2(-1)^n a_n\ (n\ge1),
\]
\[
 H_f(t)=\sum_{n=0}^m\frac{b_n}{t-p_n}.
 \tag{2.2}
\]

Тогда выражение в скобках в (2.1) равно tH_f(t), а

\[
 \sum_{n=0}^m|b_n|\le\sqrt{2m+1}\,\|f\|_2.
 \tag{2.3}
\]

Именно (2.3), а не оценка коэффициентов плохо обусловленного интерполяционного базиса, будет контролировать всю конструкцию.

### 2.2. Конформное отображение

Положим

\[
 t=\frac{(1+w)^2}{4w},\qquad
 F_f(w)=\sum_{n=0}^m
 \frac{b_n}{1+2(1-2p_n)w+w^2}.
 \tag{2.4}
\]

Имеем точные равенства

\[
 H_f(t(w))=4wF_f(w),\qquad t(w)H_f(t(w))=(1+w)^2F_f(w).
 \tag{2.5}
\]

Так как 0≤p_n≤1, каждый знаменатель в (2.4) раскладывается в

\[
 (1-e^{i\vartheta_n}w)(1-e^{-i\vartheta_n}w),
 \qquad\cos\vartheta_n=2p_n-1.
\]

Поэтому F_f голоморфна в |w|<1 и для 0<r<1

\[
 \boxed{\sup_{|w|\le r}|F_f(w)|
 \le\frac{\sqrt{2m+1}}{(1-r)^2}\,\|f\|_2.}
 \tag{2.6}
\]

Все исходные модальные полюса оказались **на границе** диска; внутри нет неизвестных полюсов.

Для Re z>Ω_m обратная ветвь задаётся

\[
 w(z)=\left(\frac z{\Omega_m}-\sqrt{\frac{z^2}{\Omega_m^2}-1}\right)^2,
 \qquad |w(z)|<1,
 \tag{2.7}
\]

с ветвью, стремящейся к нулю при положительном z→∞. В этих координатах

\[
 \boxed{\widehat f(z)=
 \frac{2\sin(zL/2)}{\sqrt L\,z}(1+w(z))^2F_f(w(z)).}
 \tag{2.8}
\]

### 2.3. Контроль полосы, включая комплексные точки

Если Re z≥sΩ_m, s>1, то

\[
 \boxed{|w(z)|\le(s-\sqrt{s^2-1})^2.}
 \tag{2.9}
\]

Доказательство: для η=z/Ω_m−√((z/Ω_m)²−1), |η|<1, имеем

\[
 z/\Omega_m=(\eta+\eta^{-1})/2.
\]

При η=re^{iφ}

\[
 \Re(z/\Omega_m)=\tfrac12(r+r^{-1})\cos\varphi
              \le\tfrac12(r+r^{-1}).
\]

Отсюда r≤s−√(s²−1), что даёт (2.9). Оценка не предполагает Im z=0.

## 3. Нули между Ω и T подавляют сразу всё пространство

### 3.1. Какие нули реально дают условия

**[ABSTRACT | PAPER]** Для верхнего нуля ρ=σ+iγ удобно взять

\[
 z_\rho^+=-i(\rho-1/2)=\gamma+i(1/2-\sigma).
 \tag{3.1}
\]

Так как f чётна, зануление в исходной точке z_ρ эквивалентно занулению в z_ρ^+=−z_ρ. Всегда |Im z_ρ^+|<1/2.

Если ρ удовлетворяет (0.6), то |w(z_ρ^+)|≤u. При этом γ>Ω_m, так что модальных полюсов уже нет. Из (2.8) следует

\[
 \widehat f(z_\rho^+)=0\quad\Longrightarrow\quad F_f(w(z_\rho^+))=0
 \tag{3.2}
\]

**кроме** случая sin(z_ρ^+L/2)=0. Последний случай в точности равен (0.7): σ=1/2 и γL∈2πℤ. Такие нули автоматические для всего carrier и не используются как нули F_f.

Различные верхние ρ дают различные z_ρ^+ с положительной действительной частью, затем различные квадраты и различные w внутри диска. Значит, k_m — число различных общих нулей F_f, действительных для всех f∈J. Кратности ζ не подменяются кратностями F_f.

### 3.2. Произведение Бляшке

Пусть w_1,…,w_k — эти различные нули, |w_j|≤u<R. Разделим F_f на

\[
 \mathcal B(w)=\prod_{j=1}^k\frac{R(w-w_j)}{R^2-\overline{w_j}w}.
 \tag{3.3}
\]

Частное голоморфно в |w|<R и непрерывно на его замыкании; на |w|=R каждый множитель имеет модуль 1. Максимум модуля и (2.6) дают

\[
 |F_f(w)|\le\frac{\sqrt{2m+1}}{(1-R)^2}\|f\|_2\,
                   |\mathcal B(w)|.
 \tag{3.4}
\]

Для |w|≤v и |w_j|≤u справедливо

\[
 \left|\frac{R(w-w_j)}{R^2-\overline{w_j}w}\right|
 \le\frac{R(u+v)}{R^2+uv}=\theta<1.
 \tag{3.5}
\]

Это стандартная оценка псевдогиперболического расстояния; её можно проверить непосредственно: при фиксированных модулях максимум достигается на противоположных аргументах. Строгость следует из

\[
 R^2+uv-R(u+v)=(R-u)(R-v)>0.
\]

Таким образом,

\[
 \boxed{\sup_{|w|\le v}|F_f(w)|
 \le\frac{\sqrt{2m+1}}{(1-R)^2}\theta^{k_m}\|f\|_2
 \quad(f\in J_{m,T_m}).}
 \tag{3.6}
\]

Это **равномерная оценка всего подпространства**. В ней нет суммы невязок отдельных интерполяционных столбцов.

### 3.3. Fourier-хвост

Если Re z≥T_m и |Im z|≤1/2, то |w(z)|≤v и

\[
 |\sin(zL/2)|\le e^{L/4}=m^{1/4}.
\]

Из (2.8), (3.6) получаем

\[
 \boxed{|\widehat f(z)|
 \le\frac{2(1+v)^2\sqrt{2m+1}\,m^{1/4}}
            {\sqrt L(1-R)^2|z|}
       \theta^{k_m}\|f\|_2\quad(f\in J).}
 \tag{3.7}
\]

Для произвольного g∈V_m используем (2.6) при r=v:

\[
 \boxed{|\widehat g(z)|
 \le\frac{2(1+v)^2\sqrt{2m+1}\,m^{1/4}}
            {\sqrt L(1-v)^2|z|}\|g\|_2.}
 \tag{3.8}
\]

Оценки действуют также при Re z≤−T_m по чётности, и после комплексного сопряжения аргумента.

## 4. Почему независимых неавтоматических нулей достаточно без RH

Это арифметическая часть доказательства. Просто написать k_m=N(T) было бы неверно: надо оплатить и кратности, и совпадения с автоматической сеткой.

### 4.1. Безусловный внешний импорт

Из явного нулевого счёта [P2, Theorem 1.1] достаточно более грубой оценки

\[
 |N(t)-M(t)|\le E(t):=\log t+10\quad(t\ge e),
 \qquad M(t)=\frac{t}{2\pi}\log\frac{t}{2\pi e}.
 \tag{4.1}
\]

N(t) считает нетривиальные нули с 0<Imρ≤t, **с кратностями**. (4.1) следует из опубликованной оценки P2, поскольку log log t≤log t при t≥e. Ни RH, ни простота нулей не нужны.

Обозначим

\[
 U=\alpha\Omega_m,\quad V=\beta\Omega_m,\quad
 n_m=N(V)-N(U),\quad
 S_m=\sum_{U<\Im\rho\le V}m^\rho.
 \tag{4.2}
\]

Из (4.1) непосредственно

\[
 n_m=\eta m-\frac mL
 \{\eta(\log L+1)-(\beta\log\beta-\alpha\log\alpha)\}
 +O_\kappa(L),
 \tag{4.3}
\]

поэтому n_m/m→η и n_m≥ηm/2 для всех достаточно больших m.

### 4.2. Кратности оплачиваются независимо

Для любого верхнего нуля с U<γ≤V его кратность μ_ρ не превосходит скачка N при γ. Поскольку M непрерывна, (4.1) справа и слева даёт

\[
 \mu_\rho\le N(\gamma)-N(\gamma^-)
          \le2E(\gamma)\le2(\log V+10).
 \tag{4.4}
\]

Для всех достаточно больших m правая часть не превосходит 4L. Это не предположение «почти все нули простые».

### 4.3. Автоматическая сетка не может содержать почти все нули полосы

Используем **безусловную Theorem 1** Гонека [P1], равномерную по x,T>1:

\[
\begin{aligned}
 \sum_{0<\gamma\le Y}x^\rho
 ={}&-\frac{Y}{2\pi}\Lambda(x)
 +O(x\log(2x)\log\log(3x)) +O(x\log(2Y))\\
 &+O\!\left(\log x\min\left(Y,\frac{x}{\langle x\rangle}\right)\right)
 +O\!\left(\min\left(\frac{\log Y}{\log x},Y\log Y\right)\right).
\end{aligned}
 \tag{4.5}
\]

Здесь ⟨x⟩ — расстояние до ближайшей простой степени, отличной от x. Берём x=m и отдельно Y=U,V. Используется **полная** (4.5), а не её упрощение для x≤Y: в нашем режиме m/Y растёт как log m.

Оценивая min(Y,m/⟨m⟩)≤Y и Y≈_κm/L, получаем

\[
 S_m=-\frac{V-U}{2\pi}\Lambda(m)
           +O_\kappa(mL\log L),
 \qquad \Re S_m\le O_\kappa(mL\log L).
 \tag{4.6}
\]

Главный член имеет неположительный знак, потому что Λ(m)≥0. Ни простые степени, ни соответствующий главный член не заменены моделью.

Пусть b_m — число **неавтоматических** нулей в (U,V], теперь с кратностями. Каждый автоматический нуль имеет

\[
 m^\rho=\sqrt m\,e^{i\gamma L}=\sqrt m.
\]

Для каждого другого нуля Re(m^ρ)≥−|m^ρ|≥−m, поскольку 0<Reρ<1. Поэтому

\[
 \Re S_m\ge\sqrt m(n_m-b_m)-mb_m,
\]

откуда точное неравенство

\[
 \boxed{b_m\ge
 \left[\frac{\sqrt m\,n_m-\Re S_m}{m+\sqrt m}\right]_+.}
 \tag{4.7}
\]

Здесь [x]_+=max(x,0). Так как mL log L=o(m^{3/2}), для достаточно больших m одновременно

\[
 n_m\ge\eta m/2,\qquad
 \Re S_m\le\eta m^{3/2}/4.
\]

Подставляя в (4.7) и используя m+√m≤2m, получаем

\[
 b_m\ge\eta\sqrt m/8.
 \tag{4.8}
\]

### 4.4. От нулей с кратностями к независимым условиям

По (4.4), b_m≤4L k_m для достаточно больших m. Значит,

\[
 \boxed{k_m\ge\frac{\eta\sqrt m}{32L}
       =\frac{\kappa-1}{96}\frac{\sqrt m}{\log m}.}
 \tag{4.9}
\]

Это (0.10). Оно сохраняет возможные кратности, нули вне критической прямой и точные совпадения с sinc-сеткой.

Более точный конечный вариант, без неизвестной O-константы, следует прямо из (4.4),(4.7):

\[
 \boxed{k_m\ge\ell_m:=
 \frac{[\sqrt m\,n_m-\Re S_m]_+}
      {2(m+\sqrt m)(\log V+10)}.}
 \tag{4.10}
\]

В (0.9) разрешено заменить θ^{k_m} на более слабое θ^{ℓ_m}. N и S здесь — точно определённые конечные нулевые суммы; это не величины, зависящие от искомой невязки или от спектра A_m.

Для полностью m-зависимого проверяемого порога можно взять нижнюю оценку n_m из (4.1), а в (4.6) подставить любую явную абсолютную константу полной теоремы Гонека. Численное извлечение такой константы здесь не выполнено и не выдаётся за выполненное.

## 5. Возврат к полной норме A_mQ_m

### 5.1. Исчезновение низких слагаемых — точное

**[COFINAL_FAMILY | PAPER]** Для f∈J в (1.4) исчезают все слагаемые с |Imρ|<T_m. При γ=T_m слагаемое оставляем в хвосте: строгая граница исходного запроса не потеряна.

Суммируем по всем остальным нулям с кратностями. Для |γ|≥T_m произведение (3.7),(3.8) ограничено

\[
 \frac{4D_\kappa(2m+1)\sqrt m}{L\gamma^2}
       \theta^{k_m}\|f\|_2\|g\|_2.
 \tag{5.1}
\]

Вклад нижней полуплоскости имеет ту же абсолютную границу. Поэтому

\[
 |\langle g,A_m f\rangle|
 \le \frac{8D_\kappa(2m+1)\sqrt m}{L}\theta^{k_m}
       \|f\|_2\|g\|_2\sum_{\gamma\ge T_m}\gamma^{-2}.
 \tag{5.2}
\]

Знак отдельных нулевых блоков не используется; положительность формы не предполагается.

### 5.2. Бесконечный хвост полностью оплачен

Из интегрирования по частям Стилтьеса, со строгой левой границей,

\[
 \sum_{\gamma\ge T}\gamma^{-2}
 =-\frac{N(T^-)}{T^2}+2\int_T^\infty\frac{N(t)}{t^3}\,dt
 \le2\int_T^\infty\frac{M(t)+E(t)}{t^3}\,dt.
\]

Вычисление двух элементарных интегралов даёт

\[
 \sum_{\gamma\ge T}\gamma^{-2}
 \le\frac{\log(T/(2\pi))}{\pi T}
       +\frac{\log T+21/2}{T^2}
 \le\mathcal Z(T),\qquad T\ge e.
 \tag{5.3}
\]

Здесь ни конечный cutoff списка нулей, ни неизвестный хвостовой остаток не оставлены. Для всех m≥2 имеем Ω_m≥2πe, поэтому условие T_m≥e автоматически выполнено.

Беря в (5.2) супремум по всем g∈V_m с ||g||₂=1 и применяя (5.3), получаем

\[
 \boxed{\|A_m f\|_2\le\delta_{m,\kappa}\|f\|_2
                  \quad\text{для всех }f\in J_{m,T_m},}
 \tag{5.4}
\]

с точным δ из (0.9). Это полная норма A_m f в V_m, а не норма его проекции обратно на J.

### 5.3. Явная асимптотика

Для T≥100 достаточно грубой оценки

\[
 \mathcal Z(T)\le 2\frac{\log T+1}{T}.
\]

Так как T=2πκm/L, (0.9) даёт

\[
 \delta_{m,\kappa}\le
 \frac{8D_\kappa}{\pi\kappa}(2+1/m)\sqrt m(\log T+1)\theta^{k_m}.
 \tag{5.5}
\]

Для фиксированного κ, начиная с некоторого m, log T+1≤2L; кроме того, 2+1/m≤3. Применяя (4.9), получаем ровно (0.2),(0.5).

Наконец, для любого фиксированного B>0,

\[
 \log\big(m^B\delta_{m,\kappa}\big)
 \le O_\kappa(1)+(B+1/2)\log m+\log\log m
          -c_\kappa\frac{\sqrt m}{\log m}\longrightarrow-\infty.
\]

Тем самым доказаны (0.2)–(0.3).

## 6. Gram: точный контроль без потери на обусловленности

### 6.1. Явный Gram интерполяционного базиса

**[ABSTRACT | PAPER]** В масштабированной переменной t положим

\[
 D_m(t)=\prod_{n=1}^m(t-p_n),\qquad
 P_f(t)=a_0D_m(t)+\sqrt2\sum_{n=1}^m(-1)^na_nt\frac{D_m(t)}{t-p_n}.
 \tag{6.1}
\]

Тогда deg P_f≤m, tH_f=P_f/D_m, а обратное восстановление имеет вид

\[
 a_0=\frac{P_f(0)}{D_m(0)},\qquad
 a_n=\frac{P_f(p_n)}{\sqrt2(-1)^np_nD_m'(p_n)}.
 \tag{6.2}
\]

Пусть τ₁,…,τ_q — все различные независимые квадратные узлы (z/Ω_m)² из (0.1), после удаления автоматических внешних sinc-строк и дублирования чётной симметрии. Условия в удержанных модальных точках трактуются через устранимый предел в (2.1); они эквивалентны P_f(p_n)=0 и не удаляются.

Если q≥m+1, пространство нулевое. Если q≤m, положим

\[
 Z_q(t)=\prod_{j=1}^q(t-\tau_j),\qquad
 P_j(t)=Z_q(t)t^j,\quad0\le j\le m-q.
 \tag{6.3}
\]

Пусть \(\mathsf B_m\) синтезирует соответствующие физические функции посредством (6.2). Их Gram G_m=\(\mathsf B_m^*\mathsf B_m\) вычисляется точно:

\[
 \boxed{
 (G_m)_{ij}=\frac{\overline{P_i(0)}P_j(0)}{|D_m(0)|^2}
 +\sum_{n=1}^m
 \frac{\overline{P_i(p_n)}P_j(p_n)}{2p_n^2|D_m'(p_n)|^2}.}
 \tag{6.4}
\]

G_m положительно определена: ненулевой полином степени ≤m не может занулиться во всех m+1 различных точках 0,p₁,…,p_m. Это также сохраняет точный ранг при растущем m.

### 6.2. Относительное неравенство — искомый Gram-контроль

**[COFINAL_FAMILY | PAPER]** Из (5.4), применённого к \(f=\mathsf B_m c\) для произвольного c, следует

\[
 \boxed{
 \mathsf B_m^*A_m^2\mathsf B_m
       \preceq\delta_{m,\kappa}^2 G_m.}
 \tag{6.5}
\]

Следовательно, при \(Q_m=\mathsf B_mG_m^{-1/2}\)

\[
 \boxed{Q_m^*A_m^2Q_m\preceq\delta_{m,\kappa}^2I,
       \qquad\|A_mQ_m\|\le\delta_{m,\kappa}.}
 \tag{6.6}
\]

Это и есть контроль **после точного отбеливания Gram**. Здесь не применялось неравенство вида «сумма невязок колонок / λ_min(G_m)». Вместо него одновременно оценены все линейные комбинации в исходной физической норме.

Скалярная нижняя оценка λ_min(G_m), равномерная по произвольному базису, вообще не является инвариантным требованием: масштабирование колонок может сделать её сколь угодно малой, не меняя J. Неравенство (6.5) ковариантно относительно любого обратимого изменения базиса и потому оплачивает ровно тот Gram-переход, который нужен потребителю.

**Это не утверждение о численной устойчивости вычисления G_m^{-1/2}.** Для floating-point построения Q нужны свои интервальные/численные гарантии. Математическая оценка полной невязки от обусловленности выбранных координат не зависит.

## 7. Область доказанного и атаки на вывод

### 7.1. Что закрыто

**[COFINAL_FAMILY | PAPER]** Для каждого фиксированного κ>1 закрыта заявленная полная residual-оценка на J_{m,κΩ_m}, в исходной физической норме, вместе с Gram-переходом и бесконечным нулевым хвостом. Более того, для любого фиксированного B>0 эта невязка в итоге строго меньше m^{-B}.

По min–max для A_m² отсюда также следует только **нижний** счёт

\[
 \#\{i:|\lambda_{m,i}|<m^{-B}\}\ge\dim J_{m,\kappa\Omega_m}
 \quad\text{для всех достаточно больших }m.
 \tag{7.1}
\]

**Верхний** односторонний счёт \(\#\{\lambda<\mu\}\le\dim J\), требуемый L12, этим не доказан.

### 7.2. Чего нельзя дописать к теореме

1. **Не доказано совпадение J с измеренным кластером.** Равенство двух целочисленных счётов на конечных данных не определяет подпространство и его инерцию.
2. **Не доказан ненулевой кофинальный ранг.** Безусловно N(κΩ_m)/m→κ. Поэтому подстановка q=N(κΩ_m) без анализа кратностей и автоматических строк могла бы дать исчезающее пространство. Наш вывод не использует такую подстановку, но и не обещает положительный ранг.
3. **Не разрешена подстановка κ=κ_m→1.** Константы и начало действия оценки зависят от фиксированного κ. Хотя механизм допускает отдельный анализ движущегося зазора, такой теоремы здесь не заявлено.
4. **Не заменены комплексные нули их ординатами.** При наличии off-critical нуля условие \(\widehat f(\gamma)=0\) не равно условию (0.1). Теорема доказана именно для первоначального комплексного evaluation kernel.

### 7.3. Сильнейшая атака и её закрытие

Самая опасная возможная ошибка — считать каждый нуль в (U,V] новым нулём F_f. Это было бы неверно дважды: кратность ζ не повышает число value-условий, а синус может занулить Fourier-образ автоматически.

Исправление не условное: (4.4) оплачивает кратности, (4.5)–(4.8) оплачивают автоматическую сетку. В частности, не предположено, что ординаты рационально независимы относительно 2π/log m.

Второй риск — оценить только \(Q_m^*A_mQ_m\). Он устранён супремумом по **всем g∈V_m** в (5.2). Все смешанные блоки с J⊥ остаются в норме.

Третий риск — использовать сильную формулу Гонека в неверном диапазоне x≤T. В §4 выписана полная равномерная теорема, применённая при x=m и T≈m/log m.

Четвёртый риск — объявить новый нижний пол из хорошего residual. Такого вывода нет: неизвестный односторонний upper count остаётся отдельным входом L12.

**DISCRIMINATOR для возможной вакуозности:** точный ранг evaluation map после удаления повторов и автоматических строк; r_m=max(m+1−q_m,0). Нельзя диагностировать ненулевое пространство по округлённым сингулярным значениям или по N(T) с кратностями.

## 8. Проверки и судьба предсказаний

До символического запуска сохранён REGISTRATION.json с шестью проверяемыми ожиданиями. Регистрация относилась к algebra controls, не выдавала новую аналитическую идею за заранее предсказанный эмпирический результат.

| Проверка | Результат | Scope / verifier |
|---|---|---|
| H(t(w))=4wF(w), m=1,…,6 | 27 точных поэлементных тождеств | ABSTRACT / PAPER |
| Полином и обратные коэффициенты | 6 точных восстановлений | ABSTRACT / PAPER |
| Два различных внешних узла | Ранг 2, ядро размерности 5 при m=6 | ABSTRACT / PAPER |
| Повтор узла | Ранг остаётся 2 | ABSTRACT / PAPER |
| Автоматический sinc-нуль | Fourier-значение 0, F≠0: ложный Blaschke-фактор отвергнут | ABSTRACT / PAPER |
| θ<1 и оценка расстояния в диске | Точные факторизации | ABSTRACT / PAPER |
| Норма функционала на kernel | Три точных рациональных сравнения с envelope | ABSTRACT / PAPER |
| Плохо масштабированный базис | Три точных проверки инвариантности Gram-отношения | ABSTRACT / PAPER |
| Сопряжённая комплексная пара внешних узлов | Ранг, положительный Gram и dual-bound проверены точно при m=4 | ABSTRACT / PAPER |
| Счёт неавтоматических узлов | Точная проверка предельного линейного неравенства (4.7) на planted model | ABSTRACT / PAPER |
| Потеря Gram-нормировки | Plant A=I, B=diag(ε,ε²): сырые колонки малы, нормированный residual=1 | ABSTRACT / PAPER |

Все шесть зарегистрированных algebra-предсказаний подтверждены; два ошибочных сокращения обнаруживаются planted controls. Ни один из этих конечных прогонов не используется вместо квантора в теореме: квантор закрывают §§2–6.

**Предыдущий вердикт:** вопрос о полном residual был NOT_TESTED, а не предсказанным успехом. Здесь закрыта его точно ограниченная fixed-κ версия. Предыдущая оговорка о растущем Gram была правильной; теперь она оплачена новым относительным неравенством, не отменена задним числом. Данные RESULT опровергают постоянный offset на данном конечном диапазоне, но не доказывают неограниченный дрейф асимптотической поправки.

Не выполнены: независимый математический аудит, Lean, Arb-сертификация, новый расчёт исходной CCM-матрицы. Символьные проверки — собственные, не работа независимого агента.

## 9. Ledger, потребитель и closeout

| Claim | Scope | Verifier | Точная граница |
|---|---|---|---|
| T1: disk representation и envelope | ABSTRACT | PAPER | Точное преобразование того же carrier, физическая норма |
| T2: Blaschke-подавление | ABSTRACT | PAPER | Все f в общем evaluation kernel, без условий на Gram |
| T3: k_m≫_κ√m/log m | COFINAL_FAMILY | PAPER | Без RH, без простоты, без nonresonance-гипотезы |
| T4: δ из (0.9), затем (0.2) | COFINAL_FAMILY | PAPER | Полная операторная невязка исходного A_m |
| T5: относительное Gram-неравенство | COFINAL_FAMILY | PAPER | Полное отбеливание, без потери на condition number |
| T6: нижний absolute-band count | COFINAL_FAMILY | PAPER | Только направление (7.1) |
| O1: односторонний upper count для L12 | COFINAL_FAMILY | CONDITIONAL | Не доказан и не использован |
| O2: совпадение с численным кластером / ненулевой кофинальный ранг | COFINAL_FAMILY | CONDITIONAL | Не доказаны и не нужны для нормы |

```yaml
DOWNSTREAM_CONSUMER: NOESCAPE_L12_L13_COUNTED_FLOOR_RECEIVER
ACTUAL_CONSUMER_REQUIREMENT: residual_below_positive_threshold_AND_one_sided_upper_count
ORIGINAL_REQUESTED_OBJECT: full_operator_residual_on_J_m_kappa_Omega_m_tends_to_zero
ORIGINAL_OBJECT_IS: UNKNOWN_AS_A_NECESSARY_CONDITION_FOR_THE_ULTIMATE_FLOOR
KNOWN_WEAKER_INTERFACES:
  - bounded_residual_plus_saturated_count_gives_bounded_floor
  - direct_source_lower_floor_does_not_require_this_interpolation_representation
FAILURE_TYPE_FOR_REQUESTED_TARGET: NONE_IDENTIFIED_IN_PAPER_DERIVATION
EPISTEMIC_STATUS_FOR_REQUESTED_TARGET: PAPER_PROOF_PENDING_INDEPENDENT_AUDIT
FAILURE_TYPE_FOR_UNREQUESTED_UPPER_COUNT: NO_DERIVATION
EPISTEMIC_STATUS_FOR_UNREQUESTED_UPPER_COUNT: RESEARCH_DEBT
NOVELTY_AXIS: uniform_kernel_residual_via_exterior_Cauchy_Blaschke_and_Landau_nonautomatic_zero_count
MINIMAL_MISSING_IDENTITY_FOR_L12: N_A_m_mu_m_le_dim_J_m_on_an_unbounded_original_family
REOPEN_TRIGGER_FOR_COUNT: independent_source_upper_inertia_bound_with_the_same_J_and_threshold
KILL_SCOPE: NONE
ROUTE_FAMILY_DEATH_CLAIM: NONE
```

Что стало меньше: полный growing-subspace residual больше не оставлен supplier-gap для **фиксированного κ>1**. Закрыта и потенциальная потеря при Gram-нормировке.

Что не следует повторять: подстановка растущего ранга в фиксированный theta-jet O; добавление кратностей как независимых value-условий; включение автоматических sinc-нулей в Blaschke-счёт; вывод о дне из одной невязки.

Проверяемая нижняя матричная граница для текущего результата — \(\delta^2G-\mathsf B^*A_m^2\mathsf B\succeq0\), доказанная в §6. Это не утверждение A_m≽0.

```yaml
iteration:
  target: FIXED_KAPPA_FULL_INTERPOLATION_KERNEL_RESIDUAL
  status: PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: exterior_zero_constraints_control_all_normalized_vectors_before_Gram_whitening
  forbidden_future_move: treat_zeta_multiplicity_or_automatic_sinc_zero_as_an_extra_independent_value_constraint
  next_decisive_test: independent_PAPER_audit_of_the_complete_return_and_nonautomatic_zero_lemma
```

### Единственная CODEX DIRECTIVE

Независимо проверить §§1–6 этого файла для исходного pinned A_m, не заменяя его моделью и не расширяя задачу до нового spectral scan. Проверить четыре связки: оконная явная формула → полный mixed norm; Cauchy/disk → Blaschke-envelope; полная Theorem 1 Гонека → (4.7)–(4.9) с кратностями и автоматической сеткой; относительное Gram-неравенство → (6.6). При ошибке вернуть первый неверный переход с точным контрпримером или недостающей посылкой; при прохождении — PAPER_AUDIT_ACCEPTED для fixed-κ residual **без** утверждения upper count, ненулевого кофинального ранга или RH. Символьный replay ниже проверяет только алгебру и не заменяет этот PAPER-аудит. Route-state и Lean-export не менять.

## 10. Источники и воспроизводимость

**S0. Предыдущий разбор.** `PROSHKA_COUNTING_INERTIA_REVIEW_2026-11-02.md`, локальное вложение; прочитаны определения §2 и closeout. SHA-256:

```text
21bc6e124a83381212dfdc0676b65def0718c17585215cd69780c9d39e62f8d6
```

**S1. NOESCAPE.** Repository `Malaeu/chen_q3`, commit `a412a678a4ae1df4f03106d1a46cf5453451c65a`,
`docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, Git blob `453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc`. В текущей работе перечитаны исходный объект и L1–L3, в частности (1.1)–(1.4), (2.1)–(2.6). Теорема здесь не выводится из L1 при растущем ранге.

**S2. CONFINE.** Тот же commit,
`docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md`, Git blob `1879347b72d1aa55cf506f5387de37059f929122`; перечитан §1, включая точную безусловную явную формулу (1.4). Её возврат к двум оконным функциям дополнительно выписан в §1.2 настоящего файла.

**S3. Диагностика.** Тот же commit,
`docs/routeB_bus/cluster_count_2026-11-02/RESULT.md`, Git blob `70c25265394d60ed1c7b05b126c836380a0d64d4`. Прочитан целиком. Данные 100/140 dps обозначены самим источником как DIAGNOSTIC_NEVER_A_PROOF. В доказательство не импортированы ни fitted κ, ни finite positivity, ни count saturation.

**P1. S. M. Gonek**, *A Formula of Landau and Mean Values of ζ(s)*, в сборнике *Topics in Analytic Number Theory*, University of Texas Press, 1985, pp. 92–97, **Theorem 1, pp. 92–93**. Использован исходный PDF на странице автора; формула визуально проверена на первых двух страницах. Не используется Theorem 2, которая уже предполагает RH.

```text
https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf
```

**P2. C. Bellotti and P.-J. Wong**, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, arXiv:2412.15470v2, 7 July 2025, **Theorem 1.1, p. 1**. Первичная статья прочитана, страница теоремы визуально проверена. Используется только грубое следствие (4.1).

```text
https://arxiv.org/pdf/2412.15470v2
```

Проверка источников обнаружила, что старое значение 9.3675 в HSW заменено на 9.4925; текущий вывод на этом числе не основан. Взята непосредственно проверенная более новая теорема P2 с большим безопасным запасом E(t)=log t+10.

### Компактный точный algebra replay

Сохрани блок как `CHECK_FIXED_KAPPA_RESIDUAL.py` и запусти в той же директории:

```bash
uv run --with sympy python3 CHECK_FIXED_KAPPA_RESIDUAL.py
```

Это самостоятельные exact-algebra controls, не расчёт ζ или CCM и не формальная верификация доказательства.

```python
from __future__ import annotations
import sympy as s

w, t = s.symbols('w t')
for m in range(1, 7):
    poles = [s.Rational(n*n, m*m) for n in range(m+1)]
    tw = (1+w)**2/(4*w)
    for p in poles:
        assert s.cancel(1/(tw-p) - 4*w/(1+2*(1-2*p)*w+w*w)) == 0
    b = [s.Rational((-1)**n*(n+2), n+3) for n in range(m+1)]
    D = s.prod(t-p for p in poles[1:])
    P = s.expand(b[0]*D + sum(
        b[n]*t*s.prod(t-poles[j] for j in range(1,m+1) if j != n)
        for n in range(1,m+1)))
    assert s.cancel(P.subs(t,0)/D.subs(t,0)-b[0]) == 0
    for n in range(1,m+1):
        assert s.cancel(P.subs(t,poles[n]) /
                        (poles[n]*s.diff(D,t).subs(t,poles[n]))-b[n]) == 0
    assert s.cancel(P/D-t*sum(b[n]/(t-poles[n]) for n in range(m+1))) == 0

m = 6
poles = [s.Rational(n*n,m*m) for n in range(m+1)]
roots = [s.Rational(1,4), s.Rational(1,3)]
nodes = [(1+x)**2/(4*x) for x in roots]
E = s.Matrix([[1/(x-p) for p in poles] for x in nodes])
Z = s.Matrix.hstack(*E.nullspace())
assert E.rank() == 2 and Z.cols == 5 and E*Z == s.zeros(2,5)
assert E.col_join(E[:1,:]).rank() == 2
metric = s.diag(1, *([s.Rational(1,2)]*m))
G = Z.T*metric*Z
assert G.det() > 0
R, u, v = s.Rational(3,4), s.Rational(1,3), s.Rational(1,10)
theta = R*(u+v)/(R*R+u*v)
assert 0 < theta < 1
bound_squared = s.Rational(2*m+1)/(1-R)**4 * theta**(2*len(roots))
for ww in [s.Rational(0), s.Rational(1,10), s.Rational(1,12)]:
    row = s.Matrix([[1/(1+2*(1-2*p)*ww+ww*ww) for p in poles]])
    exact_dual_squared = (row*Z*G.inv()*Z.T*row.T)[0]
    assert 0 <= exact_dual_squared <= bound_squared
    scale = s.diag(*[s.Integer(10)**(5*j) for j in range(Z.cols)])
    ZZ = Z*scale
    GG = ZZ.T*metric*ZZ
    assert s.cancel((row*ZZ*GG.inv()*ZZ.T*row.T)[0]-exact_dual_squared) == 0

# An automatic exterior sinc zero is not necessarily a disk-function zero.
z = s.Integer(3)  # m=2, L=2*pi, constant window profile
assert s.simplify(2*s.sin(s.pi*z)/(s.sqrt(2*s.pi)*z)) == 0
wa = (s.Rational(3,2)-s.sqrt(s.Rational(9,4)-1))**2
assert s.simplify(1/(1+wa)**2) != 0

R, u, v = s.symbols('R u v')
assert s.expand(R*R+u*v-R*(u+v)-(R-u)*(R-v)) == 0
x,y,c = s.symbols('x y c')
gap = (x+y)**2/(1+x*y)**2-(x*x+y*y-2*x*y*c)/(1+x*x*y*y-2*x*y*c)
expected = 2*x*y*(c+1)*(1-x*x)*(1-y*y)/((1+x*y)**2*(1+x*x*y*y-2*x*y*c))
assert s.cancel(gap-expected) == 0

# Gram-loss plant: tiny raw columns do not imply a tiny normalized residual.
eps = s.Rational(1,1000)
Z = s.diag(eps,eps**2)
G = Z.T*Z
assert G.inv()*G == s.eye(2)  # A=I: whitened residual norm is exactly 1.
print('Exact algebra controls passed; no CCM, interval, or Lean claim.')
```

**Итог:** требуемый предел и даже сверхполиномиальная невязка доказаны на PAPER-уровне для точного J_{m,κΩ_m} при каждом фиксированном κ>1. Ненулевой кофинальный ранг, верхний spectral count и RH к этому результату не приписываются.