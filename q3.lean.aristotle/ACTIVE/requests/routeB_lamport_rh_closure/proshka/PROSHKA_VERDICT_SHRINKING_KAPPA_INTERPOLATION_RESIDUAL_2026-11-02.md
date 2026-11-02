# STATUS: TRY_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL

```yaml
OPERATIVE_CLASS: TRY_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL
DATE: 2026-11-02
TASK_MODE: OWNER_DIRECT_MATHEMATICAL_REQUEST
FORMAL_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_OPERATOR: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
DATA_PINS: [rh_clean@bf89051, rh_clean@a412a67]
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PARENT: 722ef7e6cef5b6df03553a70981007c0e945cf0c
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
PARAMETER_RANGE: FIXED_0_LT_c_LT_1
TARGET_RESULT: PAPER_PROOF_GIVEN
NONZERO_GROWING_RANK: PROVED_IN_PAPER_DERIVATION
FULL_OPERATOR_RESIDUAL: SUPERPOLYNOMIAL_IN_PAPER_DERIVATION
GRAM_CONTROL: RELATIVE_MATRIX_DOMINATION_BEFORE_WHITENING
RH_ASSUMED: false
SIMPLE_ZEROS_ASSUMED: false
NONRESONANCE_ASSUMED: false
SPECTRAL_UPPER_COUNT_PROVED: false
RH_PROVED: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: BOUNDARY_CASE
ROUTE_SCORE: 5
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
EXACT_ALGEBRA_SELF_CONTROLS: PASSED
PARAMETER_DIAGNOSTIC_CHECKS: 160
LITERAL_CCM_RECOMPUTED: false
INDEPENDENT_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
NUMERICAL_ONSET: NOT_COMPUTED
GONEK_ABSOLUTE_CONSTANT: THEOREM_CONSTANT_NOT_NUMERICALLY_EXTRACTED
LEAN_SOURCE_CHANGED: false
ROUTE_STATE_CHANGED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. При фиксированном **0<c<1** требуемый moving-kappa результат получается. Ниже отдельно оплачены сжатие полосы нулей, вырождение Blaschke-константы, ранг и полный Gram-переход. Подстановка движущегося параметра в старое O_kappa не используется. Это PAPER-доказательство автора, не независимый аудит и не Lean-сертификат.

## 0. Теорема

**[COFINAL_FAMILY | PAPER]** Пусть

\[
 L=\log m,\quad h=1+\log L,\quad
 \varepsilon=\varepsilon_m=\frac{ch}{L},\quad
 \kappa_m=1+\varepsilon,\quad
 \Omega=\frac{2\pi m}{L},\quad T=\kappa_m\Omega.
 \tag{0.1}
\]

Здесь m — целое, c фиксировано, 0<c<1. V_m — исходный чётный оконный carrier размерности m+1; A_m — исходный оператор в физической L2-метрике. Определение пространства не меняется:

\[
 J_m=\{f\in V_m:\ \widehat f(i(\rho-1/2))=0
       \text{ для всех нетривиальных нулей }\rho,
       \ 0<|\Im\rho|<T\}.
 \tag{0.2}
\]

Это условия на **значения в фактических комплексных точках**, не на проекции нулей на критическую прямую. Условия на производные в кратных нулях не добавляются.

Пусть r_m=dim J_m и Q_m — любой изометрический синтез с образом J_m. Для всех достаточно больших m:

\[
 \boxed{r_m\ge\frac{1-c}{2}\frac{mh}{L}
       \ge\frac{1-c}{2}\frac{m\log\log m}{\log m}.}
 \tag{0.3}
\]

Одновременно

\[
 \boxed{
 \|A_mQ_m\|\le
 \frac{2^{14}}{c^2}\frac{\sqrt m\,L^3}{h^2}
 \exp\!\left[-\frac{c^2}{3072}
                    \frac{\sqrt m\,h^2}{L^3}\right].}
 \tag{0.4}
\]

Следовательно, для каждого фиксированного B>0:

\[
 \boxed{\|A_mQ_m\|=o(m^{-B}),}
 \tag{0.5}
\]

и, в частности, норма не превосходит m^{-B} для всех m начиная с некоторого m_0(c,B). Ненулевой ранг здесь доказан, а не оставлен оговоркой о возможном нулевом пространстве.

Оговорка к исходной формулировке: равенство dim J=m+1-N(T) без разбора кратностей и автоматических строк вообще не требуется. Ниже используется безусловная **нижняя** оценка dim J>=m+1-N(T). При фиксированном kappa>1 отрицательной становится эта формальная нижняя оценка, а не сама размерность. Исчезновение исходного пространства из одного счёта с кратностями не следует. Новая теорема избегает этой проблемы.

## 1. Явный нижний ранг

**[COFINAL_FAMILY | PAPER]** Обозначим через N(t) число верхних нетривиальных нулей с 0<Im rho<=t, с кратностями. Из Bellotti–Wong, Theorem 1.1 [P2], достаточно следствия

\[
 |N(t)-M(t)|\le E(t):=\log t+10,\qquad
 M(t)=\frac{t}{2\pi}\log\frac{t}{2\pi e},\quad t\ge e.
 \tag{1.1}
\]

Нижние нули не удваивают число условий: симметрия rho -> 1-rho переводит их в верхние, а соответствующие спектральные аргументы отличаются знаком; Fourier-образ чётный. Повтор нуля не увеличивает ранг value-условия. Поэтому

\[
 r_m\ge m+1-N(T).
 \tag{1.2}
\]

Точная подстановка T=(1+epsilon)2pi m/L в главную часть даёт

\[
 m-M(T)=m\left[
       (1-c)\frac hL+c\frac{h^2}{L^2}
       -\frac{(1+\varepsilon)\log(1+\varepsilon)}L\right].
 \tag{1.3}
\]

При L>=16 имеем 0<epsilon<=1, h>=1+epsilon и log(1+epsilon)<=epsilon. Следовательно, два последних члена в скобках вместе неотрицательны:

\[
 c\frac{h^2}{L^2}
 -\frac{(1+\varepsilon)\log(1+\varepsilon)}L
 \ge \frac{ch}{L^2}(h-1-\varepsilon)\ge0.
\]

Также T<=2Omega<=m, поэтому log T<=L. Из (1.1)–(1.3):

\[
 \boxed{r_m\ge(1-c)\frac{mh}{L}-2L.}
 \tag{1.4}
\]

Условие

\[
 (1-c)mh\ge4L^2
 \tag{1.5}
\]

даёт (0.3). Оно выполнено в конце всей исходной целочисленной последовательности, не только на выбранной подпоследовательности.

## 2. Равномерная дисковая оценка

### 2.1. Тот же carrier и физическая норма

**[ABSTRACT | PAPER]** Используем ортонормированный базис

\[
 \phi_0=L^{-1/2}\mathbf1_{[-L/2,L/2]},\qquad
 \phi_n=\sqrt{2/L}\cos(2\pi nx/L)\mathbf1_{[-L/2,L/2]},\quad1\le n\le m.
\]

Для f=sum a_n phi_n имеем ||f||_2^2=sum |a_n|^2. Положим

\[
 p_n=(n/m)^2,\quad b_0=a_0,\quad b_n=\sqrt2(-1)^na_n\ (n>0),
\]
\[
 F_f(w)=\sum_{n=0}^m\frac{b_n}{1+2(1-2p_n)w+w^2}.
 \tag{2.1}
\]

Подстановка z^2/Omega^2=(1+w)^2/(4w) в точную рациональную Fourier-формулу даёт

\[
 \widehat f(z)=\frac{2\sin(zL/2)}{\sqrt L\,z}(1+w)^2F_f(w).
 \tag{2.2}
\]

Все полюса F_f находятся на |w|=1. По Cauchy–Schwarz sum |b_n|<=sqrt(2m+1)||f||_2, поэтому

\[
 \sup_{|w|\le r}|F_f(w)|
 \le\frac{\sqrt{2m+1}}{(1-r)^2}\|f\|_2,\qquad0<r<1.
 \tag{2.3}
\]

В правой полуплоскости Re z>Omega нужная обратная ветвь равна

\[
 w(z)=\left(z/\Omega-\sqrt{z^2/\Omega^2-1}\right)^2.
\]

Для Re z>=s Omega, s>1, в том числе при комплексном z,

\[
 |w(z)|\le(s-\sqrt{s^2-1})^2.
 \tag{2.4}
\]

Действительно, если eta=z/Omega-sqrt(z^2/Omega^2-1)=r exp(i phi), |eta|<1, то Re(z/Omega)=(r+r^{-1})cos(phi)/2<=(r+r^{-1})/2. Отсюда r<=s-sqrt(s^2-1).

### 2.2. Все зависимости от epsilon оставлены явными

Положим

\[
 \alpha=1+\varepsilon/3,\quad \beta=1+2\varepsilon/3,
 \quad U=\alpha\Omega,\quad V=\beta\Omega<T,
\]
\[
 u=(\alpha-\sqrt{\alpha^2-1})^2,\quad
 v=(1+\varepsilon-\sqrt{(1+\varepsilon)^2-1})^2,
 \quad R=(1+u)/2,
\]
\[
 \boxed{\theta(1+\varepsilon)=\frac{R(u+v)}{R^2+uv},\qquad
 D(1+\varepsilon)=\frac{(1+v)^4}{(1-R)^2(1-v)^2}.}
 \tag{2.5}
\]

Имеем 0<v<u<R<1. Пусть k_m — число **различных** верхних нулей в U<gamma<=V, за исключением

\[
 \Re\rho=1/2,\qquad \gamma L\in2\pi\mathbb Z.
 \tag{2.6}
\]

Это ровно автоматические внешние sinc-нули. Каждый оставшийся нуль даёт общий нуль F_f для всех f in J_m: в (2.2) вне модального диапазона нет полюсов, а sin(zL/2) не равен нулю. Различные верхние rho дают различные w. Кратность zeta не подменяется кратностью F_f.

Делим F_f на конечное произведение

\[
 \prod_{j=1}^{k_m}\frac{R(w-w_j)}{R^2-\overline{w_j}w},\qquad |w_j|\le u.
\]

Его модуль на |w|=R равен единице. Принцип максимума и точная псевдогиперболическая оценка

\[
 \sup_{|w|\le v,\ |a|\le u}
 \left|\frac{R(w-a)}{R^2-\overline a w}\right|
 \le\frac{R(u+v)}{R^2+uv}
\]

дают для всех f in J_m одновременно

\[
 \boxed{\sup_{|w|\le v}|F_f(w)|
 \le\frac{\sqrt{2m+1}}{(1-R)^2}\theta^{k_m}\|f\|_2.}
 \tag{2.7}
\]

### 2.3. Явная цена сжатия зазора

Для 0<epsilon<=1:

\[
 1-u=\frac{2\sqrt{\alpha^2-1}}{\alpha+\sqrt{\alpha^2-1}}
 \ge\frac{2}{3}\sqrt{2\varepsilon/3}\ge\frac{\sqrt\varepsilon}{2}.
\]

Здесь alpha<=4/3 и alpha+sqrt(alpha^2-1)<3. Так как v<u, получаем

\[
 1-R\ge\sqrt\varepsilon/4,\qquad 1-v\ge\sqrt\varepsilon/2.
\]

Используя точное тождество

\[
 1-\theta=\frac{(R-u)(R-v)}{R^2+uv},
\]

и R-v>=R-u=(1-u)/2, R^2+uv<=2, заключаем

\[
 \boxed{-\log\theta\ge1-\theta\ge\varepsilon/32,\qquad
        D\le1024\varepsilon^{-2}.}
 \tag{2.8}
\]

Для ясности, действительные ведущие порядки точнее этих безопасных границ:

\[
 1-\theta=
 \left(\frac2{\sqrt3}-\frac13\right)\varepsilon
 +O(\varepsilon^{3/2}),\qquad
 D=3\varepsilon^{-2}(1+O(\sqrt\varepsilon)).
 \tag{2.9}
\]

В доказательстве используется (2.8), не неоценённый остаток (2.9). В частности, нельзя сохранять theta<1 как фиксированную константу при epsilon->0.

## 3. Равномерный нижний счёт k_m

### 3.1. Число нулей в сжимающейся относительной полосе

**[COFINAL_FAMILY | PAPER]** Пусть

\[
 n_m=N(V)-N(U),\qquad
 S_m=\sum_{U<\Im\rho\le V}m^\rho,
 \tag{3.1}
\]

с кратностями. Из M'(t)=log(t/(2pi))/(2pi), (1.1) и L>=16:

\[
 n_m\ge\frac{\varepsilon m}{3}
             \left(1-\frac{\log L}{L}\right)-4L
       \ge\frac{\varepsilon m}{4}-4L.
 \tag{3.2}
\]

Таким образом,

\[
 \varepsilon m\ge48L
 \quad\Longrightarrow\quad n_m\ge\varepsilon m/6.
 \tag{3.3}
\]

Это прямая оценка, равномерная по 0<epsilon<=1. Фиксированная длина относительной полосы не предполагается.

Кратность каждого нуля в этой полосе ограничена скачком N. По (1.1) и непрерывности M:

\[
 \operatorname{mult}(\rho)\le2(\log V+10)\le4L.
 \tag{3.4}
\]

### 3.2. Полная равномерная формула Гонека, не fixed-kappa O

Используется безусловная Theorem 1 [P1]. Существует абсолютная константа C_G>=1, при которой для x,Y>1 остаток в

\[
 \sum_{0<\gamma\le Y}x^\rho=-\frac{Y}{2\pi}\Lambda(x)+\mathcal R(x,Y)
\]

по модулю не превосходит C_G, умноженного на

\[
 x\log(2x)\log\log(3x)+x\log(2Y)
 +\log x\min(Y,x/\langle x\rangle)
 +\min(\log Y/\log x,Y\log Y).
 \tag{3.5}
\]

Здесь <x> — расстояние до ближайшей простой степени, отличной от x. Константа C_G не зависит от c, epsilon, m, U или V. Её численное значение в этой работе не извлекается.

Берём x=m, отдельно Y=U и Y=V. При L>=16 и 0<epsilon<=1 имеем Omega<=Y<=2Omega<=m. Четыре слагаемых (3.5) ограничены соответственно

\[
 2mLh,\qquad 2mL,\qquad4\pi m\le mL,\qquad1.
\]

Следовательно, каждый из двух остатков по модулю не превосходит 6C_G mLh, и

\[
 \boxed{\Re S_m\le12C_G mLh.}
 \tag{3.6}
\]

Главный член -(V-U)Lambda(m)/(2pi) неположителен. Он сохранён; применяется полная теорема (3.5), а не её следствие для x<=Y, которое здесь не подходит.

### 3.3. Удаление автоматических sinc-нулей

Пусть b_m — число неавтоматических нулей в полосе, с кратностями. Каждый автоматический нуль даёт m^rho=sqrt m. Для любого другого нуля Re(m^rho)>=-m. Поэтому точно

\[
 \boxed{b_m\ge
 \frac{[\sqrt m\,n_m-\Re S_m]_+}{m+\sqrt m}.}
 \tag{3.7}
\]

Условие

\[
 \boxed{\sqrt m\ge\frac{144C_G}{c}L^2}
 \tag{3.8}
\]

вместе с epsilon=ch/L обеспечивает 12C_G mLh<=epsilon m^(3/2)/12. При (3.3) получаем

\[
 b_m\ge\frac{\varepsilon\sqrt m}{24}.
\]

Делим только на доказанную верхнюю границу кратности (3.4):

\[
 \boxed{
 k_m\ge\frac{\varepsilon\sqrt m}{96L}
       =\frac{c\sqrt m\,(1+\log\log m)}{96(\log m)^2}.}
 \tag{3.9}
\]

Это требуемая равномерная замена старой fixed-kappa оценки. Контроль относительной ошибки явный:

\[
 \frac{mLh}{\varepsilon m^{3/2}}=\frac{L^2}{c\sqrt m}\longrightarrow0.
\]

Таким образом, сжатие относительной полосы не уничтожает доказательство. Ни простота нулей, ни запрет точных резонансов с sinc-сеткой не добавлены.

## 4. Полный оператор, бесконечный хвост и Gram

### 4.1. Возврат к исходному A_m

**[ABSTRACT | PAPER]** Из исходной безусловной явной формулы CONFINE (1.4), с исходными нормировками NOESCAPE, имеем

\[
 \langle g,A_mf\rangle
 =\sum_\rho\overline{\widehat g(\overline{z_\rho})}\widehat f(z_\rho),
 \qquad z_\rho=i(\rho-1/2).
 \tag{4.1}
\]

Это не сумма квадратов, полученная предположением RH. Полный арифметический оператор, все простые степени, полюсы и концы окна входят в (4.1).

Возврат формулы к двум оконным cosine-функциям можно осуществить при каждом фиксированном m гладкой свёрткой. Их нулевые продолжения имеют ограниченную вариацию; Fourier-образы в |Im z|<=1/2 ограничены C/(1+|Re z|). Поэтому нулевая сторона абсолютно суммируема. Гладкие свёртки имеют равномерный Fourier-множитель <=exp(epsilon_smooth/2), что разрешает доминированный переход. На арифметической стороне поддержки лежат в общем компакте, prime-power-сумма конечна, граничные корреляции сходятся. Архимедова корреляционная разность у нуля есть O(s) равномерно по сглаживанию вследствие BV-границы; множитель j(s)=O(1/s) оплачивается. Полюсные функционалы сходятся. Этот фиксированный-m переход не подменяет дальнейший равномерный бюджет.

Для f in J_m слагаемые с |Im rho|<T исчезают точно. При равенстве |Im rho|=T слагаемое остаётся в хвосте.

По (2.2), (2.3), (2.7) и |sin(zL/2)|<=m^(1/4), для |Re z|>=T, |Im z|<=1/2:

\[
 |\widehat f(z)|\le
 \frac{2(1+v)^2\sqrt{2m+1}\,m^{1/4}}
      {\sqrt L(1-R)^2|z|}\theta^{k_m}\|f\|_2,
\]
\[
 |\widehat g(z)|\le
 \frac{2(1+v)^2\sqrt{2m+1}\,m^{1/4}}
      {\sqrt L(1-v)^2|z|}\|g\|_2\qquad(g\in V_m).
 \tag{4.2}
\]

### 4.2. Явный конечный бюджет

Из (1.1), интегрированием Стилтьеса с N(T^-), получаем

\[
 \sum_{\gamma\ge T}\gamma^{-2}
 \le\mathcal Z(T):=\frac{\log T}{\pi T}
                 +\frac{\log T+21/2}{T^2}.
 \tag{4.3}
\]

Действительно, можно отбросить неположительный член -N(T^-)/T^2 и интегрировать 2(M(t)+E(t))/t^3 от T до бесконечности. Первый интеграл равен log(T/(2pi))/(pi T), второй — (log T+21/2)/T^2. Оба знака gamma учтены отдельным множителем 2.

Следовательно,

\[
 \boxed{
 \|A_m|_{J_m}\|\le
 \delta_m:=8D\frac{(2m+1)\sqrt m}{L}
                \mathcal Z(T)\theta^{k_m}.}
 \tag{4.4}
\]

Это оценка mixed pairing с **произвольным** единичным g in V_m; связь с J_m-perp не выброшена. (4.4) — не только оценка сжатия Q_m^*A_mQ_m.

Все коэффициенты (4.4) явны; k_m — конечный счёт фактических нулей, а не неизвестный спектральный счёт A_m. Для вычислимого конечного варианта разрешено заменить k_m более слабой нижней границей

\[
 \ell_m=\frac{[\sqrt m\,n_m-\Re S_m]_+}
 {2(m+\sqrt m)(\log V+10)}.
 \tag{4.5}
\]

Никакая константа теоремы Гонека в (4.4)–(4.5) не спрятана; она нужна только для получения оценки в одних m,c с гарантией её асимптотического начала.

### 4.3. Gram оплачивается до отбеливания

**[COFINAL_FAMILY | PAPER]** Для любого точного базисного синтеза mathsf B_m пространства J_m положим G_m=mathsf B_m^*mathsf B_m. Ранг положителен по §1, G_m положительно определена. Поскольку (4.4) действует на все линейные комбинации, получаем

\[
 \boxed{\mathsf B_m^*A_m^2\mathsf B_m\preceq\delta_m^2G_m.}
 \tag{4.6}
\]

Поэтому при Q_m=mathsf B_m G_m^(-1/2):

\[
 \boxed{Q_m^*A_m^2Q_m\preceq\delta_m^2I,\qquad
             \|A_mQ_m\|\le\delta_m.}
 \tag{4.7}
\]

Оценка не теряет lambda_min(G_m) в знаменателе: вся семья нормированных физических векторов уже оценена. Это математический Gram-контроль, а не обещание устойчивости floating-point построения базиса.

Для явного полиномиального базиса положим D_m(t)=prod_(n=1)^m(t-p_n). Если P_j(t) — полиномы степени <=m, делящиеся на произведение различных активных квадратных узлов, коэффициенты соответствующих функций равны

\[
 a_{0,j}=P_j(0)/D_m(0),\qquad
 a_{n,j}=\frac{P_j(p_n)}{\sqrt2(-1)^np_nD'_m(p_n)}.
\]

Автоматические внешние sinc-строки удаляются, повторные строки не добавляются, удержанные модальные точки трактуются через устранимый предел. Тогда

\[
 (G_m)_{ij}=\frac{\overline{P_i(0)}P_j(0)}{|D_m(0)|^2}
 +\sum_{n=1}^m\frac{\overline{P_i(p_n)}P_j(p_n)}{2p_n^2|D'_m(p_n)|^2}.
 \tag{4.8}
\]

Положительная определённость следует из невозможности ненулевого полинома степени <=m занулиться во всех m+1 точках 0,p_1,...,p_m. Неравенство (4.6) сохраняется при любом обратимом изменении такого базиса.

## 5. Итоговый явный спад и условия начала действия

**[COFINAL_FAMILY | PAPER]** При L>=16 имеем T>=100, T<=m и

\[
 \mathcal Z(T)\le2(\log T+1)/T,\qquad \log T+1\le2L.
\]

Из (4.4):

\[
 \delta_m\le\frac{48D}{\pi\kappa_m}\sqrt m\,L\,\theta^{k_m}.
\]

Подстановка (2.8), (3.9), kappa_m>=1 и pi>3 даёт

\[
 \delta_m\le2^{14}\varepsilon^{-2}\sqrt m\,L
       \exp\left[-\frac{\varepsilon^2\sqrt m}{3072L}\right].
 \tag{5.1}
\]

Подставляя epsilon=ch/L, получаем (0.4) с заявленными численными константами.

Достаточные условия для одновременной применимости (0.3)–(0.4):

\[
 \boxed{L\ge16,\quad \varepsilon m\ge48L,\quad
 \sqrt m\ge144C_G L^2/c,\quad (1-c)mh\ge4L^2.}
 \tag{5.2}
\]

Все они выполнены для всех достаточно больших m при каждом фиксированном 0<c<1. Константа C_G абсолютна и определена непосредственно в (3.5); её численное извлечение не выполнено.

Для конкретного B достаточно дополнительно проверить

\[
 \frac{c^2}{3072}\frac{\sqrt m\,h^2}{L^3}
 \ge (B+1/2)L+3\log L-2\log h+14\log2-2\log c.
 \tag{5.3}
\]

Левая часть, делённая на L, стремится к бесконечности. Поэтому (5.3) в итоге выполняется с неограниченно растущим запасом, что доказывает не только <=m^(-B), но и o(m^(-B)). Это закрывает оба требуемых квантора: ненулевой растущий ранг и полную сверхполиномиальную невязку на том же J_m.

## 6. Проверки, границы и ledger

Перед символическими/параметрическими контролями были зарегистрированы: ведущий коэффициент 1-theta, предел epsilon^2 D, точная главная часть ранга, сокращение относительной ошибки Гонека до L^2/(c sqrt m), инвариантность Gram-перехода при растяжении базиса. Все пять algebra-проверок прошли. Дополнительно проверены 160 значений epsilon из (0,1], включая 10^(-60), при 100 десятичных знаках. Эти последние проверки диагностические, не интервальные сертификаты и не доказательство универсальных неравенств; их доказательства находятся выше.

| Утверждение | Scope | Verifier | Граница |
|---|---|---|---|
| Нижний ранг (0.3) | COFINAL_FAMILY | PAPER | Без простоты нулей, без точного равенства q=N(T) |
| Равномерные theta,D (2.8) | ABSTRACT | PAPER | Все 0<epsilon<=1 |
| Нижний счёт (3.9) | COFINAL_FAMILY | PAPER | Автоматические нули удалены, кратности оплачены |
| Полная невязка (0.4)–(0.5) | COFINAL_FAMILY | PAPER | Исходные A_m,V_m и физическая норма |
| Gram-доминирование (4.6) | COFINAL_FAMILY | PAPER | Все линейные комбинации, не отдельные колонки |
| Односторонний верхний spectral count | COFINAL_FAMILY | CONDITIONAL | Не доказан, не использован |

Сильнейшие проверки против вывода: нельзя переносить fixed-kappa O на kappa_m; нельзя считать повторные/автоматические нули независимыми; нельзя заменить mixed norm сжатием; нельзя считать N(T) рангом без проверки; нельзя использовать RH-условную Theorem 2 Гонека. Ни одно из этих сокращений в доказательство не входит.

Диапазон c<=0 не заявлен: он уже не задаёт kappa_m>1. Диапазон c>=1 не заявлен: положительный ведущий бюджет ранга здесь теряется. Оценка не равномерна по c, стремящемуся к 0 или 1 вместе с m.

Из min–max для A_m^2 дополнительно следует **нижний** absolute-band count не меньше r_m для любого фиксированного B в достаточно поздних ячейках. Это не верхний счёт всех уровней lambda<mu и не RH. Данные capacity_matrix и cluster_count не используются в доказательстве как посылки.

```yaml
DOWNSTREAM_CONSUMER: NOESCAPE_L12_L13_EQUATION_5_4
ACTUAL_CONSUMER_REQUIREMENT: residual_below_mu_AND_signed_upper_count_at_most_dim_J
ORIGINAL_REQUESTED_OBJECT: nonzero_rank_and_superpolynomial_residual_at_kappa_m_1_plus_c_h_over_L
ORIGINAL_OBJECT_IS: UNKNOWN_AS_NECESSARY_FOR_THE_ULTIMATE_LOWER_FLOOR
KNOWN_WEAKER_INTERFACES:
  - bounded_residual_plus_saturated_count_implies_constant_floor
  - direct_source_constant_floor_bypasses_interpolation
FAILURE_TYPE_FOR_REQUESTED_TARGET: NONE_IDENTIFIED_IN_PAPER_DERIVATION
EPISTEMIC_STATUS_FOR_REQUESTED_TARGET: PAPER_PROOF_PENDING_INDEPENDENT_AUDIT
FAILURE_TYPE_FOR_REMAINING_SIGNED_COUNT: NO_DERIVATION
EPISTEMIC_STATUS_FOR_REMAINING_SIGNED_COUNT: RESEARCH_DEBT
NOVELTY_AXIS: uniform_boundary_regime_with_positive_rank_and_explicit_Blaschke_loss
MINIMAL_MISSING_IDENTITY_FOR_L12: N_A_m_mu_m_le_dim_J_m_on_an_unbounded_original_family
REOPEN_TRIGGER_FOR_SIGNED_COUNT: independent_source_upper_inertia_bound_for_same_J_and_mu
KILL_SCOPE: NONE
ROUTE_FAMILY_DEATH_CLAIM: NONE
```

Что стало меньше: прежний residual-поставщик теперь имеет ненулевой растущий ранг на требуемом движущемся cutoff. Что не переносится автоматически: насыщенность счёта и знак дна. Судьба прошлой оговорки: fixed-kappa доказательство само по себе не разрешало этот режим; новая работа оплачивает именно отсутствовавшую равномерность, не объявляет её ранее доказанной.

## 7. Источники и передача проверки

**S0. Предыдущий fixed-kappa вердикт:** локальное вложение `PROSHKA_VERDICT_FIXED_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, SHA256 `3685974dfd90ba82fe001374e6c5e795e757500eeda03505c9cdfbdd02c7b6e5`, Git blob вычисленного содержимого `7eb51d104401e0dfb57bfa75d25d0a7deaf15555`. Использованные дисковые и mixed-form аргументы повторены выше, так что новый текст не зависит от доступа к вложению.

**S1. Исходный оператор:** `Malaeu/chen_q3`, `rh_clean@a412a678a4ae1df4f03106d1a46cf5453451c65a`; `docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, blob `453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc`; `PROSHKA_VERDICT_CONFINE_2026-10-30.md` в той же директории, blob `1879347b72d1aa55cf506f5387de37059f929122`. Нормировки (4.1) не заменяют исходный оператор модельной Gram-матрицей.

**S2. Диагностика, не посылка:** `rh_clean@a412a67`, `docs/routeB_bus/cluster_count_2026-11-02/RESULT.md`; `rh_clean@bf89051`, `docs/routeB_bus/capacity_matrix_2026-11-02/RESULT.md`. Финитные данные, в том числе множитель 2 перед Gram верхних критических нулей, не используются для вывода глобальной положительности или сходимости хвоста.

**P1. S. M. Gonek**, *A Formula of Landau and Mean Values of zeta(s)*, Theorem 1, pp. 92–93. Первые две страницы первичного PDF повторно визуально проверены; Theorem 2, предполагающая RH, не используется.

```text
https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf
```

**P2. C. Bellotti and P.-J. Wong**, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, arXiv:2412.15470v2, Theorem 1.1, p. 1. Страница теоремы повторно визуально проверена. Используется безопасное следствие (1.1), а не численные предположения о нулях.

```text
https://arxiv.org/pdf/2412.15470v2
```

### Единственная CODEX DIRECTIVE

Независимо проверить §§1–5 этого вердикта, особенно равномерность (3.2), полную безусловную Theorem 1 в (3.5), удаление автоматических строк (3.7), деградацию theta,D в (2.8), mixed-form возврат (4.1) и относительный Gram (4.6). Результат проверки: `PAPER_AUDIT_ACCEPTED` либо первый точный неверный переход с контрпримером/недостающей посылкой. Не заменять этот аудит новым spectral scan, не утверждать верхний signed count, не менять Lean-export или route-state.

Ветка доставки: `proshka_inbox_2026-10-31`; единственный родитель нового коммита: `722ef7e6cef5b6df03553a70981007c0e945cf0c`. Записывается только этот новый Markdown-файл в `docs/routeB_bus/proshka/`. Старые вердикты, Lean и состояние маршрута не редактируются. SHA доставки сообщается в сопроводительном ответе после успешной записи и проверки ref; собственный SHA коммита не встраивается в его содержимое. Lean-аксиомный профиль и lake-команды неприменимы: Lean-файлы не создавались. Git-запись не является математической или kernel-проверкой.

**Итог:** при каждом фиксированном 0<c<1 доказаны положительный растущий ранг (0.3) и полная сверхполиномиальная невязка (0.4)–(0.5), с явными theta, D и k_m. RH, верхний spectral count и независимое подтверждение доказательства не заявлены.
