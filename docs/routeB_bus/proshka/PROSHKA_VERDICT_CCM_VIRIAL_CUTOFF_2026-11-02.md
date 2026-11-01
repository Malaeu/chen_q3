# STATUS: TRY_CCM_VIRIAL_WITH_EXPLICIT_CUTOFF_REMAINDER
```yaml
OPERATIVE_CLASS: TRY_CCM_VIRIAL_WITH_EXPLICIT_CUTOFF_REMAINDER
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_GLOBAL_VIRIAL_AND_WINDOW_ERROR_REQUEST
SOURCE_COMMIT: d8983a2a3b05ef0368fc6f284bef1fd22b4cd50c
SOURCE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CCM_POHOZAEV_2026-11-02.md
SOURCE_SHA256: a6b7f67ab1e4bb7f0af7171f67f838087e4b51d79056cb9b9a5d45d01edc392b
SOURCE_GIT_BLOB: 12780e227a4dc2e6e1a85c60bdad687c1f266494
SOURCE_HASH_CHECK: LOCAL_BYTES_MATCH_REMOTE_BLOB
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: PARTIAL_WITH_EXACT_WINDOW_DECOMPOSITION
PART_I_GLOBAL_VIRIAL: PROVED_PAPER
PART_II_FINITE_DIFFERENCE_DECOMPOSITION: PROVED_PAPER
PART_II_CLASSICAL_EQUALITY_AT_ALL_WINDOWS: NOT_ESTABLISHED
PART_II_EQUALITY_WITH_EXISTING_ERROR_VARIATION: PROVED_PAPER
SHARP_WINDOW_PROJECTOR: MULTIPLICATION_BY_INDICATOR_NOT_FINITE_FOURIER_PROJECTION
D_GENERATOR: MINUS_ONE_HALF_MINUS_X_D_DX
MIXED_TERM: K_L_OF_P_L_D_H_AND_E
CUTOFF_REMAINDER: EXPLICIT_INDEPENDENT_TAIL_FORMULA_AND_BOUND
CUTOFF_REMAINDER_ON_NORMALIZED_BOTTOMS: O_C_EXP_MINUS_C_EXP_L_FOR_EVERY_C_LESS_THAN_PI
CUTOFF_REMAINDER_DOES_NOT_ABSORB_UNPROVED_ERROR_DERIVATIVE: true
PRIME_THRESHOLD_ERROR_AND_CUTOFF_KICKS: EXACTLY_CANCEL
W11_ASSUMED: false
ZERO_LOCATION_ASSUMED: false
VERIFIER: PAPER
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: MIXED_TERM_AND_FULL_CLIPPING_BUDGET_NOT_ARITHMETIC_SIGN
EXACT_LOCAL_CHECKS: EIGHT_GROUPS_PASSED
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
```

## 0. Ответ и точная граница

**(i) Доказано:** для буквального глобального h
\[
\left.\frac{d}{d\tau}\mathfrak k[U_\tau h]\right|_{\tau=0}=0.
\]
Это следствие полной билинейной радикальности, не предположения RH.

**(ii) Доказано точное разложение вариационных разностей** вокруг `v=P_L h`, с правильным смешанным членом, явным остатком обрезки и независимой оценкой этого остатка. Для единичных полных минимизаторов остаток действительно стремится к нулю быстрее `exp(-c exp L)` при любом фиксированном `0<c<pi`.

**Равенство именно с `L lambda_0^infinity'(L)` требует дополнительного предельного перехода.** В неатомной точке, где lambda дифференцируема и существует двусторонняя дилатационная вариация e, получено ровно
\[
L\lambda_0^{\infty\,\prime}(L)
=2\mathfrak k_L(P_LDh,e)+\Phi_L[e]+R_L[e].
\tag{0.1}
\]
Без предпосылки о вариации e доказаны двусторонние вариационные границы (8.1), а не выдуманное равенство. Ни (E), ни (F) закреплённого источника не утверждали существования всех старых атомных производных. Удалить этот guard только потому, что h беззвучна, нельзя. В атомных точках существуют разные явно вычисленные остатки `R_L^+` и `R_L^-`; их разность компенсирует искусственный излом вариации обрезанного error-профиля.

## 1. Источник, область и конвенции

S0: закреплённый POHOZAEV, 34405 bytes, 439 LF, SHA-256 и Git blob в header. Прочитаны весь файл, особенно (3.8)–(3.12), соответствующие (E),(F) чат-сводки. Байты пересчитаны локально; blob совпал с GitHub.

S1: CONFINE §1, в том же коммите, blob `1879347b72d1aa55cf506f5387de37059f929122`, SHA-256 `57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb`: полная форма, theta-функция и билинейная радикальность.

S2: CCM_INFINITE_WINDOW §§2–5, в том же коммите, blob `e8bd22411090230102b353c7c22ea25c314dde51`, SHA-256 `91e1928f76d192083263cc6d83a8e2bcafbd5a23881ac37a69f4050b1f63b600`: достижение, ограниченный непрерывный представитель, нулевой обычный след и локальная Lipschitz-регулярность нижнего уровня. Эти PAPER-поставщики наследуются; нового независимого аудита всей цепочки нет.

Протокол получен через GitHub с rh_clean, включая конец. Новых внешних теорем, quasi-RH, новых условий на нули или результатов отозванной статьи не импортировано.

**[ABSTRACT | PAPER; definitions.]** Все функции в вычислениях вещественны и чётны. Положим
\[
b=L/2,\quad I_L=(-b,b),\quad P_Lu=\mathbf1_{I_L}u,
\]
\[
(U_\tau u)(x)=e^{-\tau/2}u(e^{-\tau}x),\qquad
Du=-\tfrac12u-xu'.
\tag{1.1}
\]
`P_L` здесь — проекция на поддержку, НЕ конечная Fourier-проекция. Если генератор обозначать с противоположным знаком, знак смешанного члена тоже меняется.

Обозначим
\[
Q_{u,v}(s)=\int u(x)[v(x+s)+v(x-s)]dx,
\quad Q_u=Q_{u,u},
\]
\[
j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad m_j(s)=(sj(s))',
\quad c_*=\gamma+\log(8\pi)+\pi/2,
\]
\[
a_n=\log n,\quad\omega_n=\frac{\Lambda(n)}{\sqrt n},\quad
p(x)=\sqrt2\cosh(x/2),\quad q(x)=\sqrt2\sinh(x/2),
\]
\[
A_u=\langle p,u\rangle,\qquad B_u=\langle xq,u\rangle.
\]
На чётных функциях оба нечётных pole-паринга равны нулю по симметрии. До этого сокращения полная форма содержит оба полюсных сектора. На используемой области
\[
\mathfrak k(u,v)=-c_*\langle u,v\rangle
+\int_0^\infty j(s)[2\langle u,v\rangle-Q_{u,v}(s)]ds
-\sum_{n\ge2}\omega_nQ_{u,v}(a_n)+A_uA_v.
\tag{1.2}
\]
Все степени простых включены. Форма `k_L` есть ограничение (1.2) на поддержку в `I_L`, без изменения коэффициентов. Поэтому выражение `k_L(Dh,e)` в запросе понимается строго как `k_L(P_LDh,e)`; глобальное Dh само не принадлежит оконной области.

Далее
\[
h(x)=\sum_{n\ge1}(16\pi^2n^4e^{9x/2}-24\pi n^2e^{5x/2})e^{-\pi n^2e^{2x}}.
\]
Из S1 наследуются чётность, гладкость, все экспоненциально взвешенные нормы фиксированных производных и `k(h,u)=0` для допустимых партнёров.

### Зарегистрированные до вычислений проверки

P1: генератор (1.1) даёт положительный смешанный член `2k(Dh,e)` и нулевую глобальную вариацию h.
P2: оконная запись требует дополнительного `+2k((1-P_L)Dh,e)` в хвостовом остатке.
P3: при `L=log n` jump вариации e равен `-2 omega_n L h(b)^2`, а jump остатка — противоположному числу.
P4: малость остатка обрезки не оплачивает предел вариации e на старых внутренних атомах.

## 2. Глобальное вириальное тождество со всем источником

### Теорема 1

**[ABSTRACT | PAPER; literal global source.]** Для (1.1)
\[
\boxed{\left.\partial_\tau\mathfrak k[U_\tau h]\right|_0
=2\mathfrak k(Dh,h)=0.}
\tag{2.1}
\]
В исходниковых координатах это равенство имеет вид
\[
\boxed{
0=-\|h\|_2^2-\int_0^\infty m_j(s)Q_h(s)ds
+A_h^2+A_hB_h
+\sum_{n\ge2}\frac{\Lambda(n)\log n}{\sqrt n}Q_h'(\log n).
}
\tag{2.2}
\]
Никакая prime-power часть или полюсный вклад не отброшены.

**Доказательство.** Пространство гладких функций с любыми экспоненциальными весами устойчиво при U_tau в компактной окрестности нуля. В соответствующих фиксированных взвешенных Sobolev-нормах
\[
U_\tau h=h+\tau Dh+o(\tau).
\]
Форма (1.2) непрерывна в достаточном конечном наборе этих норм. Например, с `T_1(u)=||e^{|x|}u||_2`,
\[
|Q_{u,v}(s)|\le2e^{-s}T_1(u)T_1(v),
\quad \sum_{n\ge2}\omega_ne^{-a_n}<\infty.
\tag{2.3}
\]
Для smooth u архимедов second difference имеет L2-норму не больше `s^2||u''||_2`; его j-интеграл конечен. Pole-паринги непрерывны в весе сильнее `exp(|x|/2)`. Поэтому дифференцирование квадратичной формы законно. Билинейная радикальность h применяется к Dh, что даёт (2.1).

Для проверки всей исходниковой записи:
\[
Q_{U_\tau h}(s)=Q_h(e^{-\tau}s),\quad
\partial_\tau Q_{U_\tau h}(s)|_0=-sQ_h'(s).
\]
У скаляра `-c_*||h||^2` производная нулевая. Архимедова производная равна `int s j(s) Q_h'(s)ds`; интегрирование по частям даёт
\[
\int_0^\infty sjQ_h'=-\|h\|^2-\int_0^\infty m_jQ_h,
\]
так как `Q_h(0)=2||h||^2`, `sj(s)->1/2` при s->0 и хвост убывает. Pole-производная равна `A_h^2+A_hB_h`; нечётный pole-паринг остаётся нулевым при всех tau. Производная prime-части имеет знак плюс в (2.2). Её абсолютная сходимость следует из
\[
|Q_h'(s)|\le2e^{-s}T_1(h)T_1(h'),\qquad
\sum\omega_na_ne^{-a_n}<\infty.
\]
Те же оценки с slightly stronger weights дают доминирование для tau в окрестности нуля. Это завершает проверку всех обменов. ∎

Это тождество в одной точке tau=0. Не утверждается, что `U_tau h` радикальна при tau!=0. В частности,
\[
\widehat{Dh}(t)=\tfrac12H(t)+tH'(t),\quad H(t)=4\xi(1/2-it),
\tag{2.4}
\]
и Dh вообще не является беззвучной: нули H не обязаны быть нулями tH'. Поэтому смешанный член с Dh нельзя занулить.

### Смешанная версия без производной второго аргумента

**[ABSTRACT | PAPER.]** Если u имеет ограниченную поддержку и конечную логарифмическую энергию, либо является одной из theta-хвостовых функций ниже, то
\[
\boxed{\left.\partial_\tau\mathfrak k(U_\tau h,U_\tau u)\right|_0
=\mathfrak k(Dh,u).}
\tag{2.5}
\]
Не требуется, чтобы Du существовала в L2.

Действительно, `k(h,U_tau u)=0`, и потому
\[
\mathfrak k(U_\tau h,U_\tau u)
=\mathfrak k(U_\tau h-h,U_\tau u).
\]
Делим на tau. Первый аргумент сходится к Dh во всех нужных smooth weighted нормах, второй — к u в weighted L2. Непрерывность с фиксированным гладким первым аргументом следует из оценки в §6. Радикальность расширяется на таких партнёров не через глобальную L2-непрерывность формы: при фиксированном h его source-оператор гладок на компактах и нулевой как распределение, а tail-extension оплачивается (2.3). Это обосновывает использованное равенство. ∎

## 3. Квадратичная вариация ошибки: определение без скрытого W11

**[ABSTRACT | PAPER.]** Для произвольного вещественного чётного u в оконной области определим ТОЧНУЮ конечную разность
\[
\Phi_{L,\tau}[u]
=\frac{\mathfrak k_{Le^\tau}[U_\tau u]-\mathfrak k_L[u]}\tau,
\qquad\tau\ne0.
\tag{3.1}
\]
Она является квадратичным функционалом u. Это не новое имя неизвестного eigenvalue: её независимая исходниковая формула есть
\[
\begin{aligned}
\Phi_{L,\tau}[u]={}&
\int_0^\infty\frac{e^\tau j(e^\tau s)-j(s)}\tau
 [2\|u\|^2-Q_u(s)]ds\\
&-\sum_{n\ge2}\omega_n
 \frac{Q_u(a_ne^{-\tau})-Q_u(a_n)}\tau
+\frac{A_u(\tau)^2-A_u^2}{\tau},\\
A_u(\tau)={}&e^{\tau/2}\int p(e^\tau x)u(x)dx.
\end{aligned}
\tag{3.2}
\]
При ограниченном tau prime-сумма конечна вследствие поддержки, а не выбрасывания слагаемых. У arch-разности сингулярность `1/(2s)` сокращается. Все выражения конечны на форменной области.

Если существует двусторонний предел (3.1), обозначим его Phi_L[u]. Если существуют Q'_u(a_n) на старых атомах, то вне порогов
\[
\Phi_L[u]=-\|u\|^2-\int_0^\infty m_jQ_u+A_u^2+A_uB_u
+\sum_{a_n<L}\omega_na_nQ_u'(a_n).
\tag{3.3}
\]
В отличие от единичного f, ошибка e не нормирована: первый член здесь `-||e||^2`, НЕ -1.

Для смешанных пар используем поляризацию конечных разностей. Когда соответствующие пределы существуют, обозначим
\[
\mathcal V^\pm(u,v)=\left.\partial_{\tau,\pm}
\mathfrak k(U_\tau u,U_\tau v)\right|_0.
\]
Их регулярная часть равна
\[
\mathcal D(u,v)=-\langle u,v\rangle-\int_0^\infty m_jQ_{u,v}
+A_uA_v+\tfrac12(A_uB_v+B_uA_v).
\tag{3.4}
\]
Prime-часть есть предел `-sum omega_n [Q_uv(a_n e^-tau)-Q_uv(a_n)]/tau`. Никакая производная шероховатого второго аргумента не постулируется.

## 4. Явный оконный остаток: конечные source-формулы

Пусть f — единичный полный минимизатор при текущем L. Наследуем из S2 его ограниченный непрерывный представитель с нулевым обычным граничным следом. Положим
\[
v=P_Lh,\quad e=f-v,\quad g=Dh,\quad z=P_Lg,
\quad t=(1-P_L)h,\quad t_g=(1-P_L)g.
\tag{4.1}
\]
Тогда `f=v+e=h+e-t` и
\[
e(-b)=e(b)=-h(b).
\tag{4.2}
\]
v,z,t,t_g принадлежат нужным форменным областям: их конечные jumps дают `O(s)` в translation-square около s=0, а их хвосты имеют все экспоненциальные веса. e также лежит в оконной области. Малость e НЕ предполагается. В распределительном смысле
\[
D(P_Lh)-P_LDh=b h(b)(\delta_b+\delta_{-b}).
\]
Поэтому эти два выражения нельзя отождествлять или отдельно подставлять граничные дельта-массы в сингулярную форму. Ниже используются только конечные корреляции.

Для `0<s<L` имеются точные формулы
\[
Q_{v,e}(s)=2\int_{s-b}^{b}h(y-s)e(y)dy,
\]
\[
\boxed{
Q_{v,e}'(s)=-2h(b)e(s-b)
-2\int_{s-b}^{b}h'(y-s)e(y)dy.
}
\tag{4.3}
\]
Они используют лишь непрерывность e, не e'. При s>L корреляция нулевая. Для Q_v та же формула с `e(y)=h(y)` внутри окна. На верхнем конце
\[
Q_v'(L^-)=-2h(b)^2,\qquad
Q_{v,e}'(L^-)=-2h(b)e(b).
\tag{4.4}
\]

Определим полностью вычислимые числа
\[
V_L^\pm(v,e)=\mathcal D(v,e)
+\sum_{a_n<L}\omega_na_nQ_{v,e}'(a_n)
-2\mathbf1_{\{\pm=+,\ L=\log n\}}\omega_nLh(b)e(b),
\tag{4.5}
\]
с суммированием по возможному endpoint-атому; `V_L^pm(v,v)` аналогично. Плюс относится к расширению окна: аргумент `a_n e^-tau` тогда подходит к L слева. Все эти односторонние пределы существуют.

**[FINITE_CELL | PAPER; source-exact clipping remainder.]** Положим
\[
\boxed{
R_L^\pm[e]=V_L^\pm(v,v)+2V_L^\pm(v,e)-2\mathfrak k_L(z,e).
}
\tag{4.6}
\]
Здесь `k_L(z,e)` вычисляется по полной форме (1.2); никаких derivatives e, новых eigenvalues или неизвестной shape-скорости в (4.6) нет.

Точная поляризация конечной разности и (4.3) дают
\[
\boxed{
\frac{\mathfrak k_{Le^\tau}[U_\tau f]-\mathfrak k_L[f]}\tau
=2\mathfrak k_L(z,e)+\Phi_{L,\tau}[e]
+R_L^\pm[e]+o(1),\qquad\tau\to0^\pm.
}
\tag{4.7}
\]
До предела это же равенство точно с `R_(L,tau)` из поляризованных (3.2) вместо `R_L^pm+o(1)`. Предел остатка доказан независимо от существования предела Phi[e]. На фиксированном неатомном L оба R совпадают.

## 5. Независимое хвостовое выражение: остаток действительно от обрезки h

Формула (4.6) удобна для конечных сумм, но её малость нельзя доказывать вычитанием больших чисел. Следующая формула вычисляет тот же остаток непосредственно через внешние хвосты.

### Теорема 2

**[FINITE_CELL | PAPER; full prime-power history.]**
\[
\boxed{
R_L^\pm[e]=\mathcal V^\pm(t,t)-2\mathfrak k(g,t)
-2\mathcal V^\pm(t,e)+2\mathfrak k(t_g,e).
}
\tag{5.1}
\]
Все четыре слагаемых существуют, хотя De не предполагается. Именно последний член требуется при записи смешанного члена как `k_L(P_LDh,e)`.

**Доказательство.** Раскрываем `v=h-t` в поляризации вариации. По (2.1),(2.5),
\[
\mathcal V(v,v)=\mathcal V(t,t)-2\mathfrak k(g,t),
\quad \mathcal V(v,e)=\mathfrak k(g,e)-\mathcal V(t,e).
\]
Но `k(g,e)=k_L(z,e)+k(t_g,e)`. Подстановка в (4.6) доказывает (5.1). ∎

Для независимой реализации (5.1):
\[
Q_{t,e}(s)=2\int_{-b}^{\min(b,s-b)}h(y-s)e(y)dy,
\]
\[
Q_{t,e}'(s)=2\mathbf1_{s<L}h(b)e(s-b)
-2\int_{-b}^{\min(b,s-b)}h'(y-s)e(y)dy.
\tag{5.2}
\]
Вторая формула имеет оба односторонних значения при s=L. Для t самого:
\[
Q_t(s)=4\int_b^\infty h(x)h(x+s)dx
+2\mathbf1_{s>L}\int_{b-s}^{-b}h(x)h(x+s)dx.
\tag{5.3}
\]
Её derivative имеет только указанный corner при s=L и smooth интегралы вне него. Эквивалентная запись, удобная для оценки, с `t_1=1_(outside)h'`:
\[
Q_t'(s)=2\int t(x)t_1(x+s)dx
+2h(b)\bigl[\mathbf1_{s>L}h(s-b)-h(s+b)\bigr].
\tag{5.4}
\]
В endpoint берётся нужная односторонняя конвенция.

Вычислять V(t,t),V(t,e) следует из (3.4) и `sum_(n>=2) omega_n a_n Q'(a_n)` с (5.2)–(5.4). Здесь суммы действительно бесконечны: в хвостовом остатке сохранены и n>exp L. Для `k(t_g,e)` поддержки раздельны, поэтому
\[
\mathfrak k(t_g,e)=-\int_0^\infty jQ_{t_g,e}
-\sum_{n\ge2}\omega_nQ_{t_g,e}(a_n)+A_{t_g}A_e.
\tag{5.5}
\]
В (5.2) заменяем h на g для его корреляции. Архимедова часть (5.5) конечна даже у общей границы; её явный бюджет ниже. Никакие произведения дельта-распределений с сингулярным оператором не используются.

## 6. Полностью явный бюджет остатка

**[ABSTRACT | PAPER.]** Следующие положительные конечные числа определены без неизвестной lambda-скорости:
\[
J_2=\int_0^\infty s^2j(s)ds,\qquad
J_m=\int_0^\infty|m_j(s)|ds,
\]
\[
\mathfrak s_0=\sum_{n\ge2}\Lambda(n)n^{-3/2}\le16,
\qquad
\mathfrak s_1=\sum_{n\ge2}\Lambda(n)\log n\,n^{-3/2}\le256.
\tag{6.1}
\]
Грубые константы следуют из `Lambda<=log`, `log n<=4 n^(1/4)`, `(log n)^2<=64 n^(1/4)` и `sum_(n>=2)n^(-5/4)<=4`. Это bounds только вспомогательного tail-остатка, не новая оценка основного знака.

Положим
\[
T_1(u)=\|e^{|x|}u\|_2,\quad
\mathsf s_b(u)=\sup_{x\ge b}e^{x-b}|u(x)|,
\quad H_b=|h(b)|,
\]
\[
P_b=\|p\mathbf1_{I_L}\|_2=\sqrt{L+2\sinh b},
\quad X_b=\|xq\mathbf1_{I_L}\|_2\le bP_b,
\quad S_L^{(1)}=\sum_{a_n\le L}\omega_na_n.
\tag{6.2}
\]
Определим следующие явно вычислимые мажоранты:
\[
\begin{aligned}
K_{g,t}={}&(c_*\|g\|_2+J_2\|g''\|_2)\|t\|_2
+2\mathfrak s_0T_1(g)T_1(t)+|A_gA_t|,\\
V_t={}&(1+2J_m)\|t\|_2^2+|A_t|^2+|A_tB_t|
+2\mathfrak s_1T_1(t)T_1(t_1)\\
&+2H_b\mathfrak s_1(1+e^{2b})\mathsf s_b(h),\\
C_{t,e}={}&2J_m\|t\|_2+P_b|A_t|
+\tfrac12(X_b|A_t|+P_b|B_t|)
+2\mathfrak s_1e^bT_1(t_1),\\
C_{g,e}={}&2\mathfrak s_0e^bT_1(t_g)+P_b|A_{t_g}|.
\end{aligned}
\tag{6.3}
\]
Все величины с t,t_1,t_g или mathsf s_b являются внешними theta-хвостами.

Тогда для каждой стороны при любом L>0:
\[
\boxed{
|R_L^\pm[e]|\le
V_t+2K_{g,t}
+2(C_{t,e}+C_{g,e})\|e\|_2
+\bigl(4H_bS_L^{(1)}+2\pi\mathsf s_b(g)\bigr)\|e\|_\infty.
}
\tag{6.4}
\]
Атом при L включён в верхний бюджет независимо от выбранной стороны.

**Проверка каждого слагаемого.** Исходниковая оценка с гладким первым аргументом g даёт
\[
|\mathfrak k(g,t)|\le K_{g,t}:
\]
используем L2-оценку второй разности `s^2||g''||` для архимедова интеграла, (2.3) для простых и сохраняем полюсное произведение. В (5.4) регулярная часть производной не превосходит `2e^-s T1(t)T1(t1)`. Также
\[
|h(a_n+b)|\le e^{-a_n}\mathsf s_b(h),
\quad \mathbf1_{a_n\ge2b}|h(a_n-b)|\le e^{2b-a_n}\mathsf s_b(h).
\]
Вместе с (3.4) это доказывает `|V^pm(t,t)|<=V_t`.

В (5.2) продифференцированный интеграл ограничен величиной
`2e^-s T1(t1)T1(e)`, где `T1(e)<=e^b||e||`. Граничный член даёт не больше `2H_b S_L^(1)||e||infinity`. Архимедов и полюсный члены дают остальную часть C_(t,e). Следовательно,
\[
|\mathcal V^\pm(t,e)|\le C_{t,e}\|e\|_2
+2H_bS_L^{(1)}\|e\|_\infty.
\]
В (5.5) prime- и pole-части не превосходят `C_(g,e)||e||`. Для архимедовой части Фубини с модулями даёт
\[
\int_0^\infty j(s)|Q_{t_g,e}(s)|ds
\le2\|e\|_\infty\int_b^\infty|g(x)|
       \int_{x-b}^{x+b}j(s)ds\,dx.
\]
Используя `|g(b+r)|<=mathsf s_b(g)e^-r`, ограничиваем правую часть величиной
\[
2\mathsf s_b(g)\|e\|_\infty
\int_0^\infty j(s)(1-e^{-s})ds
=\pi\mathsf s_b(g)\|e\|_\infty.
\]
Последний интеграл равен ровно pi/2 после замены `z=e^(-s/2)`. Поэтому
`|k(t_g,e)|<=C_(g,e)||e||+pi mathsf s_b(g)||e||infinity`.
Объединение четырёх независимо оценённых слагаемых (5.1) доказывает (6.4). ∎

### Следствие: остаток обрезки действительно мал на выбранных нижних векторах

**[COFINAL_FAMILY | PAPER; используется явный L-infinity поставщик S2.]** Для каждого фиксированного `0<c<pi`, равномерно по всем нормированным чётным нижним собственным функциям на окне L,
\[
\boxed{|R_L^\pm[f-P_Lh]|=O_c(e^{-c e^L})\qquad(L\to\infty).}
\tag{6.5}
\]
Это не утверждение о малости e.

Полное сравнение роста имеет следующий вид. Для каждого фиксированного порядка производной r theta-ряд даёт при x>=0:
\[
|h^{(r)}(x)|\le C_r e^{(2r+9/2)x}e^{-\pi e^{2x}}.
\]
Константа конечна благодаря суммируемости `n^(2r+4) exp[-pi(n^2-1)]`; дифференцирование порождает лишь фиксированный полином от `pi n^2 e^(2x)`. Та же оценка с дополнительным фиксированным полиномом от x действует для g=Dh и нужных производных. Интегрирование хвостов и взятие mathsf s_b поэтому ограничивают коэффициенты (6.4) величиной
\[
C\exp(C L-\pi e^L).
\tag{6.6}
\]
Кроме того, `||e||<=1+||h||`. Для оценки `||e||infinity` S2 предоставляет
\[
\|f\|_\infty\le\tfrac12e^{\gamma_L}
+\|p_L\|_2\|p_L\|_\infty
 \frac{e^{\gamma_L}-1}{\gamma_L},\quad
\gamma_L=\lambda_0^\infty(L)+c_*+2\sum_{a_n<L}\omega_n\ge0.
\tag{6.7}
\]
При gamma_L=0 дробь имеет значение 1. Нормированный постоянный тест на интервале даёт
\[
\lambda_0^\infty(L)\le-c_*+
\frac2L\int_0^L sj(s)ds+2\int_L^\infty j(s)ds
+\frac{32\sinh^2(L/4)}L.
\tag{6.8}
\]
Не включённый в эту ВЕРХНЮЮ оценку prime-вклад неположителен именно на данном постоянном тесте; из оператора он не удалён. Из `Lambda<=log` следует
`gamma_L<=C(1+L)e^(L/2)` для больших L. Значит,
\[
\|e\|_\infty\le\exp(C(1+L)e^{L/2}).
\]
Подстановка этой оценки и (6.6) в (6.4) доказывает (6.5). На исходных значениях L=log m получается `O_c(exp(-c m))`. Это оценка только остатка обрезки, НЕ Phi[e] и НЕ смешанного члена. ∎

## 7. Prime-пороги: искусственный излом ошибки обязан сократиться

**[FINITE_CELL | PAPER.]** Пусть L=log n и omega_n>0. Непрерывный граничный след (4.2) даёт
\[
Q_e(L-\delta)=2h(b)^2\delta+o(\delta).
\]
Поэтому вклад этого единственного атома в разность правой и левой вариаций e равен
\[
\Delta_n\Phi[e]=-2\omega_nLh(b)^2.
\tag{7.1}
\]
Из (4.4)–(4.6),
\[
\boxed{R_L^+[e]-R_L^-[e]=+2\omega_nLh(b)^2.}
\tag{7.2}
\]
Их сумма равна нулю. Это согласуется с нулевым следом настоящей f и унаследованным эффектом `o(tau)` входящего атома. Сокращение не предоставляет производные корреляций на других старых атомах. Для целого, не являющегося степенью простого, omega_n=0 и оба показанных излома отсутствуют.

## 8. Что позволяет заключить точная минимальность

**[ABSTRACT | PAPER; без W11.]** В любой точке дифференцируемости унаследованной локально Lipschitz-функции lambda минимальность и (4.7) дают
\[
\boxed{
2\mathfrak k_L(z,e)+R_L^-[e]
 +\limsup_{\tau\uparrow0}\Phi_{L,\tau}[e]
\le L\lambda_0^{\infty\,\prime}(L)
\le2\mathfrak k_L(z,e)+R_L^+[e]
 +\liminf_{\tau\downarrow0}\Phi_{L,\tau}[e].
}
\tag{8.1}
\]
Пределы могут принимать расширенные вещественные значения; это непосредственная информация исходника. При делении вариационной оценки на отрицательное tau знак неравенства меняется.

**[ABSTRACT | CONDITIONAL; точная дополнительная предпосылка.]** В неатомной точке L существование конечного двустороннего предела Phi_L[e] превращает (8.1) в (0.1). Достаточно существования `Q_e'(log n)` на каждом поддержанном старом prime-power сдвиге. Требуется конкретное свойство корреляции, не W11. На пороге используются два односторонних предела и (7.2); равенство следует, если полные выражения с обеих сторон (8.1) совпадают. Существование этих пределов для каждого минимизатора при каждом L не утверждается.

Дифференцируемость минимума сама по себе не дифференцирует каждый касающийся его тест: у абстрактного семейства `diag(|tau|,0)` минимум постоянно равен 0, но первая координата минимальна при tau=0 и имеет пробную энергию `|tau|`. Это не опровержение более сильной CCM-теоремы. Контроль выделяет шаг, который не следует из одного неравенства Рэлея.

Итак, глобальное вириальное тождество доказано, обрезка оплачена, а классическая формула доказана при существовании исходниковой вариации ошибки. Безусловное классическое равенство для всех оконных минимизаторов пока не получено. Определить R как разность неизвестной производной lambda и остальных членов означало бы спрятать этот вопрос; здесь R независимо вычислен в (5.1)–(6.4).

## 9. Журнал утверждений и следующий дискриминатор

| Claim | Scope | Verifier | Boundary |
|---|---|---|---|
| Global virial (2.1)–(2.2) | ABSTRACT | PAPER | All primes and poles; inherited bilinear radicality |
| Mixed differentiation (2.5) | ABSTRACT | PAPER | Smooth h in first slot, no derivative of second |
| Window quotient (4.7) | FINITE_CELL | PAPER | Exact finite-difference expansion; both sides at atoms |
| Independent tail remainder (5.1), budget (6.4) | FINITE_CELL | PAPER | All exterior primes retained |
| Uniform bottom clipping price (6.5) | COFINAL_FAMILY | PAPER | Uses inherited boundedness of normalized minimizers |
| Equality (0.1) | ABSTRACT | CONDITIONAL | Error correlation limits and lambda differentiability |

Два оставшихся представления перед любыми большими вычислениями:

1. **Регулярность корреляций выбранного минимизатора на атомах.** Доказать сходимость конечной суммы в (3.2), используя полное слабое eigen-equation. Высокая различающая сила / высокая аналитическая цена. Не выводить её из малости хвоста h.
2. **Сохранить конечные дилатационные разности и применить слабое eigen-equation непосредственно.** Искать знаковую оценку полной разности после вычитания известных смешанного и хвостового членов. Это может работать без точечного предела Phi. Высокая различающая сила / средняя цена представления, высокая цена исходникового знака.

Это не исчерпывает методы NOESCAPE или RH. Дискриминатор нуль-согласованного результата — пара односторонних атомных разностных отношений e на старых сдвигах, с сохранением знака и сравнением полных границ (8.1). Собственное вириальное тождество h равно нулю и не различает оставшийся вопрос.

### Единственная CODEX DIRECTIVE

`AUDIT_VIRIAL_CUTOFF_AND_TEST_OLD_ATOM_CORRELATION_LIMIT`

Сначала проверить только на чтение (2.5), (5.1), каждый коэффициент (6.4) и два противоположных граничных излома. Затем исследовать только существование общего двустороннего предела конечного old-atom отношения для настоящего единичного минимизатора в неатомной длине. Сохранить источник; не предполагать W11, простоту или RH-оценку. Успех: конечный предел с независимо оплаченной равномерностью, предоставляющий (0.1). Отчёт о неудаче: конкретный старый сдвиг и оставшаяся оценка регулярности, а не уже оплаченная обрезка. Код ниже проверяет только алгебру, не этот аналитический переход.

### Consumer-first closeout

DOWNSTREAM_CONSUMER: source-geometric control of full-window bottoms, then the unchanged RH/noescape entrance.
ACTUAL_CONSUMER_REQUIREMENT: a useful signed drift or retention estimate; a classical derivative at every L is not established as necessary.
ORIGINAL_REQUESTED_OBJECT: global virial plus classical window expansion.
ORIGINAL_OBJECT_IS: UNKNOWN as a necessary interface; part (i) established, part (ii) conditional at the specified derivative step.
KNOWN_WEAKER_INTERFACES: exact finite-difference source estimates and the Dini sandwich (8.1).
FAILURE_TYPE: NO_DERIVATION of old-atom correlation limits for all minimizers.
EPISTEMIC_STATUS: RESEARCH_DEBT, not mathematical death.
REOPEN_TRIGGER: eigenfunction-specific correlation regularity or a signed finite-difference supplier.
NOVELTY_AXIS: explicit full cutoff remainder and its uniform exponentially small price.

P1–P3 подтверждены аналитическим выводом и соответствующими точными проверками. P4 сохраняет действительную границу результата: малый остаток обрезки доказан, отсутствующая производная ошибки — нет. Оставшийся RH-знак не переименован в теорему. Не повторять `Dh is radical`, `P_L Dh=D(P_L h)` или `lambda differentiable implies every trial differentiable`.

Отдельный проверяющий, Lean и Arb не запускались. Доставка этого нового артефакта не изменяет исходники, унаследованные вердикты или файлы состояния. Загрузка файла не повышает математический статус результата.

## Приложение A. Исполненные точные локальные проверки

Следующий скрипт исполнен; все восемь групп прошли. Он проверяет знаки и конечную алгебру, не сходимость бесконечных сумм, унаследованные аналитические поставщики или существование Phi[e].

```python
#!/usr/bin/env python3
"""Exact local checks of the CCM virial/cutoff identities, not an RH proof.
Run: uv run --with sympy PROSHKA_VIRIAL_CUTOFF_CHECKS_2026-11-02.py
These checks do not certify the analytic imports, infinite sums, or the
existence of the error-profile dilation derivative.
"""
import sympy as s


def main() -> None:
    x, y, a, tau = s.symbols('x y a tau', real=True)
    b, ell, omega = s.symbols('b ell omega', positive=True)
    h = s.Function('h')
    U = s.exp(-tau/2)*h(s.exp(-tau)*x)
    D = -h(x)/2-x*s.diff(h(x), x)
    assert s.simplify(s.diff(U, tau).subs(tau, 0)-D) == 0
    Q = s.Function('Q')
    assert s.simplify(s.diff(Q(a*s.exp(-tau)), tau).subs(tau, 0)
                      + a*s.diff(Q(a), a)) == 0
    print('PASS 1 generator and correlation scaling signs')

    q = s.symbols('q', positive=True)
    j = s.exp(-q/2)/(1-s.exp(-2*q))
    assert s.limit(q*j, q, 0, dir='+') == s.Rational(1, 2)
    assert s.limit(q*j, q, s.oo) == 0
    assert s.limit(s.diff(q*j, q), q, 0, dir='+') == s.Rational(1, 4)
    print('PASS 2 archimedean boundary constant and regularity')

    hp = 1+x*x
    phi = 1+x**4
    gp = -hp/2-x*s.diff(hp, x)
    lhs = s.integrate(hp*(phi/2+x*s.diff(phi, x)), (x, -b, b))
    rhs = s.integrate(gp*phi, (x, -b, b)) \
        + b*hp.subs(x,b)*(phi.subs(x,b)+phi.subs(x,-b))
    assert s.simplify(lhs-rhs) == 0
    assert s.simplify(s.integrate(gp*hp, (x,-b,b))
                      + b*hp.subs(x,b)**2) == 0
    print('PASS 3 sharp-cutoff distribution and interior trace sign')

    ep = 2-3*y*y
    hp_shift = 1+(y-a)**2
    qve = 2*s.integrate(hp_shift*ep, (y,a-b,b))
    dqve = -2*(1+b*b)*ep.subs(y,a-b) \
        -2*s.integrate(2*(y-a)*ep, (y,a-b,b))
    assert s.simplify(s.diff(qve,a)-dqve) == 0
    qte = 2*s.integrate(hp_shift*ep, (y,-b,a-b))
    dqte = 2*(1+b*b)*ep.subs(y,a-b) \
        -2*s.integrate(2*(y-a)*ep, (y,-b,a-b))
    assert s.simplify(s.diff(qte,a)-dqte) == 0
    print('PASS 4 interior and exterior mixed correlation derivatives')

    Vee,Vtt,Vhe,Vht,Vte,kze,ktge,kgt = s.symbols(
        'Vee Vtt Vhe Vht Vte kze ktge kgt', real=True)
    expansion = Vee+Vtt+2*Vhe-2*Vht-2*Vte
    expansion = expansion.subs({Vhe:kze+ktge,Vht:kgt})
    residual = Vtt-2*kgt-2*Vte+2*ktge
    assert s.expand(expansion-(Vee+2*kze+residual)) == 0
    print('PASS 5 full tail remainder including exterior Dh term')

    hb,eb = s.symbols('hb eb', real=True)
    error_kick = -2*omega*ell*eb**2
    cut_kick = -2*omega*ell*hb**2
    mixed_kick = -2*omega*ell*hb*eb
    residual_kick = cut_kick+2*mixed_kick
    assert s.simplify(residual_kick.subs(eb,-hb)-2*omega*ell*hb**2) == 0
    assert s.simplify((error_kick+residual_kick).subs(eb,-hb)) == 0
    print('PASS 6 prime-threshold clipping/error kicks cancel')

    assert s.simplify(j*(1-s.exp(-q))
                      -s.exp(-q/2)/(1+s.exp(-q))) == 0
    z = s.symbols('z', positive=True)
    assert s.integrate(2/(1+z*z), (z,0,1)) == s.pi/2
    print('PASS 7 exterior archimedean budget integral pi/2')

    # ABSTRACT guard: a differentiable minimum does not differentiate
    # every touching trial. This is not a CCM counterexample.
    t = s.symbols('t', real=True)
    trial = s.Abs(t)
    right = s.limit(trial/t, t, 0, dir='+')
    left = s.limit(trial/t, t, 0, dir='-')
    assert (left, right) == (-1, 1)
    assert left <= 0 <= right
    print('PASS 8 differentiable-minimum / nondifferentiable-trial guard')
    print('ALL 8 EXACT LOCAL GROUPS PASSED')


if __name__ == '__main__':
    main()
```

Зафиксированный stdout:
```text
PASS 1 generator and correlation scaling signs
PASS 2 archimedean boundary constant and regularity
PASS 3 sharp-cutoff distribution and interior trace sign
PASS 4 interior and exterior mixed correlation derivatives
PASS 5 full tail remainder including exterior Dh term
PASS 6 prime-threshold clipping/error kicks cancel
PASS 7 exterior archimedean budget integral pi/2
PASS 8 differentiable-minimum / nondifferentiable-trial guard
ALL 8 EXACT LOCAL GROUPS PASSED
```
