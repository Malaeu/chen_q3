# STATUS: TRY_SCREW_LINE_WHOLE_HISTORY_SIGNED_PREDICTION

```yaml
OPERATIVE_CLASS: TRY_SCREW_LINE_WHOLE_HISTORY_SIGNED_PREDICTION
REQUEST: SCREW_LINE_PREDICTION_v1
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_REQUEST_IN_CHAT
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: fcb70c5dd82a434dd77f4ea5c001cb6715a917d5
INBOX_SOURCE: ab8d123e124f0a32d04ac6711a770a41073319fa
SOURCE_SCREW_BLOB: b56a16a0540ed3f81858c113bc48de68c909b8c8
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
OBJECT: ONE_SOURCE_KERNEL_AND_ITS_WHOLE_HISTORY_PREDICTION_FUNCTIONAL
UNCONDITIONAL_SOURCE_NONNEGATIVE_CONTINUATION: NOT_PROVED
EXACT_ARITHMETIC_PREDICTION_IDENTITY: PROVED_PAPER
INFINITE_HISTORY_DUAL_NORM_FORMULA: PROVED_PAPER_WITH_EXPLICIT_PSD_HISTORY_GUARD
EXACT_INDEX_LINK: PROVED_PAPER
FINITE_HISTORY_LOCAL_INNOVATION_LAW: PROVED_PAPER
LOCAL_LAW_IS_A_ZETA_DISCRIMINATOR: false
PURE_POINT_IMPLIES_ZERO_FINITE_PAST_ERROR: REFUTED_ABSTRACT_THEOREM_SHAPE
EDGE_RATIO_EQUALS_OPTIMAL_PREDICTION_ERROR: NOT_ASSERTED
RH_JUDGE: CONDITIONAL_PASS_WITH_UNIFORM_UPPER_AND_RECURRENCE
W_JUDGE: PROVED_NEGATIVE_UPPER_ON_DYADIC_ORIGINAL_CONSTANT_MODES
W_NUMERICAL_FIRST_NEGATIVE_INCREMENT_BLOCK: 6
W_NUMERICAL_FIRST_NEGATIVE_PIVOT: 6
NEW_CCM_EIGENSYSTEMS: 0
NUMERICAL_DPS: [45,65,75]
INDEPENDENT_ANALYTIC_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
ADDITIONAL_PROGRESS: EXACT_SOURCE_RETURN_AND_LOCAL_LAW
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 4
```

Ы. Рассмотрен один объект: полный kernel g=-Psi и ошибка его продолжения по всему заданному прошлому. Получено точное арифметическое тождество и проверяемый отрицательный контроль. Не получена безусловная неотрицательность ошибки для действительной zeta. Теория предсказания не может быть импортирована как доказательство этого знака: ее положительная спектральная мера является предпосылкой, которая здесь еще требует доказательства.

Особенно важны два результата. Для любого фиксированного положительного конечного прошлого короткий шаг имеет положительный главный член h log(1/h), причем такой же закон имеет посаженный мир. А чисто точечный спектр НЕ заставляет ошибку предсказания по конечному прошлому быть нулевой. Оба shortcut исключены без отрицания исходной арифметической цели.

## 1. Источник, координаты и граница Hilbert-интерпретации

**[ABSTRACT / PAPER; E,F,A,LA.]** Наследуем ровно заданный g=-Psi и

\[
 K(s,t)=g(s-t)-g(s)-g(-t),\qquad g(0)=0.
 \tag{1}
\]

Он определен без RH, реален, четен и непрерывен. Безусловно это эрмитово ядро, а не уже доказанная ковариация случайного процесса. Слова «винтовая линия в Hilbert-пространстве» и «дисперсия» становятся буквальными лишь после положительности соответствующего Gram-блока. До этого ниже используется подписанный квадратичный функционал.

Пусть B_g(mu,nu)=integral integral K(s,t) dmu(s) dnu(t) для вещественных компактных конечных мер. Для мер полной массы нуль члены g(s),g(-t) исчезают. Исходный поставщик дает

\[
 B_g(\mu_f,\mu_h)=\mathfrak k(f,h),\quad
 \mu_f=f'_{\rm int}1_{(-b,b)}dx+f(-b)\delta_{-b}-f(b)\delta_b.
 \tag{2}
\]

Все физические нормы и N=m,L=log(m) сохранены. Формула также применима к компактным ступенчатым профилям: их производные — конечные атомные меры, архимедова энергия конечна, поскольку ||f-T_s f||^2=O(s) у нуля. Это расширение тестов для описания самой кривой; оно не заменяет исходный конечный cosine-carrier.

Конечная матрица CCM является ограничением формы, не тождественно бесконечномерным оператором Фридрихса Suzuki A_a. Для нужных endpoint-масс используется (2), а не молчаливое включение cosine-функций в H_0^1.

## 2. Одна лемма полного предсказания

**Лемма. [ABSTRACT / PAPER; LA,A.]** Зафиксируем прошлые функционалы nu_1,...,nu_n и новый nu_*. Это могут быть точки delta_s-delta_0 или реальные меры mu_f из (2). Обозначим

\[
 K_{ij}=B_g(\nu_i,\nu_j),\quad b_i=B_g(\nu_i,\nu_*),\quad d=B_g(\nu_*,\nu_*),
\]
\[
 \mathcal E(a)=B_g\left(\nu_*-\sum a_i\nu_i,\nu_*-\sum a_i\nu_i\right)
 =d-2a^Tb+a^TKa.
 \tag{3}
\]

Если K>=0 и b in ran K, то

\[
 a_*=K^\dagger b,\qquad
 \boxed{\mathcal E(a)=\sigma^2+(a-a_*)^TK(a-a_*),\quad
 \sigma^2=d-b^TK^\dagger b.}
 \tag{4}
\]

Это точное разложение на неотрицательный квадрат и ПОДПИСАННЫЙ остаток. Знак остатка не предполагается. Если K>=0, но b notin ran K, inf_a E(a)=-infinity. Если у K уже есть отрицательное направление, тот же инфимум равен -infinity.

Доказательство: раскрыть квадрат при Ka_*=b. При нарушении range-condition выбрать v in ker K с v^Tb!=0 и a=tv. При отрицательном v^TKv взять a=tv и |t|->infinity. Это одновременно обрабатывает точную нулевую границу, а не заменяет ее численным порогом.

### Весь прошлый отрезок, а не выбранная сетка

Пусть P — линейное пространство ВСЕХ конечных комбинаций прошлых функционалов на заданном отрезке. Положим q(u)=B_g(u,u), ell(u)=B_g(u,nu_*). При q>=0 на P определим

\[
 \|\ell\|_{P,*}^2=\sup_{q(u)>0}\frac{|\ell(u)|^2}{q(u)},
 \tag{5}
\]

с бесконечным значением, если ell не зануляется на ker q. Тогда точно, как расширенное вещественное число,

\[
 \boxed{\Sigma_P^2=d-\|\ell\|_{P,*}^2
       =\inf_{u\in P}\{d-2\ell(u)+q(u)\}.}
 \tag{6}
\]

Если норма конечна, доказательство — теорема Рисса в пополнении P/ker q и завершение квадрата. Если бесконечна, сначала оптимизировать масштаб одного u, затем взять последовательность с растущим отношением в (5). Если q имеет отрицательное направление, инфимум снова -infinity, и положительной «ошибки предсказания» уже нет.

Формула (6) сохраняет всю историю. Дискретные (4) — ее ограничения; их инфимум по всем конечным историям равен (6). Никакого обмена пределов inverse/mesh без guard не произведено.

## 3. Полный арифметический возврат этого же остатка

**[FINITE_CELL / PAPER; E,F,I,A,LA.]** Для точек 0<s_1<...<s_n<=a<t зададим

\[
 f_a(x)=1_{(0,t)}(x)-\sum_{i=1}^n a_i1_{(0,s_i)}(x).
 \tag{7}
\]

Его распределительная производная есть минус остаточная мера в (3); общий знак не меняет квадрат. Поэтому

\[
 \boxed{\mathcal E(a)=\mathfrak k[f_a].}
 \tag{8}
\]

Введем Q_f(u)=2 integral f(x)f(x+u)dx, c_*=gamma_E+log(8pi)+pi/2,

\[
 j(u)=\frac{e^{-u/2}}{1-e^{-2u}},\quad
 H[f]=\int_0^\infty j(u)\|f-T_uf\|_2^2du,\quad
 A_\pm(f)=\int e^{\pm x/2}f(x)dx.
\]

Тогда искомое точное тождество через весь источник:

\[
 \boxed{\sigma^2=
 H[f_*]-c_*\|f_*\|_2^2
 -\sum_{2\le n\le e^t}\frac{\Lambda(n)}{\sqrt n}Q_{f_*}(\log n)
 +2A_+(f_*)A_-(f_*),\quad f_*=f_{a_*}.}
 \tag{9}
\]

Без существования конечного минимизатора правая часть берется под inf в (6). Все простые степени включены; атом на длине полной поддержки дает Q_f(t)=0. Архимедов интеграл идет до infinity. Оба полюса сохранены: для нечетного/непаритетного step-предиктора pole-term нельзя заменить одним положительным квадратом. В исходном четном carrier он равен |<sqrt(2)cosh(x/2),f>|^2.

Для явного вычисления положим t_0=t,c_0=1,t_i=s_i,c_i=-a_i. Тогда

\[
 \|f_a\|^2=\sum_{i,j}c_ic_j\min(t_i,t_j),\qquad
 Q_{f_a}(u)=2\sum_{i,j}c_ic_j\min\bigl(t_i,(t_j-u)_+\bigr),\quad u\ge0.
 \tag{10}
\]

A_+=2 sum c_i(e^{t_i/2}-1), A_-=2 sum c_i(1-e^{-t_i/2}). Таким образом, (9) — конечные явные арифметические суммы и интегралы от кусочно-линейных корреляций. Предсказатель a_* определяется тем же источником, не подбирается из неизвестного положительного спектра.

На всем прошлом [0,a] функция (7) равна 1 на (a,t). Поэтому (6) есть ровно вариационный минимум полной формы на профилях с фиксированным конечным терминальным куском. Это не емкость одного endpoint f(b), уже отвергнутая данными.

### Что показывает Euler, а чего не показывает

Пусть один арифметический вес c_n=Lambda(n)/sqrt(n) временно варьируется, остальные члены g фиксированы. При K>0 оптимальный a_* гладок по этому весу. Теорема об огибающей или прямое дифференцирование (4) дает

\[
 \boxed{\frac{\partial\sigma^2}{\partial c_n}=-Q_{f_*}(\log n).}
 \tag{11}
\]

Производная a_* сокращается из-за Ka_*=b. Это зависимость от ВСЕЙ предшествующей пружины через f_*, а не независимый закон одного удара.

Положительность c_n не задает знак Q_{f_*}. Например, среди допустимых остатков 1_(0,2a)-alpha 1_(0,a) корреляция на сдвиге a равна 2a(1-alpha). Этот пример не утверждает, что произвольная alpha оптимальна для zeta: он точно показывает, какое дополнительное свойство оптимизатора пришлось бы доказать. В (9) знак H виден, но постоянная, source-correlations и оба полюса не исчезли. Новая односторонняя совместная оценка правой части не получена.

## 4. Точный индекс и Toeplitz-координаты той же кривой

**[FINITE_CELL / PAPER; LA.]** При обратимом K конгруэнция дает

\[
 n_-\begin{pmatrix}K&b\\b^T&d\end{pmatrix}
 =n_-(K)+1_{\{\sigma^2<0\}}.
 \tag{12}
\]

Для K>=0 и b in ran K верно то же с нулевым первым индексом. При b notin ran K появляется отрицательное направление даже если число d-b^TK^dagger b положительно. Точный planted algebra control: K=[0],b=[1],d=1; псевдо-Schur число равно 1, но determinant полного блока равен -1. Значит, «первый отрицательный sigma» требует range-guard, а не только подсчета знаков scalar pivots.

Индекс f6c9cd8 при пороге mu относится к A-mu I. Его исключаемый блок D-mu I отрицателен, поэтому точный остаток

\[
 G-\mu I+B(\mu I-D)^{-1}B^T
 \tag{13}
\]

имеет плюс перед coupling. Это signed Schur-объект, не ковариационная дисперсия положительного прошлого. При mu=0 и положительном прошлом обычное предсказание дает минус BD^dagger B^T. Эти два разных знака не смешиваются.

### Равномерные отсчеты не изменяют объект

Для Delta>0 положим X_j=x(jDelta)-x(0), Y_j=X_j-X_(j-1). Формально определяем их Gram непосредственно через K, не предполагая существования процесса. Тогда

\[
 r_k=\Psi((k+1)\Delta)+\Psi((k-1)\Delta)-2\Psi(k\Delta),\qquad
 T_n=(r_{i-j})_{i,j=1}^n.
 \tag{14}
\]

Переход Y->X — нижнетреугольная матрица единиц с determinant 1. Поэтому, если прошлый блок положительно определен,

\[
 \boxed{\sigma_n^2=\frac{\det T_n}{\det T_{n-1}},\qquad
 \det\operatorname{Gram}(X_1,...,X_n)=\det T_n.}
 \tag{15}
\]

Здесь sigma_n предсказывает новую точку по ВСЕМ n-1 прежним точкам, эквивалентно новый increment по всем прежним increments. Все r_k вычисляются из исходной формулы Psi. Для k>=1 prime-вклад равен

\[
 -\sum_n\frac{\Lambda(n)}{\sqrt n}
       (\Delta-|\log n-k\Delta|)_+,
 \tag{16}
\]

а в r_0 он равен -2 sum c_n(Delta-log n)_+. Это точное сглаживание арифметической меры треугольным kernel; положительность Toeplitz-матрицы из него еще не следует.

## 5. Положительный локальный закон, который проходит также w-судью

**[FINITE_CELL / PAPER; F,A,LA.]** Для фиксированного прошлого 0<s_1<...<s_n=a с K>0 и h->0+:

\[
 \boxed{\sigma^2(a+h\mid s_1,...,s_n)
 =h\log(1/h)-2A h+O_K(h^2\log^2h),\quad
 A=\tfrac12(\log(2\pi)-1+\gamma_E).}
 \tag{17}
\]

Константа зависит от всего фиксированного прошлого, в частности от ||K^-1||. Она НЕ равномерна при сгущении истории или увеличении окна.

Доказательство. Из явного arch-источника, до первого prime-порога,

\[
 g(h)=\tfrac12h\log h+A h+O(h^2).
\]

Этот разбор также выписан в Suzuki 2606.09096, (2.2). Предсказывая increment x(a+h)-x(a), получаем точно

\[
 \sigma^2=2\Psi(h)-c_h^TK^{-1}c_h,\quad
 (c_h)_i=K(s_i,a+h)-K(s_i,a).
 \tag{18}
\]

Для i<n функция g локально Lipschitz в ненулевых аргументах, в том числе на prime-изломах, так что (c_h)_i=O(h). Последний компонент равен g(h)-g(a+h)+g(a)=O(h log h). Поэтому subtracted square есть O_K(h^2 log^2h), что доказывает (17).

Гладкая посаженная четверка добавляет к g(h) только O(h^2) и сохраняет локальную Lipschitz-регулярность при h!=0. Следовательно, (17) остается верным в w-мире для каждого фиксированного положительного прошлого. Для симметричных even-окон y(b)=x(b)-x(-b) тот же расчет дает ведущий член 2h log(1/h): движутся два конца. Это не замена исходного оператора, а его точная четная комбинация.

Таким образом, один положительный бесконечно малый шаг не является нужным дискриминатором. Последовательность гарантированных шагов может иметь конечную суммарную длину, когда ||K^-1|| растет. Нельзя из pointwise local continuation вывести global continuation без равномерного контроля всей истории. Утверждение такого вывода опровергается w-миром ниже.

## 6. Три разных смысла «всего прошлого»

**[ABSTRACT / PAPER; LA,A.]** Если положительное непрерывное ядро уже задано до endpoint t включительно, то предсказание x(t) по всем s<t, сколь угодно близким к t, имеет ошибку ровно нуль:

\[
 0\le\Sigma^2\le\|x(t)-x(t-h)\|^2=2\Psi(h)\longrightarrow0.
 \tag{19}
\]

Для этого не нужна чистая точечность спектра. Поэтому запись «sigma^2(t) по всему [0,t)» без положительного горизонта вырождается и не объясняет численный edge-law.

Под RH можно реализовать X(t) в l2 реальных нулей координатами sqrt(nu_gamma)(e^{-i gamma t}-1)/gamma. Сумма S=sum nu_gamma/gamma^2 конечна. Для любого конечного прошлого при доступном последнем наблюдении a:

\[
 \boxed{0\le\Sigma^2(a+h\mid past)\le2\Psi(h)\le4S.}
 \tag{20}
\]

Это условный RH-контроль без положительного lift с расходящимся весом. Ограничение 3ce4968 не обходится новым перемасштабированием.

Для бесконечного удаленного прошлого ошибка также равна нулю, но по другой причине. Для любого конечного набора частот существуют сколь угодно большие почти-периоды q, на которых все e^{i gamma q} близки к 1; это следует из одновременного диофантова приближения на конечном торе. Выбирая сначала конечный спектральный head и затем q, получаем

\[
 \|X(t)-X(t-q)\|^2
 \le\text{small finite-head error}+4\sum_{\text{tail}}\nu_\gamma/\gamma^2\to0.
 \tag{21}
\]

При q->infinity наблюдение t-q принадлежит удаленному прошлому. Доказательство не дает скорости по log(m) и не отождествляет эти нормы с полным ||A_m Q_m||.

### Точный pure-point контрпример конечному прошлому

Возьмем положительный периодический kernel со спектральными весами 1/n^2, n in Z\{0}, и периодом P=2pi. Его anchored covariance на 0<=s,t<=P равна

\[
 K_{\rm per}(s,t)=P\min(s,t)-st.
 \tag{22}
\]

Это следует из sum_(n!=0)e^{inu}/n^2=pi^2/3-pi|u|+u^2/2. Для 0<a<a+h<P лучший предиктор по ВСЕМУ [0,a] равен

\[
 \frac{P-a-h}{P-a}X(a),
\]

поскольку его остаток ортогонален каждому X(s),s<=a. Его ошибка

\[
 \boxed{\Sigma^2_{[0,a]}(a+h)=\frac{P h(P-a-h)}{P-a}>0.}
 \tag{23}
\]

Спектр чисто точечный, процесс даже периодичен, но конечный прошлый отрезок не предсказывает finite-horizon будущее точно. Полный бесконечный past предсказывает: он содержит предыдущий период. Это строгий ABSTRACT-контроль, не другая zeta.

### Граница импорта Колмогорова--Сегё--Крейна

THEOREM: спектральное представление, геометрия линейного предсказания и результаты о singular/regular компонентах действуют для положительных ковариаций. CONDITIONAL: применение к полной кривой zeta допустимо после установления ее положительности; под RH спектральная мера чисто точечная. NOT A SUPPLIER: положительность спектральной меры нельзя получить, объявив kernel ковариацией и затем применив формулу Сегё. В w-мире нет положительной меры на реальной оси, реализующей его исходный kernel. Замена комплексных тонов действительными с положительными весами меняет объект.

Szego regular spectral-factor formula относится к абсолютно непрерывной части; для чисто точечного спектра плотность равна нулю почти всюду. Она не дает нового положительного finite-past резерва. Формула (21) доказывает нужное условное infinite-past утверждение напрямую, без сингулярной подстановки в regular formula.

## 7. Точная связь с четным окном, тихими формами и edge-law

**[FINITE_CELL / PAPER; LA,A.]** Обозначим y(r)=x(r)-x(-r) как формальный функционал исходного kernel. Его Gram:

\[
 B_g(y(r),y(s))=2\{\Psi(r+s)-\Psi(r-s)\}.
 \tag{24}
\]

Для каждого действительного четного f на [-b,b], e=f(b), тождественно

\[
 f=e1_{[-b,b]}-\int_0^b f'(r)1_{[-r,r]}\,dr.
\]

Значит, с точными распределительными endpoint-массами,

\[
 \boxed{\mathfrak k[f]=
 B_g\left(e y(b)-\int_0^b f'(r)y(r)dr,
          e y(b)-\int_0^b f'(r)y(r)dr\right).}
 \tag{25}
\]

Если e!=0, то lambda/e^2 для выбранного единичного eigenvector есть точная ошибка КОНКРЕТНОГО предиктора a_f(r)=f'(r)/e. Она НЕ равна infimum ошибки по всем предикторам. По всему непрерывному past r<b этот infimum под RH равен нулю по (19). В конечном физическом классе оптимизация с e=1 дает именно ранее измеренную endpoint-capacity, а не нормированный spectral minimum. Повторять это как объяснение R≈4 нельзя: закрепленный edge_capacity report дает 0/8 и сохраняющийся мягкий endpoint-zero режим.

Нижние нули, endpoint-tail, cross и remainder-square в H+C+X+V — это спектральное раскрытие одного и того же остатка (25). Оно не доказывает, что его коэффициенты совпадают с оптимальным предиктором. При e=0 остается энергия integral f'(r)y(r)dr; мягкость не обязана исчезать.

Под RH для единичного f in J_m, ||A_m Q_m||<=delta_m дает k[f]<=delta_m. Для любой выбранной истории мер его best prediction error находится между 0 и k[f], так что малые residual-формы дают малые ошибки В ЭТИХ НАПРАВЛЕНИЯХ. Обратный универсальный вывод и одинаковый scalar rate для новой точки неверны. Уже diag(epsilon,1): одно направление тихое, но ошибка второго по первому равна 1. Определение физических норм и масштаба функционала обязательно.

## 8. Посаженная четверка: полный отрицательный судья

**[COFINAL_FAMILY / PAPER; A,LA; положительный baseline условен.]** Пусть baseline имеет только вещественные тона с S=sum nu_gamma/gamma^2<infinity. Добавим одну четверку ±w,±bar(w), кратности nu, где

\[
 w=\gamma+i\eta,\quad \gamma=2\pi/\log2,\quad0<\eta<1/2,
\]
\[
 g_w(t)=g_0(t)+4\nu\Re\frac{\cos(wt)-1}{w^2}.
 \tag{26}
\]

Для L_k=k log2, m_k=2^k и a_w=Re(1/w^2)=(gamma^2-eta^2)/(gamma^2+eta^2)^2>0:

\[
 \boxed{2\Psi_w(L_k)\le4S-8\nu a_w\{\cosh(\eta L_k)-1\}<0}
 \tag{27}
\]

на всех достаточно поздних k. Это строгий отрицательный UPPER. Для любого фиксированного положительного прошлого с range-guard sigma^2<=d=2Psi_w(L_k)<0. Для all-past infimum выбор нулевого предиктора также дает upper (27); если прошлое само стало неопределенным, результат -infinity, а не допустимая дисперсия. Применение к исходной постоянной моде возвращает

\[
 \langle\phi_0,A_{m_k}^w\phi_0\rangle=2\Psi_w(L_k)/L_k\to-\infty.
 \tag{28}
\]

Таким образом, в w-мире глобальная неотрицательность продолжения действительно ложна, хотя local-law (17) сохраняется.

### Где первая отрицательная ошибка возникает относительно всего прошлого

В четных measure-координатах одна четверка добавляет один положительный и один отрицательный квадрат: 4nu[(Re F(w))^2-(Im F(w))^2]. Пусть полный positive baseline плюс этот положительный квадрат имеет блок [[C,b],[b^T,d]], C>0. Отрицательный квадрат задается колонкой (u,alpha). Положим

\[
 \theta=u^TC^{-1}u,\quad
 \beta=\alpha-u^TC^{-1}b,\quad
 s_+=d-b^TC^{-1}b.
\]

Пока theta<1, прошлый signed блок C-uu^T положителен, а его точная новая ошибка равна

\[
 \boxed{\sigma_w^2=s_+-\frac{\beta^2}{1-\theta}.}
 \tag{29}
\]

Доказательство: сначала завершить квадрат positive baseline по прошлым координатам, затем исключить rank-one отрицательный квадрат, либо применить Sherman--Morrison; оба дают (29). Величины theta,beta используют ВЕСЬ прошлый C, не только последнюю точку. При theta=1 и beta!=0 срабатывает null-range failure. При theta=1,beta=0 отрицательное дополнение не создается этим шагом и остается s_+.

Это не новый постулат о действительной zeta. Это строгий контроль того, что правильный prediction functional обязан увидеть в мире с четверкой. Для sampled increments Delta=log2 добавка в Toeplitz covariance равна

\[
 -q_w\cosh(\eta\Delta(i-j)),\quad
 q_w=8\nu a_w(\cosh(\eta\Delta)-1)>0.
 \tag{30}
\]

Она разлагается как +q_w ss^T-q_w cc^T, s_i=sinh(eta Delta i),c_i=cosh(eta Delta i). Поэтому тот же rank-one механизм действует на всей dyadic истории.

## 9. Какая арифметика оплачивает знак и чего нет у DH

**[ABSTRACT / PAPER для идентичностей; COFINAL_FAMILY / CONDITIONAL для недоказанного знака.]**

| Шаг | Метки | Статус |
|---|---|---|
| Заданный g и точный возврат Weil/source | E,F,A,I | THEOREM, унаследованный источник |
| Формулы (3)--(6), индекс (12)--(15) | LA,A | PAPER, с явными range/PSD guards |
| Архимедов cusp и fixed-history (17) | F,A,LA | PAPER; одинаков в planted-мире |
| Реальные дискретные спектральные веса под RH | Z,A + RH | CONDITIONAL, не безусловный импорт |
| Infinite-past recurrence и finite-past контрпример | LA,A | PAPER; не дает m-rate |
| Arithmetic gradient (11), prime triangles (16) | E,I,LA | PAPER; корреляция подписана |
| Positive source continuation на всех длинах | E,F,A,I совместно | NOT PROVED |

Z здесь означает счет нулей, не их неизвестное положение и не положительность спектральной меры. Счет O(T log T) оплачивает сходимость sum |gamma|^-2, но не Cauchy--Schwarz для подписанного kernel.

У DH нет неотрицательной prime-power меры логарифмической производной: b_D(3)=-tau log3, b_D(6)=(1+tau^2)log6!=0. Также gamma/conductor и полюсная часть отличаются: j_D=e^{-3u/2}/(1-e^{-2u}), poles отсутствуют. Формула (9) переносится с ЭТИМИ источниковыми заменами; ее signed residual не превращается в положительную variance. Эти нормировки прочитаны по закрепленному EFZ-файлу, blob a3912756efbfac0825d96f29f35c0e834d38f560.

Точная gamma-FE обычной zeta, обычные целочисленные частоты и допустимый рост являются жестким контрактом идентификации источника. Классический Hamburger converse (при его полных условиях) определяет функцию с точностью до константы; он не утверждает нужной нижней границы quadratic prediction remainder. Ссылка на уникальность без положительной source-matched конструкции лишь возвращает нас к тому же g. DH имеет другую gamma-FE, а посаженная полиномиальная четверка меняет гладкую часть g и не сохраняет полный арифметический контракт zeta.

Приведенный в запросе G0/G1 остается унаследованным lever, не новым theorem import: файл CALIBRATE_EULER_LEVER по указанному имени на base вернул 404 и поиском не найден. Этот поставщик не использован ни в одном новом доказательстве. Никакого вывода о его математической ложности из transport failure не сделано.

## 10. Что именно еще нужно, без нового объекта и без нарезки задачи

В одной формуле для всего прошлого P и нового nu_* нужно доказать

\[
 \boxed{|B_g(u,\nu_*)|^2\le B_g(\nu_*,\nu_*)B_g(u,u)
 \quad\text{для всех }u\in P,}
 \tag{31}
\]

вместе с неотрицательностью прошлого и отсутствием null-range дефекта. Это ровно ||ell||_(P,*)^2<=d, то есть Sigma_P^2>=0. Правая и левая стороны полностью вычисляются через source (9)--(10). Здесь не предъявлена новая независимая арифметическая оценка (31).

Положительное завершение абстрактного положительного отрезка не обязано совпадать с заданным последующим g_zeta. Нельзя выбрать удобную положительную spectral extension и объявить, что она сохраняет будущие prime-атомы, gamma-term и полюсы. Нельзя получить (31) из local (17): этот кандидат проходит w-мир и потому отвергнут как закрывающий механизм.

Две координатные формы ТОГО ЖЕ неоплаченного объекта, не новые подзадачи: (i) signed source residual (9) на полном остаточном профиле; (ii) Toeplitz determinant/prediction (14)--(16) или full-history dual norm (5)--(6). Первая показывает точные арифметические корреляции (высокая kill-power, средняя цена source-аудита); вторая показывает обусловленность и первый signed pivot (высокая finite kill-power, низкая конечная цена; без арифметического bound не закрывает бесконечный квантор).

DISCRIMINATOR для нуль-согласованного результата: нижний envelope полной (9)/(31) вместе с range-guard; для опровержения — отрицательный верхний envelope на одном полном остатке. В finite-матрицах проверяется также nullspace coupling, не только округленный scalar pivot. Если PSD-head не установлен, числу нельзя давать вероятностное название variance.

## 11. Проверки, предрегистрация и граница результата

Предсказания P1--P6 записаны в registration.json до запусков. P1 (source/Schur/determinant agreement), P2 (pure-point finite-past obstruction), P3 (одинаковый local-law), P4 (planted-failure в первых 12 dyadic endpoints), P5 (rank-one и null-range guard), P6 (полный source-return step-профилей) подтверждены в указанной области. P4 — только зарегистрированный численный диапазон, не теорема о первом onset.

Четыре exact sympy controls: формула (23); real rank-one (29); null-range plant; Schur determinant. Еще исполнены source/increment проверки при 45/75 dps, independent integral source-return при 65 dps, и проверка envelope derivative (11). Это не независимый аналитический аудит.

Для g_zeta из арифметической формулы и g_w с eta=1/4,nu=1,Delta=log2 получено:

| n | m=2^n | zeta pivot | planted pivot | planted lambda_min(T_n) | 2Psi_w(nDelta) |
|---:|---:|---:|---:|---:|---:|
| 5 | 32 | 0.05076566120 | 0.003465366834 | 0.0002684106652 | 0.05332911726 |
| 6 | 64 | 0.04777024522 | -1.071811821 | -0.003776321401 | 0.03588504734 |
| 7 | 128 | 0.04400544525 | 0.1317963534 | -0.007038480060 | 0.005184505981 |
| 8 | 256 | 0.04384793481 | 0.08284064781 | -0.009274231352 | -0.001360590498 |

Важно: на n=6 старый planted-block еще положителен, новый pivot отрицателен, хотя диагональный длинный increment еще положителен. Это реальная чувствительность ко всей истории. Положительные pivots после n=6 не восстанавливают положительность: прошлое уже indefinite, эти значения только algebraic pivots.

Все 12 zeta sampled-increment блоков численно положительны. Никакая конечная таблица не доказывает (31). Максимальное абсолютное расхождение 24 pivots при 45/75 dps: 4.80e-35. Два прямых source-return residuals при 65 dps: 7.57e-66 и 1.44e-65; ошибка central-difference проверки (11): 5.41e-42. Local ratio sigma/[h log(1/h)] при h=1e-8 равен 0.9231785433 для zeta и 0.9231788660 для planted; медленное сближение с 1 согласуется с линейным членом -2Ah, а не заменяет его доказательство.

Никакие числа здесь не объявлены ARB_INTERVAL. python-flint в среде отсутствовал; Lean не запускался. Новых больших CCM-матриц не строилось. Тесты касаются kernel отсчетов и точного source-return, не отождествляют T_n с A_(2^n).

## 12. Source ledger, imports и handoff

R0. Protocol fetched полностью с rh_clean, blob e0127d491799f7764e4f50e1ae4ed4cfcaf73c13.
R1. SCREW_LINE_INVARIANT_v1, inbox ab8d123e124f0a32d04ac6711a770a41073319fa, blob b56a16a0540ed3f81858c113bc48de68c909b8c8: measure pullback, threshold-index boundary, planted normalization. Унаследованные выводы не передоказаны как новые результаты.
R2. `docs/routeB_bus/fake_worlds_2026-11-02/edge_capacity/RESULT.md`, base fcb70c5..., blob 7e27620b8d8271ff59c2e50f1a52dc4e69a5ca8b: прочитан, DIAG, capacity explanation closed 0/8.
R3. EFZ source, тот же base, blob a3912756efbfac0825d96f29f35c0e834d38f560, §§3.1--3.3: DH coefficient and source conventions.
R4. 3ce4968 RH-branch scale obstruction и 2176dab quiet-residual используются ровно как унаследованные результаты запроса, не как новый sign supplier.

P1. Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, arXiv:2206.03682v4, (1.1)--(1.9), Theorems 1.2,1.6,1.7. THEOREM; абсолютная сумма complex zeros не есть положительная мера. PDF pp.1,3,4 проверены также screenshot.
https://arxiv.org/pdf/2206.03682v4
P2. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1, §2.2 (2.2), §1.2 domains. THEOREM для expansion/описанных операторов; не импортируется открытый spectral limit. Прочитан первичный HTML.
https://arxiv.org/html/2606.09096v1
P3. N.H. Bingham, *Prediction theory in continuous time*, arXiv:2111.08560, §§1--2, обсуждение finite past. THEOREM при положительной covariance; CONDITIONAL application to zeta. PDF pp.3,5 просмотрены screenshot; p.2 screenshot вернул cache miss, текст прочитан. Его regular-component formulas не используются на singular spectrum.
https://arxiv.org/pdf/2111.08560
P4. Kaczorowski--Molteni--Perelli, *A converse theorem for Dirichlet L-functions*, Comment. Math. Helv. 85 (2010), introduction p.1: точный Hamburger contract. THEOREM о source uniqueness, не о sign. Первичный текст прочитан; screenshot p.1 вернул cache miss. Никакая невидимая таблица/иллюстрация не использована.
https://sites.unimi.it/molteni/research/papers-pdf/23-molteni-A_converse_theorem_for_Dirichlet_L-functions.pdf

DOWNSTREAM_CONSUMER: source-matched nonnegative screw continuation, then unchanged Weil/window criterion; no RH export in this artifact.
ACTUAL_CONSUMER_REQUIREMENT: full-history signed residual nonnegative with null-range guards, or a separately sufficient inherited floor.
ORIGINAL_REQUESTED_OBJECT: unconditional arithmetic proof of Sigma_P^2>=0.
ORIGINAL_OBJECT_IS: UNKNOWN as a necessary interface among all RH routes; necessary for this exact global positive-kernel continuation.
KNOWN_WEAKER_INTERFACES: pinned constant complementary floor or subpolynomial polylog-carrier floor; neither proved here.
FAILURE_TYPE: NO_DERIVATION for actual zeta sign; COUNTEREXAMPLE for pure-point=>zero finite-past and local-law=>global shortcuts.
EPISTEMIC_STATUS: RESEARCH_DEBT for zeta; MATHEMATICALLY_DEAD only for the two named ABSTRACT shortcut theorem-shapes.
KILL_SCOPE: THEOREM_SHAPE, not route family.
KILL_EVIDENCE: (23) strict positive residual; (27) strict negative upper despite (17).
REOPEN_TRIGGER: independent source-specific bound (31), not a general Hilbert prediction theorem or another finite positive table.
NOVELTY_AXIS: exact source predictor, local cusp law with nonuniformity exposed, even-window predictor identity, signed quartet regression on the same history.

CODEX DIRECTIVE (одна): audit this whole prediction functional, its source-return, range guards, and two judges; do not split it into new mathematical goals or promote positivity from the diagnostics. Success means mathematical audit of (4),(6),(9),(17),(23),(25),(27),(29) with unchanged norms; failure names the first incorrect equality and a witness. For an executed self-check, use Appendix in the repository root with `uv run --with sympy --with mpmath python -` and the displayed code on stdin. No lake or axiom profile applies: Lean source is not written.

META CLOSEOUT: полный signed consumer не закрыт. Исключены неправильный переход от pure-point к finite-past determinism и универсальное локальное продолжение как RH-дискриминатор. Не повторять: объявлять весь g ковариацией до (31), использовать pseudo-Schur без range, называть eigenvector edge-ratio оптимальным predictor error. Один оставшийся объект — та же Sigma_P^2 из (6),(9). Форма/метрика/границы возвращены точно; глобальная арифметическая оценка остается открытой.

## Appendix: executable compact exact/diagnostic checks

Ниже минимальные воспроизводимые контроли основных формул и dyadic judges. Сложение по prime powers выполняется точно по их индексам; mpmath-числа диагностические. Временные Python-переменные: Delta — шаг времени, eta — мнимая часть посаженной spectral-точки, r — increment covariance, T — ее Toeplitz matrix, n — число increments (НЕ число cosine-мод).

```python
import math
import sympy as s
import mpmath as mp
# Exact finite-past pure-point counterexample.
a,h,P=s.symbols('a h P', positive=True)
t=a+h
assert s.factor(t*(P-t)-a*(P-t)**2/(P-a)-P*h*(P-a-h)/(P-a))==0
# Exact signed regression identity and null-range failure.
C=s.Matrix([[2,1],[1,3]])
b=s.Matrix([s.Rational(1,2),s.Rational(1,3)])
u=s.Matrix([s.Rational(1,3),s.Rational(1,4)])
alpha=s.Rational(7,5); d=s.Rational(5,2)
K=C-u*u.T; bw=b-u*alpha
lhs=d-alpha**2-(bw.T*K.inv()*bw)[0]
rhs=d-(b.T*C.inv()*b)[0]-(alpha-(u.T*C.inv()*b)[0])**2/(1-(u.T*C.inv()*u)[0])
assert s.factor(lhs-rhs)==0
assert s.Matrix([[0,1],[1,1]]).det()==-1
# Zeta source plus one planted quartet: no zero list is used.
mp.mp.dps=75
Delta=mp.log(2); eta=mp.mpf(1)/4; w=2*mp.pi/Delta+1j*eta
limit=4096
pr=[True]*(limit+1); pr[0]=pr[1]=False
for p in range(2,math.isqrt(limit)+1):
    if pr[p]:
        for n in range(p*p,limit+1,p): pr[n]=False
atoms=[]
for p in range(2,limit+1):
    if pr[p]:
        n=p
        while n<=limit:
            atoms.append((mp.log(n),mp.log(p)/mp.sqrt(n))); n*=p

def g(t):
    t=abs(t)
    if not t: return mp.mpf(0)
    z=-8*(mp.cosh(t/2)-1)-t*(mp.digamma(mp.mpf(1)/4)-mp.log(mp.pi))/2
    z-=(mp.pi**2+8*mp.catalan-mp.exp(-t/2)*mp.lerchphi(mp.exp(-2*t),2,mp.mpf(1)/4))/4
    return z+mp.fsum(c*(t-a) for a,c in atoms if a<t)

g0=[g(k*Delta) for k in range(13)]
gw=[z+4*mp.re((mp.cos(w*k*Delta)-1)/w**2) for k,z in enumerate(g0)]
for label,gs in [('zeta',g0),('planted',gw)]:
    r=[-2*gs[1]]+[2*gs[k]-gs[k-1]-gs[k+1] for k in range(1,12)]
    for n in range(1,13):
        T=mp.matrix([[r[abs(i-j)] for j in range(n)] for i in range(n)])
        old=mp.det(T[:n-1,:n-1]) if n>1 else mp.mpf(1)
        pivot=mp.det(T)/old
        total=mp.fsum(T[i,j] for i in range(n) for j in range(n))
        assert abs(total+2*gs[n])<mp.mpf('1e-60')
        eig=mp.eigsy(T,eigvals_only=True)[0]
        print(label,n,'pivot',mp.nstr(pivot,14),'min',mp.nstr(eig,14))
print('Exact controls passed; printed values are NOT interval certificates.')
```
