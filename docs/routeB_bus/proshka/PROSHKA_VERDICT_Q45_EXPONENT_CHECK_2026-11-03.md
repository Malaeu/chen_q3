# STATUS: TRY_Q45_EXPONENT_CHECK

```yaml
OPERATIVE_CLASS: TRY_Q45_EXPONENT_CHECK
DATE: 2026-11-03
REQUEST_ID: Q45_EXPONENT_CHECK_v1
AUTHORITY: DIRECT_OWNER_SOURCE_PINNED_AUDIT
TASK_MODE: MATHEMATICAL_AUDIT_NOT_FORMAL_TXT_BUS_ADJUDICATION
SOURCE_BASE: 9c4cbbbf566815030c3e8746876d6e0c6ef7244a
SOURCE_INBOX: 174263d1a095e5cc680cf9e5c5e2ee543106f2bd
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
Q45_PRICE: CONFIRMED_WITH_ADDITIONAL_LOG_LOG_M_FACTOR
EDGE_TRANSFER: NO_STRICT_HALF_PLANE_IMPROVEMENT_FROM_THE_STATED_MERTENS_ENVELOPE
QUARTER_COMPARISON: FORMAL_EXPONENT_COMPARISON_ONLY_NOT_AN_AUTOMATIC_Q45_TRANSFER
BOUNDARY_LOG_LOSS: EXPLICITLY_RETAINED
MINIMAL_ACTUAL_PAIR_INTERFACE: ONE_SIDED_LOWER_COEFFICIENT_MARGIN
NEW_J_LONG_SIGN_BOUND: NOT_PROVED
GENERIC_BILINEAR_CANCELLATION_FROM_IDENTITY_ONLY: NOT_VALID
RH_PROVED: false
CALIBRATE_EULER_LEVER_v1_COMPLETED: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_RESULT: PROVED_LIMIT_OF_THE_SPECIFIED_EXPONENT_BOOTSTRAP
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
CCM_EIGENPROBLEMS: 0
EXACT_ALGEBRA_GROUPS: 8
ROUTE_STATE_CHANGED: false
```

## 0. Решение и точная область

Ы. Арифметика Q45 подтверждается с восстановлением множителя `log L`. Краевой сигнал позволяет исключить только `Re rho > beta`, тогда как сама гипотеза `M(x)=O(x^beta)` уже исключает эту полуплоскость. На граничной прямой логарифмическая цена не исчезает: отношение цены к краевому сигналу равно `L^{6(1-beta)} log L`.

Есть две поправки к буквальной постановке. Во-первых, beta — показатель Mertens-supplier, а не просто метка бесконулевой области: переход от области к этому supplier должен иметь собственный аналитический бюджет. Во-вторых, Q45 доказан для конкретной комплексной пары и `y=L-2log L`. Его нельзя без доказательства приложить к новому чётному quarter-window witness.

Ниже доказано препятствие только для повторного применения указанного абсолютного конверта. Не доказана невозможность нового направленного арифметического выигрыша. Такой выигрыш сформулирован в минимальной коэффициентной форме; ни один из проверенных источников его не поставляет.

Это ответ на Q45_EXPONENT_CHECK_v1. Отдельный пакет CALIBRATE_EULER_LEVER_v1 (оконные G0/G1/G2/E1) здесь не объявляется выполненным; классический G0 используется только как проверенная ограниченная ссылка.

## 1. Источники и конвенции

**[FINITE_CELL | PAPER: provenance, не численная сертификация.]** Прочитаны закреплённые документы и непосредственно необходимые им поставщики:

- S0: `docs/routeB_bus/audits/POLYLOG_RECEIVER_AUDIT_2026-11-02/Q27_Q45_OBSTRUCTION.md`, base 9c4cbbbf, blob `d2b7a5496a3edb1a59ce853f89125f8ce637a9e8`.
- S1: `docs/literature/openai_math_2026-10-07/CCM_Q45_PAIR_POLYLOG_DIVISOR_REDUCTION.md`, тот же base, blob `0f9771e5949456e1c00cfd336e88f84ce103f643`; весь текст A1–A6, completion budget, all-P transfer boundary.
- S2: `docs/literature/openai_math_2026-10-07/CCM_Q45_PAIR_SHORT_DIVISOR_QUADRATURE.md`, тот же base, blob `bfb4d3788d78e7edce97b2f03b2b8ad782abc87e`; в частности S8 и оба конца частичного суммирования.
- S3: `docs/routeB_bus/proshka/PROSHKA_VERDICT_POLYLOG_REENTRY_CENTERED_BUDGET_2026-11-02.md`, inbox 174263d1, §§1–5: quarter-window witness, subpolynomial consumer и вспомогательная Gram-цена.
- S4: `docs/literature/openai_math_2026-10-07/CCM_RESTRICTED_PRIME_RECEIVER.md`, base, blob `897a92716a746ce8b9a36adb77e66c83b19bdf59`.
- S5: `docs/literature/openai_math_2026-10-07/CCM_Q17_PAIR_AVERAGING_ATTEMPT.md`, base, blob `129ca639e40b534ee1d72eee6d6ac7ec02c16229`.
- S6: `docs/literature/openai_math_2026-10-07/CCM_AFTER_Q20_MARGIN_CONCLUSION.md`, base, blob `57e358724d2d4a2718d01a9be245df7173730e16`, и соответствующие §§2–4 полного `PROSHKA_CCM_AFTER_Q20_SHARP_PAIR_MARGIN_2026-10-25.md`.

Это необходимые математические файлы вне `routeB_bus`, а не поиск другой задачи по очереди. Старые аналитические поставщики наследуются на их PAPER-уровне; whole-chain recertification не выполнена.

Внешние первичные справки: P1 NIST DLMF 27.4.5, 27.4.12 и 27.5.2, 27.5.5; P2 T. Tao, *Derived multiplicative functions* (2014), формулы (4),(5); P3 K. Kedlaya, *Notes on analytic number theory*, §8.3, Theorem 8.8. Их роль ограничена тождествами и классическим zero-free механизмом, не новой оценкой actual pair.

Используем обозначения

\[
L=\log m,\quad y=L-2\log L,\quad D=\lfloor m/L^6\rfloor,
\quad w=\eta+i\gamma,\quad 0<\eta<\tfrac12.
\]

`eta` — горизонтальное смещение гипотетического нуля `rho=1/2+w`; `nu` — его кратность. `beta` — показатель гипотезы о `M(x)=sum_{d<=x}mu(d)`. Все параметры w,beta фиксируются до предела m→∞. Константы могут зависеть от w и beta; выбирать beta=beta(m) без равномерного supplier запрещено.

Сохраняем ТОТ ЖЕ вес `C(v)=integral conjugate(g(t))k(t+v)dt` и раздельные нормировки actual pair. Точный остаток есть

\[
J_{\rm long}(m)=\sum_{k<L^6}\frac{\log k}{\sqrt k}
 \sum_{D<d\le m/k}\frac{\mu(d)}{\sqrt d}
 \{C(y-\log(dk))+C(y+\log(dk))\}.
\tag{1}
\]

Нулевая по `log 1` строка k=1 сохранена без эффекта. Пустые диапазоны равны нулю, верхние floors буквальные. S1 даёт `J=J_long+o_w(1)`, а не удаление какого-либо сектора prime powers. Исходные N=m, производство R/P и физическая норма не меняются.

## 2. Точное восстановление цены Q45

**[COFINAL_FAMILY | CONDITIONAL на Mertens-supplier; арифметика переноса PAPER. Класс A+I+LA.]** Предположим

\[
|M(x)|\le K_\beta x^\beta,\qquad \tfrac12\le\beta<1.
\tag{2}
\]

По S1–S2, включая нижний M(D), верхний floor и обратную ориентацию C,

\[
|J_{\rm long}|\le A_{w,\beta}K_\beta
 e^{(\beta-1/2)y}\sum_{k<L^6}\frac{\log k}{k^\beta}+o_w(1).
\tag{3}
\]

Для фиксированного beta<1 интегрирование и ограниченная вариация подынтегральной функции дают

\[
\sum_{k<X}\frac{\log k}{k^\beta}
=\frac{X^{1-\beta}\log X}{1-\beta}
 -\frac{X^{1-\beta}}{(1-\beta)^2}+O_\beta(1+X^{-\beta}\log X).
\]

Отсюда, при X=L^6,

\[
\boxed{\mathcal P_\beta(m)
 = A'_{w,\beta}K_\beta\,
 m^{\beta-1/2}L^{7-8\beta}\log L,
 \qquad |J_{\rm long}|\le\mathcal P_\beta+o(1).}
\tag{4}
\]

Проверка логарифмов: `e^{(beta-1/2)y}=m^{beta-1/2}L^{1-2beta}`, а сумма по k имеет цену `L^{6-6beta} log L`; складываются `1-2beta+6-6beta=7-8beta`. Множитель `log L=log log m` нельзя терять на границе показателей.

При beta=1 формулу (4) нельзя брать пределом с прежней константой. Отдельно

\[
\sum_{k<L^6}\frac{\log k}{k}=18(\log L)^2+O(1),
\quad \mathcal P_1(m)=O_w(\sqrt m(\log L)^2/L).
\tag{5}
\]

Это upper PRICE, не lower на фактический J и не асимптотика J.

## 3. Сигнал против цены: оба сравнения и края

**[COFINAL_FAMILY | PAPER для сравнений; signals наследуются как условные adverse suppliers. Класс LA+A.]** Обозначим

\[
X_q=m^{\eta/2},\qquad X_e=m^\eta L^{-2\eta}=e^{\eta y}.
\]

Тогда

\[
\boxed{\frac{\mathcal P_\beta}{X_q}
 \asymp_{w,\beta,K_\beta}
 m^{\beta-1/2-\eta/2}L^{7-8\beta}\log L,}
\tag{6}
\]
\[
\boxed{\frac{\mathcal P_\beta}{X_e}
 \asymp_{w,\beta,K_\beta}
 m^{\beta-1/2-\eta}L^{7-8\beta+2\eta}\log L.}
\tag{7}
\]

Знак степенного показателя решает предел при строгом неравенстве. Поэтому при наличии корректного полного переноса:

| Сигнал | Условие, при котором цена o(сигнала) | Исключаемые нули |
|---|---|---|
| Quarter | eta>2beta-1 | Re rho>2beta-1/2 |
| Edge, actual Q45 | eta>beta-1/2 | Re rho>beta |

При краевом равенстве `eta=beta-1/2`:

\[
\boxed{\mathcal P_\beta/X_e\asymp L^{6(1-\beta)}\log L\longrightarrow\infty.}
\tag{8}
\]

При quarter-равенстве `eta=2beta-1`, если оно вообще лежит в `0<eta<1/2`, имеем `1/2<beta<3/4` и `7-8beta>1`, так что отношение тоже расходится. При beta=1 и eta=1/2 краевая цена/сигнал имеет порядок `(log L)^2`, а для eta<1/2 есть ещё положительная степень m.

Калибровка, НЕ импорт каких-либо новых zero-free теорем:

| beta | power price | log power price | edge boundary ratio | formal quarter line |
|---|---|---|---|---|
| 7/8 | 3/8 | 0 | L^(3/4) log L | Re rho>5/4 |
| 11/12 | 5/12 | -1/3 | L^(1/2) log L | Re rho>4/3 |

На критической полосе обе quarter-строки вообще пусты.

### 3.1. Почему это строгое препятствие данному выводу, но не source no-go

Если eta<beta-1/2, то для любых фиксированных a,b

\[
m^{\beta-1/2-\eta}L^a(\log L)^b\to\infty.
\]

Ни фиксированная логарифмическая экономия, ни множитель `exp(o(L))` не устраняет положительную степенную разность. Более того, когда `nu X_e<=mathcal P_beta`, скалярная модель `B_m=-nu X_e` одновременно удовлетворяет adverse signal и `|B_m|<=mathcal P_beta`. Эти два неравенства логически совместимы. Модель проверяет только этот вывод, не подменяет mu или actual C.

Следовательно, нельзя получить противоречие из одного (4) на этой области. Это не утверждение, что настоящий J обязан иметь размер цены, или что все способы оценить J невозможны.

### 3.2. Важная граница quarter-сравнения

S3 даёт новый even receiver, S1 даёт actual complex-pair estimate. S0 прямо запрещает их молчаливое отождествление. Даже при сохранении C нельзя просто заменить y на L/2, оставив D=m/L^6: в A3–A4 Q45 используется `K_d=e^y/d>=L^4`, а тогда

\[
K_D\sim L^6/\sqrt m\to0,
\qquad q^2D/e^y\asymp\sqrt m/L^2\to\infty
\quad(q\asymp L^2).
\tag{9}
\]

Прежняя малая quadrature-bracket становится большой. Это точный отказ данного переноса, не запрет нового расписания D или иной оценки. Таблица quarter выше — корректная арифметика предложенного сравнения, но не новая доказанная теорема о совместимости двух suppliers.

## 4. Почему зона не расширяется

**[COFINAL_FAMILY | PAPER. Класс E+I+A.]** Вход (2) сам уже исключает нули при Re s>beta. Для Re s>1 имеем

\[
\frac1{\zeta(s)}=s\int_1^\infty M(x)x^{-s-1}dx.
\]

Правая часть при (2) голоморфна в Re s>beta. Она совпадает с 1/zeta справа от 1, поэтому аналитическое продолжение равенства `zeta(s)F(s)=1` исключает нуль zeta в этой полуплоскости. Точка s=1 — полюс zeta, не нуль. Начальное Dirichlet-series identity — P1, DLMF 27.4.5; продолжение доказано здесь.

Значит, edge-перенос Q45 возвращает область, уже содержащуюся в самом входе. Если начальная область `Re s>beta0` используется только через дополнительные оценки `M(x)=O_epsilon(x^{beta0+epsilon})`, то для каждого фиксированного epsilon новое условие есть `Re rho>beta0+epsilon`. Предел по фиксированным epsilon возвращает `Re rho>beta0`, не левее. Обратный переход от zero-free области к Mertens-оценке не доказан одним S0 и в этом вердикте не вставляется скрытно.

Вывод «максимум в саму себя» подтверждён именно для такого Mertens-переноса. Для quarter он может быть слабее; для другого signed supplier этот предел не доказан.

### RH-ветвь: правильный тест масштаба

**[COFINAL_FAMILY | CONDITIONAL, только consistency check.]** При подстановке RH-совместимого семейства показателей beta=1/2+epsilon цена равна

\[
O_{w,\epsilon}(m^\epsilon L^{3-8\epsilon}\log L).
\tag{10}
\]

Для каждого фиксированного eta>0 выбор epsilon<eta (edge), либо epsilon<eta/2 (формальное quarter-сравнение), делает цену o соответствующего сигнала. При формальном exact-beta=1/2 остаётся polylog `L^3 log L`, а S3 допускает любой subpolynomial floor. Exact bound M(x)=O(sqrt x) здесь НЕ приписывается RH.

Поэтому polylog-расходимость не убивает этот receiver. Подставлять eta=0 и сравнивать с off-critical signal нельзя: такой сигнал построен при eta>0. Сам actual pair с off-critical параметром на RH-ветви не утверждается существующим.

## 5. Минимальный необходимый новый вход: одна сторона и тот же C

**[COFINAL_FAMILY | PAPER: достаточность на унаследованном adverse supplier. Класс LA; построение пары F+A.]** Фиксируем w и его кратность nu. Пусть

\[
B_m=\Re(e^{i\gamma y}J_{\rm long}(m)),\qquad X_m=e^{\eta y}.
\tag{11}
\]

У S4–S5 при целой паре `u_h=e^{-i gamma h}tau_h g-e^{i gamma h}tau_{-h}k`, h=y/2,

\[
Prime[u_h]=Self_m-2\Re(e^{i\gamma y}J(h;m)).
\]

После исходной cutoff/projection/contact correction, не отдельно каждого атома,
`K[z_m]=-2nu X_m+e_K`, `Prime[z_m]=Self_m-2Re(e^{i gamma y}J)+e_S`,
`K[z_m]=Arch[z_m]-Prime[z_m]`. Следовательно

\[
B_m=-\nu X_m+r_m,\qquad |r_m|\le R_w(m)=O_w(L)+o_w(1).
\tag{12}
\]

Допустимая полная цена:

\[
R_w(m)=\frac{D_w(50L+8)+C_{self,w}+\rho_K+\rho_S}{2}
       +\epsilon_{prefix,w}(m),\qquad\epsilon_{prefix,w}=o(1).
\]

Здесь D_w — верх нормы возвращённой пары, а не divisor cutoff D; self terms сохранены, оба возврата уплачены один раз, S1 prefix добавлен по модулю только как уже доказанный o(1). (12) — неблагоприятное следствие гипотетического нуля, не новый положительный arithmetic supplier.

Достаточно НЕ абсолютного `|J_long|=o(X)`, а независимого

\[
\boxed{B_m\ge-(\nu-\vartheta_w)X_m-e_w(m),
\quad \vartheta_w>0,\quad e_w(m)=o_w(X_m).}
\tag{13}
\]

Из (12),(13) следует `vartheta_w X_m<=R_w+e_w`, противоречие, поскольку `R_w/X_m→0`. Семья m может быть любой неограниченной для фиксированного w.

Ещё более слабый точный интерфейс:

\[
\boxed{B_m\ge-\nu X_m+g_w(m)X_m-e_w(m),\quad
       g_w(m)X_m>R_w(m)+e_w(m)}
\tag{14}
\]

на поздней неограниченной семье, где g_w и e_w — независимо оплаченные неотрицательные функции. Равенство или неизвестный знак не дают противоречия. Например, g_w=1/L и e_w=o(X_m/L) достаточно. Это уже известный коэффициентный consumer S6, а не заявка на новизну.

Направление обязательно LOWER для B_m. Оно соответствует UPPER prime-формы из-за минуса перед `2B_m`. Нельзя менять его на верхнюю оценку B_m, менять C на |C| или нормировать фазу после теста. Усреднённый B_T из S6 имеет отдельный сигнал E_T~X_m/L; если выбран именно он, усреднять надо и полный Q45-budget, а не только adverse signal.

### 5.1. Минимальный выигрыш, выраженный как сокращение цены

Если кандидат сохраняет форму (4), но делит её на положительный S_m, то для sufficient `o(X_m)` требуется

\[
\boxed{\frac{S_m}
 {m^{\beta-1/2-\eta}L^{7-8\beta+2\eta}\log L}\to\infty.}
\tag{15}
\]

Для S_m=m^Delta L^s это означает

\[
Delta>\beta-\tfrac12-\eta,
\]

либо равенство степеней и `s>7-8beta+2eta`. При равенстве также логарифмических степеней нужна дополнительная экономия, превосходящая log L. Это критерий o-сигнала; известный малый leading coefficient по (13) может быть слабее.

Фиксированный новый степенной выигрыш Delta в таком directed bound меняет edge-line на `Re rho>beta-Delta`. При supplier beta>beta0 с произвольно малой фиксированной потерей и одним Delta в окрестности beta0 он способен дать `Re rho>beta0-Delta`. Одни логарифмы не дают фиксированного сдвига влево.

## 6. Есть ли независимый источник такого выигрыша?

Ни S0–S6, ни проверенные P1–P3 не поставляют (13), (14) или положительную Delta для этой actual pair. Это ограниченный source-audit, НЕ утверждение об отсутствии всех возможных результатов в литературе.

### 6.1. Lambda>=0: что следует и что не следует

**[ABSTRACT | PAPER. E+LA.]** Для действительного веса

\[
W_y(n)=n^{-1/2}\Re[e^{i\gamma y}
     (C(y-\log n)+C(y+\log n))]
\]

положительность даёт только `sum Lambda W_y >= -sum Lambda(-W_y)_+`. Контроль последнего выражения ещё не получен. Положительная мера не даёт знака интеграла произвольного знакопеременного ядра. Например, один положительный атом при отрицательном значении W даёт отрицательный интеграл. Этот пример опровергает общее правило знака, не является другой zeta и не опровергает (13).

### 6.2. mu*1=delta: полный возврат, не сокращение до нуля

**[FINITE_CELL | PAPER. E+I+LA.]** Положим `Psi_y(n)=n^{-1/2}(C(y-log n)+C(y+log n))`. Перегруппировка (1) точно даёт

\[
J_{long}=\sum_{n\le m}\Psi_y(n)b_D(n),\quad
b_D(n)=\sum_{d\mid n,\ d>D}\mu(d)\log(n/d)
=\Lambda(n)-\sum_{d\mid n,\ d\le D}\mu(d)\log(n/d).
\tag{16}
\]

Здесь k=n/d<L^6 следует из исходного D; это не новый cutoff. Тождество mu*1 не применимо как зануление из-за log(n/d), ограничения d>D и веса Psi_y. Даже при D=3 получаем точно `b_D(10)=-log2`, `b_D(12)=+log2`. Это конкретное препятствие шагу «длинный коэффициент имеет знак Lambda» или «mu*1 его зануляет».

Идентичность mu*log=Lambda возвращает исходную совместную сумму. Она не даёт отдельно положительный/отрицательный знак длинного сектора. Не утверждается, что глубокое новое следствие той же арифметики невозможно.

### 6.3. Vaughan / Heath–Brown

**[ABSTRACT | PAPER. E+I для идентичностей; A для требуемой новой оценки.]** P2 задаёт точные разложения в Type I/II и многолинейные суммы. Взвешивание их тем же Psi_y законно, но новый выигрыш требует оценки полученных сумм с фактическими коэффициентами и всеми cutoffs. В S1 не предъявлена такая оценка.

Точная граница общего аргумента: одна билинейная структура и bounded coefficients не обеспечивают power saving. Для
`K(a,b)=V(ab/X)(ab)^(-it0)`, V неотрицательна и положительна на фиксированном интервале, возьмём `a_r=r^(it0)`, `b_s=s^(it0)`. На фиксированном прямоугольнике r~R,s~S, RS~X, фаза полностью сокращается; сумма имеет порядок RS (или sqrt(RS) после half-density normalization). Это exact class obstruction для универсального bounded-coefficient cancellation, не утверждение о настоящей mu.

Здесь C — фиксированная функция логарифма произведения; рост m сам по себе не добавляет большой фазовый параметр после d=(e^y/k)u. Следовательно, отдельное arithmetic Type-II theorem, а не только identity, является необходимым новым поставщиком данного подхода. Его перенос на актуальный C здесь не доказан.

### 6.4. Рычаг G0

**[ABSTRACT | PAPER: калибровка классического входа. E+I+A; F для completed analytic estimates.]**

\[
3+4\cos\theta+\cos2\theta=2(1+\cos\theta)^2\ge0
\]

даёт при sigma>1

\[
\sum_n\Lambda(n)n^{-\sigma}
[3+4\cos(t\log n)+\cos(2t\log n)]\ge0.
\tag{17}
\]

P3 выводит из этого и аналитических оценок классическую область `sigma>1-c/log|t|`. Это другой неотрицательный тест, а не (13). Перенос его благоприятного знака на W_y не предъявлен. Сам пакет оконной калибровки G0–G2 здесь не заменяется классическим доказательством.

Даже если отдельно предоставлен сильный субэкспоненциальный Mertens-bound вида `|M(x)|<=x exp(-a sqrt(log x))`, его Q45-цена на d>D остаётся

\[
O_w\left(\frac{\sqrt m(\log L)^2}{L}
 e^{-a\sqrt{\log D}}\right)=m^{1/2-o(1)}.
\]

Отношение к X_e при любом фиксированном eta<1/2 расходится: логарифм отношения равен `(1/2-eta)L-o(L)`. В более общем виде любая экономия exp(-o(L)) при ведущей степени 1/2 не исключает нуль с фиксированным eta<1/2 этим absolute-envelope argument. Это доказательство границы конкретного переноса, не запрет всех будущих E+F способов.

## 7. Невозможные переходы и не доказанные утверждения — отдельно

**[ABSTRACT/COFINAL_FAMILY | PAPER.]**

1. Получить фиксированный сдвиг полуплоскости из (4) одной логарифмической экономией невозможно: положительная разность степеней и модель §3.1 дают доказательство.
2. Перенести Q45 A1 на все компактно поддержанные автокорреляции невозможно в буквальной форме: C_f=0 при |s|>L, C_f(0)=||f||²>0; голоморфность в полосе, содержащей R, противоречит теореме тождественности. Это архивный scope-obstruction, не запрет другого all-P supplier.
3. Удалить long sector посредством mu*1 неверно: точная формула (16) и оба знака в примерах.
4. Вывести power saving для любых bounded bilinear coefficients из одной структуры суммы неверно: резонансный пример §6.3.

Ни один пункт не доказывает ложность (13) для actual C и настоящих mu/Lambda. Такая source-specific оценка остаётся исследовательским долгом, а не математически запрещённой задачей.

## 8. Классификация, дальнейший объект, closeout

E — конкретная Euler-арифметика; F — конкретные gamma/pole/functional-equation данные; Z — счёт нулей, не их фактические координаты; LA — линейная/вариационная алгебра; A — комплексный анализ и оценки рядов/интегралов; I — обычная целочисленная арифметика.

| Шаг | Класс | Scope / verifier |
|---|---|---|
| Q45 mu*log, floors, prime powers | E/I/LA | FINITE_CELL/PAPER |
| Fixed actual C, strip/tails, prefix quadrature | F/A/I | COFINAL_FAMILY/PAPER inherited |
| Hypothesis M(x)<=K x^beta | A/I, дополнительный supplier | COFINAL_FAMILY/CONDITIONAL |
| Цена и сравнение показателей | LA/A | COFINAL_FAMILY/PAPER |
| Mertens bound => zero-free half-plane | E/I/A | COFINAL_FAMILY/PAPER conditional on M-bound |
| Adverse actual-pair identity | F/A/LA, фактический условный w | COFINAL_FAMILY/CONDITIONAL on hypothetical zero |
| Коэффициентный зазор => противоречие | LA | COFINAL_FAMILY/PAPER on inherited receiver |
| Vaughan/HB identities | E/I/LA | ABSTRACT/PAPER |
| Новый directional Type-II margin | A/E/I, пока supplier отсутствует | COFINAL_FAMILY/CONDITIONAL |
| Новый zero-count Z или интервал нуля | Не использовался | — |

Два кандидата, без объявления нового результата:

- Прямой фазовый scalar B_m из (11): доказать (13) или (14), сохраняя действительный C, все веса и полный возврат. Дискриминатор: LOWER envelope `B_m+nu X_m-e_w` с выигрышем больше R_w. Сила 5/5, новая аналитическая цена неизвестна.
- Точный arithmetic Type-II decomposition (16) с сохранённым C: установить одностороннюю совокупную оценку, которая даёт тот же margin, а не отдельные нормы блоков. Сила 5/5, алгебраическая цена 2/5, аналитическая высокая. Нулесогласованная конечная проверка не заменяет кофинальный lower envelope.

**CODEX DIRECTIVE — Q45_SAME_PAIR_MARGIN_AUDIT:** проверить (4),(6)–(9),(12)–(16) на закреплённых S1–S6; отдельно подтвердить LOWER-ориентацию и все два раза mixed fee. Для нового поставщика предъявить ровно (13)/(14) или явную Delta>0, не переименовывать усиленный глобальный Mertens-bound в независимый выигрыш. Не переносить A1 на новый even H_m без доказательства. Не запускать спектральный scan для проверки асимптотического показателя. Никакого RH-export после аудита этих тождеств.

DOWNSTREAM_CONSUMER: исключение гипотетического off-critical zero на исходном actual-pair receiver.
ACTUAL_CONSUMER_REQUIREMENT: независимый односторонний коэффициентный зазор больше полных ошибок.
ORIGINAL_REQUESTED_OBJECT: проверить баланс Q45 и найти независимый минимальный gain.
ORIGINAL_OBJECT_IS: global improved Mertens bound NOT_NECESSARY; directed margin is a sufficient interface.
FAILURE_TYPE: NO_DERIVATION of new J_long bound; explicit counterexamples only for named invalid shortcuts.
EPISTEMIC_STATUS: RESEARCH_DEBT for actual-pair margin, not route death.
NOVELTY_AXIS: точная калибровка показателей, endpoint/log и scope audit; коэффициентный consumer восстановлен из архива, не новый.
REOPEN_TRIGGER: независимый same-C направленный supplier с полным бюджетом.
FORBIDDEN_REPEAT: новая итерация того же Mertens exponent с заявкой на self-bootstrap; абсолютные нормы после разложения без нового gain.

Что стало точнее: вход Mertens уже содержит возвращаемую область; quarter-transfer имеет отдельную неоплаченную гипотезу; минимальный выигрыш может быть коэффициентным, не степенным. Что не закрыто: источник этого выигрыша. Восемь зарегистрированных exact-control predictions подтверждены. Аналитическая независимая проверка не выполнялась.

## 9. Воспроизведение и доставка

Проверки зарегистрированы до исполнения в `registration.json` рабочего каталога. Восемь групп exact algebra и отдельная runtime scope-проверка прошли. Это не Lean, Arb, интервальная матричная сертификация и не проверка условного Mertens-supplier.

План доставки: только этот новый Markdown в `docs/routeB_bus/proshka/`, ветка `proshka_inbox_2026-10-31`; существующие источники не редактируются. SHA коммита сообщается после успешной записи и readback; собственный SHA не встраивается в содержимое. Для воспроизведения извлечь единственный Python-блок ниже в `checks.py` и выполнить `python3 checks.py`. Lean-paths и axiom profile неприменимы, Lean не изменяется.

Первичные внешние locators:
- P1: https://dlmf.nist.gov/27.4 ; https://dlmf.nist.gov/27.5
- P2: https://terrytao.wordpress.com/2014/09/24/derived-multiplicative-functions/
- P3: https://kskedlaya.org/ant/chap-zeroes.html , §8.3 Theorem 8.8.

## Appendix. Exact checks

```python
"""Exact algebra audit for Q45; not a sign certificate for CCM or primes."""
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path


def mobius(n: int) -> int:
    if n < 1:
        raise ValueError('n must be positive')
    ans, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            ans = -ans
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -ans if n > 1 else ans


def factor_log(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def log_convolution(n: int, lower: int = 0) -> dict[int, int]:
    out: dict[int, int] = {}
    for d in range(lower + 1, n + 1):
        if n % d:
            continue
        for p, power in factor_log(n // d).items():
            out[p] = out.get(p, 0) + mobius(d) * power
    return {p: a for p, a in out.items() if a}


def main() -> None:
    here = Path(__file__).resolve().parent
    # Predictions P1-P8 were registered before the original execution.
    checks: list[str] = []
    for j in range(50, 100):
        b = F(j, 100)
        assert 1 - 2*b + 6*(1-b) == 7 - 8*b
    checks.append('P1: Q45 logarithmic exponent')
    for j in range(50, 100):
        b = F(j, 100)
        eta = b - F(1, 2)
        assert 7 - 8*b + 2*eta == 6*(1-b) > 0
    checks.append('P2: edge boundary logarithmic deficit')
    for j in range(51, 75):
        b = F(j, 100)
        eta = 2*b - 1
        assert b - F(1, 2) - eta/2 == 0
        assert 0 < eta < F(1, 2) and 7 - 8*b > 1
    checks.append('P3: quarter boundary in the critical strip')
    b = F(11, 12)
    assert (b-F(1,2), 7-8*b, 6*(1-b), 2*b-F(1,2)) == (F(5,12), F(-1,3), F(1,2), F(4,3))
    checks.append('P4: exact 11/12 calibration')
    b, delta, eta = F(7, 8), F(1, 16), F(5, 16)
    assert b-F(1,2)-delta-eta == 0
    assert F(1,2)+eta == b-delta
    checks.append('P5: power-saving line')
    # K = Arch - Prime; Prime = Self - 2 B; K = -2 nu X + eK.
    nu, X, arch, self_term, eK = F(3), F(100), F(7), F(2), F(1,3)
    B = -nu*X + (eK-arch+self_term)/2
    assert arch-(self_term-2*B) == -2*nu*X+eK
    theta, R, E = F(1,4), F(4), F(2)
    assert theta*X > R+E  # makes adverse interval and improved lower bound disjoint
    checks.append('P6: actual-pair phase orientation and coefficient gap')
    for n in range(1, 151):
        assert sum(mobius(d) for d in range(1,n+1) if n%d==0) == int(n==1)
        f = factor_log(n)
        target = {next(iter(f)): 1} if len(f)==1 else {}
        assert log_convolution(n) == target
    assert log_convolution(10,3) == {2:-1}
    assert log_convolution(12,3) == {2:1}
    checks.append('P7: Mobius-log identity and signed long coefficients')
    for k in range(-100, 101):
        x = F(k,100)
        assert 3+4*x+(2*x*x-1) == 2*(1+x)**2 >= 0
    checks.append('P8: exact 3-4-1 polynomial')
    assert 6*F(1,2)**2 == F(3,2)  # not used as asymptotic evidence
    checks.append('scope: no eigensolver, zero data, or floating arithmetic used')
    result = {'status':'EXACT_ALGEBRA_CONTROLS_PASSED', 'groups':len(checks), 'checks':checks,
              'proves_J_long_bound':False, 'independent_analytic_audit':False}
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
```
