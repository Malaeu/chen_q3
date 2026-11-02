# STATUS: TRY_CALIBRATE_EULER_LEVER_V1

```yaml
OPERATIVE_CLASS: TRY_CALIBRATE_EULER_LEVER_V1
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_CALIBRATE_EULER_LEVER_v1
TASK_MODE: MATHEMATICAL_CALIBRATION_NOT_FORMAL_TXT_BUS_ADJUDICATION
SOURCE_BASE: 8acecc1574740c5163c2a4e8ef75049f6df84313
SOURCE_INBOX: 0dbf384877d6d20af0bdb4369f43f93422b79547
SOURCE_E_CONE_BLOB: b40a7b01de09cccad7803047a45ee16433f440d4
SOURCE_KERNEL_BLOB: 98380adf97aab19a900e332b6583c8f731b6d3f6
SOURCE_DH_BEURLING_BLOB: a3912756efbfac0825d96f29f35c0e834d38f560
SOURCE_QUIET_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_LEDGER_REPORT_BLOB: 2fc7d805c437bcc08e988131874878b7117f0c81
RH_PREFLIGHT_REFERENCE: 3ce4968d7ae23390f65e6c62daa6c3cf2cf6960d
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
G0: CLASSICAL_NONVANISHING_REPROVED_WITH_EXACT_WINDOW_E_CERTIFICATE
G0_CONE_FLOOR_ALONE: NOT_CLAIMED_SUFFICIENT
G0_COSINE_MODULATION_CARRIER_CLOSURE: REFUTED
G1: EXPLICIT_CLASSICAL_ZONE_PROVED_C_EQ_1_OVER_200_FOR_ABS_t_GE_3
G1_NOVEL_ZERO_FREE_RESULT: false
G2: EXACT_PREFIX_POISSON_AND_TURAN_MOMENT_INTERFACES
G2_AUTOMATIC_GAIN_FROM_QUIET_RESIDUAL: REFUTED_IN_THE_DECLARED_INFORMATION_CLASS
G2_NEW_COFINAL_ZONE_FOR_LITERAL_ZETA: NOT_PROVED
E1: EXACT_ZERO_PAIR_PLUS_BOUNDARY_MIXED_AND_BULK_TAIL_IDENTITY
E1_BOUNDARY_ONLY_TAIL: FAILS_RH_BRANCH_ON_THE_FULL_COMPLEMENT
E1_FULL_TAIL_SIGN_WITHOUT_RH: NOT_ESTABLISHED_OR_REFUTED_FOR_LITERAL_ZETA
E1_FIXED_m_BOUNDARY_COEFFICIENT: EVENTUALLY_POSITIVE_UNCONDITIONALLY
E1_MOVING_T_ASYMPTOTIC: NOT_INFERRED_FROM_FIXED_m_RESULT
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_PROGRESS
NEW_RH_SOURCE_FLOOR: NONE
RH_PROVED: false
INDEPENDENT_ANALYTIC_REVIEW: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
EXACT_CONTROL_GROUPS: 6
NUMERICAL_FOURIER_CONTROLS: 4
NEW_CCM_EIGENPROBLEMS: 0
WRITE_BRANCH: proshka_inbox_2026-10-31
ROUTE_STATE_CHANGED: false
```

## 0. Краткий результат и граница

G0 действительно воспроизводится из положительности настоящей эйлеровой меры. При этом **пол конуса не является сам по себе доказательством неравенства для произвольных модуляций**: умножение на cos(tx) не сохраняет конечный carrier и добавляет вторую корреляцию. Ни одна из этих операций не объявляется бесплатной.

G1: ниже дан самостоятельный, заведомо не оптимальный вывод

\[
\boxed{\zeta(\sigma+it)\ne0\quad\text{при}\quad
 |t|\ge3,\qquad \sigma\ge1-\frac1{200\log|t|}.} \tag{0.1}
\]

Это калибровка классического метода, не новое улучшение известных зон и не приближение к доказательству RH само по себе.

G2: известный префикс нулей действительно предоставляет вычислимые Poisson-суммы и частичные суммы степеней. Он допускает точную локальную лемму исключения нового нуля. Но \(\|A_mQ\|\to0\) не предоставляет требуемую дополнительную оценку логарифмических производных. Ни новая кофинальная зона, ни невозможность всякого арифметического усиления здесь не заявлены.

E1: точная формула содержит не только \(f(b)^2\), но также смешанный и внутренний хвосты. Чисто граничная замена опровергается уже на RH-ветви. Для отдельного граничного коэффициента положительный **fixed-m, T→∞** главный член выводится без RH. Это не знак всего хвоста на движущемся \(T\simeq\Omega_m\).

### Источники и терминология

S1. Inbox pin: `PROSHKA_VERDICT_EULER_SIGN_CONE_DH_SCOPE_2026-11-02.md`, §§0–3; определение E-конуса, пол и различие полной архимедовой формы и H_m. Локальный полный файл имеет тот же Git blob, что S1.

S2. Inbox pin: `PROSHKA_VERDICT_KERNEL_ORTHOGONALITY_2026-11-02.md`, §§1–3; физический Gram, точная корреляционная матрица и движущийся край. Локальный полный файл побайтно совпал по Git blob.

S3. Inbox pin: `PROSHKA_VERDICT_FAKE_WORLD_EFZ_DH_BEURLING_2026-11-02.md`; легенда E/F/Z/LA/A/I, корректный conductor-5 odd-gamma DH без полюса, signed coefficients. Не подменяется файлом с похожим именем без BEURLING.

S4. `2176dab`, `PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, особенно (4.1)–(4.7). Наследуется PAPER-поставщик полной невязки и оценок внешних evaluation-функционалов; заново без нулей он не доказывается.

S5. Base pin: `docs/routeB_bus/fake_worlds_2026-11-02/ledger_diff/ledger.csv` и `RESULT.md`. Это диагностика на **минимизаторах сжатия на дополнение**, не обязательно на полном bottom. Данные используют native kappa=1.1 и дополнительные cutoffs, не один доказанный кофинальный закон. Строки zeta55/zeta80 отдельно пересчитаны скалярно; матрицы не пересчитывались.

S6. `3ce4968`: использован именно принцип RH-first falsifier. Его conditional Gonek/Montgomery доказательство centered no-go в этой работе не импортируется как новое независимое подтверждение.

Классы сохраняются: **E** — Euler product/положительные Mangoldt-коэффициенты; **F** — конкретный functional-equation/gamma/pole контракт; **Z** — счёт нулей и кратностей, не их индивидуальные координаты; **LA** — алгебра/Fourier-геометрия/интегрирование; **A** — аналитическое продолжение, рост, фактические узлы; **I** — обычная целочисленная структура.

Внешние проверенные первичные справочники: Titchmarsh–Heath-Brown, *The Theory of the Riemann Zeta-Function*, §§2.12, 3.3, 9.6 (https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf); NIST DLMF 5.9.13 (https://dlmf.nist.gov/5.9.E13). Для масштаба уже известных результатов, **не как вход нашего доказательства**, Mossinghoff–Trudgian–Yang, arXiv:2212.06867, Theorem 1.3, имеет 5.558691 вместо нашего 200. PDF-тексты прочитаны; web-screenshot этих PDF вернул cache miss, дополнительная загрузка книжного PDF также не удалась. Это не визуальная/независимая проверка всего первичного доказательства. Новые формулы ниже выведены явно.

## 1. Неизменённая форма и RH-first gate

Пусть
\[
 L=\log m,\ b=L/2,\quad
 \phi_j(x)=d_j(-1)^jL^{-1/2}\cos(2\pi jx/L)\mathbf1_{[-b,b]},
 \quad d_0=1,\ d_j=\sqrt2\ (j>0).
\]
Используется вещественный чётный carrier \(V_m\), размерность m+1; действительных векторов достаточно для собственных значений вещественной симметричной матрицы. Комплексная версия получается поляризацией.
\[
 Q_f(s)=2\int f(x)f(x+s)dx,\quad
 \mu_m=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n},
\]
\[
 \mathfrak k_m[f]=\mathcal A[f]-c_*\|f\|^2
 +|\langle p,f\rangle|^2-\int Q_f\,d\mu_m,
\quad c_*=\gamma_E+\log(8\pi)+\pi/2.
\]
Все простые степени, архимедов хвост и полюс сохраняются. J_m и W_m=J_m^perp — исходные пространства S4; не заменяются real-zero-only kernel.

**RH-gate, до дальнейших выводов:**

| Узел | Проверка в RH-мире | Результат |
|---|---|---|
| G0 | tilted prime series абсолютно сходится при sigma>1; P(theta)>=0 | Нет недопустимого расходящегося остатка |
| G1 | цена gamma/pole — O(log t), именно такой бюджет заявлен; после деления на log t она конечна | Классическая зона совместима с RH; O(1) remainder здесь не обещан |
| G2 | тихая невязка может быть сверхмалой, но вклад нового критического нуля в высокую логарифмическую производную не мал | Перенос residual→Turan upper не проходит даже RH-control; §4.3 |
| E1 | на W_m∩ker(f→f(b)) есть ненулевые векторы; их RH-tail строго положителен | Хвост не может быть только rank-one функцией f(b); §5.4 |

Слово «расходится» относится к **заявленному бюджету**: логарифмическую цену в доказательстве зоны нельзя ошибочно считать опровержением теоремы, которая как раз допускает эту цену. У E1 отношение хвоста к f(b)^2 вообще не определено/неограниченно на нулевом следе.

## 2. G0 — точная калибровка эйлерова знака

### 2.1. Что даёт конус, а чего он не даёт

**[COFINAL_FAMILY | PAPER; E+F+LA.]** На S1-конусе Q_f(log p^k)<=0 сумма prime-вкладов неположительна и \(\mathfrak k_m[f]\ge-c_*\|f\|^2\). Это остаётся верным для каждого m. Но данное утверждение только на конусе не разрешает произвольное умножение f на cos(tx).

Для вещественного f точно
\[
 Q_{f\cos(t\cdot)}(s)=\frac12\cos(ts)Q_f(s)
 +\int f(x)f(x+s)\cos(2tx+ts)dx.                 \tag{2.1}
\]
Второе слагаемое не равно нулю по чётности. При добавлении sin-модуляции оно сокращается:
\[
 Q_{f\cos(t\cdot)}+Q_{f\sin(t\cdot)}=\cos(ts)Q_f.
\]
Однако f sin(tx) нечётна, а обе модуляции обычно выходят из исходного конечного носителя.

**Точное LA-препятствие.** При t≠0 никакое ненулевое конечномерное подпространство L2(I_L) не инвариантно относительно умножения на cos(tx). Иначе ограничение этого оператора имеет собственный вектор u≠0: (cos(tx)−a)u=0 почти всюду. Уровень cos(tx)=a имеет меру нуль, следовательно u=0. Противоречие. Даже при t=2πk/L верхняя мода создаёт новые частоты; lattice t не спасает фиксированный N=m.

Таким образом, ниже не производится запрещённое «получение всех модуляций из пола конуса». Используется тот же **E-поставщик**, но на его положительном скалярном двойственном тесте. Это явная граница, а не скрытая замена оператора.

### 2.2. Положительный сертификат в тех же оконных координатах

**[FINITE_CELL | PAPER; E+LA.]** Положим P(theta)=3+4cos(theta)+cos(2theta)=2(1+cos(theta))². Для phi_0=L^(-1/2)1_I имеем Q_phi0(s)=2(1−s/L)_+. Поэтому при sigma>1
\[
 \mathscr E_{m}(\sigma,t)
 =\frac12\int e^{-(\sigma-1/2)s}P(ts)Q_{\phi_0}(s)d\mu_m(s)
 =\sum_{n\le m}\Lambda(n)n^{-\sigma}
    (1-\log n/L)P(t\log n)\ge0.                    \tag{2.2}
\]
Это точное неравенство на исходной арифметике каждого окна. phi_0 не объявляется элементом W_m. Полюсные/архимедовы части не подвергаются неподтверждённой модуляционной оценке.

Пусть D(s)=−zeta'(s)/zeta(s). Абсолютная сходимость Euler product в Re s>1 и m→∞ при фиксированных sigma,t дают
\[
 \boxed{3D(\sigma)+4\Re D(\sigma+it)+\Re D(\sigma+2it)\ge0.} \tag{2.3}
\]
Используя вместо Lambda(n) вес Lambda(n)/log n, получаем также
\[
 \boxed{\zeta(\sigma)^3|\zeta(\sigma+it)|^4
                  |\zeta(\sigma+2it)|\ge1.}        \tag{2.4}
\]
Все prime powers сохранены. Это стандартный de la Vallée Poussin механизм, воспроизведённый через оконный taper, не новый критерий Weil-положительности.

### 2.3. Нулей на Re s=1 нет

**[ABSTRACT | PAPER; E+A+LA.]** При t0≠0 предположим нуль порядка r>=1 в 1+it0. Мероморфное продолжение zeta имеет единственный простой полюс в 1. Поэтому при eta↓0:
\[
 \zeta(1+\eta)=O(\eta^{-1}),\quad
 \zeta(1+\eta+it_0)=O(\eta^r),\quad
 \zeta(1+\eta+2it_0)=O(1).
\]
Левая сторона (2.4) равна O(eta^(4r−3))→0, противореча (2.4). Следовательно
\[
 \boxed{\zeta(1+it)\ne0\quad(t\ne0).}                \tag{2.5}
\]
В t=0 находится полюс, не конечное значение и не нуль. F/gamma, нулевой счёт Z и RH для (2.5) не нужны. Сам пол E-конуса, без глобального Euler product и указанного A-контракта, не является достаточным входом.

### 2.4. Точное место поломки DH

**[FINITE_CELL | PAPER; E-failure+LA, source-correct DH.]** В S3
\(b_D(2)=\tau\log2>0\), \(b_D(3)=−\tau\log3<0\),
\(b_D(6)=(1+\tau^2)\log6\ne0\). Поддержка — не только prime powers.

Есть строгий оконный отрицательный контроль **самой (2.2)**. Возьмём m=4, L=log4, t=π/log2. Тогда P(t log2)=P(π)=0; атом n=4 обнулён taper. Остаётся
\[
 \mathscr E^D_4(\sigma,t)=
 -\tau\log3\,3^{-\sigma}(1-\log3/\log4)
             P(\pi\log3/\log2)<0.                  \tag{2.6}
\]
Последний P строго положителен: равенство нулю требовало бы log3/log2 нечётным целым, то есть 3=2^(2k+1), что невозможно. Это настоящие DH-коэффициенты, а не произвольная отрицательная мера.

Кроме того, ряд −D_D'/D_D для DH нельзя переносить на всю Re s>1: там есть полюса в DH-нулях beta>1. Его достаточная область абсолютной сходимости дальше справа. У DH нет и zeta-полюса в 1. Таким образом, ломается уже E-шаг, до заключения о нулях; иной F_D-контракт не восстанавливает (2.2).

Для Beurling положительная Euler-мера сохраняет (2.2) на собственной опоре. Чтобы вывести (2.5), отдельно требуется A-контракт простого полюса и регулярности в 1+it. Чтобы перенести следующий G1 с его gamma-бюджетом, нужен уже конкретный F-контракт; S3 не поставляет его для DMV.

## 3. G1 — явная классическая зона с c=1/200

### 3.1. RH-precheck и разрешённый analytic import

На RH-ветви все последующие Poisson-числители sigma−beta положительны; dropping их не скрывает отрицательный остаток. Цена O(log t) заранее оставлена и не заменяется константой. Это классический zero-free аргумент, не новый положительный знак исходной CCM-формы.

Используется точный Hadamard/gamma identity, следующий из order-one product xi (Titchmarsh §2.12):
\[
 \Re D(s)=B(s)-\sum_\rho
     \frac{\sigma-\beta}{(\sigma-\beta)^2+(t-\gamma)^2},
\quad s=\sigma+it,\ \sigma>1,                       \tag{3.1}
\]
\[
 B(s)=\Re\left(\frac1s+\frac1{s-1}\right)
             -\frac12\log\pi+\frac12\Re\psi_\Gamma(s/2).
\]
Сумма считает все нетривиальные нули с кратностями. Здесь \(\psi_\Gamma\) — digamma, не арифметическая psi.

Для полноты, реальная константа Hadamard product исчезает точно: из xi(s)=xi(1−s), подстановок s=0,1 и симметрии нулей следует \(B_{Had}+\sum\Re(1/\rho)=0\). Поэтому (3.1) не содержит неизвестной O(1). Все нули имеют 0<=beta<=1 благодаря E вне Re s>1 и F-отражению; после G0 границы исключены. Это не RH.

### 3.2. Все численные константы

DLMF 5.9.13 даёт при Re z>0
\[
 \psi_\Gamma(z)=\log z-
 \int_0^\infty\left(\frac1{1-e^{-u}}-\frac1u\right)e^{-zu}du.
\]
Скобка лежит между 0 и 1, следовательно
\[
 |\psi_\Gamma(z)-\log z|\le (\Re z)^{-1}.             \tag{3.2}
\]
При 1<sigma<=2, t>=3 отсюда
\[
 B(\sigma+it)\le\tfrac12\log t+\tfrac43.             \tag{3.3}
\]
Действительно, две рациональные части <=3/t²<=1/3; |s/2|<=t; ошибка digamma/2 <=1; отрицательный −logπ/2 можно отбросить.

При вещественном sigma=1+eta<=2, digamma(sigma/2)<=digamma(1)=−gamma_E<0, поэтому
\[
 D(\sigma)\le\eta^{-1}+1.                            \tag{3.4}
\]

Пусть rho=beta+it — гипотетический нуль, t>=3, d=1−beta. Удерживаем его в (3.1), остальные положительные Poisson-ядра отбрасываем. Из (2.3):
\[
\begin{split}
0&\le3D(\sigma)+4\Re D(\sigma+it)+\Re D(\sigma+2it)\\
 &\le \frac3\eta-\frac4{\eta+d}
      +\frac52\log t+\frac{29}3+\frac12\log2\\
 &\le \frac3\eta-\frac4{\eta+d}+13\log t.             \tag{3.5}
\end{split}
\]
Последняя оценка использует log3>1 и log2<1. Кратность >=1 только усиливает отрицательное слагаемое.

Выбираем
\[
 \eta=\frac1{24\log t},\qquad 0\le d\le\frac1{200\log t}.
\]
Тогда правая часть (3.5) не превосходит
\[
 \left(72-\frac{600}7+13\right)\log t
 =-\frac57\log t<0.                                \tag{3.6}
\]
Противоречие доказывает (0.1); отрицательные t покрываются сопряжением. Никакой оптимизации или fitted constant не использовано.

**[COFINAL_FAMILY | PAPER; E+F+A+LA.]** G1 закрыт как классическая калибровка. Индивидуальное расположение всех нулей и RH не предполагались. Это не означает, что та же положительность уже дошла до Re s=1/2 либо до J_m^perp-floor.

### 3.3. Честный оконный возврат

Предел m→∞ выше берётся при фиксированных sigma,t. Если нужен совместный конечный бюджет, элементарный Chebyshev \(\psi(x)\le4\log2\,x\) даёт
\[
 0\le \mathscr E_\infty-\mathscr E_m
 \le8(4\log2)\sigma
       \left[\frac{m^{-\eta}}\eta+\frac1{L\eta^2}\right]. \tag{3.7}
\]
Знак разности также точен: P>=0 и taper<=1. Для доказательства nonvanishing этот остаток благоприятен; его не требуется мажорировать и затем вычитать с неправильным знаком.

Если всё же требуется абсолютная точность меньше (log t)/2, при eta из (3.6) достаточно явного, не оптимального L>=65536 log t. Upper в (3.7), делённый на log t, тогда <3465/8192<1/2. Этот масштаб нельзя незаметно отождествить с режимом t≈2πm/log m. При t≈Omega имеем L≈log t: (3.7) не даёт малой относительной ошибки. Сам знак (2.2) остаётся точным, но численная идентификация с полным logarithmic derivative требует своего бюджета.

## 4. G2 — что префикс нулей даёт Turan-методу и чего не даёт residual

### 4.1. Положительная лемма: префикс уже можно использовать

**[FINITE_CELL | PAPER; E+F+A+LA, actual zero data.]** Пусть все нули |gamma|<=T известны с кратностями. Определим
\[
 P_T(\sigma,u)=\sum_{|\gamma|\le T}
       \frac{\sigma-\beta}{(\sigma-\beta)^2+(u-\gamma)^2},
\quad \sigma>1,
\]
\[
 K_T=3P_T(\sigma,0)+4P_T(\sigma,t)+P_T(\sigma,2t),
\quad H=3B(\sigma)+4B(\sigma+it)+B(\sigma+2it).
\]
Если t>T и beta0<1, то
\[
 \boxed{H-K_T<\frac4{\sigma-\beta_0}
 \quad\Longrightarrow\quad
 \text{нет нуля }\beta+it\text{ с }\beta\ge\beta_0.}    \tag{4.1}
\]
Доказательство: при наличии такого **нового**, не включённого в префикс нуля (3.1) и (2.3) дают 0<=H−K_T−4/(sigma−beta)<=H−K_T−4/(sigma−beta0)<0. Префикс вычтен без изменения знака; полюсы и gamma остаются в H.

Это корректный способ получить дополнительную локальную область из проверенного списка. Она может улучшить конкретную константу или отдельный локальный interval. В текущем батче полный список не считывался и (4.1) не сертифицировалось численно; новая кофинальная зона из него не объявляется. \(\|AQ\|\) не входит в (4.1).

### 4.2. Точный объект для высоких степеней

**[ABSTRACT | PAPER; E+F+A+LA.]** Для k>=2 и Re s>1:
\[
 M_k(s):=\frac{(-1)^{k-1}}{(k-1)!}
       \left(\frac{\xi'}\xi\right)^{(k-1)}(s)
       =\sum_\rho(s-\rho)^{-k}.                       \tag{4.2}
\]
Положим h(s)=1/s+1/(s−1)−logπ/2+psi_Gamma(s/2)/2. Тогда
\[
 M_k(s)=\frac{(-1)^{k-1}h^{(k-1)}(s)}{(k-1)!}
 -\frac1{(k-1)!}\sum_{n\ge2}\Lambda(n)(\log n)^{k-1}n^{-s}.
                                                               \tag{4.3}
\]
Известные нули дают ровно
\[
 K_{k,T}(s)=\sum_{|\gamma|\le T}(s-\rho)^{-k}.
\]
Неизвестный объект Turan —
\[
 \boxed{U_{k,T}(s)=M_k(s)-K_{k,T}(s)
                  =\sum_{|\gamma|>T}(s-\rho)^{-k}.}   \tag{4.4}
\]
Это суммы степеней **обратных расстояний**, не оконных значений \(\widehat f(z_\rho)\). Тихая невязка не является ни их верхней оценкой, ни значениями производных xi'/xi.

Точный elementary E/I-upper при sigma=1+eta:
\[
 \frac1{(k-1)!}\left|\sum\Lambda(n)(\log n)^{k-1}n^{-s}\right|
 \le\frac{(4\log2)\sigma}{\eta^k}.                  \tag{4.5}
\]
Он получается интегрированием по частям против psi(x) и Gamma-интегралом. Гипотетический нуль с beta=1−d, gamma=t имеет масштаб (eta+d)^(-k), **не превосходящий** eta^(-k). Следовательно (4.5) само по себе не даёт противоречия для d>=0; увеличение k не создаёт выигрыш автоматически. Нужна новая фазовая/совместная арифметическая оценка (4.3) после вычитания известного префикса.

### 4.3. RH-first отрицательный контроль: residual не является Turan-данными

**[ABSTRACT | PAPER; унаследованный кофинальный evaluation-upper.]** Это контроль класса информации, не модификация истинной zeta с сохранением E. Для каждого m добавляется свой конечный набор новых нулей; не утверждается построение одного нового Euler/Dirichlet-источника на всех m. Контроль исключает универсальный перенос, который использует только перечисленные данные.

По S4 (4.2) для всех unit f in J_m значения \(\widehat f(z)\) сверхполиномиально малы равномерно при Re z>=T_m, |Im z|<=1/2. Обозначим этот upper через e_m. Для произвольного unit f in V_m норма evaluation-функционала не больше \(K_m=\sqrt L m^{1/4}\).

**Сначала RH-ветвь.** Добавим над cutoff одну пару реальных spectral-нулей ±Gamma, Gamma>T_m, к real-even completion, умножив её на 1−z²/Gamma². Все нули ниже T_m и J_m неизменны; RH-тип всех нулей сохраняется, order-one рост и ведущий zero-count тоже. В zero-form добавляется \(2vv^T\), поэтому
\[
 \|\Delta A_m Q\|\le2K_m e_m=o(m^{-B})\quad\forall B. \tag{4.6}
\]
Но в (4.4), при s=1+eta+iGamma, добавка содержит
\[
 (1/2+\eta)^{-k}+O((2\Gamma)^{-k}).                  \tag{4.7}
\]
При фиксированном k это не o(1); при растущем k может расти, несмотря на сверхмалую (4.6). Таким образом, перенос «quiet residual => small missing power sums» уже не проходит RH-контроль.

**Контроль новой зоны.** Добавим quartet ±z0, ±bar z0, z0=Gamma+i(1/2−d), Gamma>T_m, 0<d<1/2. Для s-нулей есть rho0=1−d+iGamma. Множитель
\[
 P(z)=\frac{(z^2-z_0^2)(z^2-\bar z_0^2)}{|z_0|^4}
\]
real-even, равен 1 в нуле, не меняет старые нули. Для real/imag evaluation-строк a,b новая форма равна 4(aa^T−bb^T) и
\[
 \|\Delta A_m Q\|\le8K_m e_m.                        \tag{4.8}
\]
Однако в (4.4) появляется (eta+d)^(-k), со сколь угодно малым выбранным d>0. Ни список ниже T, ни малость residual не запрещают такую добавку.

**Область опровержения:** F-симметрия, A/order/strip, ведущий Z-count, геометрия carrier, точный префикс и quiet-residual сами по себе не дают новой зоны. Полиномиально изменённая completion НЕ объявляется ordinary Euler-product zeta и может не иметь её Dirichlet/gamma-normalization контракта. Следовательно это не опровержение возможного усиления с новым E/I-поставщиком. У literal zeta отсутствующая оценка остаётся (4.4)/(4.3), а не источник J.

## 5. E1 — точная формула, граничная часть и незаменимый внутренний хвост

### 5.1. Exact identity для любого сжатого eigenvector

**[FINITE_CELL | PAPER; F+A+LA, inherited full source identity.]** Пусть f in W_m единична и является собственным вектором сжатия \(A_m\) на W_m с eigenvalue lambda. Тогда lambda=\(\mathfrak k[f]\). Это не требует, чтобы f была полным bottom.

Берём low-list |gamma|<=T; если исходный J определён строго |gamma|<T, граничные нули gamma=T включаются в low-list отдельно. Повторные нули имеют их настоящую кратность. Обозначим y=E_Tf. В вещественных координатах:
\[
 \mathcal J_T=\bigoplus[2\nu]\ \oplus\!
                \bigoplus\begin{pmatrix}4\nu&0\\0&-4\nu\end{pmatrix}.
\]
Первый блок соответствует критической паре, второй — complex quartet. Никакие derivative constraints при кратных нулях не добавляются.
\[
 \boxed{\lambda=y^T\mathcal J_Ty+\mathcal T_T[f],\qquad
 \mathcal T_T[f]=\sum_{|\gamma|>T}\widehat f(z_\rho)^2.} \tag{5.1}
\]
Здесь real-even f позволяет записать квадрат, не модуль. Общий Hermitian вариант есть \(\overline{\widehat f(\bar z_\rho)}\widehat f(z_\rho)\). Все суммы абсолютно сходятся для фиксированного m; их реальность следует из полной симметричной группировки.

### 5.2. Точный endpoint/bulk split без асимптотического пропуска

Пишем f=sum a_j phi_j, omega_j=2πj/L, e=f(b)=sum d_j a_j/sqrt L. При |Re z|>Omega:
\[
 \widehat f(z)=s_L(z)[e+r_f(z)],\quad
 s_L(z)=\frac{2\sin(bz)}z,
\quad
 r_f(z)=\frac1{\sqrt L}\sum_{j=1}^m
               \frac{d_j a_j\omega_j^2}{z^2-\omega_j^2}.       \tag{5.2}
\]
Это точное частичное разложение рациональной Fourier-формулы. Эквивалентно
\[
 \widehat f(z)=\frac{2e\sin(bz)}z
       -\frac{\widehat{f''_{int}\mathbf1_I}(z)}{z^2},          \tag{5.3}
\]
так как f'(±b)=0 для конечного cosine-carrier. Нулевое продолжение не объявляется глобально H2.

Следовательно
\[
 \boxed{\lambda=y^T\mathcal J_Ty+
        e^2 B_T+2e L_T[f]+Q_T[f],}                            \tag{5.4}
\]
\[
 B_T=\sum_{|\gamma|>T}s_L(z_\rho)^2,\quad
 L_T[f]=\sum_{|\gamma|>T}s_L(z_\rho)^2r_f(z_\rho),\quad
 Q_T[f]=\sum_{|\gamma|>T}s_L(z_\rho)^2r_f(z_\rho)^2.
\]
B_T — чисто граничный коэффициент; остальные два члена остаются. Их определение независимо от желаемого знака. Ортогональность W_m не зануляет их: на W_m известные evaluation-values свободны в своей физической Gram-метрике (S2).

### 5.3. Явный бюджет полной ошибки boundary-only приближения

Пусть T>Omega, theta_T=1−Omega²/T²>0, и
\[
 D_m(f)=\|f\|_2\left(\frac2L\sum_{j=1}^m\omega_j^4\right)^{1/2},
\quad S_k(T)=\sum_{\gamma>T}\gamma^{-k},
\]
где S_k считает верхние нули с кратностями. Тогда
\[
 |r_f(z_\rho)|\le\frac{D_m(f)}{\theta_T\gamma^2},
\quad |s_L(z_\rho)|\le\frac{2m^{1/4}}{|\gamma|}.
\]
Отсюда без RH
\[
 \boxed{|2eL_T[f]+Q_T[f]|
 \le8\sqrt m\left[
    \frac{2|e|D_m(f)}{\theta_T}S_4(T)
    +\frac{D_m(f)^2}{\theta_T^2}S_6(T)\right].}          \tag{5.5}
\]
При RH множитель sqrt m можно заменить на 1. Это absolute upper, не утверждение о знаке реального хвоста.

С явным счётом S4 можно пользоваться полностью численным majorant: если N(u)<=u log u/(2π)+log u+10 для u>=T>=e, то
\[
 S_k(T)\le\frac{kT^{1-k}}{2\pi}
 \left[\frac{\log T}{k-1}+\frac1{(k-1)^2}\right]
 +T^{-k}(\log T+10+1/k),\quad k>1.                       \tag{5.6}
\]
Это следствие интегрирования по частям с отброшенным неположительным −N(T)/T^k; endpoint multiplicities не теряются.

На T=kappa_m Omega с kappa_m↓1 множитель theta_T^(-1) растёт, а e может быть сколь угодно мал. Поэтому (5.5) НЕ является относительной o(e² log T/T)-оценкой. Неудача этого upper сама по себе не refutation настоящего selected-bottom asymptotic.

### 5.4. RH-first: чисто граничный хвост невозможен на всём W_m

**[FINITE_CELL | CONDITIONAL on RH; exact theorem-shape obstruction.]** При RH
\[
 \mathcal T_T[f]=2\sum_{\gamma>T}\nu_\gamma
                         |\widehat f(\gamma)|^2\ge0.          \tag{5.7}
\]
Более того, для каждого фиксированного m и T он строго положителен на каждом ненулевом f in V_m.

Доказательство строгого знака, без предположения простоты. Рациональная формула S2 даёт \(\widehat f(z)=2z\sin(bz)P_f(z^2)/(\sqrt L\prod_{j=0}^m(z^2-\omega_j^2))\), где ненулевой P_f имеет степень <=m. Если (5.7)=0, все поздние zeta-нули, кроме конечного числа корней P_f, должны быть automatic sinc-нулями: gamma log m in 2πZ. Тогда при RH
\[
 \sum_{0<\gamma\le Y}m^\rho=\sqrt m\,N(Y)+O_{m,T,f}(1).
\]
Но fixed-x Landau/Gonek, уже используемый S4, даёт для x=m>=2
\[
 \sum_{0<\gamma\le Y}m^\rho
       =-\frac{Y}{2\pi}\Lambda(m)+O_m(\log Y),
\]
что несовместимо с N(Y)~Y log Y/(2π). Кратности стоят в обеих суммах, никаких distinct/simple assumptions нет. Противоречие.

Если dim W_m>=2, найдётся ненулевой f in W_m с e=f(b)=0. Для него \(\mathcal T_T[f]>0\), тогда как B_T e²=0. Следовательно ни exact boundary-only identity, ни universal upper \(\mathcal T_T[f]\le C_{m,T}|f(b)|²\) не возможны даже в RH-мире. Хвостовый оператор на W_m имеет полный ранг dim W_m, а endpoint form — ранг <=1.

**Область:** это утверждение о всём дополнении. Оно не утверждает, что конкретный измеренный complement-minimizer имеет нулевой след, и не опровергает отдельный selected-vector asymptotic с дополнительной relative-error теоремой. Выбросить Q_T и mixed term для всех f нельзя.

### 5.5. Что можно сказать без RH о знаке

1. У каждого complex quartet полный вклад равен \(4\nu[(\Re\widehat f(z))^2-(\Im\widehat f(z))^2]\). Это indefinite pairing, не абсолютный квадрат. Поэтому знака **полной** \(\mathcal T_T\) из одной симметрии и счёта нет. Отрицательность настоящего tail для zeta при заданном T этим тоже НЕ доказана.

2. Для отдельного B_T есть полезный, но строго fixed-m результат. При фиксированном целом m>=2, T→∞, без RH:
\[
 \boxed{B_T=\frac2{\pi T}
 \left[\log\frac{T}{2\pi}+1+\frac{\Lambda(m)}{\sqrt m}\right]
 +O_m\!\left(\frac{\log T}{T^2}\right)>0
 \quad\text{для достаточно больших T}.}                \tag{5.8}
\]

Доказательство. По beta in (0,1), замена z_rho^(-2) на gamma^(-2) имеет цену O_m(log T/T²). Используем 4sin²(bz)=2−2cos(Lz). Положительный неосциллирующий момент равен
\[
 \sum_{\gamma>T}\gamma^{-2}
 =\frac{\log(T/(2\pi))+1}{2\pi T}
       +O(\log T/T²).
\]
Симметрия beta↔1−beta и fixed-x Landau/Gonek дают
\[
 A_m(Y):=\sum_{0<\gamma\le Y}\cos(Lz_\rho)
 =m^{-1/2}\Re\sum_{0<\gamma\le Y}m^\rho
 =-\frac{\Lambda(m)}{2\pi\sqrt m}Y+O_m(\log Y).
\]
Интегрирование Стилтьеса с весом gamma^(-2), затем удвоение для обоих знаков gamma, дают (5.8). Все кратности сохранены. Это E+F+A+Z+LA, не RH и не численный fit.

Нельзя подставлять m→∞, T≈m/log m в O_m из (5.8). Именно такой неоплаченный uniformity-переход вернул бы старую проблему. Тем более положительность B_T не доказывает положительность B_Te²+2eL_T+Q_T.

### 5.6. Чтение эмпирической константы

Из S5 пересчитаны только скалярные отношения для двух сохранённых строк:
\[
 \frac{\lambda}{f(b)^2\log T/(\pi T)}
 =3.58052952828253854\quad(m=55),
\qquad 4.30005139932603235\quad(m=80).
\]
Это подтверждает заявленный диагностический масштаб, не его интерпретацию. lambda здесь включает \(y^T\mathcal J_Ty\), mixed tail и Q_T; это минимум **сжатия на дополнение**. T native=1.1 Omega. Постоянный fixed-m главный коэффициент B_T в (5.8) — 2, а не автоматически 4; finite transition T≈Omega и low-value contribution не позволяют отождествить наблюдаемое отношение с B_T. Даже при RH верх 0<=B_T<=8 S_2(T) даёт лишь envelope порядка 4 log T/(πT), не точную формулу.

## 6. Реестр E / F / Z / LA / A / I

| Шаг | Непосредственные входы | Что не импортируется |
|---|---|---|
| Пол E-конуса | E+F+LA | Нет full complement sign |
| P=2(1+cos)^2 и finite tilted test | E+LA | Нет carrier invariance |
| G0, pole-versus-zero contradiction | E+A+LA | Ни F/gamma, ни RH, ни zero count |
| DH отрицательный tilted m4 test | фактические signed коэффициенты + LA/I | Не численный отрицательный eigenvalue |
| G1 Hadamard/gamma budget | E+F+A+LA | Не расположение всех нулей на линии |
| Оконный Chebyshev budget | E+I+LA | Не uniform equality при t≈Omega |
| G2 prefix Poisson criterion | actual nodes A + E+F+LA | Не вывод из delta |
| Turan power-sum identity | E+F+A+LA | Quiet values не заменяют derivatives |
| Added-zero controls | LA+A+F-симметрия+ведущий Z | Не сохраняется E/ordinary Dirichlet contract |
| E1 точная нулевая формула | inherited E+F+A, затем LA | Нет absolute-square подмены |
| E1 boundary split и explicit bound | LA+A+Z | Нет automatic relative error |
| E1 fixed-m coefficient | E+I+F+A+Z+LA через Landau | Не moving-m uniformity |
| E1 all-tail positivity | CONDITIONAL RH | Безусловно для moving cutoff не получена |

## 7. Проверки, closeout и единственный следующий тест

Предрегистрация локальных проверок выполнена до запуска: тождество 3–4–1, modulation cross term, рациональный margin −5/7, DH m4 отрицательный знак, modal boundary/bulk split, quartet metric и две ledger-строки. Шесть exact-control groups прошли; четыре независимых физических Fourier-интеграла при 65 dps совпали с (5.2), максимальное расхождение 1.26492631389e−65. Это floating diagnostic, не interval enclosure и не доказательство общего квантора. Скрипт и результат ниже включены полностью.

P1–P5 подтверждены в своих заявленных областях; P6 подтверждён только как повторная скалярная диагностика сохранённых данных. Независимых агентов/аудитов не запускалось. Lean/Arb не выполнялись. Код не содержит нового eigenproblem.

Что закрыто: G0 и явная G1 как классические калибровки; точные префиксные формулы G2; полная E1 с количественным endpoint/bulk бюджетом; RH-обструкция universal rank-one tail и конкретный finite DH E-failure.

Что НЕ закрыто: новая кофинальная нулевая зона из quiet space, знак полного moving-tail, fixed lower floor на исходном дополнении, RH.

DOWNSTREAM_CONSUMER: constant lower floor исходного literal CCM на неограниченной семье.
ACTUAL_CONSUMER_REQUIREMENT: источник-заданный совместный арифметический lower bound, не новая запись классической зоны.
ORIGINAL_REQUESTED_OBJECT: калибровка G0/G1/G2/E1 с RH-first проверкой.
ORIGINAL_OBJECT_IS: диагностический интерфейс, NOT_NECESSARY как единственный путь к consumer.
FAILURE_TYPE: COUNTEREXAMPLE для modulation-closure и RH boundary-only theorem-shapes; NO_DERIVATION для нового literal G2/tail-sign.
EPISTEMIC_STATUS: RESEARCH_DEBT у literal sign; точные scope-обструкции не означают смерть RH-маршрута.
REOPEN_TRIGGER: независимая quantitative upper оценка (4.4) либо signed bound всей (5.4) на требуемом carrier.
NOVELTY_AXIS: исключение недопустимых переносов; не заявляется новизна классического zero-free результата.

Две допустимые репрезентации следующей попытки:

1. **Prefix Poisson (4.1).** На actual known nodes вычисляется нижняя граница K_T, а H — явно. Сила высокая для конечного local exclusion; цена умеренная. Кофинальный выигрыш требует доказанной униформности, не файла всё большего размера.
2. **Turan residual (4.4) / полный tail (5.4).** Удержать known prefix и положительную gamma-часть до оценки остатка, либо оценивать полный tail в kernel Gram, не только endpoint. Сила максимальная для проверки механизма; цена высокая из-за арифметрических смешанных членов. delta не используется как их upper.

DISCRIMINATOR: для G2 — строгая отрицательная верхняя граница H−K_T−4/(sigma−beta0), с полными interval costs; для E1 — полный signed Rayleigh tail и отдельные e²B_T,2eL_T,Q_T на одном векторе. Нуль-согласованный результат не является сертификатом знака. Отдельно тестировать endpoint-zero directions; это cheapest falsifier rank-one обрезки.

**CODEX DIRECTIVE: CALIBRATE_EULER_LEVER_SOURCE_AUDIT.** На закреплённых источниках проверить (2.1)–(2.6), digamma-budget и margin (3.6), затем (5.1)–(5.5) в физической норме, со всеми кратностями. Для сохранённых complement-vectors из ledger_DIFF разложить одно и то же lambda на low-pair, boundary, mixed и bulk tail с честным zero-tail envelope; endpoint-only не подставлять. G2: отдельный quantified сертификат (4.1), не residual-saturation. Отчёт должен различать exact algebra, floating agreement и interval theorem; никаких новых route-state/RH exports.

Memory entry: fixed window does not commute with arbitrary modulation; a full-operator quiet residual is not a logarithmic-derivative bound; far-zero endpoint expansion is nonuniform at T/Omega→1. Forbidden move: replacing a rank-full RH tail by one endpoint square, or interpreting an added-zero falsifier as an Euler-product zeta counterexample.

Verification handoff: новый Markdown в `docs/routeB_bus/proshka/`, ветка inbox. Собственный SHA коммита сообщается после записи, не встраивается в его содержимое. Lean-файлы не пишутся; axiom profile и lake-команды неприменимы. Для локального повторения извлечь Appendix A в файл и запустить `uv run --with sympy --with mpmath python checks.py`. Это исполняет локальные контроли, не независимый analytic audit.

## Appendix A. Исполненный код

```python
#!/usr/bin/env python3
"""Local algebra and numerical diagnostics for CALIBRATE_EULER_LEVER_v1.
Not interval arithmetic. No CCM matrix is diagonalized. Dependencies: sympy, mpmath.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sympy as s
import mpmath as mp

def main() -> None:
    mp.mp.dps=65
    th,u,v,z,p=s.symbols('th u v z p', real=True)
    assert s.trigsimp(3+4*s.cos(th)+s.cos(2*th)-2*(1+s.cos(th))**2)==0
    assert s.trigsimp(s.cos(u)*s.cos(u+v)+s.sin(u)*s.sin(u+v)-s.cos(v))==0
    assert s.simplify(z/(z*z-p)-1/z-p/(z*(z*z-p)))==0
    margin=F(3,1)/F(1,24)-F(4,1)/(F(1,24)+F(1,200))+13
    assert margin == -F(5,7)
    window_error=F(27648,65536)+F(1152,2**20)
    assert window_error < F(1,2) < F(5,7)
    a,b=s.symbols('a b', real=True)
    assert s.expand(2*(a+s.I*b)**2+2*(a-s.I*b)**2-4*(a*a-b*b))==0
    # Numerical DH coefficient/sign control; strict proof is supplied in the text.
    tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
    L=mp.log(4); t=mp.pi/mp.log(2); sig=mp.mpf('1.2')
    poly=lambda x: 2*(1+mp.cos(x))**2
    dh3=-tau*mp.log(3)*mp.power(3,-sig)*(1-mp.log(3)/L)*poly(t*mp.log(3))
    assert dh3 < 0
    # Exact algebra has already checked the rational decomposition. These are
    # independent physical integrations on the same phased cosine basis.
    maxerr=mp.mpf(0)
    for m in (4,8):
        L=mp.log(m); bb=L/2
        coeff=[mp.mpf(j+1)/mp.mpf(m+2) for j in range(m+1)]
        def phys(x):
            return sum(coeff[j]*(1 if j==0 else mp.sqrt(2))*(-1)**j*
                       mp.cos(2*mp.pi*j*x/L)/mp.sqrt(L) for j in range(m+1))
        endpoint=phys(bb)
        for zz in (mp.mpc(2*mp.pi*m/L+3,'0.1'),mp.mpc(2*mp.pi*m/L+7,'-0.4')):
            ff=mp.quad(lambda x: phys(x)*mp.e**(-1j*zz*x),[-bb,0,bb])
            rr=sum((1 if j==0 else mp.sqrt(2))*coeff[j]*(2*mp.pi*j/L)**2/
                   (zz**2-(2*mp.pi*j/L)**2) for j in range(m+1))/mp.sqrt(L)
            expr=2*mp.sin(bb*zz)/zz*(endpoint+rr)
            err=abs(ff-expr); maxerr=max(maxerr,err)
            assert err < mp.mpf('1e-55')
    # Values transcribed from the pinned ledger.csv, not a new eigensystem.
    rows=[(55,'94.8592726168121105720022029268766262702321442302337',
           '0.00010705124623306283988812377053502070877247361688355',
           '0.0442402041727675167452963573123961797131716687348126'),
          (80,'126.179129687775835326116556085892776564838432141588',
           '0.00000038176331644860424123011145374064298429261298606845',
           '-0.00269717665873658608049902132233767880341316308978514')]
    ratios=[]
    for m,T,lam,fb in rows:
        T,lam,fb=map(mp.mpf,(T,lam,fb))
        ratio=lam/(fb**2*mp.log(T)/(mp.pi*T))
        assert 3 < ratio < 5
        ratios.append({'m':m,'ratio_lambda_over_edge_scale':mp.nstr(ratio,32)})
    result={'exact_control_groups':6,'numeric_fourier_samples':4,
            'max_fourier_error':mp.nstr(maxerr,12),
            'G1_margin_over_log_t':str(margin),
            'safe_window_error_over_log_t':str(window_error),
            'DH_m4_negative_tilted_sum':mp.nstr(dh3,24),
            'ledger_ratios':ratios,'interval_certificate':False,
            'new_CCM_eigenproblems':0,'independent_analytic_review':False}
    Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
```

## Appendix B. Фактический локальный результат

```json
{
  "exact_control_groups": 6,
  "numeric_fourier_samples": 4,
  "max_fourier_error": "1.26492631389e-65",
  "G1_margin_over_log_t": "-5/7",
  "safe_window_error_over_log_t": "3465/8192",
  "DH_m4_negative_tilted_sum": "-0.0553546731876805377472686",
  "ledger_ratios": [
    {
      "m": 55,
      "ratio_lambda_over_edge_scale": "3.5805295282825385400813641273516"
    },
    {
      "m": 80,
      "ratio_lambda_over_edge_scale": "4.3000513993260323459900714056819"
    }
  ],
  "interval_certificate": false,
  "new_CCM_eigenproblems": 0,
  "independent_analytic_review": false
}

```
