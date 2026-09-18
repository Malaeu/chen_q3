# STATUS: TRY_SIGNED_THETA_CURVATURE_WITH_PAID_COMPACT
```yaml
OPERATIVE_CLASS: TRY_SIGNED_THETA_CURVATURE_WITH_PAID_COMPACT
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-18
SOURCE_COMMIT: 181873396b93324681c7041972f2b68adbe1d672
PREVIOUS_VERDICT_COMMIT: 4dd6fe34401e1436144ef93b03548e780ee25507
SOURCE_FAMILY: LITERAL_FOLDED_THETA_RAYS
EVIDENCE_STATE: PAPER_PROOF_WITH_EXECUTED_EXACT_INTEGER_INTERVAL_CHECKER
VERIFIER: PAPER
ARITHMETIC: OUTWARD_DYADIC_PYTHON_INTEGERS
PRECISION_BITS: 384
PRECISION_REPEAT_BITS: 768
INDEPENDENT_EXTERNAL_REVIEW: PENDING
LEAN_KERNEL_CHECKED: false
ARB_USED: false
ABSOLUTE_ENCLOSURE_REDERIVED: true
SIGNED_E_COH_CONTINUUM:
  T: sqrt(20)
  sigma: (0,1/2]
  N: all_integers_at_least_5
  scope: FINITE_CELL
COMPACT_FULL_H:
  T: [-30,30]
  sigma: (0,1/2]
  lower_bound: sigma*exp(-pi*abs(T)/2)/25
  scope: FINITE_CELL
ORIGINAL_ADAPTIVE_HEAD:
  T: [4,30]
  lower_bound: 9*sigma*exp(-pi*T/2)
  scope: FINITE_CELL
GLOBAL_TAIL_ABOVE_30: OPEN
GLOBAL_E_COH_LOWER_BOUND: NOT_PROVED
GLOBAL_RELATIVE_MPLUS_BUDGET: NOT_PROVED
GLOBAL_QUARTER_MASS_GAP: NOT_PROVED
OLD_ONE_FIFTH_BUDGET:
  status: REFUTED
  KILL_SCOPE: THEOREM_SHAPE
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_FIXED_BUDGET
  evidence: section_3_exact_negative_upper_endpoint
THETA_HEAD_NEGATIVE_WITNESS: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
PRODUCTION_STATE_CHANGED: false
LEAN_FILES_CHANGED: false
CODEX_DISPATCHED: false
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
```

Ы. Получены две нижние оценки для буквальной theta-источника: подписанный полный E_coh на целом горизонтальном отрезке и положительная полная H на целом компактном прямоугольнике. Бесконечный хвост по T не закрыт. Численная сетка не занимает квантор: конечная арифметика проверяет коэффициенты полиномиальной нижней оболочки, а аналитические оценки оплачивают оба бесконечных остатка.

## 1. Источники, объект и область утверждений

[ABSTRACT][PAPER] Прочитан действующий протокол `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` на `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`.

Математический источник: `docs/routeB_bus/proshka/PROSHKA_FOLDED_FULL_SOURCE_CONTOUR_ENCLOSURE_2026-09-17.md`, §§1–6, на SOURCE_COMMIT, blob `796f1cb127b3b9d2caeff01e25d5c10f33a3fc61`.

Предыдущий вердикт: `docs/routeB_bus/proshka/PROSHKA_VERDICT_COHERENT_MEANS_SIGN_TRANSFER_2026-09-18.md` на PREVIOUS_VERDICT_COMMIT. Его отдельный достаточный бюджет epsilon <= 1/5 проверен, а не принят как гипотеза. Старые файлы не изменяются.

Сохраняем

\[
a_n=\pi n^2,\quad
\phi_n(z)=(4a_n^2e^{9z/2}-6a_ne^{5z/2})e^{-a_ne^{2z}},\quad
\Phi=\sum_{n\ge1}\phi_n,
\]
\[
F(p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt=\xi(1/2+p),\qquad
\mathcal H(p)=4\Re(F'(p)\overline{F(p)}).
\]

Для фиксированных theta,N:

\[
I_n(p,\theta)=\int_0^\infty\phi_n(t+i\theta)e^{p(t+i\theta)}dt,
\quad J_N=\sum_{n\le N}[I_n(p,\theta)+I_n(-p,-\theta)],
\quad h_N=4\Re(J_N'\overline{J_N}).
\]

Все производные берутся при фиксированных theta,N. Никто не дифференцирует округлённый срез или theta(T). В компактном доказательстве вспомогательные головы выбираются по блокам; их спектральные массы не отождествляются с массами исходного адаптивного среза. Неизменным объектом между блоками служит полная F.

Нормировка M_+ сохраняется: положительная спектральная часть полной эрмитовой матрицы A_ij=2(conj(u_i)v_j+conj(v_i)u_j), вычисленная на e=(1,...,1). Это не положительное собственное значение само по себе.

## 2. Точное подписанное сокращение E_coh

[ABSTRACT][PAPER] Пишем X=sum I_n^+, Y=sum I_n^-, X_t=X'-i theta X, Y_t=i theta Y-Y'. При XY != 0:

\[
\alpha=X_t/X,\quad\beta=Y_t/Y,\quad
m=(\Re\alpha+\Re\beta)/2,
\]
\[
\frac{h_N}{4}=m(|X|^2-|Y|^2)+E_{\rm coh},
\]
\[
E_{\rm coh}=\frac{\Re\alpha-\Re\beta}{2}|X+Y|^2
-(\Im\alpha+\Im\beta)\Im(X\overline Y).
\]

При фиксированном T введём A(s)=exp(-i theta s)X(s+iT). Сопряжённость буквальных лучей даёт

\[
Y(s)=e^{i\theta s}\overline{A(-s)},\quad
\alpha(s)=A'(s)/A(s),\quad\beta(s)=\overline{\alpha(-s)}.
\]

Если A не обращается в ноль на соответствующей окрестности, то

\[
C(s)=\frac{\alpha(s)-\alpha(-s)}{2s}
=\frac1{2s}\int_{-s}^s(\log A)''(u)\,du
\]

продолжается чётно и голоморфно через s=0. Положим W=|X|^2+|Y|^2+2X conjugate(Y). Тогда точно

\[
\boxed{E_{\rm coh}/s=\Re(C(s)W(s)).}
\tag{2.1}
\]

Доказательство: alpha-beta_conjugate=2sC. Следовательно Re alpha-Re beta=2s Re C и Im alpha+Im beta=2s Im C. Действительная часть W равна |X+Y|^2, мнимая равна 2 Im(X conjugate(Y)). Подстановка даёт (2.1).

Это не модульная оценка: отрицательная и положительная части комплексного произведения сохраняются до последнего шага. Ни общего вещественного tau, ни Коши–Шварца по N здесь нет. В точках возможного нуля кластера используется безделительная конструкция §5, а не неопределённое отношение.

## 3. Два результата для настоящих лучей при T=sqrt(20)

[FINITE_CELL][PAPER] Здесь theta=pi/4-1/(sqrt(20)+1).

### 3.1 Старый бюджет 1/5 действительно ложен

При sigma=1/64, N=10 точная наружная интервальная арифметика даёт

\[
-4.554\cdot10^{-7}
< E_{\rm coh}+\frac15\sigma m|X|^2
< -4.193\cdot10^{-7}<0.
\tag{3.1}
\]

Это отрицательная ВЕРХНЯЯ граница для прежнего достаточного запаса. Положительность самой головы не опровергнута: одновременно h_N > 0.00030972. Интервал epsilon=-E_coh/(sigma m|X|^2) находится внутри (0.20241049,0.20261750).

Проверяется буквальная формула луча. Программа использует первые четыре луча и аналитическую оценку всех остальных; производную считает центральной разностью с шагом 2^-20 и явным третьепроизводным остатком D step^2/6. Никакая разность не объявляется точной производной. Срез N=10 проверен через ceil из (6.3).

KILL_SCOPE: THEOREM_SHAPE. Убит ровно фиксированный бюджет epsilon <= 1/5. Не theta-голова, не источник, не RH.

### 3.2 Нижняя оценка полного E_coh на всём горизонтальном отрезке

[FINITE_CELL][PAPER] Для ВСЕХ N >= 5 и ВСЕХ 0 < sigma <= 1/2 доказано:

\[
\boxed{-\frac{23}{10000}\sigma<E_{\rm coh}< -\frac{22}{10000}\sigma,}
\tag{3.2}
\]
\[
\boxed{m>\frac4{25},\qquad
E_{\rm coh}\ge-\frac{51}{250}\sigma m|X|^2.}
\tag{3.3}
\]

Полученные интервалы до рационального округления:

| Величина | Нижняя граница | Верхняя граница |
|---|---:|---:|
| E_coh/sigma | -0.002256986 | -0.002243842 |
| epsilon | 0.1717035 | 0.2037382 |
| m | 0.1627291 | 0.1628273 |
| h_N/sigma | 0.01982358 | 0.02006431 |

В частности h_N >= (19/1000)sigma. Это целый отрезок, включая сколь угодно малые положительные sigma, а не набор выбранных sigma.

Механизм проверяем: на |z| <= 3 строятся коэффициентные интервалы A; первые пять лучей вычисляются, весь n>=6 хвост оплачивается. На |z| <= 2 доказано |A(z)| > 0.0835773. Это разрешает деление в alpha=A'/A. Для alpha доказана верхняя модульная граница <1.5108 на диске радиуса 2. Коэффициенты alpha получаются треугольным делением рядов, C — из нечётных коэффициентов alpha, m — из чётных. W раскрывается целиком. Остатки рядов оплачиваются через Коши; затем интервальный Horner применяется к sigma^2 в [0,1/4]. Именно поэтому (3.2) является подписанной оценкой на континууме.

Константа 51/250 — ремонт после отказа 1/5, НЕ заранее предсказанный результат. Она не переносится на другие T без нового доказательства.

## 4. Абсолютная оболочка: независимая повторная выкладка

[ABSTRACT][PAPER] При c=cos(2theta)>0, M=N+1 и pi c M^2>=1 определим

\[
D(c)=4c^{-4},\qquad B(c,M)=448c^{-1}M^3e^{-\pi cM^2}.
\]

Для j=0,1,2 и |Re p|<=1/2:

\[
|F^{(j)}|,|J_N^{(j)}|\le D(c)e^{-\theta T},\qquad
|F^{(j)}-J_N^{(j)}|\le B(c,M)e^{-\theta T}.
\tag{4.1}
\]

Деталь констант. Подстановка u=e^(2t), |t+i theta|^j <= exp(jt) и |exp(pt)|<=exp(t/2) мажорируют вклад пары выражением

\[
4a_n^2\int_1^\infty u^3e^{-a_ncu}du+
6a_n\int_1^\infty u^2e^{-a_ncu}du.
\]

Полная сумма <=36c^-4 pi^-2 sum n^-4 <4c^-4; последнее сравнение следует из рациональной верхней границы 880625/221841<4. При b_n=a_nc>=1 интегралы ограничены соответственно 16e^-b_n/b_n и 5e^-b_n/b_n. Затем

\[
\sum_{n=M}^\infty n^2e^{-bn^2}
\le e^{-bM^2}\left(M^2+\frac{M}{2b}+\frac1{4b^2M}\right)
\le\frac74M^3e^{-bM^2}
\]

и 64pi+30<256 дают B. Те же оценки применимы к чистым t-моментам после удаления общего контура-фазы, когда |Re z|+j<=7/2; это используется в §5.

По Jacobi-сопряжённости J_N(-conj(p))=conj(J_N(p)), поэтому H(iT)=h_N(iT)=0. Положим E_j=F^(j)-J_N^(j). Точное раскрытие

\[
F''\bar F-J_N''\bar J_N=E_2\bar F+J_N''\bar E_0
\]

и аналогичная разность квадратов первых производных дают

\[
|\partial_\sigma(\mathcal H-h_N)|\le16DB e^{-2\theta T}.
\]

Интегрирование от нулевого начального значения доказывает

\[
\boxed{|\mathcal H-h_N|\le\sigma e_N,\quad
 e_N=28672c^{-5}M^3e^{-\pi cM^2-2\theta T}.}
\tag{4.2}
\]

Никакой нижней границы M_+ в этом выводе нет. Ни деления на F, ни предположения об отсутствии её нулей тоже нет.

Контур законен: Jacobi делает полную Phi чётной в |Im z|<pi/4; её ряд локально нормально сходится, а e^-a_n c exp(2t) оплачивает горизонтальные концы и производные. Конечная сумма не объявляется чётной: сохраняется именно отражённая пара лучей, включая дефект шва исходной конструкции.

Для исходного r=0 среза

\[
\theta(T)=\pi/4-1/(T+1),\quad
M(T)=\left\lceil\sqrt{\frac{(T+1)(32+20\log(T+1))}{3}}\right\rceil
\]

при T>=1 сохраняется абсолютное следствие источника

\[
e_{N(T)}\le e^{-\pi T/2}.\tag{4.3}
\]

Оно следует из c>=1/(T+1), exp(-2theta T)<=8exp(-pi T/2), и того же явного бюджета §6 исходника. Из (4.2) или (4.3) НЕ следует глобальное e_N<M_+/4.

В этой работе повторно выведен абсолютный блок. Это не внешняя независимая приёмка автором, не участвовавшим в предыдущих обсуждениях. INDEPENDENT_EXTERNAL_REVIEW остаётся PENDING.

## 5. Полная H положительна на всём |T|<=30

[FINITE_CELL][PAPER] Получен результат

\[
\boxed{\mathcal H(\sigma+iT)\ge\frac1{25}\sigma e^{-\pi|T|/2}>0
\quad(0<\sigma\le1/2,\ |T|\le30).}
\tag{5.1}
\]

Для 4<=|T|<=30 доказана более сильная граница

\[
\boxed{\mathcal H(\sigma+iT)\ge10\sigma e^{-\pi|T|/2}.}\tag{5.2}
\]

Здесь не используются прежний сертификат q>18, список известных нулей, RH, простота нулей, четвертная оценка G или относительная нижняя граница M_+. Доказательство строится непосредственно из phi_n.

### 5.1 Блоки и аналитический объект

Центры t_j=1,3,...,29. В j-м блоке T находится в замкнутом [t_j-1,t_j+1], sigma в [0,1/2]. Угол theta_j=pi/4-1/(t_j+1) и N_j из (6.3) В ЦЕНТРЕ фиксируются на всём блоке.

Определим

\[
A_j(z)=e^{\theta_j t_j-i\theta_jz}
\sum_{n\le N_j}I_n(it_j+z,\theta_j).
\]

Это в точности интеграл sum phi_n(t+i theta_j) exp(it_j t) exp(zt). Следовательно |A_j(z)|<=D_j=4c_j^-4 на диске |z|<=3. При |Re z|<=1/2 производные порядков 0,1,2 также ограничены D_j.

Пусть A_j^*(z)=conj(A_j(conj(z))) и P_j(z)=A_j(z)+A_j^*(-z). Тогда

\[
J_{N_j}(it_j+z;\theta_j)=e^{-\theta_jt_j+i\theta_jz}P_j(z),
\quad h_{N_j}=4e^{-2\theta_jT}\Re(P_j'(z)\overline{P_j(z)}).
\]

Общий мнимый сдвиг производной сокращается. При z=sigma+it, t=T-t_j, область имеет |z|<=sqrt(5)/2.

### 5.2 Коши вместо вывода из сетки

64 вычисления на единичной окружности получают Taylor-коэффициенты a_k, k<=32. Для omega_l=exp(2pi i l/64):

\[
\widetilde a_k=\frac1{64}\sum_l A_j(\omega_l)\omega_l^{-k},\qquad
|a_k-\widetilde a_k|\le\frac{D_j3^{-k}}{3^{64}-1}.
\tag{5.3}
\]

Это точное следствие ряда Коши и суммирования корней единицы: остаются коэффициенты a_(k+64q). Их бесконечная сумма оплачена правой частью. Узлы окружности НЕ являются сеткой для вывода знака на прямоугольнике.

Берём точные dyadic-середины коэффициентных интервалов. Их радиусы переносим в отдельные бюджеты eta_0,eta_1,eta_2. Для r=sqrt(5)/2, q=r/3 и m_0=33 хвост P оценивается:

\[
e_0=2D_j\frac{q^{m_0}}{1-q},\quad
e_1=\frac{2D_j}{3}\frac{q^{m_0-1}(m_0-(m_0-1)q)}{(1-q)^2},
\]
\[
e_2=\frac{2D_j}{9}q^{m_0-2}
\left(\frac{m_0(m_0-1)}{1-q}+\frac{2m_0q}{(1-q)^2}+\frac{2q^2}{(1-q)^3}\right).
\]

К ним добавляются 2 sum radius(a_k) r^k и соответствующие производные. Получаются eta_j. Поскольку точный и полиномиальный HB числители равны нулю при sigma=0, их производные дают бюджет ПОСЛЕ удаления sigma:

\[
B_{\rm jet}=4[2D_j\eta_2+(2D_j+\eta_2)\eta_0+(4D_j+\eta_1)\eta_1].
\tag{5.4}
\]

Это исключает потерю при sigma->0. Никакой непокрытой полоски у оси нет.

### 5.3 Нижняя оболочка целого подписанного полинома

Пусть P_32 — полином из середин. Полином psi(w)=P_32(iw) имеет вещественные коэффициенты. Поэтому |psi(t+i sigma)|^2 чётен по sigma и

\[
R_j(\sigma^2,t)=\frac2\sigma\partial_\sigma|\psi(t+i\sigma)|^2
=\frac{4\Re(P_{32}'\overline{P_{32}})}\sigma
\]

есть полином степени <=31 по u=sigma^2 и <=62 по t. Знак мнимой координаты при переходе z=i(t-i sigma) не меняет квадрат модуля вещественного psi.

Переводим u в [0,1/4], t в [-1,1] в тензорный базис Бернштейна степени (31,62). Все 32*63=2016 базисных функций неотрицательны и в сумме равны единице. Следовательно минимальная нижняя граница коэффициента есть нижняя граница R_j НА ВСЁМ ПРЯМОУГОЛЬНИКЕ.

Вычитаем оба оплаченных остатка:

\[
\boxed{\frac{\mathcal H}{\sigma e^{-2\theta_jT}}
\ge\min b_{kl}-B_{\rm jet}-16D_jB(c_j,N_j+1)=:L_j.}
\tag{5.5}
\]

### 5.4 Полное покрытие и результаты

Ниже приведены заведомо уменьшенные рациональные границы L_j. Программы сохраняют исходные целые числители и знаменатели 2^384; отображённые десятичные числа не являются округлёнными входами вычисления.

| Замкнутый интервал T | N_j | Доказано L_j > |
|---|---:|---:|
| [0,2] | 5 | 0.045 |
| [2,4] | 8 | 0.329 |
| [4,6] | 11 | 3.31 |
| [6,8] | 14 | 27.81 |
| [8,10] | 16 | 173.95 |
| [10,12] | 18 | 767.71 |
| [12,14] | 19 | 2358.31 |
| [14,16] | 21 | 5520.33 |
| [16,18] | 23 | 12483.51 |
| [18,20] | 24 | 27073.25 |
| [20,22] | 26 | 40296.00 |
| [22,24] | 27 | 47814.31 |
| [24,26] | 29 | 78689.96 |
| [26,28] | 30 | 169598.03 |
| [28,30] | 31 | 206050.5 |

Все границы >1/25. Так как exp(-2theta_j T)>=exp(-pi T/2), следует (5.1). На блоках с t_j>=5 дополнительно L_j>3 и exp(2T/(t_j+1))>=exp(4/3)>10/3. Последнее проверяется уже первыми четырьмя членами exp: 293/81>10/3. Отсюда (5.2).

Отрицательные T покрывает F(conj(p))=conj(F(p)). Все стыки T=2,4,...,28 и оба края 0,30 входят в замкнутые интервалы. Sigma=0 обслуживается аналитическим продолжением H/sigma; утверждение о строгом знаке относится к sigma>0. Смена вспомогательного N на стыке не требует дифференцирования N: оба сертификата оценивают одну F.

Последний блок повторён с 768 битами: L_29 >206090.8. При 384 битах его B_jet<47.36, при 768 битах <7.051. Оба независимо от округлительных потерь дают положительную оболочку. Другие 14 блоков не заявляются повторёнными при 768 битах.

## 6. Возврат к исходному адаптивному срезу и граница результата

[FINITE_CELL][PAPER] Используя (5.2) и (4.3) для ИСХОДНЫХ theta(T),N(T), получаем

\[
\boxed{h_{N(T)}\ge9\sigma e^{-\pi T/2}\quad(4\le T\le30).}\tag{6.1}
\]

Таким образом компакт оплачен абсолютной стороной без промежуточной глобальной оценки M_+. Это не доказательство G>=1/4 и не доказательство относительного бюджета при всех sigma. Смешивать h_N/sigma и M_+ нельзя.

[COFINAL_FAMILY][CONDITIONAL] Для T>30 в этой работе нет ни нижней оболочки H, ни универсальной нижней оценки E_coh. Глобальное e_N<M_+/4 тоже не выведено. RH не заявлена.

[ABSTRACT][PAPER] Конечному потребителю достаточно даже H>=0 при всех sigma>0,T, не обязательно одного строгого относительного пола. Тогда |F(sigma+iT)|^2 не убывает по sigma. Внеосевой нуль при sigma_0>0 заставил бы |F|^2=0 на [0,sigma_0], что противоречит теореме тождественности и F не тождественно нулю. Чётность F переносит исключение на левую половину полосы.

Другой достаточный интерфейс: для каждой фиксированной точки доказать h_(N_k)>=0 при N_k->infinity и фиксированном theta. Абсолютный B(c,N_k+1)->0 даёт H>=0. Это НОВОЕ обязательство по N, не следствие знака одной адаптивной головы.

## 7. Арифметический проверяющий код и его математические остатки

[ABSTRACT][PAPER] Все сертификатные границы вычисляются целыми числами с направленным наружу округлением на решётку 2^-P. Binary float и mpmath не участвуют в производстве этих границ. Decimal используется только для отображения. Это собственный проверяющий код, НЕ Arb и НЕ Lean.

Exp: редукция до |x|<=1/8, 64 члена и остаток <=2|x|^65/65!, затем возведение в квадрат. Sin/cos: 48 членов с остатком <=2|x|^96/96!, затем удвоение угла. Log: ряд atanh с геометрическим хвостом. Pi: формула Machin 16atan(1/5)-4atan(1/239). Все Bernoulli-числа вычисляются как Fraction.

Complete Gamma: сдвиг аргумента на 32, Stirling до B_46 и остаток логарифма

\[
|R|\le\frac{|B_{48}|}{48\cdot47(\Re(z+32))^{47}}.
\]

Это следует из интегрального остатка Euler–Maclaurin и |periodic B_48|<=|B_48|. Ветвь логарифма остаётся в правой полуплоскости. Обратный сдвиг оплачивается точной Gamma-рекурсией.

Для n<=5 верхняя неполная Gamma вычисляется из сходящегося ряда

\[
\Gamma(a,z)=\Gamma(a)-z^a\sum_{k\ge0}\frac{(-z)^k}{k!(a+k)}.
\]

После k=320 сумма хвоста ограничена

\[
\frac{R^{321}}{321!(\Re a+321)(1-R/322)},\qquad R=|z|<322.
\]

Для n>=6 используется не эвристическая асимптотика, а Taylor вдоль горизонтального интеграла:

\[
\Gamma(a,z)=z^{a-1}e^{-z}
\left[\sum_{k=0}^{63}(a-1)_{\underline k}z^{-k}+R_{64}\right],
\]
\[
|R_{64}|\le |(a-1)_{\underline{64}}|\,|z|^{-64}e^{|\Im a|\pi/2}.
\]

Доказательство: интегрируем exp(-t)(1+t/z)^(a-1) по t>=0. В остатке производной |1+ut/z|>=1 и |arg(1+ut/z)|<=pi/2 при Re z>0; Re a-65<=0. После интеграла t^64/64! множитель равен 1. Все условия проверяются кодом. Поэтому остаток законен даже там, где обычный неоценённый O-ряд был бы недостаточен.

Внешние первичные справочники для определений/рекурсий: NIST DLMF §§8.2, 8.7, 8.8; для Jacobi — §20.7; для Stirling — §5.11. Указанные явные остатки выведены выше, а не заимствованы из диагноза численного совпадения.

Выполненные контроли: 300 exact-rational тестов примитивов; psi(w)=1+w^2 даёт отрицательный коэффициент h/sigma=8(t^2-1+sigma^2), который проверяющий код отвергает; psi(w)=w даёт положительные 4; шесть Gamma(1,z)=exp(-z) контролей двумя способами; Gamma-рекурсия; отдельный отрицательный верхний конец (3.1). Десять mpmath-сравнений с прямой xi/zeta выполнены только как диагностика, не как доказательство знака.

Зафиксированные отказы представления до результата: раннее вычисление reciprocal огромного factorial чрезмерно расширяло безопасные интервалы; заменено прямым целочисленным делением. Прямой перенос интервальных коэффициентов через смену базиса давал бесполезную отрицательную НИЖНЮЮ границу; это не отрицательный свидетель. Ремонт — точные середины плюс явно оплаченные eta_j. Степень 32 и границы блоков не менялись; степень 48 из разрешённой лестницы не понадобилась.

## 8. Предсказания, два продолжения и единственная директива

[ABSTRACT][PAPER] Регистрация предшествовала соответствующим тестам. Записи сохранены в `registration.json` сопровождающего пакета.

| Предсказание | p | Исход |
|---|---:|---|
| P_ABSOLUTE_REVIEW: абсолютная оболочка без M_+ | 0.94 | CONFIRMED |
| P_JOINT_NOT_SEPARATE: совместный запас жив, 1/5 может отказать | 0.65 | CONFIRMED, отказ (3.1) |
| P_REFLECTION_FACTOR: убрать sigma через отражение | 0.97 | CONFIRMED, (2.1) и (5.4) |
| P_COMPACT_SIGNED_JET: [4,30] покрывается подписанным полиномом | 0.80 | CONFIRMED, степень 32 |
| P_LOW_SOURCE_BLOCKS: [0,4] не требует старого q>18 | 0.97 | CONFIRMED |

Два кандидата для глобального остатка, оценки стоимости исследовательские, не вероятности доказательства:

R1: Re(CW), отражённая логарифмическая кривизна настоящей гамма-суммы. Kill-power 9/10, аналитическая стоимость 7/10. Успешный континуумный пример — §3. Нужны источник-специфические оценки фазового произведения; при нуле кластера этот координатный вид не применяется.

R2: безделительный полный h_N/sigma с абсолютным остатком либо неотрицательная кофинальная подпоследовательность голов. Kill-power 10/10, глобальная стоимость 8/10. Успешный компактный пример — §5. Нельзя просто продолжить конечную таблицу до бесконечности.

DISCRIMINATOR: подписанная величина h_N/sigma-e_N (либо коэффициентный полный нижний бюджет (5.5)). Нижний конец >=0 даёт PASS на точно указанной области; отрицательный верхний конец H/sigma даёт отрицательный свидетель; интервал, содержащий ноль, остаётся INCONCLUSIVE. Отрицательный верхний конец отдельного достаточного запаса убивает только этот запас. Возможный нуль X или Y требует безделительного объекта, не объявления благоприятного режима.

Единственная следующая локальная директива: независимо проверить математические остатки §7 и воспроизвести §§3–5 из пустого каталога. Не расширять T, не менять константы, не двигать production state, не запускать RH-export. Успех: все 15 покрытий, осевой сертификат и отрицательный plant воспроизводятся; ошибка: точное первое несовпавшее тождество/остаток/целый интервал. Это аудит нового результата, а не поручение доказать RH. Codex в этом сеансе не запущен.

## 9. Dependency epistemics и closeout

[COFINAL_FAMILY][CONDITIONAL]

DOWNSTREAM_CONSUMER: исключение внеосевых нулей полной F через неотрицательность горизонтальной производной |F|^2.
ACTUAL_CONSUMER_REQUIREMENT: H>=0 на всех 0<sigma<=1/2,T; F entire, even, nonzero.
ORIGINAL_REQUESTED_OBJECT: глобальный E_coh-бюджет и относительное e_N<M_+/4.
ORIGINAL_OBJECT_IS: NOT_NECESSARY как обязательная форма доказательства; достаточный, но более сильный интерфейс.
KNOWN_WEAKER_INTERFACES: прямое H>=0; h_N/sigma>=e_N; неотрицательная кофинальная подпоследовательность голов с абсолютной сходимостью.
FAILURE_TYPE: NO_DERIVATION для T>30; COUNTEREXAMPLE только для фиксированного 1/5.
EPISTEMIC_STATUS: RESEARCH_DEBT для глобального хвоста; MATHEMATICALLY_DEAD для точной формы 1/5.
NOVELTY_AXIS: сохранение подписанной комплексной кривизны и безделительная сертификация компактного полного HB-значения.
REOPEN_TRIGGER: доказанная источник-специфическая нижняя граница полного подписанного выражения при T>30 или отрицательная верхняя граница того же полного выражения. Новая сетка средних не является таким событием.

Что стало меньше: компакт |T|<=30 выведен из открытого глобального фронта на уровне PAPER/checker; E_coh на T=sqrt(20) имеет действительную континуумную нижнюю границу; абсолютный и относительный бюджеты разъединены.
Что убито: ровно 1/5 отдельной потери, отрицательная верхняя оболочка (3.1).
Что не повторять: принимать положительные средние за знак; считать совпадение масс контролем числителя; объявлять отрицательный нижний конец контрпримером; глобализировать конечное покрытие.
Минимальный оставшийся gap: SOURCE_SIGNED_FULL_H_FOR_T_ABOVE_30.
Memory entry: reflection removes the axial zero before bounding; exact midpoint polynomial preserves cancellation; absolute enclosure can pay compact source positivity without a relative mass floor.

## 10. Воспроизведение и handoff

[FINITE_CELL][PAPER] Этот файл содержит шесть исходников в сжатом JSON. Кодировка — только упаковка; проверка не доверяет кодировке как математической аксиоме. JSON SHA-256 после распаковки:

`7bf70bc8c38196fff25c6df56545063a33cabd25a0f3496cc843ee5e6b6e7fee`

Все шесть исходников используют только Python standard library. Строку `<verdict.md>` в команде надо заменить путём к этому файлу, например `docs/routeB_bus/proshka/PROSHKA_VERDICT_SIGNED_THETA_CURVATURE_PAID_COMPACT_2026-09-18.md`. `<audit-dir>` — новый пустой каталог, например `/tmp/theta_signed_audit`.

```bash
python3 - <verdict.md> <audit-dir> <<'PY'
import base64,gzip,hashlib,json,pathlib,re,sys
text=pathlib.Path(sys.argv[1]).read_text()
s=re.search(r'<!-- REPRODUCER_BEGIN -->\s*```text\s*(.*?)\s*```\s*<!-- REPRODUCER_END -->',text,re.S).group(1)
data=gzip.decompress(base64.b64decode(s))
assert hashlib.sha256(data).hexdigest()=='7bf70bc8c38196fff25c6df56545063a33cabd25a0f3496cc843ee5e6b6e7fee'
out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
assert not any(out.iterdir()), 'use an empty directory'
for name,body in json.loads(data).items():
    assert pathlib.Path(name).name==name and name.endswith('.py')
    (out/name).write_text(body)
PY
```

WORKDIR: выбранный audit-dir.

```bash
python3 check_exact_corner.py
python3 build_axis_jets.py
python3 certify_axis.py
for c in 1 3 5 7 9 11 13 15 17 19 21 23 25 27 29; do
  python3 compact_certificate.py "$c"
done
DYADIC_BITS=768 python3 compact_certificate.py 29
python3 self_tests.py
python3 - <<'PY'
import json
from fractions import Fraction
from pathlib import Path
for c in range(1,30,2):
    r=json.loads(Path(f'compact_certificate_T{c}_K32.json').read_text())
    L=Fraction(r['integer_paid_lower'],r['denominator'])
    assert r['domain']=={'sigma':['0','1/2'],'T':[c-1,c+1]}
    assert L>Fraction(1,25)
    if c>=5: assert L>3
assert json.loads(Path('exact_corner_certificate.json').read_text())['old_budget_negative']
a=json.loads(Path('axis_certificate.json').read_text())
assert a['E_ge_minus_51_over_250_sigma_m_X2']
assert a['signed_E_bounds_minus23_minus22_over10000']
r=json.loads(Path('compact_certificate_T29_K32_P768.json').read_text())
assert Fraction(r['integer_paid_lower'],r['denominator'])>3
print('EXACT_COMPACT_AND_SIGNED_COHERENCE_CHECKS_PASS')
PY
```

Переменная c в цикле — центр замкнутого T-блока; например c=5 означает T в [4,6], а не одну проверяемую точку. DYADIC_BITS задаёт число битов знаменателя 2^P. При повторном запуске программа использует локальный кэш jets; независимый первый запуск поэтому обязательно проводится в пустом каталоге.

Lean-files: none. Lean gate и axiom profile: not applicable; Lean/Arb verification не заявлена. Репозиторный путь записи — только новый документ с этим вердиктом. SHA коммита сообщается отдельно после успешной записи; файл не приписывает себе заранее неизвестный commit id.

<!-- REPRODUCER_BEGIN -->
```text
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
```
<!-- REPRODUCER_END -->
