# STATUS: TRY_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47
```yaml
OPERATIVE_CLASS: TRY_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47
REQUEST_ID: Q47_SOURCE_DERIVED_JOINT_COMPENSATION
DATE: 2026-10-26
LANGUAGE: ru
SOURCE_OBJECT: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
BASE_COMMIT: 0595798839449a77539470e333e886d7cfab6461
PACKET_BYTES: 129191
PACKET_LF: 2357
PACKET_SHA256: 072b38a5e63f8411daf467eceb6ad2598b5c462fda7116cfbf9857cb7be9f11b
SOURCE_BODIES: 10
MANIFEST: VERIFIED
CONSUMER_PROGRESS: NO_PROGRESS
INDEPENDENT_FAVORABLE_SIGN: NOT_DERIVED
NEW_CONSUMER_EXPONENT: NOT_PROVED
NEW_PAIR_MARGIN: NOT_PROVED
CHOSEN_MECHANISM: FINITE_ALTERNATING_INTEGER_STATE_WITH_COMPLETE_DYADIC_LOG_DERIVATIVE_RETURN
FIRST_COEFFICIENT_MISMATCH: ETA_GENERATOR_AT_2_IS_MINUS_LOG2_NOT_PLUS_LOG2
FIRST_UNPAID_STEP: SIGN_OF_THE_COMPLETE_LINKED_STATE_DERIVATIVE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
VERIFIER: PAPER
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
INDEPENDENT_NEW_AUDIT: NOT_RUN
LEAN: NOT_RUN
ARB: NOT_RUN
PRODUCTION_CCM_SPECTRUM: NOT_RUN
RH: OPEN_NOT_CLAIMED
PX_RH_CLAIM: NOT_MADE
ALL_P_GOAL: OPEN
CONDITIONAL_ZF78: NOT_USED_NOT_UPGRADED
CF22_PYSR: PARKED_REOPENABLE
REPOSITORY_WRITES: NONE
PACKAGE_INSTALLATIONS: NONE
NEXT_QUESTION_DISPATCH: NONE
```

Ы. **Независимой совместной знаковой оценки нужной силы я не получил.** Проверен один конкретный кандидат: заменить недифференцированный арифметический transfer его точно связанным знакопеременным целочисленным каналом, воспользоваться ограниченными частичными суммами этого канала, затем вернуть **всю** логарифмическую производную на исходном пространстве.

Проверка не использует положительность центрированной меры. Сентябрьская \(V\) не отождествляется с \(C^0\). Уравнение двух связанных состояний и точная формула их полной квадратичной энергии построены непосредственно из конечной арифметики. Однако её знаковая производная не контролируется малостью прямого канала.

**Первое конкретное расхождение:** логарифмическая производная чередующегося канала имеет при \(n=2^j\) коэффициент \((1-2^j)\log2\), а не \(\log2\). Полный dyadic-return добавляет \(2^j\log2\) и восстанавливает исходный источник. Нельзя оставить маленький прямой канал и удалить этот возврат. После сохранения всей компенсации новое одностороннее неравенство не получено.

Ни классическое тождество для \(\eta\), ни доказанные ниже вспомогательные оценки, ни конечные проверки не объявляются улучшением CCM. **Основное требование Q47 о независимом благоприятном знаке остаётся невыполненным.**

## 1. Source lock, прочитанные материалы и исходный потребитель

Прочитан весь канонический UTF-8 TXT, включая все десять внешних source bodies и исторические код/JSON-приложения S1. Проверены размеры, LF, SHA-256, порядок и byte-counted границы каждого тела; единственный separator LF не включался в тело. Общий SHA-256 вычислен в этом запуске: в коротком сообщении пользователя он не задавался.

Из GitHub-коннектора заново прочитан весь `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, ветка `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Единственное поручение — root Q47. Исторические инструкции не исполнялись; репозиторий не изменялся.

Принятые входы, без повышения их статуса:

| Источники | Использование | Что не принимается |
|---|---|---|
| S1–S2 | неизменная \(C^0\), полный fallback, одна short/arch-плата | prime-gap geometry как контроль арифметических масс |
| S3–S4 | точный signed generator и уже проверенная граница positive-jump импорта | положительность centered measure, знак разности двух положительных энергий |
| S5–S7 | исходный синтез, контакты, \(-H_d\), sparse receiver | компактная Fourier-поддержка zero-extension, бесплатная смена пространства |
| S8 | отдельная actual-pair редукция, её область и оставшаяся длинная \(\mu\)-сумма | продвижение pair-only к all-\(P\), Mertens power |
| S9–S10 | требования к точной state/supply-карте, границам и storage | равенство September \(V=C^0\), готовый положительный storage |

Сохраняем
\[
N=m,\quad L=\log m,\quad M=R=\lfloor m^\epsilon\rfloor,
\quad0<\epsilon<1/32,\quad\Omega=2\pi M/L.
\tag{1.1}
\]
\(\epsilon\) фиксировано до предела. \(P\) — прежний проектор на три исходных контакта, с теми же частотами. Для \(c=Pc\) обозначим через \(f=F_Mc\) исходный Fourier-синтез на \([0,L]\), продолженный нулём. Тогда
\[
\|f\|_2=\|c\|_2,\quad f(0)=f(L)=0,\quad
\|f'\|_{L^2(0,L)}\le\Omega\|f\|_2,
\quad \int_0^L e^{\pm t/2}f(t)dt=0.
\tag{1.2}
\]
Никакие дополнительные ограничения на \(f\) не вводятся.

Нужна по-прежнему односторонняя all-\(P\) оценка
\[
C_m^0\preceq C_\epsilon m^{\eta(\epsilon)}P,
\qquad\eta(\epsilon)\longrightarrow0,
\tag{1.3 OPEN}
\]
либо достаточная полная оценка \(T_{>R}\). Константы и onset могут зависеть от фиксированного \(\epsilon\), но не от \(c\). Ниже не назначается численно гипотетический нуль и не доказывается отдельный pair-margin.

## 2. Один выбранный кандидат и его реальный дополнительный вход

**Идея для проверки:** у настоящего целочисленного counting-source имеется точный чередующийся канал
\[
a(n)=(-1)^{n-1}=1-2\mathbf1_{2\mid n},\qquad
A(x)=\sum_{n\le x}a(n)=
\begin{cases}1,&\lfloor x\rfloor\text{ нечётно},\\0,&\lfloor x\rfloor\text{ чётно}.
\end{cases}
\tag{2.1}
\]
Следовательно, **\(0\le A(x)\le1\) точно**, не только асимптотически. Это существенно сильнее отдельного тривиального контроля счётной функции \(\sum_{n\le x}1\), но относится к специальному связанному каналу, **не к \(\Lambda\), \(\mu\) или \(E=\psi-(x-1)\)**.

Классическая скалярная запись —
\[
\eta(s)=(1-2^{1-s})\zeta(s)=\sum_{n\ge1}(-1)^{n-1}n^{-s}.
\tag{2.2}
\]
Первичная справочная формула проверена в NIST DLMF **25.2.3**; обычная область ряда — \(\Re s>0\). Для доказательств ниже аналитическое продолжение, отсутствие нулей или бесконечная обратная серия **не требуются**: используются конечные причинные полиномы. Формулы Dirichlet convolution, \(\mu*\mathbf1=\delta_1\) и \(\mu*\log=\Lambda\) сверены с DLMF **27.5.1, 27.5.2, 27.5.5**, а нужные конечные случаи выведены непосредственно.

Внешние справочные адреса:
```text
[E1] NIST DLMF 25.2.3: https://dlmf.nist.gov/25.2.E3
[E2] NIST DLMF 27.5:   https://dlmf.nist.gov/27.5
```
Здесь не импортируется внешний theorem о знаке оператора. Инструменты классические; мировой приоритет и новизна самих тождеств не заявляются. Отличие испытываемого входа от S3–S4 — используется **знакопеременный целочисленный transfer**, а не положительный jump generator. Отличие от Q46 — это коэффициентная, а не геометрическая информация о поддержке.

Проверяемая надежда была конкретной: малый полный transfer и его производная, полученные из (2.1), могли бы дать управляемую supply-форму после **совместного** возвращения обратного канала и dyadic correction. Ни знак производной энергии, ни малость обратного канала в эту надежду как предпосылки не включаются.

## 3. Точный конечный арифметический оператор

Все тождества §§3–5 имеют scope `[ABSTRACT | PAPER]`: они верны для каждого конечного \(m>2\) на исходном физическом \(L^2(0,L)\).

Пусть
\[
(V_su)(t)=\mathbf1_{t\ge s}u(t-s),\qquad 0<t<L.
\]
Тогда
\[
V_sV_t=V_{s+t},\qquad V_s=0\ (s\ge L),\qquad\|V_s\|\le1.
\tag{3.1}
\]
Определим для вещественного вспомогательного \(\sigma\)
\[
Z_\sigma=\sum_{n\le m}n^{-\sigma}V_{\log n},\qquad
M_\sigma=\sum_{n\le m}\mu(n)n^{-\sigma}V_{\log n}.
\tag{3.2}
\]
Все произведения выполняются **на физическом пространстве до сжатия**, с полным условием \(dk\le m\). Атом \(n=m\), когда он целый, сохраняется формально и имеет оператор \(V_L=0\).

По настоящему \(\mu*\mathbf1=\delta_1\)
\[
Z_\sigma M_\sigma=M_\sigma Z_\sigma=I.
\tag{3.3}
\]
Это конечная обратимость; здесь нет обратимости \(\zeta(\sigma+it)\) на бесконечной прямой. Минимальный ненулевой сдвиг \(\log2\) делает положительно-сдвиговую часть конечной нильпотентной алгеброй.

Дифференцирование по \(\sigma\), обозначаемое точкой, возвращает именно настоящую меру Мангольдта:
\[
B_\sigma:=-\dot Z_\sigma M_\sigma
=\sum_{n\le m}\frac{\Lambda(n)}{n^\sigma}V_{\log n}.
\tag{3.4}
\]
Коэффициент при \(n\) слева есть
\(\sum_{dk=n}\log k\,\mu(d)=\Lambda(n)\). Поэтому \(\Lambda(p^j)=\log p\), не \(j\log p\), и смешанные произведения не потеряны.

Для непрерывного канала введём
\[
G_\sigma=\int_0^L e^{(1-\sigma)s}V_s\,ds.
\tag{3.5}
\]
На \(\sigma_*=1/2\), с \(I_m=F_M|_{\operatorname{ran}P}\), точно
\[
A_m=I_m^*(B_{\sigma_*}+B_{\sigma_*}^*)I_m,
\]
\[
C_m^0=I_m^*(B_{\sigma_*}+B_{\sigma_*}^*
                    -G_{\sigma_*}-G_{\sigma_*}^*)I_m
=A_m+H_d,
\quad0\preceq H_d\preceq4P.
\tag{3.6}
\]
Последнее равенство — принятый полный continuous return S7, не новая компенсация этого ответа. Оно уже включает оба времени и оба экспоненциальных контакта.

## 4. Прямой чередующийся канал действительно дешевле — в точной области

Положим
\[
D_\sigma=I-2^{1-\sigma}V_{\log2},\qquad
E_\sigma=D_\sigma Z_\sigma.
\tag{4.1}
\]
Для каждого \(n\) коэффициент \(E_\sigma\) равен
\(n^{-\sigma}(1-2\mathbf1_{2\mid n})\). Значит,
\[
E_\sigma=\sum_{n\le m}a(n)n^{-\sigma}V_{\log n}.
\tag{4.2}
\]
Никакие \(n>m\) не добавлены, а промежуточный \(P\) не вставлен.

### 4.1. Полная Abel-карта с исходной левой границей

Пусть \(u\in H^1(0,L)\), \(u(0)=0\), и \(\sigma>0\). Для почти каждого \(t\in(0,L)\) конечная Stieltjes-формула даёт
\[
\begin{aligned}
E_\sigma u(t)={}&A(e^t)e^{-\sigma t}u(0)\\
&+\int_1^{e^t}A(x)x^{-\sigma-1}
 [\sigma u(t-\log x)+u'(t-\log x)]dx.
\end{aligned}
\tag{4.3}
\]
Верхний член исчезает **из-за \(u(0)=0\)**. Его нельзя удалить для произвольного входа. Нижний левый след \(A(1^-)=0\); атом \(n=1\) уже входит в интеграл через скачок \(A\).

После \(s=\log x\) получаем
\[
E_\sigma u=k_\sigma*(u'+\sigma u),\qquad
k_\sigma(s)=\mathbf1_{s\ge0}A(e^s)e^{-\sigma s},
\tag{4.4}
\]
с причинной свёрткой на том же окне. Продление ядра на всю полуось используется только для верхней оценки его \(L^1\)-нормы: при \(t<L\) участвует лишь \(0\le s\le t\), поэтому новых атомов \(n>m\) здесь нет. Из **точного actual coefficient fact (2.1)**
\[
\|k_\sigma\|_1\le\sigma^{-1},\qquad
\|s k_\sigma\|_1\le\sigma^{-2}.
\]
Следовательно,
\[
\boxed{\|E_\sigma u\|_2\le\|u\|_2+\sigma^{-1}\|u'\|_2,}
\tag{4.5}
\]
\[
\boxed{\|\dot E_\sigma u\|_2
\le 2\sigma^{-1}\|u\|_2+\sigma^{-2}\|u'\|_2.}
\tag{4.6}
\]
Вторая строка следует из
\(\dot E_\sigma u=k_\sigma*u-(s k_\sigma)*(u'+\sigma u)\).
Все верхние границы и производная множителя \(\sigma u\) сохранены.

На первоначальном входе \(f=F_Mc\), \(c=Pc\), это даёт
\[
\boxed{\|E_{1/2}f\|_2\le(1+2\Omega)\|f\|_2,
\qquad
\|\dot E_{1/2}f\|_2\le4(1+\Omega)\|f\|_2.}
\tag{4.7}
\]
**Граница:** это upper для прямого канала и его действия на \(H^1\)-входе. Это не upper его логарифмической производной, не bound для обратного transfer и не signed estimate для \(C^0\). В частности, малый показатель прямой платы \(\epsilon\) не является показателем CCM.

### 4.2. Действительный обратный канал

Конечное геометрическое обращение \(D_\sigma\) и (3.3) дают
\[
E_\sigma^{-1}=M_\sigma D_\sigma^{-1}
=\sum_{n\le m}h(n)n^{-\sigma}V_{\log n},
\]
\[
h(n)=\sum_{2^j\mid n}2^j\mu(n/2^j).
\tag{4.8}
\]
Если \(n=2^ju\), \(u\) нечётно, то
\[
\boxed{h(u)=\mu(u),\qquad
h(2^ju)=2^{j-1}\mu(u)\quad(j\ge1).}
\tag{4.9}
\]
Доказательство: при \(j\ge1\) в сумме остаются только показатели \(j\) и \(j-1\); они дают \((2^j-2^{j-1})\mu(u)\). Если \(u\) не squarefree, оба равны нулю. Это вычисление не заменяет настоящую \(\mu\) независимыми знаками.

Обозначим \(J_m=\lfloor\log m/\log2\rfloor\). Из \(|\mu|\le1\) и \(\sum_{u\le x}u^{-1/2}\le2\sqrt x\) следует законный доступный upper
\[
\|E_{1/2}^{-1}\|\le K_m,
\qquad K_m=(J_m+2)\sqrt m.
\tag{4.10}
\]
Каждый фиксированный \(j\ge1\) в (4.9) стоит не более \(\sqrt m\); нечётный сектор — не более \(2\sqrt m\). Это **верх**, не нижняя оценка истинной обратной нормы. Доказательства необходимости такой платы нет и здесь не требуется.

Если \(x=E_{1/2}^{-1}f\), то \(x\in H^1(0,L)\), \(x(0)=0\), и
\[
\|x\|_2\le K_m\|f\|_2,
\qquad\|x'\|_2\le K_m\Omega\|f\|_2.
\tag{4.11}
\]
При дифференцировании \(V_sf\) на \((0,L)\) внутренний скачок равен \(f(0)\), поэтому здесь он нулевой. **Не утверждается** \(x\in\operatorname{ran}P\), \(x(L)=0\) или сохранение его Fourier-полосы. Для (4.5)–(4.6) они не нужны; подставлять (1.2) непосредственно для \(x\) без (4.11) было бы незаконно.

## 5. Первая несовпадающая арифметика и полная компенсация

Из конечного правила дифференцирования произведения:
\[
B_{\eta,\sigma}:=-\dot E_\sigma E_\sigma^{-1}
=B_\sigma-Y_\sigma,
\quad
Y_\sigma=\dot D_\sigma D_\sigma^{-1}.
\tag{5.1}
\]
Все факторы коммутируют как полиномы причинных сдвигов **до** сжатия. Явно
\[
\boxed{
Y_\sigma=(\log2)\sum_{\substack{j\ge1\\2^j\le m}}
 2^{j(1-\sigma)}V_{j\log2}.}
\tag{5.2}
\]
Поэтому
\[
B_{\eta,\sigma}=\sum_{n\le m}\lambda_\eta(n)n^{-\sigma}V_{\log n},
\]
\[
\boxed{\lambda_\eta(n)=\Lambda(n)
      -\mathbf1_{n=2^j,\ j\ge1}\,2^j\log2.}
\tag{5.3}
\]
Это exact source comparison, а не скалярная аналогия с \(\eta\).

| Индекс | \(\lambda_\eta(n)\) | Возврат \(Y\) | Полная \(\Lambda(n)\) |
|---|---:|---:|---:|
| \(2\) | \(-\log2\) | \(2\log2\) | \(\log2\) |
| \(4\) | \(-3\log2\) | \(4\log2\) | \(\log2\) |
| \(8\) | \(-7\log2\) | \(8\log2\) | \(\log2\) |
| \(p^k\), \(p\) нечётно | \(\log p\) | \(0\) | \(\log p\) |
| прочие \(n>1\) | \(0\) | \(0\) | \(0\) |

Таким образом, \(B_{\eta}=B\) неверно уже на первом source coefficient. Это **отказ буквального отождествления операторов по коэффициентам**, не доказательство какого-либо плохого спектра на \(P\). В частности, \(Y\) не является обычным маленьким proper-prime-power сектором: его числитель \(2^j\log2\), а не \(\log2\). Старые оценки для настоящих собственных степеней простых к нему не применимы.

Вся целевая форма равна
\[
\boxed{
C_m^0=I_m^*\bigl[
B_{\eta}+B_{\eta}^*+Y+Y^*-G-G^*
\bigr]I_m.}
\tag{5.4}
\]
Здесь и ниже без индекса \(\sigma\) берётся \(\sigma=1/2\). **Ни одна из трёх скобок не объявляется положительной.** Их большая общая часть может сокращаться; раздельная верхняя плата не определяет размер настоящей суммы.


### Полная конгруэнция и правильная норма состояния

Для \(E=E_{1/2}\) определим явно, без какого-либо требования положительности,
\[
\mathcal L_\eta=-E^*\dot E-\dot E^*E
       +E^*(Y+Y^*-G-G^*)E.
\]
Тогда
\[
\boxed{C_m^0=I_m^*E^{-*}\mathcal L_\eta E^{-1}I_m.}
\tag{5.5}
\]
Это получается умножением полной (5.4) слева на \(E^*\), справа на \(E\), с использованием \(B_\eta E=-\dot E\). Все adjoint- и mixed-члены сохранены. Для состояния \(x=E^{-1}I_mc\) исходная норма равна **\(\|Ex\|^2=\|c\|^2\)**, а не \(\|x\|^2\). Неравенство с неизвестным знаком \(\mathcal L_\eta\) не следует из (5.5); его положительная/отрицательная часть не конструируется через предполагаемый ответ.

## 6. Явное уравнение состояния: совпадение с \(C^0\), а не с September \(V\)

Это конкретная попытка storage-переноса, построенная из вычисленного источника, без неизвестного квадратного корня.

Фиксируем \(f=I_mc\), \(\sigma_*=1/2\), и **один раз** задаём
\[
x=E_{\sigma_*}^{-1}f,\qquad y=D_{\sigma_*}^{-1}f.
\]
При изменении \(\sigma\) в окрестности \(\sigma_*\) эти два вектора остаются фиксированными. Положим
\[
u_\sigma=E_\sigma x,\qquad v_\sigma=D_\sigma y.
\]
Их точное уравнение:
\[
\boxed{
\frac d{d\sigma}\binom{u_\sigma}{v_\sigma}
=
\begin{pmatrix}-B_{\eta,\sigma}&0\\0&Y_\sigma\end{pmatrix}
\binom{u_\sigma}{v_\sigma},
\quad u_{\sigma_*}=v_{\sigma_*}=f.}
\tag{6.1}
\]
Все операторы при конечном \(m\) ограничены; дифференцирование — конечных сумм, без гипотезы о спектре \(\zeta\).

Возьмём полностью явный **знаковый**, а не положительный storage
\[
\mathscr S_f(\sigma)=\|u_\sigma\|_2^2-\|v_\sigma\|_2^2.
\]
Тогда \(\mathscr S_f(\sigma_*)=0\), а прямое дифференцирование, с обоими комплексными mixed terms, даёт
\[
\mathscr S_f'(\sigma_*)
=2\Re\langle f,\dot E_{\sigma_*}x-\dot D_{\sigma_*}y\rangle
=-\langle f,(B+B^*)f\rangle.
\]
Следовательно,
\[
\boxed{
c^*C_m^0c=-\mathscr S_f'(\sigma_*)+c^*H_dc.}
\tag{6.2}
\]
**Это полное совпадение нужной квадратичной формы**, включая настоящий \(\mu\)-inverse, все \(\Lambda(p^k)\), исходную норму и оба времени. Оно не использует сентябрьскую \(V(x,y)\), не требует Markov property и не вставляет дополнительный проектор.

Однако (6.2) — тождество, не неравенство. Из неотрицательности двух норм по отдельности ничего не следует о знаке производной их разности. Storage \(\mathscr S_f\) также не объявляется неотрицательным. Квадрат исходной скалярной формы или \(C^0\) нигде не вводится; квадратичные нормы в storage сохраняют точное равенство первой формы. Не проводится log-chord или перенос конечной хорды на начальную производную.

### Первая реально недоказанная строка

Для (1.3) требовалось бы независимо получить
\[
\boxed{
-\mathscr S_f'(1/2)+c^*H_dc
\le s_{m,\epsilon}\|f\|_2^2,
\qquad s_{m,\epsilon}=C_\epsilon m^{\eta(\epsilon)},\quad\eta(\epsilon)\to0.}
\tag{6.3 OPEN}
\]
**(6.3) не доказано.** По (6.2) это тот же потребитель; я не предлагаю его как новый самостоятельный supplier.

Оценки (4.7) не относятся к \(x\) с прежней нормировкой и не дают (6.3). Если законно использовать (4.11), одно доступное завершение стоит
\[
-\mathscr S_f'(1/2)
\le \bigl[8(1+\Omega)K_m+2\mathfrak d_m\bigr]\|f\|_2^2,
\tag{6.4}
\]
где \(\mathfrak d_m\) явно определено ниже. Это лишь нормовая цена после остановки знакового шага. Её степень \(1/2+\epsilon\), а не \(\epsilon\). В отсутствие новой joint-оценки нет причины продолжать эту оплату или оптимизировать её константы.

## 7. Полный бюджет без бесплатного dyadic-return

Обозначим **скалярные массы**, не новые операторы,
\[
W_{<}(m)=\sum_{2\le n<m}\frac{\Lambda(n)}{\sqrt n},\qquad
 \mathfrak d_m=(\log2)\sum_{\substack{j\ge1\\2^j<m}}2^{j/2}.
\tag{7.1}
\]
Также \(W(x)=\sum_{n\le x}\Lambda(n)/\sqrt n\). Величина \(\mathfrak d_m\) — только выписанная dyadic-масса данного опыта. Имеем
\[
\|Y\|\le \mathfrak d_m\le
\frac{\log2}{1-2^{-1/2}}\sqrt m,
\quad
\|B_\eta\|\le W_{<}(m)+\mathfrak d_m.
\tag{7.2}
\]
Первая оценка — геометрическая сумма, вторая — полная цена коэффициентов (5.3). Они не являются нижними границами истинных норм.

Если после точного совместного равенства (5.4) оплачивать два производных канала раздельно, получается
\[
C_m^0\preceq s_\eta(m)P+H_d,
\quad s_\eta(m)=2W_{<}(m)+4\mathfrak d_m,
\tag{7.3}
\]
\[
s_\eta(m)\le
\left(12+\frac{4\log2}{1-2^{-1/2}}\right)\sqrt m.
\tag{7.4}
\]
Использовано только унаследованное \(W_{<}(m)\le6\sqrt m\), без PNT/Mertens/variance. **Полная цена имеет показатель \(1/2\)**. Это не lower для CCM и не утверждение о невозможности другой joint-оценки.

Более правильно сначала совместно вернуть коэффициенты (5.3): тогда большие искусственные dyadic-части точно сокращаются и остаётся \(B\). Это сразу улучшает (7.3) до старого elementary \(A_m\preceq2W_{<}(m)P\). **Но такое улучшение — восстановление исходника, не новое арифметическое сокращение.**

Полный перевод trial-бюджета с сохранённым \(H_d\):
\[
A_m=C_m^0-H_d\preceq s_\eta(m)P,
\]
\[
T_{>R}\preceq[s_\eta(m)+b_{\rm div}]P,
\qquad
PK_mP\succeq-[s_\eta(m)+50L+8]P,
\tag{7.5}
\]
\[
b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\tag{7.6}
\]
\(H_d\) не оплачивается второй раз; short fee не добавляется в direct \(K\)-возврат. Новых projection/cutoff/tail fees нет: весь расчёт сохранял тот же \(f\) и сжимал только окончательную форму.

Поскольку trial хуже уже принятого, итоговым безусловным результатом остаётся **не trial, а**
\[
s_{\rm keep}=W_{<}(m)+W(\lfloor\sqrt m\rfloor)
\le6\sqrt m+6m^{1/4},
\]
\[
\boxed{
T_{>R}\preceq(s_{\rm keep}+b_{\rm div})P,
\qquad PK_mP\succeq-[s_{\rm keep}+50L+8]P.}
\tag{7.7}
\]
Это inherited S1–S2. Показатель \(3\epsilon/2\) малоделительной платы и \(O(L)\) arch-плата не меняют оставшуюся половинную степень. Условные \(3/8\) остаются условными на прежнюю ZF78; здесь она не использована.

## 8. Контроли области, границ и сохранённого знака

### 8.1. Непрерывный контроль не платится большой нормой

Для произвольного исходного causal-канала \(B\) равенство \(B_\eta=B-Y\) имеет ту же точную выходную сборку
\[
B_\eta+Y-G=B-G.
\tag{8.1}
\]
При замене истинной меры на \(d\psi=dx\) следует заменить **сам исходный канал** на \(B=G\), а не сохранить коэффициенты истинной \(\eta\)-производной. Тогда \(B_{\eta,0}=G-Y\), и
\[
(G-Y)+Y-G=0
\tag{8.2}
\]
до adjoint, сжатия или модулей. Следовательно, \(C_m^0[dx]=0\) точно. Для этого контроля не утверждается арифметическая факторизация \(\mu*\log\) непрерывной меры.

### 8.2. Поддержка и верхний атом

Формальные коэффициенты при \(n=m\) не удалялись. Лишь их physical shift \(V_L\) равен нулю. В произведениях сохраняются все ordered \(dk\le m\); произведения с \(dk>m\) дают \(V_{\log(dk)}=0\). Геометрический inverse \(D^{-1}\) также конечен вследствие причинной поддержки, а не вследствие обнуления своих арифметических коэффициентов. Никакие contour residues или временные энергии за пределами окна не объявлялись отсутствующими по чужой формуле.

### 8.3. Исходная комплексная форма и конечные состояния

Все adjoints стоят после полного causal-произведения. В (6.2) сохранены \(\langle f,\dot Ex\rangle\) и его сопряжение, а также весь второй канал. Норма \(x\) не подменяется нормой \(f\). Уравнения (6.1) не обязаны сохранять исходный \(P\); их выход в точке \(\sigma_*\) равен исходному \(f\) точно. Это не similarity, объявленная сохранением Loewner-порядка.

### 8.4. Что опровергнуто, а что нет

Опровергнута только буквальная замена \(B\) на \(B_\eta\) без (5.2): первый coefficient mismatch дан в (5.3). **Не опровергнута** оценка (6.3), не доказана её истинность, и не установлен bad eigenvalue на исходном \(P\).

Абстрактный контроль логической ошибки: даже положительные функции \(S_\pm(t)=e^{\pm t}\) имеют одинаковое значение в нуле и противоположные производные. Это не arithmetic model и не CCM-counterexample; он лишь запрещает выводить знак производной из положительности значения storage. В нашем расчёте действительный источник задан (3.2)–(3.4), и его sign estimate должна быть доказана отдельно.

## 9. Откат и честная граница полезности

**Этот кандидат останавливается до оптимизации отдельных норм.** Доказанный арифметический факт (2.1) реально удешевил прямую знакопеременную сумму, но логарифмическая производная потребляет другой вход и точный dyadic-return. Их восстановление оставляет исходную \(\Lambda\) с коэффициентом один.

Обоснованная более ранняя точка — **недифференцированный конечный арифметический state** \(Z_\sigma\), до введения alternating-фильтра, до centered Markov-генератора и до объявления storage положительным. Она отличается от Fourier-density Q09, positive-jump Q28, theta-inverse Q45 и prime-mesh Q46: здесь сохранены настоящие \(\mu*\mathbf1=\delta_1\), общий продукт индексов и операторная \(\sigma\)-производная в исходной норме.

Карта отката конкретна и точна:
\[
E_\sigma=D_\sigma Z_\sigma
\ \longrightarrow\
-\dot Z_\sigma M_\sigma=B_\sigma
\ \longrightarrow\
C_m^0\text{ по (3.6)}.
\tag{9.1}
\]
Добавочная ошибка **ноль**. Это не просьба вновь доказывать \(\mu*\log=\Lambda\), не новый критерий RH и не заявление о новизне общих finite-inverse тождеств. **Самостоятельного неэквивалентного благоприятного неравенства и на этой ранней развилке я не вывел.** Поэтому откат не объявляется математическим продвижением и не назначается автоматический Q48.

В частности, вывести из (6.2) существование неизвестного хорошего storage — значит только переименовать исходный долг. Увеличивать число точных алгебраических проверок, улучшать постоянную в (4.7) или дополнительно сжимать уже дешёвый прямой канал для этой цели бессмысленно.

### Два сохранённых представления, не два новых успешных механизма

| Представление | Проверяемый discriminator | Цена карты / стоимость следующей проверки |
|---|---|---|
| Полный finite arithmetic state \(Z_\sigma,M_\sigma\), до (4.1) | новая лемма должна ограничивать **совместную** первую форму, а не норму прямого канала; сверить первые prime-power coefficients | карта (9.1) точна, цена 0; коэффициентный дефект обнаруживается дешёвым finite convolution; глобальный знак всё ещё требует PAPER-доказательства |
| Уже принятая полная actual-pair long-\(\mu\) сумма S8 | достаточный коэффициентный запас после всего receiver, а не \(k<\log^6m\) сам по себе | prefix и original-\(P\) return уже \(o(1)\); обычное завершение S8 сохраняет \(\sqrt m(\log\log m)^2/\log m\); повтор S8 не выбран как новый Q47 |

Вторая строка — только сохранившийся более слабый sufficient consumer, не объявленная новая атака и не замена all-\(P\). Она приведена для границы возможного reopening, а не как цикл назад к Q45.

**DISCRIMINATOR для любого ремонта:** подставить доказанный совместный upper непосредственно в (3.6), затем (7.5), и проверить \(\eta(\epsilon)\to0\). При zero-consistent конечных тестах решающим объектом остаётся аналитический upper для полной формы, а не знак прямого \(E\)-канала. Пока такого upper нет, статус не меняется.

## 10. Ledger и dependency epistemics

| Утверждение | Область и результат | Scope / verifier |
|---|---|---|
| Пакет и 10 тел | размеры/LF/hash/frame совпали | FINITE_CELL / PAPER: byte-check |
| Finite Dirichlet inverse и original generator | (3.3)–(3.4), все коэффициенты | ABSTRACT / PAPER |
| Alternating cumulative source | (2.1), точный диапазон \([0,1]\) | ABSTRACT / PAPER |
| Действие прямого канала | (4.5)–(4.7), исходный \(H^1\)/\(P\) вход | ABSTRACT / PAPER |
| Обратные actual coefficients | (4.8)–(4.11), верх, не lower нормы | ABSTRACT / PAPER |
| Первый несовпадающий коэффициент | \(-\log2\) до возврата, \(+\log2\) после | ABSTRACT / PAPER |
| Полный state/supply return | (6.1)–(6.2), точная комплексная форма | ABSTRACT / PAPER |
| Независимая signed строка | (6.3) не доказана | COFINAL_FAMILY / CONDITIONAL: OPEN |
| Полный trial | (7.3)–(7.5), степень \(1/2\) | COFINAL_FAMILY / PAPER |
| Лучший исходный fallback | (7.7), не улучшен | COFINAL_FAMILY / PAPER: inherited |
| Конечные проверки | алгебра, не actual spectral sign | FINITE_CELL / PAPER |

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_T_GT_R_UPPER
ACTUAL_CONSUMER_REQUIREMENT: one-sided eta(epsilon)->0 after original-P returns
ORIGINAL_REQUESTED_OBJECT: independent source-derived joint compensation of full C0
ORIGINAL_OBJECT_IS: UNKNOWN_AS_A_NECESSARY_METHOD
KNOWN_WEAKER_INTERFACES:
  - direct A upper with one b_div and one arch return
  - accepted separately normalized actual-pair margin with full receiver; not proved here
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
NOVELTY_AXIS: tested bounded alternating counting state against its complete finite logarithmic derivative
REOPEN_TRIGGER: independent coupled derivative bound not implied solely by (4.7) or separate positive energies
IMPOSSIBILITY_EVIDENCE: NONE_FOR_CCM_OR_RH
LOOP_DETECTED: inexpensive representation is repeatedly mistaken for an inexpensive full signed inverse/derivative
CURRENT_FAILED_STRATEGY: spend alternating-prefix cancellation before returning the exact generator
ROUTE_SCORE: 2
```

Сильнейшее возражение к выполненной попытке: после малого \(E\) снова предъявлен точный возврат старого \(B\), а не новое arithmetic inequality. **Возражение принято.** Этим объясняется `NO_PROGRESS`; ни дополнительный bound (4.7), ни явное state equation не засчитаны как уменьшение главного долга.

Что запрещено повторять как успех: \(E\) дешёвый \(\Rightarrow-\dot EE^{-1}\) дешёвый; \(B_\eta=B\); положительность отдельных norms \(\Rightarrow\) знак (6.2); September \(V=C^0\) без карты. Что не запрещено: иной настоящий jointly signed source estimate. Невозможность маршрута не доказана.

## 11. Воспроизводимые проверки и их ограничение

До новых математических запусков записан `registration_q47.json` — после полного чтения и предварительного PAPER-вывода, не якобы до любого рассуждения. Проверки подтвердили P1–P6 в их точной алгебраической области; предсказания не редактировались после запуска. Они не подтвердили незаявленную оценку (6.3).

Новый стандартный Python-проверяющий проверяет source manifest, finite Dirichlet coefficients, обратный \(h\), полную производную, возврат dyadic-поправки, конечную Abel-карту с целыми/дробными границами, оба действительных компонента комплексной energy identity и точный непрерывный ноль. Матрицы в проверке — **рациональная конечная модель алгебры**, не production-CCM. При матричном контроле формальные \(\log p\) специализируются рационально для проверки тождества; это не приближения настоящих логарифмов и не sign-certification.

Девять намеренных ошибок обнаружены: пропуск первого/высших dyadic-возвратов; замена \(2^j\) единицей; замена обратных коэффициентов на \(\mu\); удаление ненулевого верхнего trace; неверный знак Abel-интеграла; удаление центрирующего выхода; промежуточное сжатие; удаление off-diagonal complex-form вкладов. Отдельно обнаружен повреждённый байт пакета.

**Ни Lean, ни Arb, ни production spectrum, ни независимый новый аудит не запускались.** Все PAPER-доказательства выше самостоятельны в заявленной области, но не считаются формально проверенными. Исторические scripts внутри источников не выполнялись. Количество проверок не является мерой доказательного прогресса.

Одна архивная директива: проверить знаки (5.1)–(6.2), коэффициент \(2^j\), область (4.3)–(4.11), отсутствие промежуточного \(P\) и единственную оплату \(H_d\)/short/arch в (7.5); затем воспроизвести приложения. Не повышать статус потребителя без независимой (6.3). Автоматический следующий запрос не создаётся.

## 12. Манифест и полные приложения

Тела S1–S10 находятся в исходном каноническом TXT; ниже зафиксированы их полные хеши и byte-scopes. Программы ответа не исполняют historical source code.

| ID | Тело | Bytes / LF | SHA-256 | Строки raw TXT |
|---|---|---:|---|---:|
| S1 | `PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_VERDICT_2026-10-26.md` | 67638 / 1347 | `32b90944bb6195bcfe1842e282f35aaf322555e3e616a3e594a02c3682809de5` | 26–1372 |
| S2 | `CCM_Q46_CONCLUSION.md` | 2717 / 47 | `1e121c3dc8265911c66009090f2126e47fb4e5b78277881e21875658c9095f7c` | 1377–1423 |
| S3 | `CCM_POST_Q46_BOCHNER_SOURCE_PREFLIGHT.md` | 3399 / 66 | `a8d1c0f8de9b4aa72f28f1de74fe57825b62a7f57e3cc914860fe43ca09d80ad` | 1428–1493 |
| S4 | `CCM_POST_Q28_EULER_POSITIVITY_PREFLIGHT.md` | 4681 / 93 | `9ca3dc230902ef9bbd097e21ebc07a32e7494aa76ef5f906f26e8f6a28a3f8a2` | 1498–1590 |
| S5 | `CCM_Q09_AUTOCORRELATION_PREFLIGHT.md` | 4828 / 91 | `8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435` | 1595–1685 |
| S6 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 / 69 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` | 1690–1758 |
| S7 | `CCM_CONTINUOUS_RANK_TWO_TEST.md` | 3751 / 53 | `6c917626df5d97fae5df2cc4a5b409465e23753de2c38e7b41d47e66f0eecbe1` | 1763–1815 |
| S8 | `CCM_Q45_PAIR_POLYLOG_DIVISOR_REDUCTION.md` | 8129 / 148 | `b27227aec0515c8e126a7b6cab23117bc364c67cee167dfc38f23e95c40a29d7` | 1820–1967 |
| S9 | `REPORT_2026-09-13_COMPENSATION_COUPLING_HUNT.md` | 16129 / 296 | `250e638fc458e9f685c8c48944acb2e36c49c4365df146c734e0e7944e89a803` | 1972–2267 |
| S10 | `BRIEF_2026-09-13_SOURCE_PASSIVITY.md` | 4497 / 83 | `2c67b05ca651bc143bb74c9047f726f04df355a1b0e259e4ca00d24c3bf22d3f` | 2272–2354 |

### Выполнение проверок

Сохрани тело `replay_q47.py` из приложения как отдельный файл. Из каталога с этим Markdown и исходным TXT запусти:

```bash
python3 replay_q47.py \
  PROSHKA_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47_VERDICT_2026-10-26.md \
  PROSHKA_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47_2026-10-26.txt \
  q47_replay
```

Первый аргумент — путь к ответу, второй — путь к каноническому TXT, третий — создаваемый каталог для извлечённых приложений. При другом размещении замени только пути; содержимое TXT не меняй. Достаточно Python 3 со стандартной библиотекой. Программа сверяет byte/hash всех четырёх приложений, выполняет новый checker и сравнивает JSON побайтно. Исторические source bodies не исполняются.


BEGIN_ASSET registration_q47.json
BYTES: 1264
SHA256: 47ba4934ccf8d22af78010ad6f63a8b4932b58a514a98d8bd24e028e19826161
```json
{
  "task": "Q47_SOURCE_DERIVED_JOINT_COMPENSATION",
  "stage": "After reading all ten source bodies and preliminary paper derivation; before executable mathematical checks",
  "mechanism": "Finite alternating-integer causal state, exact Mobius inverse, and joint logarithmic-derivative/dyadic compensation in the original metric",
  "predictions": {
    "P1": "The alternating state has exact coefficients (-1)^(n-1) and its inverse has q(2^j u)=2^(j-1)mu(u) for odd u and j>=1.",
    "P2": "Its negative logarithmic derivative has coefficient Lambda(n)-2^j log(2) at n=2^j, not Lambda(n).",
    "P3": "The alternating Abel map retains its upper boundary for a nonzero left input trace.",
    "P4": "The two explicit linked state energies return the complete original Hermitian first form; no sign follows from their separate nonnegativity.",
    "P5": "The continuous-source control cancels exactly if both channels and the full continuous output are returned.",
    "P6": "Inserting the final projector between causal factors can invalidate the exact source map."
  },
  "scope": "Finite algebra checks only, not asymptotic original-P spectral certification",
  "historical_code_execution": false,
  "production_spectrum": false,
  "repository_writes": false
}
```
END_ASSET

BEGIN_ASSET check_q47.py
BYTES: 8953
SHA256: af5c461af01e0ab69bb0f5769456de3d954750b63a3324f738887da7e6c5cef1
```python
#!/usr/bin/env python3
"""Q47 exact checks: finite Dirichlet algebra, full signed return and source framing.
Standard library only. Rational fixtures are NOT production CCM cells.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib, json, re, sys

NAME='PROSHKA_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47_2026-10-26.txt'
SIZE=129191
LF=2357
SHA='072b38a5e63f8411daf467eceb6ad2598b5c462fda7116cfbf9857cb7be9f11b'
HEAD=re.compile(rb'^BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n',re.M)

def verify(raw: bytes) -> dict:
    if len(raw)!=SIZE or raw.count(b'\n')!=LF or hashlib.sha256(raw).hexdigest()!=SHA:
        raise ValueError('canonical packet mismatch')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'): raise ValueError('newline convention')
    if not raw.startswith(b'OPERATIVE_CLASS: TRY_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47\n'):
        raise ValueError('wrong request')
    pos=0; rows=[]
    for i in range(1,11):
        h=HEAD.search(raw,pos)
        if not h or h[1]!=f'S{i}'.encode(): raise ValueError('source order')
        start=h.end(); end=start+int(h[3]); body=raw[start:end]
        if len(body)!=int(h[3]) or body.count(b'\n')!=int(h[4]): raise ValueError('source length')
        if hashlib.sha256(body).hexdigest()!=h[5].decode(): raise ValueError('source hash')
        body.decode('utf-8')
        suffix=b'\nEND_SOURCE '+h[1]+b'\n'
        if raw[end:end+len(suffix)]!=suffix: raise ValueError('source boundary')
        rows.append(dict(id=h[1].decode(),name=h[2].decode(),bytes=len(body),lf=body.count(b'\n'),
                         sha256=h[5].decode(),start_byte=start,end_byte=end,
                         start_line=raw[:start].count(b'\n')+1,end_line=raw[:end].count(b'\n')))
        pos=end+len(suffix)
    if raw[pos:].strip(): raise ValueError('extra trailing bytes')
    return dict(packet=NAME,bytes=SIZE,lf=LF,sha256=SHA,source_count=10,
                all_source_frames_verified=True,sources=rows)

def factor(n):
    if n<1: raise ValueError('positive integer required')
    out={}; p=2
    while p*p<=n:
        while n%p==0: out[p]=out.get(p,0)+1; n//=p
        p+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def mu(n):
    fs=factor(n)
    return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)

def lladd(a,b):
    c=a.copy()
    for p,v in b.items(): c[p]=c.get(p,F())+v
    return {p:v for p,v in c.items() if v}

def llscale(a,s): return {p:v*s for p,v in a.items() if v*s}
def logn(n): return {p:F(e) for p,e in factor(n).items()}
def lam(n):
    fs=factor(n)
    return {next(iter(fs)):F(1)} if len(fs)==1 else {}
def divs(n): return [d for d in range(1,n+1) if n%d==0]
def alt(n): return 1 if n%2 else -1

def inv_alt(n):
    j=0
    while n%2==0: j+=1; n//=2
    return mu(n)*(1 if j==0 else 2**(j-1))

def dyadic(n):
    return {2:F(n)} if n>1 and n&(n-1)==0 else {}

def poly(x,co): return sum((F(v)*x**j for j,v in enumerate(co)),F())
def alt_abel(b,co):
    b=F(b); direct=sum((alt(n)*poly(F(n),co) for n in range(1,int(b)+1)),F())
    top=sum(alt(n) for n in range(1,int(b)+1))*poly(b,co)
    integral=F(); x=F(1)
    while x<b:
        k=int(x); y=min(b,F(k+1)); A=sum(alt(n) for n in range(1,k+1))
        integral+=A*(poly(y,co)-poly(x,co)); x=y
    return direct,top,integral

def zero(n): return [[F() for _ in range(n)] for _ in range(n)]
def eye(n):
    a=zero(n)
    for i in range(n): a[i][i]=F(1)
    return a

def madd(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def mscale(a,s): return [[s*x for x in row] for row in a]
def mm(a,b):
    n=len(a)
    return [[sum((a[i][k]*b[k][j] for k in range(n)),F()) for j in range(n)] for i in range(n)]
def mt(a): return [list(row) for row in zip(*a)]

def mv(a,v): return [sum((x*y for x,y in zip(row,v)),F()) for row in a]
def dot(x,y): return sum((a*b for a,b in zip(x,y)),F())
def shift(n,d):
    a=zero(n)
    for j in range(1,n+1):
        if j*d<=n: a[j*d-1][j-1]=F(1)
    return a

def combination(n,coef):
    a=zero(n)
    for d in range(1,n+1): a=madd(a,mscale(shift(n,d),coef(d)))
    return a

def spec_log(n):
    # Rational specialization of FORMAL log-prime variables, not log approximations.
    return sum((F(p,p+1)*e for p,e in factor(n).items()),F())

def math_checks():
    mutations={}; counts={}; N=96
    for n in range(1,N+1):
        assert alt(n)==1-(2 if n%2==0 else 0)
        assert sum(alt(d)*inv_alt(n//d) for d in divs(n))==(1 if n==1 else 0)
        h=sum(2**j*mu(n//(2**j)) for j in range(n.bit_length()) if n%(2**j)==0)
        assert h==inv_alt(n)
        b={}
        for d in divs(n): b=lladd(b,llscale(logn(d),F(alt(d)*inv_alt(n//d))))
        expect=lladd(lam(n),llscale(dyadic(n),F(-1)))
        assert b==expect
        full=lladd(b,dyadic(n)); assert full==lam(n)
    counts['formal_coefficient_indices']=N
    counts['alternating_prefix_indices']=N
    for n in range(1,N+1): assert sum(alt(k) for k in range(1,n+1))==n%2
    fixtures=[(F(7,2),[1]),(F(6),[1,2,3]),(F(17,3),[2,-1,0,1]),
              (F(9),[81,-18,1]),(F(5),[5,-1])]
    for b,co in fixtures:
        val,top,integ=alt_abel(b,co); assert val==top-integ
    counts['alternating_abel_fixtures']=len(fixtures)
    val,top,integ=alt_abel(*fixtures[0]); mutations['drop_nonzero_upper_trace']=val!=-integ
    val,top,integ=alt_abel(*fixtures[2]); mutations['reverse_abel_integral_sign']=val!=top+integ
    mutations['omit_first_dyadic_return']=lladd(lam(2),llscale(dyadic(2),F(-1)))!=lam(2)
    mutations['drop_higher_dyadic_powers']=dyadic(4)!={}
    mutations['replace_dyadic_2power_by_1']=dyadic(8)!={2:F(1)}
    mutations['replace_inverse_by_mu']=inv_alt(4)!=mu(4)
    # A faithful finite quotient of the Dirichlet algebra, NOT a production L2 carrier.
    n=9; I=eye(n)
    Z=combination(n,lambda d:F(1,d)); Mi=combination(n,lambda d:F(mu(d),d))
    D=madd(I,mscale(shift(n,2),-F(1))) # sigma=1: 2^(1-sigma)=1
    Di=combination(n,lambda d:F(1) if d&(d-1)==0 else F())
    Ea=combination(n,lambda d:F(alt(d),d)); Ei=combination(n,lambda d:F(inv_alt(d),d))
    Ep=combination(n,lambda d:-F(alt(d),d)*spec_log(d))
    Dp=mscale(shift(n,2),spec_log(2))
    B=combination(n,lambda d:F(sum(lam(d).get(p,F())*F(p,p+1) for p in lam(d)),d))
    Y=mm(Dp,Di); Be=mscale(mm(Ep,Ei),-1)
    assert mm(Z,Mi)==I and mm(Ea,Ei)==I and mm(D,Di)==I
    assert mm(D,Z)==Ea and madd(Be,Y)==B
    fr=[F((-1)**j,j+1) for j in range(n)]
    fi=[F(j%3-1,j+2) for j in range(n)]
    for f in (fr,fi):
        x=mv(Ei,f); y=mv(Di,f)
        assert mv(Ea,x)==f and mv(D,y)==f
        slope=2*(dot(f,mv(Ep,x))-dot(f,mv(Dp,y)))
        assert -slope==2*dot(f,mv(B,f))
    counts['exact_rational_operator_dimension']=n
    counts['complex_energy_components']=2
    # Continuous-source control is performed after changing BOTH source channels.
    G=mscale(madd(shift(n,2),shift(n,3)),F(1,3))
    Bec=madd(G,mscale(Y,-1))
    assert madd(madd(Bec,Y),mscale(G,-1))==zero(n)
    # Whole Hermitian source congruence, including the continuous term.
    Leta=madd(mscale(madd(mm(mt(Ea),Ep),mm(mt(Ep),Ea)),-1),
              mm(mm(mt(Ea),madd(madd(Y,mt(Y)),mscale(madd(G,mt(G)),-1))),Ea))
    whole=madd(madd(B,mt(B)),mscale(madd(G,mt(G)),-1))
    assert mm(mm(mt(Ei),Leta),Ei)==whole
    counts['full_hermitian_congruence']=1
    mutations['drop_centering_output']=madd(Bec,Y)!=zero(n)
    # A synthetic projector tests the illegality of an interposed compression.
    P=eye(n)
    for i in (0,1):
        for j in (0,1): P[i][j]-=F(1,2)
    assert mm(P,P)==P
    mutations['insert_intermediate_projector']=mm(mm(P,mm(D,Z)),P)!=mm(mm(mm(mm(P,D),P),Z),P)
    mutations['drop_complex_mixed_terms']=2*dot(fr,mv(B,fr))+2*dot(fi,mv(B,fi))!=0
    assert all(mutations.values())
    return dict(scope='Exact finite algebra and rational nonproduction fixtures only',
                passed=True,counts=counts,planted_errors_detected=mutations,
                first_eta_log_derivative_coefficient={'n':2,'log2_coefficient':-1},
                returned_coefficient={'n':2,'log2_coefficient':1},
                asymptotic_signed_inequality_certified=False)

def main():
    if len(sys.argv)!=2: raise SystemExit('usage: python3 check_q47.py CANONICAL_Q47.txt')
    raw=Path(sys.argv[1]).read_bytes(); provenance=verify(raw)
    bad=bytearray(raw);bad[provenance['sources'][0]['start_byte']+100]^=1
    try: verify(bytes(bad))
    except ValueError: provenance['single_byte_corruption_detected']=True
    else: raise AssertionError('missed corrupt byte')
    result=dict(provenance=provenance,mathematics=math_checks(),historical_code_executed=False,
                lean=False,arb=False,production_spectrum=False,independent_audit=False)
    txt=json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q47_checks.json').write_text(txt,encoding='utf-8');print(txt,end='')
if __name__=='__main__': main()
```
END_ASSET

BEGIN_ASSET q47_checks.json
BYTES: 4832
SHA256: 5f409f40138834b46a86674d34d211baad11a26cbc2e8d467447c07c0bb0df87
```json
{
  "arb": false,
  "historical_code_executed": false,
  "independent_audit": false,
  "lean": false,
  "mathematics": {
    "asymptotic_signed_inequality_certified": false,
    "counts": {
      "alternating_abel_fixtures": 5,
      "alternating_prefix_indices": 96,
      "complex_energy_components": 2,
      "exact_rational_operator_dimension": 9,
      "formal_coefficient_indices": 96,
      "full_hermitian_congruence": 1
    },
    "first_eta_log_derivative_coefficient": {
      "log2_coefficient": -1,
      "n": 2
    },
    "passed": true,
    "planted_errors_detected": {
      "drop_centering_output": true,
      "drop_complex_mixed_terms": true,
      "drop_higher_dyadic_powers": true,
      "drop_nonzero_upper_trace": true,
      "insert_intermediate_projector": true,
      "omit_first_dyadic_return": true,
      "replace_dyadic_2power_by_1": true,
      "replace_inverse_by_mu": true,
      "reverse_abel_integral_sign": true
    },
    "returned_coefficient": {
      "log2_coefficient": 1,
      "n": 2
    },
    "scope": "Exact finite algebra and rational nonproduction fixtures only"
  },
  "production_spectrum": false,
  "provenance": {
    "all_source_frames_verified": true,
    "bytes": 129191,
    "lf": 2357,
    "packet": "PROSHKA_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47_2026-10-26.txt",
    "sha256": "072b38a5e63f8411daf467eceb6ad2598b5c462fda7116cfbf9857cb7be9f11b",
    "single_byte_corruption_detected": true,
    "source_count": 10,
    "sources": [
      {
        "bytes": 67638,
        "end_byte": 73446,
        "end_line": 1372,
        "id": "S1",
        "lf": 1347,
        "name": "PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_VERDICT_2026-10-26.md",
        "sha256": "32b90944bb6195bcfe1842e282f35aaf322555e3e616a3e594a02c3682809de5",
        "start_byte": 5808,
        "start_line": 26
      },
      {
        "bytes": 2717,
        "end_byte": 76306,
        "end_line": 1423,
        "id": "S2",
        "lf": 47,
        "name": "CCM_Q46_CONCLUSION.md",
        "sha256": "1e121c3dc8265911c66009090f2126e47fb4e5b78277881e21875658c9095f7c",
        "start_byte": 73589,
        "start_line": 1377
      },
      {
        "bytes": 3399,
        "end_byte": 79867,
        "end_line": 1493,
        "id": "S3",
        "lf": 66,
        "name": "CCM_POST_Q46_BOCHNER_SOURCE_PREFLIGHT.md",
        "sha256": "a8d1c0f8de9b4aa72f28f1de74fe57825b62a7f57e3cc914860fe43ca09d80ad",
        "start_byte": 76468,
        "start_line": 1428
      },
      {
        "bytes": 4681,
        "end_byte": 84712,
        "end_line": 1590,
        "id": "S4",
        "lf": 93,
        "name": "CCM_POST_Q28_EULER_POSITIVITY_PREFLIGHT.md",
        "sha256": "9ca3dc230902ef9bbd097e21ebc07a32e7494aa76ef5f906f26e8f6a28a3f8a2",
        "start_byte": 80031,
        "start_line": 1498
      },
      {
        "bytes": 4828,
        "end_byte": 89698,
        "end_line": 1685,
        "id": "S5",
        "lf": 91,
        "name": "CCM_Q09_AUTOCORRELATION_PREFLIGHT.md",
        "sha256": "8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435",
        "start_byte": 84870,
        "start_line": 1595
      },
      {
        "bytes": 6174,
        "end_byte": 96021,
        "end_line": 1758,
        "id": "S6",
        "lf": 69,
        "name": "CCM_SPARSE_BAND_RECEIVER.md",
        "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
        "start_byte": 89847,
        "start_line": 1690
      },
      {
        "bytes": 3751,
        "end_byte": 99925,
        "end_line": 1815,
        "id": "S7",
        "lf": 53,
        "name": "CCM_CONTINUOUS_RANK_TWO_TEST.md",
        "sha256": "6c917626df5d97fae5df2cc4a5b409465e23753de2c38e7b41d47e66f0eecbe1",
        "start_byte": 96174,
        "start_line": 1763
      },
      {
        "bytes": 8129,
        "end_byte": 108218,
        "end_line": 1967,
        "id": "S8",
        "lf": 148,
        "name": "CCM_Q45_PAIR_POLYLOG_DIVISOR_REDUCTION.md",
        "sha256": "b27227aec0515c8e126a7b6cab23117bc364c67cee167dfc38f23e95c40a29d7",
        "start_byte": 100089,
        "start_line": 1820
      },
      {
        "bytes": 16129,
        "end_byte": 124518,
        "end_line": 2267,
        "id": "S9",
        "lf": 296,
        "name": "REPORT_2026-09-13_COMPENSATION_COUPLING_HUNT.md",
        "sha256": "250e638fc458e9f685c8c48944acb2e36c49c4365df146c734e0e7944e89a803",
        "start_byte": 108389,
        "start_line": 1972
      },
      {
        "bytes": 4497,
        "end_byte": 129174,
        "end_line": 2354,
        "id": "S10",
        "lf": 83,
        "name": "BRIEF_2026-09-13_SOURCE_PASSIVITY.md",
        "sha256": "2c67b05ca651bc143bb74c9047f726f04df355a1b0e259e4ca00d24c3bf22d3f",
        "start_byte": 124677,
        "start_line": 2272
      }
    ]
  }
}
```
END_ASSET

BEGIN_ASSET replay_q47.py
BYTES: 2182
SHA256: 414ccc321a99838593f0b0d43591bade94ef8b69cd80a41c6a035276e6b0c57c
```python
#!/usr/bin/env python3
"""Extract and replay Q47's four new assets; never execute historical sources.
Usage: python3 replay_q47.py VERDICT.md CANONICAL_Q47.txt [OUTPUT_DIRECTORY]
"""
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,subprocess,sys
HEAD=re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n',re.M)
EXPECTED={'registration_q47.json','check_q47.py','q47_checks.json','replay_q47.py'}
def extract(raw):
    assets={};pos=0
    while True:
        h=HEAD.search(raw,pos)
        if h is None: break
        name=h[1].decode();start=h.end();end=start+int(h[2]);body=raw[start:end]
        if name in assets: raise ValueError('duplicate asset')
        if len(body)!=int(h[2]) or hashlib.sha256(body).hexdigest()!=h[3].decode():
            raise ValueError('asset length/hash '+name)
        suffix=b'```\nEND_ASSET\n'
        if raw[end:end+len(suffix)]!=suffix: raise ValueError('asset frame '+name)
        assets[name]=body;pos=end+len(suffix)
    if set(assets)!=EXPECTED: raise ValueError('asset set')
    return assets

def main():
    if len(sys.argv) not in (3,4):
        raise SystemExit('usage: python3 replay_q47.py VERDICT.md CANONICAL_Q47.txt [OUTPUT_DIRECTORY]')
    verdict=Path(sys.argv[1]).resolve();canonical=Path(sys.argv[2]).resolve()
    out=Path(sys.argv[3] if len(sys.argv)==4 else 'q47_replay').resolve()
    a=extract(verdict.read_bytes());out.mkdir(parents=True,exist_ok=True)
    for name,body in a.items(): (out/name).write_bytes(body)
    run=subprocess.run([sys.executable,str(out/'check_q47.py'),str(canonical)],
                       cwd=out,capture_output=True,text=True,check=True)
    (out/'check_q47.stdout').write_text(run.stdout,encoding='utf-8')
    if (out/'q47_checks.json').read_bytes()!=a['q47_checks.json']:
        raise ValueError('checker JSON differs')
    print(json.dumps(dict(asset_count=len(a),all_hashes_match=True,checker_run=True,
                         json_byte_identical=True,historical_programs_executed=False,
                         production_spectrum_run=False),sort_keys=True,indent=2))
if __name__=='__main__':main()
```
END_ASSET

### Фактическое воспроизведение

После сборки ответа четыре приложения извлечены из самого Markdown с проверкой byte/hash. Извлечённый `check_q47.py` запущен заново на каноническом TXT; JSON совпал побайтно со встроенным. Это внутреннее воспроизведение, не независимый математический аудит.

```json
{
  "all_hashes_match": true,
  "asset_count": 4,
  "checker_run": true,
  "historical_programs_executed": false,
  "json_byte_identical": true,
  "production_spectrum_run": false
}
```

**Итог:** полный источник не подменён; выбранная state-карта проверена. Независимая совместная знаковая оценка нужной силы не получена. Исходный CCM-goal и RH не закрыты.
