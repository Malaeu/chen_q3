# STATUS: TRY_CCM_SIGNED_BLOCK_COUPLING_Q40
```yaml
OPERATIVE_CLASS: TRY_CCM_SIGNED_BLOCK_COUPLING_Q40
VERDICT_CODE: SIGNED_CHANNEL_FLOW_OPTIMUM_HAS_ISOLATED_PRIME_PRICE_FULL_SOURCE_STILL_CANCELS
DATE: '2026-10-26'
REQUEST_ID: Q40_SIGNED_BLOCK_COUPLING
REQUEST_FILE: PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_2026-10-26.txt
REQUEST_BYTES_MEASURED: 129772
REQUEST_LF_MEASURED: 2209
REQUEST_SHA256_MEASURED: 771ae3b7ce9b657227cc939bfb2d922658b5985a258ea5ef6241d14865c8987c
REQUEST_HASH_ORIGIN: measured_here_not_supplied_in_short_caption
REQUEST_READ: complete_root_and_all_ten_complete_source_bodies
SOURCE_MANIFEST: ten_byte_counts_LF_counts_SHA256_and_boundaries_match
BASE_COMMIT_AS_SUPPLIED: 9b04ba4eed017445d1c35ce83a8fa954168cfebc
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB_AS_RETURNED: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
SCHEDULE: 'N=m; L=log(m); M=R=floor(m^epsilon); fixed 0<epsilon<1/32'
SELECTED_OPERATOR: DUALIZE
EXECUTED_TRIAL: 'Unrestricted real signed incidence redistribution; full prime-channel summation before one-sided positive-part payment; exact primal and dual solutions'
PRIMARY_CONSUMER_STATUS: NO_PROGRESS
LOCAL_STATUS: SCOPED_FALSIFICATION_AND_PAID_ACTUAL_SOURCE_DISCRIMINATOR
TESTED_CERTIFICATE_POWER: 'Exactly 1/2 on the logarithmic scale, uniformly after optimization, not the power of the actual operator'
NEW_ALL_P_VANISHING_EXPONENT: false
NEW_ACTUAL_ZERO_PAIR_MARGIN: false
NEW_LOCAL_FACT: 'The actual full-k cutoff leaves isolated outer-prime channels; on a normalized original-P minus-packet family their positive sum is at least c sqrt(m)/log(m)'
COMPLEMENT_CONTROL: 'On the same family the full signed T is o(sqrt(m)/log(m)); actual negative component mass is not negligible'
EXTERNAL_INPUT: 'Unconditional PNT; for explicit diagnostic error, Johnston--Yang arXiv:2204.01980v2, Theorem 1.1 equation (1.3), and Corollary 1.3 equation (1.6)'
EXTERNAL_AUDIT_SCOPE: primary_HTML_statements_and_hypotheses_checked_not_external_proof_recertification
RH: OPEN_NOT_CLAIMED
CF22_PYSR: PARKED_REOPENABLE
REPOSITORY_WRITES: NONE
HISTORICAL_SCRIPTS_EXECUTED: false
NEW_INDEPENDENT_AUDIT: false
LEAN_RUN: false
ARB_RUN: false
PRODUCTION_SPECTRUM_RUN: false
AUTOMATIC_NEXT_REQUEST: false
```

# Q40. Совместные знаковые prime-каналы: точная оптимизация и неизбежный межканальный возврат

## 0. Результат и его точная область

**Независимый верх полной CCM с показателем \(\eta(\epsilon)\to0\) не получен.** Испытан один ход, действительно более сильный, чем S4: разрешены произвольные **знаковые**, в том числе зависящие от проверяемого вектора, веса; сначала суммируется **весь** каждый prime-канал, и только затем оплачивается его положительная часть. Ни Cauchy, ни раздельная норма каждого \(D_n\) в определение проверяемого оптимума не входят.

Получены три результата.

1. **[ABSTRACT | PAPER]** Оптимум такого одностороннего сертификата найден конструктивно и совпадает с суммой положительных **полных знаковых сумм по компонентам связности** фактического incidence-графа. Это не тождество S4 о неотрицательных весах: знаковое перераспределение в общем случае действительно может уменьшить цену, даже до нуля.
2. **[COFINAL_FAMILY | PAPER, с геометрией S2/S9 и безусловной PNT]** На одной нормированной семье из исходного \(P\) остаются изолированные настоящие простые каналы с положительной суммарной величиной не меньше \(c\sqrt m/\log m\). Их не меняет никакое разрешённое знаковое перераспределение. Оптимальная полная цена выбранного класса имеет показатель \(1/2\), даже при адаптации к \(m,c\).
3. **[COFINAL_FAMILY | PAPER, с внешним безусловным PNT-входом E1]** На **той же** семье настоящая первая сумма \(c_m^*Tc_m\) равна \(o(\sqrt m/\log m)\). Поэтому отрицательная масса других полных компонент компенсирует положительные изолированные каналы. Это конкретный контроль потери знака, а не запрет настоящего сокращения.

Последний факт не является новым all-\(P\) поставщиком: он относится к явно построенной диагностической семье, не к каждому вектору и не к нулеселективной паре. Классическая PNT и её ошибка не объявляются новым открытием. Новый локальный результат здесь — **точное решение усиленной задачи о знаковом перераспределении, её исходниковый край и полный возврат отличающей семьи**.

## 1. Чтение, source lock и проверка на повтор

Прочитаны весь канонический UTF-8 TXT и все десять тел S1–S10, включая полный Q39 с приложениями. Проверены объявленные BYTES, LF, SHA256, последовательность S1–S10 и один разделительный LF вне каждого тела. Размер всего TXT — **129772 байта**, число LF — **2209**. Общий SHA256 вычислен здесь; короткая подпись Q40 его не задавала. Манифест и повторяемый verifier находятся в приложениях.

Через GitHub connector заново прочитан bootstrap на ветке `rh_clean`; возвращён blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Исторические команды источников не исполнялись. Репозиторий не изменялся.

| Источник | Что наследуется / что не повторяется |
|---|---|
| S1, S2 | Полные \(B_d,D_d\), исходная геометрия, цены возврата; двухпростая Cauchy-корреляция не переоценивается |
| S3 | Many-prime variance и её отдельно оплаченный остаток — уже проверенная неудачная цена |
| S4 | Положительные partitions и **термовые** модули — уже исключённый класс; нынешние знаковые веса и канальные суммы шире |
| S5 | Только continuous-Abel predecessor; никакая недоказанная полная производная \(B\) не используется |
| S6 | Качественные shifted correlations не превращаются в нужную степень |
| S7 | \(A=N_\star+E_\star\), \(\|E_\star\|\le r_\star=O_\epsilon(m^{2\epsilon})\), — оплаченная карта, не новый выигрыш |
| S8 | Q34 сохраняется в своей области; секторные платы не начисляются второй раз прямому \(A\) |
| S9, S10 | Исходные три контакта, sparse receiver и лучший безусловный fallback |

**Нынешний ход не является ещё одним подбором положительных весов.** Знаковая задача решается сразу для всего класса, без поиска по сетке. Её первая односторонняя потеря будет точно указана в §8.

## 2. Исходный объект и точная знаковая свобода

### 2.1. Полные блоки

Сначала фиксируется \(0<\epsilon<1/32\), затем растёт целое \(m\). Положим
\[
L=\log m,\quad M=R=\lfloor m^\epsilon\rfloor,\quad
\Omega=2\pi M/L.
\]
Для исходного изометрического синтеза \(F_M\) и исходного трёхконтактного \(P\):
\[
c=Pc,\quad f=F_Mc,\quad \|f\|_2=\|c\|_2,
\quad f(0)=f(L)=0,\quad \int_0^L e^{\pm t/2}f(t)\,dt=0.
\tag{2.1}
\]
Функции продолжаются нулём. На физическом \(L^2(0,L)\)
\[
(V_sf)(t)=\mathbf1_{[s,L]}(t)f(t-s),\quad V_s=0\ (s\ge L),
\quad Q_M(s)=F_M^*(V_s+V_s^*)F_M.
\]
Сохраняются
\[
h(x)=x^{-1/2}PQ_M(\log x)P,\qquad
B_d=\sum_{k\le m/d}\log k\,h(dk),\qquad
D_d=\mathbf1_{R<d\le m}B_d,
\]
\[
T=\sum_{d\le m}\mu(d)D_d,\qquad
A=\sum_{n\le m}\Lambda(n)h(n)=T+T_{\le R},
\quad T_{\le R}=\sum_{d\le R}\mu(d)B_d.
\tag{2.2}
\]
Это унаследованная конечная \(\Lambda=\mu*\log\) карта S2, не новый arithmetic supplier. Все степени простых, оба временных направления, self/cross-элементы сохраняются. Внутри сдвиговых произведений нет нового \(P\).

**[ABSTRACT | PAPER, inherited]**
\[
\|B_d\|\le b/\sqrt d,\quad b=40+16\Omega,
\quad \|T_{\le R}\|\le2b\sqrt R,
\quad C^0=A+H_d,\quad0\preceq H_d\preceq4P.
\tag{2.3}
\]

### 2.2. Разрешаем больше, чем положительные partitions

Зафиксируем единичный **комплексный** \(c=Pc\). Обозначим
\[
\beta_n=c^*D_nc\in\mathbb R,\qquad z_n=\mu(n)\beta_n.
\tag{2.4}
\]
Реальность происходит от эрмитовости полной матрицы; исходный вектор в общей оценке не заменён вещественным.

Для каждого активного квадратсвободного \(n>R\) разрешим любые конечные вещественные числа
\[
\theta_{p,n}\in\mathbb R\quad(p\mid n),\qquad
\sum_{p\mid n}\theta_{p,n}=1.
\tag{2.5}
\]
Они могут зависеть от \(m,c\), быть отрицательными и сколь угодно большими. Это **не** неотрицательная partition of unity S4. При \(z_n=0\) соответствующие вклады нулевые при любых конечных весах.

Полный prime-канал:
\[
a_p(\theta,c)=\sum_{\substack{R<n\le m\,;\,p\mid n}}
\theta_{p,n}\mu(n)\beta_n
=-\sum_{\substack{k:\ p\nmid k\,;\,R<pk\le m}}
\mu(k)\theta_{p,pk}\beta_{pk}.
\tag{2.6}
\]
Вторая запись сохраняет **весь** внутренний \(k\)-блок в \(\beta_{pk}\); индекс \(k\) здесь относится к prime-incidence и не подменяет второй множитель внутри \(B\). Для не-squarefree внешнего индекса слагаемое нулевое из-за \(\mu\), но внутренние prime powers не удаляются.

До оценки точно
\[
\boxed{c^*Tc=\sum_p a_p(\theta,c).}
\tag{2.7}
\]
Проверяемая односторонняя цена после **полного сложения каждого канала**:
\[
\mathcal P(\theta,c)=\sum_p[a_p(\theta,c)]_+,
\qquad [x]_+=\max(x,0),
\]
\[
\mathcal P_{\min}(m,c)=\inf_{\theta\text{ удовлетворяет }(2.5)}\mathcal P(\theta,c).
\tag{2.8}
\]
Всегда \(c^*Tc\le\mathcal P_{\min}(m,c)\). Это более выгодная цена, чем сумма модулей каналов, и тем более чем термовые модули S4. **Никакого Cauchy и квадрата всей арифметической суммы здесь нет.**

Адаптивность означает только скалярное утверждение для фиксированного \(c\). Общий линейный оператор, зависящий от всех таких оптимизаторов одновременно, не объявляется. Если запретить адаптивность, класс станет уже; нижний контроль расширенного класса останется в силе.

## 3. Первое точное совместное решение: signed flow по компонентам

### 3.1. Фактический граф

Пусть \(\mathcal N_c=\{n:z_n\ne0\}\). Его вершины — простые, делящие хотя бы одно \(n\in\mathcal N_c\). Каждое \(n\) соединяет все свои простые делители гиперребром. Для простого \(n=p\) это одноточечное ребро.

Используется именно **активная** поддержка \(z_n\ne0\). Нулевое ребро не переносит массу при конечных \(\theta\). Для компоненты \(\mathcal C\) положим
\[
s_{\mathcal C}(c)=
\sum_{\substack{n\in\mathcal N_c:\ \{p:p\mid n\}\subset\mathcal C}}z_n.
\tag{3.1}
\]

**[ABSTRACT | PAPER]** Для каждого допустимого \(m,c\), включая пустую активную поддержку:
\[
\boxed{
\mathcal P_{\min}(m,c)=\sum_{\mathcal C}[s_{\mathcal C}(c)]_+.
}
\tag{3.2}
\]
Инфимум достигается конечными вещественными весами.

### 3.2. Нижний dual и конструкция равенства

Положим \(x_{n,p}=z_n\theta_{p,n}\). Условия — только
\(\sum_{p\mid n}x_{n,p}=z_n\). На каждой компоненте сумма каналов фиксирована:
\[
\sum_{p\in\mathcal C}a_p=s_{\mathcal C}.
\]
Следовательно
\(\sum_{p\in\mathcal C}[a_p]_+\ge[s_{\mathcal C}]_+\).
Это одновременно явный dual-сертификат: назначить всем вершинам компоненты
\(y_p=1\) при \(s_{\mathcal C}>0\) и \(y_p=0\) иначе. Тогда
\[
\sum_pa_py_p=\sum_{\mathcal C}[s_{\mathcal C}]_+
\le\sum_p[a_p]_+.
\tag{3.3}
\]

Для обратного неравенства возьмём любое начальное распределение вкладов, например поровну. Выберем остов компоненты и корень. Каждое ребро остова соединяет \(p,q\), входящие вместе в некоторое активное \(n\). Замена
\[
x_{n,p}\mapsto x_{n,p}+t,\qquad x_{n,q}\mapsto x_{n,q}-t
\tag{3.4}
\]
сохраняет весь исходный блок. Проходя листья к корню, переносим полный канал листа к родителю. В итоге только корень несёт \(s_{\mathcal C}\), остальные каналы нулевые. Поскольку \(z_n\ne0\), возвращение \(\theta=x/z_n\) законно. Это доказывает (3.2).

Здесь сохранено полное знаковое взаимодействие **всех** блоков компоненты. Нормы отдельных \(B_d\) не использовались.

### 3.3. Почему это не переименование S4

Алгебраический контроль: \(z_2=2,z_3=-3,z_6=1\). Знаковое распределение
\(x_{6,2}=-2,x_{6,3}=3\) зануляет оба полных канала; цена (2.8) равна нулю. При неотрицательной partition этого блока она не меньше 2, а термовая абсолютная цена S4 равна 6.

Это контроль различия классов, **не CCM-ячейка**. Для настоящего источника остаётся проверить структуру самого активного графа и его знаковых компонент.

## 4. Новый source-specific край: изолированные настоящие простые

### 4.1. Полный \(k\), а не удаление неудобных атомов

**[ABSTRACT | PAPER]** На физическом пространстве, ещё до \(P\),
\[
\boxed{B_n=0\quad\text{при }n\ge m/2.}
\tag{4.1}
\]
При \(n>m/2\) остаётся только \(k=1\), чей вес \(\log1=0\). При \(n=m/2\), если этот индекс целый, дополнительный \(k=2\) имеет \(nk=m\) и \(Q_M(L)=0\). В частности, это доказанное нулевое значение **полного блока**, не удаление prime-power коэффициента.

Если
\[
\max(R,m/4)<p<m/2,\qquad p\text{ простое},\qquad \beta_p\ne0,
\tag{4.2}
\]
то \(p\) — изолированная вершина фактического графа. Любой другой squarefree индекс, кратный \(p\), не меньше \(2p>m/2\), поэтому его блок нулевой. У единственного активного блока \(n=p\) обязательна \(\theta_{p,p}=1\).

Следовательно для **всех** знаковых распределений
\[
\boxed{a_p=-\beta_p\quad\text{на }(4.2).}
\tag{4.3}
\]
Нельзя переносить вклад через фиктивное нулевое ребро \(n=2p\).

Для ещё более узкой, но фиксированной относительной области
\[
 m/3<p<m/2
\]
полная сумма содержит ровно один ненулевой внутренний член:
\[
\boxed{B_p=\log2\,h(2p).}
\tag{4.4}
\]
Это не приближение и не выбор одного члена из ненулевого хвоста.

### 4.2. Связь с настоящей арифметикой

В (4.3) используется настоящий \(\mu(p)=-1\). В (4.1)–(4.4) используется настоящий \(\log k\)-вес и буквальная граница \(nk\le m\). Эти свойства отсутствуют у произвольных эрмитовых меток с теми же нормами. Следующий шаг проверяет знак \(\beta_p\) на **допустимом исходном тесте**, а не назначает его независимо.

## 5. Исходный \(P\)-тест, на котором изолированные каналы положительны

### 5.1. Фиксированный гладкий прототип

Возьмём тот же фиксированный плоский bump, что в S2, но с **противоположными** знаками двух пакетов:
\[
a=1/10,\quad
\chi(t)=\begin{cases}\exp[-1/(t(a-t))],&0<t<a,\\0,&\text{иначе},\end{cases}
\quad u=\chi''-\chi/4,\quad U=\|u\|_2^2>0,
\]
\[
\boxed{f_L^-(t)=\frac{u(t)-u(t-(L-a))}{\sqrt{2U}}.}
\tag{5.1}
\]
При \(L>4a\) пакеты не пересекаются, \(\|f_L^-\|_2=1\), все фиксированные производные имеют равномерные нормы. Интегрирование по частям даёт
\[
\int e^{\pm t/2}u(t)dt=0;
\]
оба контакта сохраняются каждым переводом отдельно. Все endpoint-traces нулевые. Пока \(f_L^-\) — физический, не полосовой тест.

Пусть
\[
r_0(v)=U^{-1}\int u(t)u(t+v)dt,
\qquad \mathfrak r(v)=r_0(v+a).
\]
\(r_0\) вещественна, чётна, поддержана на \([-a,a]\), \(r_0(0)=1\). Для полной двусторонней корреляции
\[
q_f(s)=2\Re\int\overline{f(t)}f(t+s)dt
\]
имеем
\[
q_{f_L^-}(s)=2r_0(s)-r_0(s-(L-a))-r_0(s+(L-a)).
\]
Так как \(a<\log2\), на **всей арифметической области** \(s\ge\log2\):
\[
\boxed{q_{f_L^-}(s)=-\mathfrak r(s-L).}
\tag{5.2}
\]

Зададим положительную фиксированную ширину
\[
h_*:=\min\left(a/4,\frac{\sqrt U}{2\|u'\|_2}\right)>0.
\]
Из \(\|u(\cdot+v)-u\|_2\le |v|\|u'\|_2\) следует
\[
r_0(v)\ge1-\frac{v^2\|u'\|_2^2}{2U}\ge7/8
\quad (|v|\le h_*).
\tag{5.3}
\]
\(\|u'\|_2>0\), иначе ненулевая компактная \(u\) была бы постоянной.

Положим
\[
\alpha=\tfrac12e^{-a-h_*},\qquad
\beta=\tfrac12e^{-a+h_*},\qquad I_m=(\alpha m,\beta m].
\tag{5.4}
\]
Тогда \(1/3<\alpha<\beta<1/2\). Например, \(a+h_*\le1/8\) и
\(e^{1/8}\le(1-1/8)^{-1}=8/7<3/2\). Для каждого \(p\in I_m\)
\[
|\log(2p)-(L-a)|\le h_*.
\tag{5.5}
\]

### 5.2. Полный Fourier/contact-return

**[COFINAL_FAMILY | PAPER, inherited geometry S2 §5/S9]** Для любого фиксированного целого \(q\ge2\) исходное Fourier-усечение и одновременная коррекция трёх контактов дают нормированные
\[
c_m=Pc_m,\qquad f_m=F_Mc_m,\qquad
\delta_m=\|f_m-f_L^-\|_2
\le C_q L^{q-1/2}M^{1/2-q}.
\tag{5.6}
\]
Этот перенос не берётся из receiver вне его области: у двух пакетов фиксированные равномерные нормы производных и точные нулевые контакты. Повторное интегрирование Fourier-коэффициентов даёт \(C_qL^{q-1/2}|j|^{-q}\). Нормированный endpoint-residual и обе экспоненциальные невязки имеют тот же \(\ell^2\)-порядок; исходная нормированная Gram-матрица контактов \(\succeq I/2\) eventually. Знак второго пакета этих оценок не меняет. Нормировка добавляет лишь постоянный множитель.

Для двух единичных функций и любого сдвига
\[
|q_{f_m}(s)-q_{f_L^-}(s)|\le4\delta_m.
\tag{5.7}
\]
После проекции **не предполагается** сохранение компактной поддержки пакетов. Эта ошибка не умножается на сумму модулей адаптивных весов: нижняя граница использует только неизменяемые изолированные каналы, а приближённые оптимизаторы в исходную форму не подставляются. При \(\delta_m\le1/16\), из (5.2)–(5.5), безопасно ослабляя константы,
\[
q_{f_m}(\log(2p))\le-1/2\qquad(p\in I_m).
\tag{5.8}
\]

Фиксируем один раз
\[
q>2/\epsilon+2.
\tag{5.9}
\]
Тогда \(\sqrt m\,L(1+L)(2\delta_m+\delta_m^2)=o(1)\). Фиксированные константы могут зависеть от \(\epsilon,q,\chi\), но не от \(m\).

### 5.3. Первая source-specific односторонняя арифметическая оценка

Для всех достаточно поздних \(m\), \(R<\alpha m\). На простых \(p\in I_m\) из (4.3), (4.4), (5.8):
\[
\boxed{
z_p=-c_m^*D_pc_m
\ge\frac{\log2}{2\sqrt{2p}}
\ge\frac{\log2}{2\sqrt m}>0.
}
\tag{5.10}
\]
Это утверждение о **настоящем знаковом частичном источнике**, не произвольная расстановка фаз.

По безусловной PNT для фиксированных \(\alpha,\beta\)
\[
\pi(\beta m)-\pi(\alpha m)
\ge\frac{(\beta-\alpha)m}{2L}
\tag{5.11}
\]
при всех достаточно больших \(m\). Для явного достаточного порога можно использовать E1, Corollary 1.3: достаточно \(\alpha m\ge2\) и
\[
19.18\,L^{1.515}
 e^{-0.8274\sqrt{L+\log\alpha}}\le(\beta-\alpha)/2.
\]
Действительно \(\mathrm{li}(\beta m)-\mathrm{li}(\alpha m)\ge(\beta-\alpha)m/L\), а две конечные ошибки оплачены целиком. Ни PNT в коротких относительных окнах, ни RH-size error не предполагаются: \(\alpha,\beta\) фиксированы.

Следовательно при
\[
c_0=\frac{(\beta-\alpha)\log2}{4}>0
\]
получаем
\[
\boxed{
\sum_{\substack{p\in I_m\\p\text{ простое}}}(-c_m^*D_pc_m)
\ge c_0\frac{\sqrt m}{L},\qquad
\mathcal P_{\min}(m,c_m)\ge c_0\frac{\sqrt m}{L}.
}
\tag{5.12}
\]
Последняя граница действует **одновременно для всех конечных знаковых распределений**, даже выбираемых после \(c_m\). Изолированные каналы не меняются.

## 6. Проверка полного signed return: на той же семье дорогие компоненты сокращаются

Цель этого раздела — не получить all-\(P\) оценку из PNT, а различить цену (5.12) и реальную полную первую форму. Оплата только модулей изолированных каналов была бы недостаточным выводом.

### 6.1. Полный непрерывный фон и оба момента

Пусть \(M_u(z)=\int e^{zt}u(t)dt\). Точно, как в профильной проверке S2,
\[
\int e^{zv}\mathfrak r(v)dv
=\frac{e^{-az}}U M_u(z)M_u(-z).
\tag{6.1}
\]
Два множителя имеют нули при \(z=1/2\). Поэтому
\[
\int e^{v/2}\mathfrak r(v)dv=0,
\qquad
\int v e^{v/2}\mathfrak r(v)dv=0.
\tag{6.2}
\]
Это унаследованный контроль контактов, не новый знак арифметики.

Определим
\[
F_m(x)=x^{-1/2}\mathfrak r(\log(x/m)).
\]
Его поддержка внутри \([me^{-2a},m]\), оба края плоские. Из (5.2)
\[
A_{\rm phys}[f_L^-]=-\sum_{n\le m}\Lambda(n)F_m(n),
\qquad \int_1^m F_m(x)dx=0.
\tag{6.3}
\]
В сумме остаются все \(\Lambda(p^k)\); верхний атом равен нулю по настоящему overlap.

### 6.2. Независимый внешне проверенный диагностический вход

Используется только безусловная **Theorem 1.1, equation (1.3)** Johnston–Yang, arXiv:2204.01980v2:
\[
|\psi(x)-x|
\le9.39x(\log x)^{1.515}e^{-0.8274\sqrt{\log x}}
\quad(x\ge2).
\tag{E1}
\]
Первичная HTML-формулировка, диапазон и Corollary 1.3 проверены. Полное внешнее доказательство и его вычислительные составляющие не воспроизводились. Это **не ZF78 и не предположение RH**. Новая теорема о нулях здесь не заявляется. Конкретные числа не важны для результата, но фиксируют полностью проверяемую цену.

Положив \(E(x)=\psi(x)-x\), конечное интегрирование Стилтьеса с обоими нулевыми краями даёт
\[
A_{\rm phys}[f_L^-]=\int_1^m E(x)F_m'(x)dx,
\quad F_m'(x)=x^{-3/2}\left[\mathfrak r'(\log(x/m))-\tfrac12\mathfrak r(\log(x/m))\right].
\]
Здесь сохранился полный signed интеграл; модуль ниже нужен только для данного диагностического семейства. При
\[
C_{\mathfrak r}=\int_{-2a}^0 e^{v/2}
 |\mathfrak r'(v)-\mathfrak r(v)/2|\,dv<\infty
\]
получаем
\[
\boxed{
|A_{\rm phys}[f_L^-]|
\le9.39C_{\mathfrak r}\sqrt m\,L^{1.515}
 e^{-0.8274\sqrt{L-2a}}.
}
\tag{6.4}
\]
В (6.4) не потерян главный непрерывный член: он сначала отменён **точно** в (6.3), а не отдельно оплачен большой нормой.

### 6.3. Полный \(k\)-возврат коротких делителей и проекции

S2 §4 уже доказывает для того же \(\mathfrak r\)
\[
G(T)=\sum_{k\ge1}\frac{\log k}{\sqrt k}\mathfrak r(\log(k/T)),
\qquad |G(T)|\le C_G\frac{1+\log T}{\sqrt T}.
\]
Смена знака второго пакета даёт, без усечения суммы,
\[
B_d[f_L^-]=-G(m/d)/\sqrt d.
\]
Следовательно
\[
|T_{\le R,\rm phys}[f_L^-]|
\le C_G\frac{R(1+L)}{\sqrt m}=o(1).
\tag{6.5}
\]
Это оценка короткого сектора на данной семье, а не замена общего short receiver.

Для произвольного физического \(L^2\)-вектора истинна элементарная полная норма
\[
\|\mathbf T\|
\le2\sum_{d\le m}\sum_{k\le m/d}\frac{\log k}{\sqrt{dk}}
\le4\sqrt m L(1+L).
\tag{6.6}
\]
Последнее следует из \(\sum_{k\le x}k^{-1/2}\le2\sqrt x\) и
\(\sum_{d\le m}d^{-1}\le1+L\). Оно используется только для ошибки геометрического возвращения, не как desired signed supplier. Поэтому на \(f_m\)
\[
|T[f_m]-T[f_L^-]|
\le4\sqrt m L(1+L)(2\delta_m+\delta_m^2)=o(1).
\tag{6.7}
\]
Сохранены линейные смешанные члены и квадрат ошибки. Норма конечной CCM-матрицы не применялась к неполосовому \(f_L^-\).

Объединяя (6.4)–(6.7):
\[
\boxed{
|c_m^*Tc_m|\le e_m,
}
\]
\[
e_m=9.39C_{\mathfrak r}\sqrt m L^{1.515}e^{-0.8274\sqrt{L-2a}}
+C_G R(1+L)m^{-1/2}
+4\sqrt m L(1+L)(2\delta_m+\delta_m^2),
\]
\[
\boxed{e_m=o(\sqrt m/L).}
\tag{6.8}
\]
Важно: первый член в \(e_m\) не заявляется \(o(1)\) или \(m^{o(1)}\). Его показатель всё ещё \(1/2-o(1)\). (6.8) — сравнение с диагностической ценой, не полный RH-strength результат.

### 6.4. Реальная отрицательная компенсация не исчезла

Обозначим через \(\mathcal I\) набор изолированных prime-компонент из (5.4). Вводимые сейчас матрицы — буквально части прежней суммы:
\[
T_{\rm iso}=-\sum_{p\in I_m}D_p,\qquad
T_{\rm rest}=T-T_{\rm iso}.
\]
Из (5.12), (6.8)
\[
\boxed{
c_m^*T_{\rm iso}c_m\ge c_0\sqrt m/L,
\qquad
c_m^*T_{\rm rest}c_m\le-c_0\sqrt m/L+e_m.
}
\tag{6.9}
\]
Это настоящая межблочная знаковая компенсация на одной исходной семье. Все остальные блоки, их \(k\)-суммы и prime powers находятся в \(T_{\rm rest}\), а не объявлены независимыми.

Эквивалентно, для полных компонент графа
\[
\sum_{\mathcal C}[-s_{\mathcal C}(c_m)]_+
=\mathcal P_{\min}(m,c_m)-c_m^*Tc_m
\ge c_0\sqrt m/L-e_m.
\tag{6.10}
\]
Поэтому первая форма мала относительно цены сертификата **именно благодаря тому знаку между компонентами, который сертификат отбрасывает**. Ни положительная частичная форма (5.12), ни отрицательная частичная форма (6.9) не являются нижним спектральным результатом для всей CCM.

## 7. Полная цена выбранного одностороннего завершения

Пусть
\[
\mathfrak S_m:=\sup_{\substack{c=Pc\\\|c\|=1}}\mathcal P_{\min}(m,c).
\tag{7.1}
\]
Порядок \(\sup_c\inf_\theta\) фиксирован; перестановка min–max не используется.

С одной стороны, (5.12) даёт \(\mathfrak S_m\ge c_0\sqrt m/L\). С другой стороны, допустимы обычные равные неотрицательные веса. Для них
\[
\sum_p[a_p]_+\le\sum_n[z_n]_+\le\sum_n|\beta_n|.
\]
Отсюда двумя законными способами
\[
\boxed{
\mathfrak S_m\le s_{40,T}:=
\min\{2b\sqrt m,\ 4\sqrt m L(1+L)\}.
}
\tag{7.2}
\]
Первая граница использует (2.3), вторая — полную двойную сумму (6.6). Таким образом на каждой достаточно поздней исходной ячейке
\[
\boxed{
 c_0\frac{\sqrt m}{L}\le\mathfrak S_m
 \le4\sqrt m L(1+L),\qquad
 \lim_{m\to\infty}\frac{\log\mathfrak S_m}{\log m}=\frac12.
}
\tag{7.3}
\]
**Это точная степенная классификация оптимального сертификата данного класса**, а не степени \(\lambda_{\max}(T)\).

Для любого предлагаемого \(s_m=C_\epsilon m^{\eta}\), фиксированного \(\eta<1/2\), маржа сертификата на нашей семье имеет отрицательный верх:
\[
s_m-\mathcal P_{\min}(m,c_m)
\le-\frac{c_0}{2}\frac{\sqrt m}{L}<0
\quad\text{eventually}.
\tag{7.4}
\]
Именно это, а не провал достаточного upper-конверта, отвергает утверждение о существовании sub-half-power сертификата в выбранном классе.

Если веса неадаптивны и каналы оформляются эрмитовыми матрицами \(A_p\), то
\(\langle c,(A_p)_+c\rangle\ge[\langle c,A_pc\rangle]_+\).
Поэтому отдельное сложение **матричных** положительных частей не обходит (7.4). Новые source-dependent смешанные поправки между различными компонентами сюда не включены и не опровергнуты.

### 7.1. Возврат к потребителю

Законное, но более дорогое, завершение на всех исходных векторах:
\[
T\preceq s_{40,T}P,
\qquad
A\preceq(s_{40,T}+2b\sqrt R)P,
\]
\[
\boxed{
PK_mP\succeq-[s_{40,T}+2b\sqrt R+50L+8]P.
}
\tag{7.5}
\]
Здесь short-цена \(2b\sqrt R\) оплачивает переход **T к A** один раз. Нельзя затем снова добавлять \(b_{\rm div}\) к той же прямой нижней оценке \(K_m\).

Универсальный новый сертификат хуже сохранённого S10. Поэтому итоговая рабочая оценка не заменяется:
\[
s_{\rm keep}=W_{<}(m)+W(\lfloor\sqrt m\rfloor)
\le6\sqrt m+6m^{1/4},
\]
\[
\boxed{
A\preceq s_{\rm keep}P,\quad
T_{>R}\preceq(s_{\rm keep}+b_{\rm div})P,\quad
PK_mP\succeq-[s_{\rm keep}+50L+8]P,
}
\tag{7.6}
\]
\[
b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\]
Условные \(3/8\) остаются **только** при прежней ZF78; они не использованы ни в (5.12), ни в (6.8), ни в (7.3).

### 7.2. Ledger всех возвратов

| Возврат | Полная цена / точная карта | Область |
|---|---|---|
| Полные incidence-каналы | (2.6)–(2.7), ошибка 0 | Все исходные комплексные \(c\); для адаптивных весов фиксируется \(c\) |
| Signed flow | (3.2), достигаемый точный оптимум | Весь конечный активный граф, не отдельная пара |
| Края \(n=m/2,m\) | (4.1), настоящие \(\log1=0\), \(Q_M(L)=0\) | Без удаления formal coefficients |
| Все внутренние \(k\) | (2.2), (4.4), (6.5) | Сокращение до \(k=2\) только там, где других ненулевых членов нет |
| Прототип в исходный \(P\) | (5.6)–(5.9), (6.7) | Только диагностическая семья; не новая плата общему upper |
| Непрерывный фон | \(C^0=A+H_d\), \(0\preceq H_d\preceq4P\); (6.3) | Не начисляется второй раз к прямому \(K\) |
| Общий T-to-A short | \(2b\sqrt R\) в (7.5) | Один раз |
| Прежний A-to-T short | \(b_{\rm div}\) в (7.6) | Другой путь возврата, не сумма двух short-fees |
| Архимедова часть | \(50L+8\) | Один раз на исходном \(P\) |
| Q32 near | \(N_\star=T+T_{\le R}-E_\star\), \(\|E_\star\|\le r_\star\) | Только при отчёте через near; к прямому (7.5) не добавляется |
| Q34 / proper powers | Уже внутри полных \(\mu*\log\), \(\Lambda\) | Никакого повторного \(U_{\rm sf}\) или pp-fee |

Суммы по shell-overlaps Q32 не изменялись. Мы вернулись к целому \(A\), поэтому отдельный sinc-smoothed верхний атом \(N_\star\) не объявлялся нулём. Для исходного полного \(h(m)\) нулевой overlap законен.

## 8. Первая потеря и выполненный более ранний rollback

До (2.8) все знаки сохраняются. После точной оптимизации ошибка выбранного одностороннего завершения буквально равна
\[
\boxed{
\mathcal P_{\min}(m,c)-c^*Tc
=\sum_{\mathcal C}[-s_{\mathcal C}(c)]_+.
}
\tag{8.1}
\]
**Первая потеря — удаление отрицательных полных компонент после сложения всех их каналов.** Это более поздняя потеря, чем термовые модули S4; (6.10) доказывает, что она существенна на настоящей исходной семье.

Нужное независимое сравнение полной знаковой суммы компонент не получено. Произвольный малый upper на \(\sum_\mathcal C s_\mathcal C(c)\) — ровно исходный upper на \(T\), не новая лемма-поставщик.

Выполненный rollback — **до выбора prime-incidence как пространств отдельно оплачиваемых каналов**:
\[
\boxed{
c^*C^0c=\sum_{\mathcal C}s_{\mathcal C}(c)+c^*T_{\le R}c+c^*H_dc
}\quad\text{на каждом фиксированном }c,
\tag{8.2}
\]
то есть операторно \(C^0=T+T_{\le R}+H_d\). Нулевая ошибка карты, те же \(k\), те же \(P\), все края. Конкретный отличающий расчёт этого отката — (6.8)–(6.10): большая положительная часть и компенсирующая отрицательная часть существуют одновременно в настоящей форме.

Два точных представления оставшегося долга, **не два запущенных новых механизма**:

| Представление | Различающий тест и сила | Цена / риск |
|---|---|---|
| Полная \(\sum_\mathcal C s_\mathcal C\), с отрицательными компонентами | Любой новый upper должен возвращать (6.8), а не платить лишь (5.12). Это быстро отвергает неправильное положительное доминирование | Карта 0; численный поиск по partitions больше не нужен. Сам нужный sign supplier отсутствует |
| Прежнее центральное \(N_\star\) до prime-incidence | Проверять новую связь actual \(\Lambda-1\) и единой корреляции, не separate norms | Возврат \(r_\star=O(m^{2\epsilon})\) уже оплачен; главный арифметический знак остаётся исследовательским долгом |

Никакой автоматический Q41 не назначается. Возможность математического сокращения, в том числе межкомпонентного, не исключена; на диагностической семье оно как раз установлено в ограниченном масштабе.

## 9. Сильнейшая самоатака и границы результата

**Возражение:** «Можно сложить два изолированных prime-канала с отрицательным другим каналом до положительной части и обойти lower». Да. Такое смешивание **разных компонент** находится вне (2.5)–(2.8). Если сразу соединить все компоненты, цена станет \([c^*Tc]_+\), то есть исходной неизвестной формой. Нынешний результат не запрещает доказуемого source-dependent способа выполнить такую компенсацию.

Другие обязательные ограничения:

* Семья \(c_m\) — подлинные нормированные векторы исходного \(P\), но не настоящая нулеселективная пара. Её контроль не доказывает достаточный pair margin и не all-\(P\) small upper.
* Знаковые adaptive weights — scalar construction для фиксированного \(c\). Нет фиктивного общего адаптивного линейного оператора.
* Весь \(B_n\) зануляется на верхней половине, но производственный \(A\) там не зануляется: различаются внешний divisor \(n\) и исходный product \(nk\).
* Проекция не сохраняет компактную поддержку; её полный эффект оплачен в (5.7), (6.7).
* Контроль \(T[f_m]\) использует внешний классический PNT-error только на одном фиксированном профильном семействе. Для произвольного исходного \(c\) тот же вывод не заявляется.
* Co-final lower цены не есть lower истинного спектра; сохранённые большие отрицательные компоненты прямо показывают различие.
* Ни source derivative полного \(B\), ни qualitative shifted correlation, ни RH-strength Mertens/variance не использованы как готовые входы.
* S3/S4 и прежний S2 не повторно «провалены»: их статусы наследуются. Новая проверка относится к более сильному signed channel-completion.

## 10. Статусы, dependency epistemics и closeout

| Утверждение | Scope / verifier | Статус |
|---|---|---|
| Буквальные \(B,D,T,A,C^0\), исходный P и предыдущие receiver | ABSTRACT / PAPER | Унаследовано из S1/S2/S9/S10; upstream chain целиком не пересертифицирована |
| Точный signed incidence-flow optimum (3.2) | ABSTRACT / PAPER | Доказан конструктивно вместе с dual; не арифметическое решение цели |
| Верхняя половина full-k support и prime-isolation | ABSTRACT / PAPER | Доказаны на настоящем источнике |
| (5.12) и цена оптимума (7.3) | COFINAL_FAMILY / PAPER | Доказаны с указанной геометрией и безусловной PNT |
| Полная компенсирующая форма (6.8)–(6.10) | COFINAL_FAMILY / PAPER | Только выбранная original-P семья; внешний вход E1 явно выделен |
| Новая all-P \(\eta(\epsilon)\to0\) | COFINAL_FAMILY / CONDITIONAL | Не доказана, не принималась как предпосылка |
| Новый actual-zero-pair margin | COFINAL_FAMILY / CONDITIONAL | Не получен |
| Финитные исполняемые проверки | FINITE_CELL / PAPER | Точная арифметика/алгебра; не production spectral certification |

```yaml
DOWNSTREAM_CONSUMER: Original fixed-epsilon sparse-band CCM receiver
ACTUAL_CONSUMER_REQUIREMENT: 'T_>R <= C_epsilon m^eta(epsilon) P with eta(epsilon)->0 and full returns'
ORIGINAL_REQUESTED_OBJECT: Joint signed comparison of the complete actual blocks before separate payment
ORIGINAL_OBJECT_IS: UNKNOWN
KNOWN_WEAKER_INTERFACES:
  - 'Direct A upper returns through the inherited short/arch map'
  - 'Separately justified actual zero-selective pair margin; not supplied in Q40'
TESTED_AUXILIARY_OBJECT: 'Arbitrary signed divisor-incidence redistribution followed by positive-part payment of complete prime channels'
AUXILIARY_OBJECT_IS: NOT_NECESSARY
FAILURE_TYPE: COUNTEREXAMPLE
FAILURE_SCOPE: THEOREM_SHAPE
FAILURE_EVIDENCE: 'Equations (5.12), (7.3), negative upper margin (7.4), on every sufficiently late original cell'
EPISTEMIC_STATUS_PRIMARY: RESEARCH_DEBT
EPISTEMIC_STATUS_AUXILIARY: 'Sub-half-power certificate disproved in the exact class (2.5)-(2.8)'
MATHEMATICALLY_DEAD_ROUTE: false
NOVELTY_AXIS: 'Exact signed-channel optimization, hyperbolic isolation, and quantitative same-P cancellation discriminator; no world-novelty claim'
REOPEN_TRIGGER: 'A proved comparison retaining cancellation between distinct components or a different source-preserving joint estimate'
```

Регистрация была записана после полного чтения и предварительного PAPER-проектирования, до новых исполняемых тестов. Это не слепая preregistration всего рассуждения. Судьба прогнозов:

| Прогноз | Результат |
|---|---|
| P1: оптимум равен положительным полным компонентным суммам | Подтверждён §3, primal/dual exact controls |
| P2: full-k cutoff оставляет изолированные большие внешние простые | Подтверждён §4, finite coefficient controls |
| P3: opposite-packet исходного P делает эти каналы положительными с ценой \(\sqrt m/L\) | Подтверждён §5; cofinal аргумент PAPER, не численная экстраполяция |
| P4: полная цена сертификата остаётся половинной | Подтверждён §7 |
| P5: на той же семье полный signed источник меньше цены | Подтверждён §6 при безусловном E1; не all-P theorem |

Выполнены **13 групп, 2507 перечисленных конечных случаев и 11 обнаруженных намеренных ошибок**. Источниковый verifier отдельно сверил весь TXT и все десять body. Проверки используют только стандартную библиотеку Python; устанавливать пакеты не требуется. Generic Hermitian matrices в коде контролируют полную \(\mu*\log\) алгебру с комплексными mixed entries, а не численный исходный спектр. Контроли contact prefactor не заменяют аналитическое доказательство гладкой семьи. Внешний PNT-proof не исполнялся.

После сборки полного Markdown все шесть приложений извлечены, их byte-count/SHA256 проверены и оба checker запущены повторно. Результирующие JSON побайтно равны вложенным. Исторические checker из S2 не запускались.

**Что изменилось:** исключено указанное strengthened completion даже со свободными знаковыми весами и полной внутриканальной компенсацией; найдена конкретная межкомпонентная компенсация, которую оно теряет. **Что не изменилось:** полный исходный показатель и статус RH. **Что не надо повторять:** искать новые incidence-веса, если конец всё равно \(\sum_p[a_p]_+\). **Что остаётся открытым:** независимый quantitative upper полной знаковой формы до этой потери.

**CODEX DIRECTIVE — один bounded PAPER audit, не новый goal:** проверить §3 primal/dual optimum, §4 точный cutoff \(D_n=0\) для \(n\ge m/2\), §5 знак opposite-packet после полной трёхконтактной проекции и §6 возврат настоящей полной \(\Lambda\)-суммы с обоими краями. Затем воспроизвести два новых checker. Особо проверить, что маленький полный signed контроль относится только к \(c_m\), а нижняя цена — только к (2.8). Результат аудита не повышает main-consumer статус и не разрешает автоматически Q41 или запись в репозиторий.

```yaml
iteration: Q40
status_primary: NO_PROGRESS
local_status: SCOPED_FALSIFICATION_PROGRESS
failed_strategy: Signed prime-incidence balancing followed by independent positive parts of complete channels
cognitive_operator_used: DUALIZE
current_smallest_gap: Original joint signed block bound before discarding negative component totals
invariant_learned: Original full-k cutoff creates isolated true-prime channels, but other actual components cancel their positive contribution
forbidden_future_move: Transfer the optimal channel-certificate lower price to the complete CCM spectrum
next_decisive_test: Bounded PAPER audit of the stated signed-flow class and the complete same-P discriminator
primary_route_score: 2
automatic_successor: false
```

## 11. Внешние источники и граница импорта

**E1.** Daniel R. Johnston, Andrew Yang, *Some explicit estimates for the error term in the prime number theorem*, arXiv:2204.01980v2. Использованы только Theorem 1.1, equation (1.3), и Corollary 1.3, equation (1.6), с областью \(x\ge2\). Проверены первичные HTML-формулировки, определения \(\psi\) со всеми prime powers и отсутствие условной RH-предпосылки у этих утверждений. Полный внешний proof, его таблицы и вычислительные сертификаты не пересертифицированы. PDF не использовался; бинарный PDF-хеш не заявляется.

**E2.** NIST DLMF §27.12, equations 27.12.4–27.12.5: безусловная PNT и классическая ошибка. Дополнительная проверка масштаба, не источник нового CCM-supplier. В доказательстве можно использовать только E1, который уже даёт нужные две области.

```text
E1 primary HTML: https://arxiv.org/html/2204.01980v2
E1 statement locations: Theorem 1.1 (1.3); Corollary 1.3 (1.6)
E2: https://dlmf.nist.gov/27.12
```

Внутренние S1–S10 — только замороженные тела канонического Q40, а не текущие HEAD-версии других файлов. Полный манифест — в приложении `q40_source_verification.json`.

**Итог:** один новый усиленный совместный ход выполнен и ограничен на настоящем источнике. Полный знаковый выигрыш не найден; прежний безусловный fallback сохранён. Никакого нового независимого аудита, Lean, Arb, production-спектральных вычислений или записи в репозиторий в этой сессии не было.

---

# Приложения: полный исполняемый оригинал

Тело каждого приложения — UTF-8 с указанным BYTES/SHA256, включая последний LF. Код не запускает исторические инструкции и не обращается к сети. После извлечения достаточно:

```bash
python3 check_q40.py
python3 verify_sources_q40.py ./PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_2026-10-26.txt
```

Либо одним replay:

```bash
python3 replay_q40.py ./PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_VERDICT_2026-10-26.md ./PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_2026-10-26.txt ./q40_replay
```

Здесь первые два аргумента — реальные пути к этому Markdown и исходному TXT. Последний аргумент — папка только для извлечённых новых проверок и их выходов; существующие исходные документы не изменяются.

## Asset: `registration_q40.json`

BEGIN_ASSET registration_q40.json
BYTES: 1795
SHA256: bacb1c6067333d06a39e665111574e25730d1f4561d3c38475307bbdc099fa31
```json
{
  "stage": "After complete reading of Q40 and all ten source bodies and preliminary PAPER design; before new mathematical executable tests. Not blind registration of the reasoning.",
  "selected_mechanism": "Arbitrary signed, test-adaptive redistribution on the actual prime-divisibility incidence graph; sum each complete prime channel before positive-part payment, with exact primal/dual optimization.",
  "P1": "The best channel-positive-part cost is the sum of positive signed component totals, rather than the termwise modulus price in S4.",
  "P2": "The actual full-k block is identically zero for n>=m/2; hence active outer primes in (m/4,m/2) are isolated incidence vertices and no signed internal redistribution changes their channel.",
  "P3": "A minus two-end packet returned to the original P makes a fixed-relative window of those isolated actual-prime channels positive; ordinary PNT supplies a cofinal sqrt(m)/log(m) lower price for this certificate, not a lower bound for the full CCM form.",
  "P4": "The unrestricted all-P scalar certificate has a legal sqrt(m) times fixed-logarithm upper bound; no vanishing exponent is expected from this completion. Short and arch return must be charged once.",
  "P5": "The exact signed terminal-band sum on the same two-end packet is o(sqrt(m)/log(m)) using the classical unconditional PNT error; this distinguishes the positive component price from the actual first moment. This is a diagnostic on one family, not an all-P supplier.",
  "scope_limits": "Only this incidence-preserving channel-positive-part completion is tested. Arbitrary joint grouping across distinct components, other operator inequalities, and the actual target are not refuted. No repository writes, no independent agents, no Lean/Arb, no production spectrum."
}
```
END_ASSET

## Asset: `check_q40.py`

BEGIN_ASSET check_q40.py
BYTES: 9198
SHA256: 0758a39197da7196f8d6fa2777eae514cbb7c928730b641e7c033f3e1a4c3dbe
```python
#!/usr/bin/env python3
"""Exact controls of Q40's signed incidence-flow calculation.
Not a production CCM computation, interval certificate, or asymptotic proof.
Standard library only. Writes check_q40_results.json next to this script.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

checks: dict[str, int] = {}
planted: list[str] = []

def check(name: str, predicates: list[bool]) -> None:
    if not all(predicates):
        raise AssertionError(name)
    checks[name] = len(predicates)

def reject(name: str, false_claim: bool) -> None:
    if false_claim:
        raise AssertionError('Undetected planted error: ' + name)
    planted.append(name)

def factor(n: int) -> dict[int,int]:
    if n < 1: raise ValueError('Positive integer required')
    ans: dict[int,int] = {}; d=2
    while d*d <= n:
        while n%d == 0:
            ans[d]=ans.get(d,0)+1; n//=d
        d+=1
    if n>1: ans[n]=ans.get(n,0)+1
    return ans

def mobius(n: int) -> int:
    fs=factor(n)
    return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)

def primes(n: int) -> list[int]:
    return [p for p in range(2,n+1) if factor(p)=={p:1}]

def positive(x: F) -> F:
    return max(x,F(0))

# Hermitian matrix encoded by diagonal entries a,d and off-diagonal b+i*c.
Z=(F(0),)*4

def add(a, b): return tuple(x+y for x,y in zip(a,b))
def scale(a, r): return tuple(r*x for x in a)
def h(n: int, m: int):
    if n==m: return Z
    return (F(n%7-3,n+1),F(n%5-2,n+2),F(n%11-5,n+3),F(n%13-6,n+4))

def blocks(m: int):
    """Formal logarithms: B_d is a dict prime -> Hermitian coefficient."""
    ans={}
    for d in range(1,m+1):
        terms={}
        for k in range(1,m//d+1):
            for p,e in factor(k).items():
                terms[p]=add(terms.get(p,Z),scale(h(d*k,m),F(e)))
        ans[d]={p:v for p,v in terms.items() if v!=Z}
    return ans

# Construct the exact primal minimizer and the matching dual certificate.
def signed_flow(values: dict[int,F]):
    values={n:F(v) for n,v in values.items() if v}
    if any(n<2 or mobius(n)==0 for n in values):
        raise ValueError('Only active squarefree n>1')
    support={n:sorted(factor(n)) for n in values}
    vertices=sorted({p for ps in support.values() for p in ps})
    edges={p:[] for p in vertices}
    allocation={n:{p:values[n]/len(ps) for p in ps} for n,ps in support.items()}
    for n,ps in support.items():
        for p in ps[1:]:
            edges[ps[0]].append((p,n)); edges[p].append((ps[0],n))
    totals={p:sum((allocation[n].get(p,F(0)) for n in values),F(0)) for p in vertices}
    components=[]; seen=set()
    for root in vertices:
        if root in seen: continue
        seen.add(root); queue=deque([root]); order=[]; parent={}
        while queue:
            p=queue.popleft();order.append(p)
            for v,n in sorted(edges[p]):
                if v not in seen:
                    seen.add(v);parent[v]=(p,n);queue.append(v)
        members=set(order)
        source_total=sum((z for n,z in values.items() if support[n][0] in members),F(0))
        for v in reversed(order[1:]):
            p,n=parent[v];amount=totals[v]
            allocation[n][v]-=amount;allocation[n][p]+=amount
            totals[p]+=amount;totals[v]=F(0)
        components.append((order,source_total))
    expected=sum((positive(s) for _,s in components),F(0))
    cost=sum((positive(x) for x in totals.values()),F(0))
    dual={p:F(s>0) for ps,s in components for p in ps}
    dual_value=sum((dual[p]*x for p,x in totals.items()),F(0))
    return support,allocation,totals,components,dual,cost,expected,dual_value

matrix_cases=[]; support_cases=[]; k2_cases=[]; incidence_cases=[]
for m in (8,9,10,12,16,24,30,31,32,48,64,96):
    B=blocks(m); ps=primes(m)
    for ell in ps:
        lhs=Z;rhs=Z
        for d in B: lhs=add(lhs,scale(B[d].get(ell,Z),F(mobius(d))))
        v=ell
        while v<=m:
            rhs=add(rhs,h(v,m)); v*=ell
        matrix_cases.append(lhs==rhs)
    support_cases += [B[d]=={} for d in range(1,m+1) if 2*d>=m]
    for p in ps:
        if 3*p>m and 2*p<m:
            k2_cases.append(B[p]==({2:h(2*p,m)} if h(2*p,m)!=Z else {}))
    R=max(1,isqrt(m)//2)
    for ell in ps:
        T=Z; channels=Z
        for n in range(R+1,m+1): T=add(T,scale(B[n].get(ell,Z),F(mobius(n))))
        for p in ps:
            for k in range(1,m//p+1):
                n=p*k
                if n<=R or k%p==0 or not mobius(k): continue
                theta=F(1,len(factor(n)))
                channels=add(channels,scale(B[n].get(ell,Z),-mobius(k)*theta))
        incidence_cases.append(T==channels)
check('actual_mu_log_full_complex_matrix',matrix_cases)
check('exact_full_k_upper_half_support',support_cases)
check('isolated_prime_k2_formula',k2_cases)
check('full_k_prime_channel_return',incidence_cases)

flow_cases=[]; dual_cases=[]; signs_used=0; example_result=None
for m in (20,40,80,160,320):
    for R in (1,2,5,11):
        for shift in range(4):
            values={n:F(mobius(n)*((n+shift)%9-4),n+1)
                    for n in range(R+1,m) if 2*n<m and mobius(n)}
            support,alloc,totals,comps,y,cost,expected,dv=signed_flow(values)
            vals={n:v for n,v in values.items() if v}
            ok=cost==expected==dv and sum(totals.values(),F())==sum(vals.values(),F())
            ok &= all(sum(alloc[n].values(),F())==v for n,v in vals.items())
            ok &= all(sum((alloc[n].get(p,F()) for n in vals),F())==v for p,v in totals.items())
            ok &= all(len({y[p] for p in ps})==1 for ps in support.values())
            flow_cases.append(ok)
            # An independent deterministic signed allocation, not the optimizer.
            trial={p:F() for p in totals}
            for n,ps in support.items():
                split=[F((p+n+shift)%7-3,2) for p in ps[:-1]]
                split.append(F(1)-sum(split,F()))
                for p,t in zip(ps,split): trial[p]+=t*vals[n]
            dual_cases.append(sum((positive(v) for v in trial.values()),F())>=expected)
            signs_used+=any(x/vals[n]<0 for n,mp in alloc.items() for x in mp.values())
check('constructive_signed_primal_component_optimum',flow_cases)
check('dual_lower_bound_for_other_signed_allocations',dual_cases)
check('signed_allocations_are_genuinely_used',[signs_used>0])

# The signed class is not the S4 nonnegative termwise certificate.
ex={2:F(2),3:F(-3),6:F(1)}
_,alloc,totals,comps,y,cost,expected,dv=signed_flow(ex)
check('signed_rebalancing_strictly_better_in_control',[
    cost==0, alloc[6][2]==-2, alloc[6][3]==3,
    sum(map(abs,ex.values()),F())==6])

isolated=[]
for m in range(16,257):
    active=[n for n in range(2,m) if 2*n<m and mobius(n)]
    for p in primes(m//2):
        if 4*p>m and 2*p<m:
            isolated.append([n for n in active if n%p==0]==[p])
check('actual_integer_incidence_isolation',isolated)

# Double Mellin-zero algebra and projection exponents: exact controls only.
z=F(1,2)
check('two_contact_double_zero_prefactor',[(z*z-F(1,4))**2==0,
      4*z*(z*z-F(1,4))==0, ((-z)**2-F(1,4))**2==0])
exponents=[]
for eps in (F(1,64),F(1,100),F(1,1000)):
    q=int(2/eps)+3
    exponents += [F(1,2)+eps*(F(1,2)-q)<0,
                  eps-F(1,2)<0,
                  F(3,2)*eps<F(1,2)]
check('fixed_order_projection_and_short_exponents',exponents)
check('signed_packet_cross_orientation',[
    F(2)*F(1,2)*(-1)==-1,
    F(1,2)+F(1,2)==1,
    F(7,8)-4*F(1,16)>=F(1,2)])
# source-test derivative x^(-1/2) r(log(x/m)) by exponent bookkeeping.
check('pnt_weight_and_normalization_exponents',[
    F(1)-F(3,2)+F(1)==F(1,2),
    F(303,200)+1==F(503,200),
    F(939,100)==F('9.39'), F(4137,5000)==F('0.8274')])

# Planted errors are each checked against an explicit counter-witness.
reject('drop_mu_channel_minus',mobius(3)==mobius(1))
reject('omit_coprimality_mask',mobius(4)==-mobius(2))
reject('replace_full_k_log_by_log_product',factor(1)==factor(2))
reject('lose_n_equal_m_over_2_seam',bool(blocks(20)[10]))
reject('allow_zero_block_to_bridge_isolated_prime',bool(blocks(100)[94]))
reject('signed_channels_same_as_termwise_moduli',cost==sum(map(abs,ex.values()),F()))
reject('permit_transfer_between_distinct_components',signed_flow({2:F(2),3:F(-2)})[5]==0)
reject('drop_cross_time_orientation',F(1,2)*(-1)==-1)
reject('wrong_packet_relative_sign',F(2)*F(1,2)*(1)==-1)
reject('drop_linear_projection_error',(1+F(1,10))**2-1==F(1,10)**2)
reject('prime_power_deletion',sum(mobius(d)*factor(4//d).get(2,0)
       for d in (1,2,4))==0)

out={
 'scope':'Finite exact arithmetic, incidence-flow, generic Hermitian algebra and exponent controls; not a numerical original-P cell or cofinal sign certification.',
 'groups':checks,'groups_passed':len(checks),'finite_cases':sum(checks.values()),
 'planted_failures_detected':planted,'planted_count':len(planted),
 'historical_scripts_executed':False,'external_pnt_proof_recertified':False,
 'lean':False,'arb':False,'production_spectrum':False}
text=json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True)+'\n'
Path(__file__).with_name('check_q40_results.json').write_text(text,encoding='utf8')
print(text,end='')
```
END_ASSET

## Asset: `check_q40_results.json`

BEGIN_ASSET check_q40_results.json
BYTES: 1476
SHA256: 30f4bdf95fba5a6fcb29659b2968b60e8cc6cc3a999bac622fcda8bfc1ada54f
```json
{
  "arb": false,
  "external_pnt_proof_recertified": false,
  "finite_cases": 2507,
  "groups": {
    "actual_integer_incidence_isolation": 1860,
    "actual_mu_log_full_complex_matrix": 121,
    "constructive_signed_primal_component_optimum": 80,
    "dual_lower_bound_for_other_signed_allocations": 80,
    "exact_full_k_upper_half_support": 201,
    "fixed_order_projection_and_short_exponents": 9,
    "full_k_prime_channel_return": 121,
    "isolated_prime_k2_formula": 20,
    "pnt_weight_and_normalization_exponents": 4,
    "signed_allocations_are_genuinely_used": 1,
    "signed_packet_cross_orientation": 3,
    "signed_rebalancing_strictly_better_in_control": 4,
    "two_contact_double_zero_prefactor": 3
  },
  "groups_passed": 13,
  "historical_scripts_executed": false,
  "lean": false,
  "planted_count": 11,
  "planted_failures_detected": [
    "drop_mu_channel_minus",
    "omit_coprimality_mask",
    "replace_full_k_log_by_log_product",
    "lose_n_equal_m_over_2_seam",
    "allow_zero_block_to_bridge_isolated_prime",
    "signed_channels_same_as_termwise_moduli",
    "permit_transfer_between_distinct_components",
    "drop_cross_time_orientation",
    "wrong_packet_relative_sign",
    "drop_linear_projection_error",
    "prime_power_deletion"
  ],
  "production_spectrum": false,
  "scope": "Finite exact arithmetic, incidence-flow, generic Hermitian algebra and exponent controls; not a numerical original-P cell or cofinal sign certification."
}
```
END_ASSET

## Asset: `verify_sources_q40.py`

BEGIN_ASSET verify_sources_q40.py
BYTES: 2297
SHA256: 115e06957159e4ea2ad8d92afd389f4c2eb2e0ba0082e43b23055c4ec0cdc6cf
```python
#!/usr/bin/env python3
"""Byte-exact Q40 intake verification; no historical script execution.
Usage: python verify_sources_q40.py /path/to/canonical_Q40.txt
"""
from __future__ import annotations
import hashlib, json, re, sys
from pathlib import Path

NAME='PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_2026-10-26.txt'
EXPECTED_BYTES=129772
EXPECTED_LF=2209
EXPECTED_SHA='771ae3b7ce9b657227cc939bfb2d922658b5985a258ea5ef6241d14865c8987c'
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/mnt/data')/NAME
raw=p.read_bytes(); sha=hashlib.sha256(raw).hexdigest()
if (len(raw),raw.count(b'\n'),sha)!=(EXPECTED_BYTES,EXPECTED_LF,EXPECTED_SHA):
    raise ValueError('Canonical Q40 mismatch')
raw.decode('utf8',errors='strict')
pat=re.compile(rb'^BEGIN_SOURCE (S\d+) ([^\n]+?) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n',re.M)
rows=[];pos=0
for i in range(1,11):
    match=pat.search(raw,pos)
    if not match or match.group(1)!=f'S{i}'.encode():
        raise ValueError('Source sequence mismatch')
    sid,name,n,lf,digest=match.groups();start=match.end();stop=start+int(n)
    body=raw[start:stop];body.decode('utf8',errors='strict')
    if (len(body),body.count(b'\n'),hashlib.sha256(body).hexdigest().encode())!=(int(n),int(lf),digest):
        raise ValueError('Body mismatch: '+sid.decode())
    end=f'\nEND_SOURCE S{i}\n'.encode()
    if raw[stop:stop+len(end)]!=end:
        raise ValueError('Size-locked boundary mismatch')
    rows.append({'id':sid.decode(),'name':name.decode(),'bytes':int(n),'lf':int(lf),
                 'sha256':digest.decode(),'first_body_line':raw[:start].count(b'\n')+1,
                 'last_body_line':raw[:stop].count(b'\n')})
    pos=stop+len(end)
if raw[pos:].strip(): raise ValueError('Unexpected trailing content')
out={'canonical_file':NAME,'canonical_bytes':len(raw),'canonical_lf':raw.count(b'\n'),
     'canonical_sha256':sha,'whole_file_hash_origin':'Measured here; Q40 caption did not specify a whole-file hash.',
     'all_declared_bytes_lf_sha256_match':True,'strict_source_boundaries_match':True,
     'body_count':len(rows),'sources':rows,'historical_scripts_executed':False}
text=json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True)+'\n'
Path(__file__).with_name('q40_source_verification.json').write_text(text,encoding='utf8')
print(text,end='')
```
END_ASSET

## Asset: `q40_source_verification.json`

BEGIN_ASSET q40_source_verification.json
BYTES: 3110
SHA256: a73a62e694489c8684f52485e56c5683a2abe0b9cc2474f9d7b9f634b839177b
```json
{
  "all_declared_bytes_lf_sha256_match": true,
  "body_count": 10,
  "canonical_bytes": 129772,
  "canonical_file": "PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_2026-10-26.txt",
  "canonical_lf": 2209,
  "canonical_sha256": "771ae3b7ce9b657227cc939bfb2d922658b5985a258ea5ef6241d14865c8987c",
  "historical_scripts_executed": false,
  "sources": [
    {
      "bytes": 4706,
      "first_body_line": 28,
      "id": "S1",
      "last_body_line": 116,
      "lf": 89,
      "name": "CCM_Q39_CONCLUSION.md",
      "sha256": "bd1f0d1c19b4a461a6e87a11b0a882be0f8641d6c4284c59e697a4c9dcd53f72"
    },
    {
      "bytes": 79517,
      "first_body_line": 121,
      "id": "S2",
      "last_body_line": 1462,
      "lf": 1342,
      "name": "PROSHKA_CCM_JOINT_CENTRAL_SOURCE_ROLLBACK_Q39_VERDICT_2026-10-26.md",
      "sha256": "fa3cff84fb70f7961253fbf6ed26ae5e997d2422cd34793a3beaddc5bcb3c85d"
    },
    {
      "bytes": 5016,
      "first_body_line": 1467,
      "id": "S3",
      "last_body_line": 1574,
      "lf": 108,
      "name": "CCM_POST_Q39_MANY_PRIME_VARIANCE.md",
      "sha256": "c03f7e4c7e8bb94de88149688f08d31503cb562a1697a549d2d2ac16c65dbae0"
    },
    {
      "bytes": 4280,
      "first_body_line": 1579,
      "id": "S4",
      "last_body_line": 1662,
      "lf": 84,
      "name": "CCM_POST_Q39_EXACT_PRIME_PARTITION.md",
      "sha256": "ee07620f2d46cf66c196d319b1848ef9a2b33d9a874e180a4c2674eb70aea8b8"
    },
    {
      "bytes": 4463,
      "first_body_line": 1667,
      "id": "S5",
      "last_body_line": 1765,
      "lf": 99,
      "name": "CCM_Q02_DIRECT_ABEL_TEST.md",
      "sha256": "59a3a857e6f4af54a1bec1cd9f7175bdbb7cc155babb4f389b7223454670b352"
    },
    {
      "bytes": 5958,
      "first_body_line": 1770,
      "id": "S6",
      "last_body_line": 1879,
      "lf": 110,
      "name": "CCM_Q05_LOG_CORRELATION_PREFLIGHT.md",
      "sha256": "d0fa55c54b7c6f268d6e2f7f875b982b3b34dc09559cb3e2fc2189607055bfdf"
    },
    {
      "bytes": 3625,
      "first_body_line": 1884,
      "id": "S7",
      "last_body_line": 1947,
      "lf": 64,
      "name": "CCM_Q32_CONCLUSION.md",
      "sha256": "183d938014b47b8ac21e83ee13e5e605908f27f1198011a26513b365ed127245"
    },
    {
      "bytes": 5747,
      "first_body_line": 1952,
      "id": "S8",
      "last_body_line": 2050,
      "lf": 99,
      "name": "CCM_Q34_CONCLUSION.md",
      "sha256": "acbf977ad791fac2910bea0876969a817ddbd8d57211cf7a4312372c4b6b0e2e"
    },
    {
      "bytes": 6174,
      "first_body_line": 2055,
      "id": "S9",
      "last_body_line": 2123,
      "lf": 69,
      "name": "CCM_SPARSE_BAND_RECEIVER.md",
      "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06"
    },
    {
      "bytes": 3555,
      "first_body_line": 2128,
      "id": "S10",
      "last_body_line": 2207,
      "lf": 80,
      "name": "CCM_POST_Q30_SURVIVING_PRODUCTS.md",
      "sha256": "204a0aa14f8480f691f8430440d8d2e8a860617c6b946b80d7639361814efd0d"
    }
  ],
  "strict_source_boundaries_match": true,
  "whole_file_hash_origin": "Measured here; Q40 caption did not specify a whole-file hash."
}
```
END_ASSET

## Asset: `replay_q40.py`

BEGIN_ASSET replay_q40.py
BYTES: 2051
SHA256: 86cd2c7d9fef8e312869ca474cda35b404f4a62429d4a26c3a351948f2060759
```python
#!/usr/bin/env python3
"""Replay Q40's new exact controls only; no network or installation.
Usage: python replay_q40.py verdict.md canonical_Q40.txt output_directory
"""
from __future__ import annotations
import hashlib, json, re, subprocess, sys
from pathlib import Path
if len(sys.argv)!=4: raise SystemExit(__doc__)
verdict,canonical,outdir=(Path(x).resolve() for x in sys.argv[1:])
raw=verdict.read_bytes()
pat=re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```(?:python|json)\n',re.M)
assets={};pos=0
while True:
    mat=pat.search(raw,pos)
    if not mat: break
    name,count,digest=mat.groups();name=name.decode();end=mat.end()+int(count)
    body=raw[mat.end():end]
    if name in assets or len(body)!=int(count) or hashlib.sha256(body).hexdigest().encode()!=digest:
        raise ValueError('Asset mismatch: '+name)
    if not raw[end:].startswith(b'```\nEND_ASSET'):
        raise ValueError('Asset fence mismatch: '+name)
    assets[name]=body;pos=end+len(b'```\nEND_ASSET')
expected={'registration_q40.json','check_q40.py','check_q40_results.json',
          'verify_sources_q40.py','q40_source_verification.json','replay_q40.py'}
if set(assets)!=expected: raise ValueError('Unexpected asset list')
outdir.mkdir(parents=True,exist_ok=True)
for name,body in assets.items(): (outdir/name).write_bytes(body)
for script,args in [('check_q40.py',[]),('verify_sources_q40.py',[str(canonical)])]:
    run=subprocess.run([sys.executable,str(outdir/script),*args],cwd=outdir,
                       check=True,capture_output=True,text=True)
    (outdir/(script+'.stdout')).write_text(run.stdout,encoding='utf8')
for name in ('check_q40_results.json','q40_source_verification.json'):
    if (outdir/name).read_bytes()!=assets[name]:
        raise ValueError('Output is not byte-identical: '+name)
print(json.dumps({'assets':len(assets),'asset_hashes_match':True,'checkers_run':2,
                  'both_json_byte_identical':True,'historical_scripts_executed':False},
                 indent=2,sort_keys=True))
```
END_ASSET
