# STATUS: KILL_CCM_Q56_INDEPENDENT_AMPLIFIER_PAYMENTS
```yaml
OPERATIVE_CLASS: KILL_CCM_Q56_INDEPENDENT_AMPLIFIER_PAYMENTS
REQUEST_ID: Q56_ACTUAL_JOINT_ARITHMETIC
DATE: 2026-10-27
PACKET_SHA256: b3a5f4823019bd3e9464973b3457e7d3e9497241be81e49b0cccbc08099b270a
PACKET_BYTES: 160453
PACKET_LF: 2597
SOURCE_BODIES: 14
MANIFEST: VERIFIED
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: ORIGINAL_FULL_CCM_WITH_ORIGINAL_THREE_CONTACT_P
PRODUCTION_SCHEDULE: N=m; L=log(m); M=R=floor(m^epsilon); fixed_0<epsilon<1/32
TESTED_METHOD: ACTUAL_MOBIUS_PRIME_DILATION_AMPLIFICATION_OF_FULL_INNER_SUM
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
LOCAL_PROGRESS_CLASS: FALSIFICATION_PROGRESS
CONSUMER_PROGRESS: NO_PROGRESS
CONSUMER_FAILURE_TYPE: NO_DERIVATION
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: ORIGINAL_P_COFINAL_WITNESS_FOR_EXACT_CERTIFICATE_PRICES
KILL_EVIDENCE_REFERENCE: THIS_FILE_SECTIONS_4_5_EQUATIONS_4.6_5.5_5.7
KILL_BOUNDARY: INDEPENDENT_NONNEGATIVE_PAYMENTS_IN_THE_DEFINED_AMPLIFIER_CERTIFICATE_ONLY
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
EPISTEMIC_SCOPE: THE_TWO_EXACT_CERTIFICATE_CLASSES_ONLY
ACTUAL_SOURCE_EPISTEMIC_STATUS: RESEARCH_DEBT
RETAINED_FULL_POWER: 1/2
EXPLICIT_WEAK_TRIAL_FULL_POWER: 1/2+epsilon
ETA_EPSILON_TO_ZERO: NOT_DERIVED
RH: OPEN
PX_RH_CLAIM: NOT_MADE
CF22_PYSR: PARKED
CONDITIONAL_ZF78: NOT_USED_NOT_UPGRADED
VERIFIER: PAPER_OWN_DERIVATION_WITH_INHERITED_Q55_SCALAR_INPUT_IN_SECTION_5_ONLY
INDEPENDENT_NEW_AUDIT: NOT_RUN
LEAN: NOT_RUN
ARB: NOT_RUN
PRODUCTION_SPECTRUM: NOT_RUN
REPOSITORY_WRITES: NONE
HISTORICAL_PROGRAMS_EXECUTED: false
NEXT_QUESTION_DISPATCH: NONE
```

Ы. **Новый верх полной исходной формы с показателем \(\eta(\epsilon)\to0\) не выведен: `NO_DERIVATION`.** Проверен один другой арифметический ход — усиление полной Мёбиусовой суммы простыми дилатациями, то есть заменой индекса \(r\) на \(pr\). В нём используется настоящее соотношение между \(\mu(pr)\) и \(\mu(r)\), включая обязательную поправку при \(p\mid r\).

Результат не сводится к новой записи исходного неравенства. Построен **точный допустимый пяти-модовый свидетель**, который доказывает:

\[
\boxed{\text{цена двух явно определённых классов завершений}
       \ \ge c\,\frac{\sqrt m}{(\log m)^{10}}.} \tag{0.1}
\]

Первый класс оставляет всю внутреннюю арифметическую сумму и все смешанные простые каналы вместе, но затем платит за их спаривание с \(\mu(r)\) посредством Cauchy. Второй допускает произвольные неотрицательные веса вспомогательных простых до \(m/4\), но независимо оплачивает остаток абсолютными величинами. Точные области — §§4–5. В частности, нельзя спасти эти завершения только настройкой указанного набора простых или его весов.

**Это нижняя оценка цены конкретного достаточного сертификата, не нижняя оценка \(A_m\), \(T_{>R}\) или CCM.** Полная знаковая компенсация остаётся открытой. Сохранённый результат Q55 по-прежнему имеет полный показатель \(1/2\). Утверждение о непригодности сертификата ниже доказывается свидетелем, а не выводится из одного отсутствия успеха.

## 1. Что именно испытывается

### 1.1. Source lock и анти-повторный экран

**[FINITE_CELL | PAPER — transport].** Прочитан весь канонический TXT, сначала текущая инструкция, затем S1–S14, включая исторический код как текст. Совпали внешний SHA-256, 160453 bytes, 2597 LF и все 14 размерно зафиксированных тел. Полный manifest встроен в новое приложение `q56_checks.json`. Старые программы не запускались.

Bootstrap получен через GitHub connector из `Malaeu/chen_q3`, `rh_clean`, `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, строки 1–225 и 226–450, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Другой запрос или очередь вместо Q56 не выбирались.

Поправки S1–S2 приняты: Hilbert/divided-difference map не новый; Q55 дал именно uniform VK/Perron completion. Его независимый replay — semantic match, **не** побайтное совпадение всех binary64 строк. Здесь не выполняется повторный аудит Q55.

Не повторяются affine/BMO, Pick/Loewner, положительная Fourier-плотность, Vaughan, Selberg \(\Lambda_2\), carrier graph и Jordan/Taylor. Старые контактные профили и положительные raw-shell препятствия сами по себе также не объявляются открытием. Отличающийся проверяемый объект настоящего опыта — **цена конечного prime-divisor amplification для полной recombined \(\mu*\log\)-формы**, с обоими её арифметическими остатками. Глобальная новизна и отсутствие аналогичного результата за пределами приложенного корпуса не заявляются.

### 1.2. Объект и показатель до завершения оценки

**[COFINAL_FAMILY | PAPER — inherited definitions].** Фиксируются
\[
0<\epsilon<1/32,\quad N=m,\quad L=\log m,\quad
M=R=\lfloor m^\epsilon\rfloor,\quad\Omega=2\pi M/L.
\]
\(P\) остаётся исходным трёхконтактным проектором. Для произвольного комплексного \(c=Pc\), \(\|c\|=1\), берётся исходная синтеза
\[
f(t)=L^{-1/2}\sum_{|j|\le M}c_j e^{2\pi ijt/L},\qquad 0\le t\le L,
\]
и её **нулевое**, не периодическое, продолжение. Обозначим
\[
q_f(s)=2\Re\int_{\mathbb R}\overline{f(t)}f(t+s)\,dt,
\qquad
A_m[f]=\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}\,q_f(\log n). \tag{1.1}
\]
Здесь обе временные ориентации и все \(\overline c_jc_k\) сохранены.

Единственный испытуемый новый способ оценки: усилить **полную** конечную сумму
\[
A_m[f]=\sum_{d\le m}\mu(d)b_f(d),\qquad
b_f(d)=\sum_{k\le m/d}\frac{\log k}{\sqrt{dk}}q_f(\log(dk)), \tag{1.2}
\]
с помощью настоящих простых делителей \(d\), а не оценивать отдельно частоты или отдельные \(k\). Равенство (1.2) старое \(\Lambda=\mu*\log\), а не результат Q56. Новый предмет проверки — направленная **оценка** после усиления, (2.6).

Целевой полный показатель был бы
\[
\eta(\epsilon)=\max\{\theta(\epsilon),2\epsilon\}\longrightarrow0
\]
при доказанном \(A_m\preceq C_\epsilon m^{\theta(\epsilon)}P\). На этом опыте вместо него получается лишь слабый исполнимый upper порядка \(m^{1/2+\epsilon}\) с логарифмами, §6. Более существенно, для двух классов попыток сертификат **не может** иметь никакой фиксированный показатель меньше \(1/2\).

### 1.3. Что взято из внешнего источника

Первичный источник [E1], Bourgain–Sarnak–Ziegler, **Theorem 2, печатная с. 2**, проверен по PDF и изображению страницы. Он связывает малые корреляции \(F(p_1r)\overline{F(p_2r)}\) с ортогональностью к ограниченным мультипликативным коэффициентам. Проверено и начало §2, с. 3: малый параметр фиксирован до предела; Note 2 допускает исключения среди пар простых.

**Его асимптотическая теорема не применяется автоматически к меняющемуся \(F=F_m\), и её параметр не заменяется функцией \(m\) без оплаты onset.** Для текущего опыта ниже отдельно доказывается полностью конечное неравенство. Оно использует тот же арифметический принцип, но не выдаётся за буквальную формулировку или оптимальную реализацию Theorem 2. Непригодность нашего завершения не опровергает теорему BSZ и все её возможные адаптации.

## 2. Конечное арифметическое усиление: полная сумма до модулей

### 2.1. Границы и точная prime-square поправка

**[FINITE_CELL | PAPER].** В (1.2) сохраняются все \(dk\le m\). Поскольку \(\log1=0\) и \(q_f(L)=0\),
\[
b_f(d)=0\quad(d>m/2).
\]
При чётном \(m\) член \(d=m/2,k=2\) также равен нулю, но его не требуется удалять. Положим \(D=\lfloor m/2\rfloor\). Это лишь край арифметического индекса; **production \(N=m\) не меняется**.

Пусть \(\mathcal P\) — непустой конечный набор настоящих простых \(p\le D\), \(a_p\ge0\), не все нулевые. Нулевые веса можно удалить. Определим
\[
H=\sum_{p\in\mathcal P}\frac{a_p}{p}>0,
\qquad v(d)=\sum_{\substack{p\in\mathcal P\\p\mid d}}a_p,
\]
\[
r_* =\left\lfloor\frac D{\min\mathcal P}\right\rfloor,
\qquad G_f(r)=\sum_{\substack{p\in\mathcal P\\pr\le D}}a_p b_f(pr).
\tag{2.1}
\]
Во всём \(G_f\) используется **один и тот же** исходный \(f\). Внутренняя сумма по \(k\) не раскрывается в независимые нормы.

Настоящая функция Мёбиуса удовлетворяет для каждого простого \(p\) и каждого \(r\ge1\)
\[
\boxed{\mu(pr)=-\mu(r)+\mathbf1_{p\mid r}\mu(r).} \tag{2.2}
\]
При \(p\nmid r\) это мультипликативность; при \(p\mid r\) левая сторона нулевая из-за \(p^2\mid pr\), а два правых члена сокращаются. Это не правило для произвольных меток вместо \(\mu\).

Введём **знаковые** остатки
\[
\begin{aligned}
\mathcal E_f&=\sum_{p\in\mathcal P}a_p
 \sum_{\substack{r\le D/p\\p\mid r}}\mu(r)b_f(pr),\\
\mathcal R_f&=\sum_{d\le D}\mu(d)(H-v(d))b_f(d).
\end{aligned} \tag{2.3}
\]
Конечная перестановка сумм и (2.2) дают
\[
\boxed{H A_m[f]= -\sum_{r\le r_*}\mu(r)G_f(r)
                    +\mathcal E_f+\mathcal R_f.} \tag{2.4}
\]
Знак перед первой суммой — минус. В частности, \(\mu(p^2)=0\) не даёт права удалить \(\mathcal E_f\): именно она возвращает правильный коэффициент после усиления.

### 2.2. Одна совместная Cauchy-оценка и её точная цена

Положим
\[
Q=\sum_{r\le r_*}\mu(r)^2,
\qquad \mathscr G_f=\sum_{r\le r_*}|G_f(r)|^2,
\]
\[
\begin{aligned}
E_f^{\rm abs}&=\sum_{p\in\mathcal P}a_p
 \sum_{\substack{r\le D/p\\p\mid r}}|\mu(r)|\,|b_f(pr)|,\\
R_f^{\rm abs}&=\sum_{d\le D}|\mu(d)|\,|H-v(d)|\,|b_f(d)|.
\end{aligned}
\]
Тогда из (2.4)
\[
\boxed{A_m[f]\le\mathfrak C_{m,\mathcal P,a}(f)
 :=\frac{\sqrt{Q\mathscr G_f}+E_f^{\rm abs}+R_f^{\rm abs}}{H}.} \tag{2.5}
\]
Это действительно доказанный направленный upper для полного источника. Он не требует изменения \(P\), замены фактических \(\mu\), удаления степеней простых или независимого выбора фаз.

Важно, что
\[
\mathscr G_f=\sum_r\sum_{p,q}a_pa_q\,b_f(pr)b_f(qr)
\]
содержит **все смешанные \(p,q\)** и через каждый \(b_f\) — все внутренние \(k\). Мы не оценивали отдельно корреляции каждой пары. Таким образом, даже сохранение всей этой совместности ещё не гарантирует малой цены.

Испытуемая достаточная строка была
\[
\sup_{\substack{c=Pc\\\|c\|=1}}
\mathfrak C_{m,\mathcal P,a}(f)
\stackrel{?}{\le} C_\epsilon m^{\theta(\epsilon)},
\qquad \theta(\epsilon)\to0. \tag{2.6}
\]
Далее не просто сообщается, что (2.6) не доказана. Для двух точно указанных классов выбора \(\mathcal P,a\) она **опровергается на исходном пространстве**.

## 3. Точный исходный свидетель, без проекционной ошибки

**[COFINAL_FAMILY | PAPER].** Для \(L>0\) положим
\[
g_L(t)=\sin^4(\pi t/L),\quad
u_L=(\partial_t^2-1/4)g_L,\quad
Z_L=\|\nu_L\|_{L^2(0,L)},\quad f_L=\nu_L/Z_L. \tag{3.1}
\]
Нулевое продолжение за \([0,L]\) сохраняется.

### 3.1. Три контакта и точная полоса

Имеем \(g_L(0)=g_L(L)=g'_L(0)=g'_L(L)=g''_L(0)=g''_L(L)=0\). Следовательно, \(f_L(0)=f_L(L)=0\). Для \(\sigma=\pm1/2\) интегрирование по частям даёт
\[
\int_0^L e^{\sigma t}\nu_L(t)dt
 =\big[e^{\sigma t}(g'_L(t)-\sigma g_L(t))\big]_0^L=0. \tag{3.2}
\]
Это ровно два исходных экспоненциальных контакта.

Обозначив \(a=2\pi/L\), получаем
\[
\nu_L(t)=-\frac3{32}
 +\frac{a^2+1/4}{2}\cos(at)
 -\frac{4a^2+1/4}{8}\cos(2at). \tag{3.3}
\]
Поэтому \(f_L\) содержит только моды \(j=0,\pm1,\pm2\), а
\[
Z_L^2=L\left[
\frac9{1024}+\frac{(a^2+1/4)^2}{8}
 +\frac{(4a^2+1/4)^2}{128}\right]>0. \tag{3.4}
\]
Для каждого фиксированного \(\epsilon>0\) при \(m\ge 2^{1/\epsilon}\) эти моды лежат в исходном \(M=\lfloor m^\epsilon\rfloor\). Исходный коэффициентный вектор нормирован и **точно** лежит в \(\operatorname{ran}P\). Ни sparse Fourier approximation, ни последующая Gram-коррекция не нужны.

### 3.2. Явный нижний bound физического overlap у верхнего края

Пусть \(\alpha=\pi/L\), \(L\ge4\pi\). Прямое дифференцирование даёт
\[
\nu_L(t)=\sin^2(\alpha t)
 \big[12\alpha^2-(16\alpha^2+1/4)\sin^2(\alpha t)\big].
\]
Для \(0\le t\le1\), поскольку \(\alpha\le1/4\),
\[
\sin(\alpha t)\ge\alpha t/2,\qquad
12\alpha^2-(16\alpha^2+1/4)\sin^2(\alpha t)\ge8\alpha^2.
\]
Кроме того, на всём окне \(|\nu_L|\le28\alpha^2+1/4\le2\), так что \(Z_L\le2\sqrt L\). Поэтому
\[
\boxed{f_L(t)\ge\pi^4 L^{-9/2}t^2\quad(0\le t\le1).} \tag{3.5}
\]
Точная симметрия \(f_L(L-t)=f_L(t)\) сохраняет знак на обоих концах. Для \(0\le u\le1\)
\[
\begin{aligned}
q_{f_L}(L-u)
 &=2\int_0^u f_L(t)f_L(u-t)dt\\
 &\ge 2\pi^8L^{-9}\int_0^u t^2(u-t)^2dt
 =\boxed{\frac{\pi^8}{15L^9}u^5}.
\end{aligned} \tag{3.6}
\]
Это полноценная физическая оценка, не формальная частотная модель. Контакты зануляют полные экспоненциальные моменты, но не этот частичный overlap.

Как отдельный контроль нормировки, при фиксированном \(t\)
\[
L^{9/2} f_L(t)\to\pi^4\sqrt{2048/35}\,(12t^2-t^4/4).
\]
Свёртка полинома \(q(t)=12t^2-t^4/4\) с собой на \([0,u]\) равна
\[
\int_0^u q(t)q(u-t)dt
 =\frac{24}{5}u^5-\frac{2}{35}u^7+\frac{u^9}{10080}.
\]
Этот предел не используется вместо явного bound (3.6); его коэффициенты проверены точной рациональной арифметикой.

## 4. Первая непригодность: совместный простой канал не имеет малой нормы

### 4.1. Класс утверждения

**[COFINAL_FAMILY | PAPER].** Здесь \(a_p=1\), \(2\in\mathcal P\subseteq\{p\le D\}\). Набор может зависеть от \(m\), \(\epsilon\) и даже от испытываемого вектора. Не предполагается, что другие простые образуют начальный отрезок. Утверждение относится к нормовой оплате **уже собранного** \(-\sum_r\mu(r)G_f(r)\).

Возьмём целые
\[
I_m=\{r:\ m/8\le r\le m/7\}.
\]
На этом интервале активными могут быть только простые 2 и 3: для \(p\ge5\) имеем \(pr>m/2\), следовательно, \(b_{f_L}(pr)=0\) точно. При этом
\[
2r\in[m/4,2m/7],\qquad3r\in[3m/8,3m/7].
\]
В каждом ненулевом внутреннем члене \(b_{f_L}(2r)\) или \(b_{f_L}(3r)\), \(k\ge2\) и
\[
0\le L-\log(pkr)\le\log2<1.
\]
По (3.6) все эти члены неотрицательны. В частности, оставляя только **для нижней оценки этого неотрицательного канала** член \(p=2,k=2\),
\[
G_{f_L}(r)\ge b_{f_L}(2r)
\ge\frac{c_g}{\sqrt m L^9},\qquad
c_g=\frac{\pi^8\log2}{15}\big[\log(7/4)\big]^5>0. \tag{4.1}
\]
Никакие остальные члены исходного \(A_m\) здесь не удалены: оценивается один участок вспомогательной суммы квадратов, а не источник снизу.

### 4.2. Настоящие квадратсвободные индексы и вся Cauchy-цена

Нужно учитывать, что коэффициент спаривания — фактическая \(\mu(r)\), а не единица. Достаточно элементарного подсчёта. Если интервал содержит \(T\) последовательных целых, число его элементов, делящихся хотя бы на одно \(k^2\), \(k\ge2\), не превосходит
\[
\sum_{2\le k\le\sqrt m}(T/k^2+1)
\le\frac34T+\sqrt m,
\]
поскольку \(\sum_{k\ge2}k^{-2}\le1/4+\int_2^\infty t^{-2}dt=3/4\). Значит,
\[
\#\{r\in I_m:\mu(r)^2=1\}
\ge\frac14\# I_m-\sqrt m
\ge\frac m{448} \tag{4.2}
\]
для всех достаточно больших \(m\); например, \(m\ge10^6\) достаточно для этой грубой последней оценки.

Сочетая (4.1)–(4.2), получаем **нижнюю оценку всей абсолютной оплаты**, не отдельных pairwise maxima:
\[
\sum_{r\le r_*}|\mu(r)G_{f_L}(r)|
\ge\frac{c_g}{448}\frac{\sqrt m}{L^9}. \tag{4.3}
\]
С другой стороны, законная Cauchy-плата удовлетворяет
\[
\sqrt{Q\mathscr G_{f_L}}
\ge\sum_{r\le r_*}|\mu(r)G_{f_L}(r)|. \tag{4.4}
\]
Наконец, для не взвешенного набора
\[
H=\sum_{p\in\mathcal P}1/p\le1+\log D\le2L.
\]
Следовательно,
\[
\boxed{\frac{\sqrt{Q\mathscr G_{f_L}}}{H}
\ge\frac{c_g}{896}\frac{\sqrt m}{L^{10}}.} \tag{4.5}
\]
В частности,
\[
\boxed{\sup_{\substack{c=Pc\\\|c\|=1}}
\mathfrak C_{m,\mathcal P,1}(f)
\ge\frac{c_g}{896}\frac{\sqrt m}{L^{10}}.} \tag{4.6}
\]
Это верно для каждого достаточно позднего исходного \(m\), а не только на выбранной последовательности. Начало также учитывает \(M\ge2\).

Усиление (4.3) полезно для точного scope: сокращение Cauchy к ненулевой поддержке или выбор положительных Cauchy-весов не спасает **абсолютную** оплату данного канала. Она всё равно не меньше его \(\ell^1\)-массы. Но (4.3) **не** ограничивает снизу знаковое число \(-\sum_r\mu(r)G_{f_L}(r)\).

При произвольных неотрицательных весах то же локальное доказательство даёт
\[
\frac{\sum_r|\mu(r)G_{f_L}(r)|}{H}
\ge\frac{c_g}{448}\frac{a_2}{H}\frac{\sqrt m}{L^9},
\]
если \(a_2>0\). Свободно занулить или резко уменьшить \(a_2/H\) можно, поэтому этот вариант **не** объявляется равномерным препятствием всем весам. Следующий раздел закрывает другой, точно указанный класс весов.

## 5. Вторая непригодность того же завершения: произвольные короткие prime weights

### 5.1. Класс утверждения и сохранённый знак

**[COFINAL_FAMILY | PAPER, с inherited scalar input из S1–S2].** Теперь \(a_p\ge0\) произвольны, \(H>0\), но
\[
\operatorname{supp}a\subseteq\{p\text{ prime}:p\le m/4\}. \tag{5.1}
\]
Это включает любой фиксированный набор и любые пределы \(p\le m^\vartheta\) с фиксированным \(\vartheta<1\), в конечном счёте. Веса и набор могут зависеть от \(m,f\). Не требуется присутствие простого 2.

Рассмотрим настоящие простые
\[
\mathcal J_m=\{d\text{ prime}:m/3<d\le3m/8\}.
\]
У каждого из них \(v(d)=0\), \(\mu(d)=-1\). В полной внутренней сумме (1.2) остаётся только \(k=2\), поскольку \(k=1\) имеет \(\log1=0\), а \(d>m/3\). Поэтому **точно**
\[
b_{f_L}(d)=\frac{\log2}{\sqrt{2d}}q_{f_L}(\log(2d))
\ge\frac{c_b}{\sqrt m L^9},\quad
c_b=\frac{\pi^8\log2}{15}\big[\log(4/3)\big]^5. \tag{5.2}
\]
Сами эти члены \(\mathcal R_{f_L}\) равны \(-H b_{f_L}(d)\): это **благоприятный отрицательный кредит** для upper! Именно его независимая абсолютная оплата превращает в положительную цену. Нельзя обратить этот знак и заявить lower для исходного источника.

### 5.2. Число настоящих простых: точный расход принятого Q55

Для этого раздела нужна лишь уже принятая в S1 скалярная оценка \(E_x(0)=o(\sqrt x)\), а не полный новый арифметический supplier. Она даёт
\[
W(x):=\sum_{n\le x}\frac{\Lambda(n)}{\sqrt n}
=2\sqrt x+o(\sqrt x). \tag{5.3}
\]
Для вещественного \(x\) используется \(\lfloor x\rfloor\); изменение главного члена — \(O(x^{-1/2})\). Важно: (5.3) расходуется из **скалярного** вывода Q55, а не выводится из одного матричного upper \(A_m\preceq sP\).

Все собственные степени простых оплачиваются отдельно только в этом подсчёте:
\[
\begin{aligned}
\sum_{\substack{p^k\le m\\k\ge2}}\frac{\log p}{p^{k/2}}
&\le\frac1{1-1/\sqrt2}\sum_{p\le\sqrt m}\frac{\log p}{p}\\
&\le C(1+L)^2=o(\sqrt m).
\end{aligned}
\]
Следовательно, из разности (5.3) на \((m/3,3m/8]\)
\[
\sum_{d\in\mathcal J_m}\frac{\log d}{\sqrt d}
=2\big(\sqrt{3/8}-\sqrt{1/3}\big)\sqrt m+o(\sqrt m).
\]
Поскольку каждый summand не больше \(\sqrt3 L/\sqrt m\), в конечном счёте
\[
\#\mathcal J_m\ge\frac{m}{100L}. \tag{5.4}
\]
Константа намеренно не оптимизирована. Нового эффективного численного onset для Q55 здесь не заявляется. Степени простых удалены только из вспомогательного счётного lower с полной ошибкой, **не** из \(A_m\), \(b_f\) или (2.4).

### 5.3. Uniform lower самой цены, независимо от весов

Для каждого \(d\in\mathcal J_m\), \(|H-v(d)|=H\). Поэтому (5.2)–(5.4) дают
\[
\boxed{\frac{R_{f_L}^{\rm abs}}{H}
\ge\sum_{d\in\mathcal J_m}b_{f_L}(d)
\ge\frac{c_b}{100}\frac{\sqrt m}{L^{10}}.} \tag{5.5}
\]
Нормировка и все значения \(a_p\) исчезли **точно**. Это исключает оптимизацию (2.6) посредством любых неотрицательных весов с (5.1), даже адаптивных. Дополнительная абсолютная или Cauchy-плата может только увеличить определённый сертификат.

Это не третья самостоятельная попытка: §§4–5 — два теста разных частей **одного** prime-dilation completion.

### 5.4. Машинно корректное направление отрицательного вердикта

Для каждого фиксированного \(\eta<1/2\), \(C>0\),
\[
\frac{\sqrt m/L^{10}}{m^\eta}\longrightarrow\infty. \tag{5.6}
\]
В каждом из двух классов рассмотрим именно зазор предлагаемого сертификата
\[
\mathcal D^{\rm cert}_{m,C,\eta}
=Cm^\eta-\mathfrak C_{m,\mathcal P,a}(f_L).
\]
Доказана его **верхняя** оболочка
\[
\boxed{\mathcal D^{\rm cert}_{m,C,\eta}
\le Cm^\eta-c\sqrt m/L^{10}<0\quad\text{eventually}.} \tag{5.7}
\]
Поэтому `KILL_SCOPE: THEOREM_SHAPE` опирается на правильное направление \(U<0\). Это не inference «наш upper большой, значит источник большой».

Не исключены: иной конечный bilinear decomposition BSZ; signed payment \(\mathcal E+\mathcal R\); сохранение знака \(\mu\) в главном спаривании; веса вне (5.1), не подпадающие под §4; более слабый sufficient cofinal consumer. Для этих возможностей нет доказательства математической невозможности.

## 6. Полностью оплаченный слабый trial и возврат к исходному потребителю

### 6.1. Явный uniform upper без предположения о decorrelation

**[COFINAL_FAMILY | PAPER — finite inequality плюс inherited inner-sum bound].** Чтобы не оставлять цену (2.5) только формальным функционалом, завершим её заведомо слабым, но полностью оплаченным способом. Это проверка возврата того же опыта, не новый механизм.

S8, раздел о full-log input, даёт на исходном пространстве
\[
|b_f(d)|\le B_m/\sqrt d,\qquad B_m=40+16\Omega,
\quad\|f\|=1. \tag{6.1}
\]
Это наследуемая оценка всей внутренней \(k\)-суммы, а не новый результат Q56.

Для проверки именно требуемой области можно воспроизвести её короткий bound, не приписывая ему новизны. На исходном \(P\), \(|q_f(s)|\le2\), \(|q_f'(s)|\le2\Omega\). Контакты и производная рангового ядра \(2\cosh(\sigma(u-t))\) при \(\sigma=1/2\) дают
\[
\int_0^L e^{s/2}q_f(s)ds=-\int_0^L e^{-s/2}q_f(s)ds,
\qquad
\int_0^L s e^{s/2}q_f(s)ds=\int_0^L s e^{-s/2}q_f(s)ds.
\]
Производная ранговой формы нулевая, потому что оба её моментных множителя равны нулю; знак второй формулы не копируется из первой.

При \(a=\log d\) непрерывная сумма для (1.2) равна
\(d^{-1}\int_a^L(s-a)e^{s/2}q_f(s)ds\). Полный интеграл от 0 имеет модуль не больше \((8+4a)/d\le8/\sqrt d\); вычитаемый нижний отрезок — не больше \(8/\sqrt d\). Для
\(g(t)=d^{-1/2}t^{-1/2}\log t\,q_f(\log(dt))\), \(1\le t\le m/d\), оба крайних значения нулевые. Поэтому ошибка sum–integral не больше
\[
\int_1^{m/d}|g'(t)|dt
\le\frac1{\sqrt d}\int_1^\infty t^{-3/2}
 [2+(1+2\Omega)\log t]dt
=\frac{8+8\Omega}{\sqrt d}.
\]
Итого \(|b_f(d)|\le(24+8\Omega)/\sqrt d\le B_m/\sqrt d\), включая нецелый верхний край. Это только проверка расходуемой старой оценки, не новый выигрыш степени.

Берём \(\mathcal P=\{2\}\), \(a_2=1\), \(H=1/2\). Тогда \(r_*=\lfloor D/2\rfloor\),
\[
Q\le m/4,\qquad
\mathscr G_f=\sum_{r\le D/2}b_f(2r)^2
\le\frac{B_m^2}{2}(1+L).
\]
Также
\[
\begin{aligned}
R_f^{\rm abs}
 &=\frac12\sum_{d\le D}|\mu(d)b_f(d)|
 \le B_m\sqrt{m/2},\\
E_f^{\rm abs}
 &\le\sum_{s\le D/4}|b_f(4s)|
 \le B_m\sqrt{m/8}.
\end{aligned}
\]
При подсчёте \(E\) фактическое \(|\mu(2s)|\le1\) лишь укрупнено; поправка не занулена. Деление на \(H\) даёт
\[
\boxed{A_m\preceq s_{\rm trial}(m)P,\qquad
s_{\rm trial}=B_m\sqrt m\left[\sqrt{\frac{1+L}{2}}+\frac3{\sqrt2}\right].}
\tag{6.2}
\]
Для каждого фиксированного допустимого \(\epsilon\) полный показатель этого trial — \(1/2+\epsilon\), не \(\eta(\epsilon)\to0\). Его логарифмические множители не выдаются за выигрыш. Это слабее уже принятого Q55.

### 6.2. Все платы возвращены ровно один раз

По неизменённому receiver [S13] и current request, из (6.2)
\[
\begin{aligned}
T_{>R}&\preceq(s_{\rm trial}+b_{\rm div})P,\\
PK_mP&\succeq-(s_{\rm trial}+50L+8)P,\\
b_{\rm div}&=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\end{aligned} \tag{6.3}
\]
Весь источник уже входит в \(b_f\) и (2.4). Нет второй short-платы в direct \(K_m\), нет новой contour-платы, и arch оплачена один раз. Prime-square error \(\mathcal E\) и divisibility remainder \(\mathcal R\) уже входят в \(s_{\rm trial}\) и не добавляются повторно.

Если требуется возврат к полной \(\Psi\)-форме из S14, (6.2) ограничивает \(A_m\), а не \(A_m-A_{\rm cont}\). Поэтому надо учитывать \(-4\le A_{\rm cont}\le0\):
\[
R_\tau^\Psi-\Psi_\tau
\le\left[\frac\tau2(s_{\rm trial}+4)-\tau h_m-1\right]\|f\|^2,
\quad h_m=\sum_{n\le m}\Lambda(n)/n. \tag{6.4}
\]
Это только старый точный возврат нового слабого upper, не новая Taylor-конструкция. Комплексные смешанные члены не удалены. У retained Q55 прямой bound для \(A-A_{\rm cont}\) не требует этой дополнительной 4.

### 6.3. Что реально сохраняется после опыта

**[COFINAL_FAMILY | PAPER — inherited S1–S2].** Остаётся Q55:
\[
s_{55}(m)=C\sqrt m\exp\left[-c\left(
\frac{L}{\log(e+L)}\right)^{1/3}\right],
\qquad A_m\preceq s_{55}(m)P.
\]
На его eventual области можно брать минимум с независимым явным fallback
\[
s_0(m)=6\sqrt m+6m^{1/4}.
\]
Для неизвестных явных констант/onset Q55 это не новый исполняемый finite-cell certificate. Вне такой сертификации остаётся доступен прежний \(s_0\).

Итоговый сохранённый бюджет —
\[
\boxed{T_{>R}\preceq(s_{\rm retained}+b_{\rm div})P,
\qquad PK_mP\succeq-(s_{\rm retained}+50L+8)P.} \tag{6.5}
\]
**Не прибавляем** к нему \(s_{\rm trial}\), \(\mathfrak C\), Cauchy-плату или цену остатков этого опыта. Они альтернативные upper bounds. Полный сохранённый показатель равен \(1/2\); условные \(3/8\)/ZF78 не использованы.

## 7. Первая неоплаченная строка, откат и граница полезности

### 7.1. Где именно потерян нужный знак

В (2.4) знак ещё полностью сохранён. Первый решающий шаг выбранного completion —
\[
-\sum_r\mu(r)G_f(r)\ \le\ \sqrt{Q\mathscr G_f}. \tag{7.1}
\]
Он удаляет корреляцию с **настоящими** знаками \(\mu(r)\), хотя связь между простыми каналами внутри \(G_f\) сохранена. §4 показывает, что малость правой части не может быть источником нужной степени в указанном классе. §5 независимо показывает цену удаления знака \(\mathcal R_f\), даже после произвольной перенастройки коротких prime weights.

Если оставить \(\mathcal E_f,\mathcal R_f\) знаковыми, более слабая достаточная строка была бы
\[
\boxed{\sqrt{Q\mathscr G_f}+\mathcal E_f+\mathcal R_f
\stackrel{?}{\le}H C_\epsilon m^{\theta(\epsilon)}\|f\|^2.}
\tag{7.2 OPEN}
\]
Она **не доказана**, и не исключена нижними оценками положительных цен. В отличие от исходного равенства, это достаточный вход после конкретной Cauchy-потери; он может быть сильнее необходимого. Назвать (7.2) supplier без нового арифметического доказательства было бы новой переупаковкой долга.

Без Cauchy левая часть (2.4), делённая на \(H\), просто равна \(A_m\). Этому равенству не приписывается новый прогресс. Таким образом, результат Q56 — **исключение точно определённых способов оплатить новый арифметический ход**, а не разрешение главного знака.

### 7.2. Сильнейшие возражения

**«Ты снова проверил лишь достаточное условие».** Да. Поэтому `NO_DERIVATION` относится к запрошенному full bound, а `KILL` — только к (2.6) в классах §§4–5. Отличие от простого сообщения об отсутствии оценки: здесь есть явный original-P свидетель, uniform lower цены и строго отрицательная upper envelope (5.7).

**«Простой 2 можно выбросить».** Можно; §4 тогда не применяется. Но для любых оставшихся неотрицательных весов до \(m/4\) сохраняется §5. Выход за оба класса или сохранение знаковых кредитов не запрещены. Никакого consumer-wide no-go нет.

**«Нужно использовать только одну сторону, а ты заплатил модуль».** Верно. Это и есть причина остановки данного завершения. В (5.2)–(5.5) показан точный участок, где модуль превращает благоприятный член в расход. Не разрешается продолжать этот расчёт как доказательство малой односторонней цены.

**«Это просто старое raw-shell препятствие».** Контактная геометрия похожа и не считается новой. Но в §§4–5 возвращены **полные** \(b_f(pr)\), коэффициенты \(\mu(pr)\), prime-square correction и общий divisibility remainder. Доказывается lower другого, точно определённого сертификата, равномерный по названным вспомогательным наборам/весам. Нижняя оценка raw prime shell вместо этой карты не использовалась.

### 7.3. Документированный ранний откат

Откат — **к исходной полной форме до prime-divisor amplification и независимых неотрицательных плат**, а не к Hilbert/Pick, новой производной \(\Psi\) или настройке VK. Текущий независимый арифметический ход проверен и остановлен в точно ограниченном классе.

Две допускаемые дальнейшие репрезентации — это кандидаты, **не выполненные попытки и не новые результаты**:

| Репрезентация | Отличающийся проверяемый вход | Цена и сила отсечения |
|---|---|---|
| Сохранить общий signed \(\mathcal E+\mathcal R\) вместе с главным спариванием | Нужна независимая односторонняя арифметическая оценка, а не положительность \(\mathscr G\). Контрольные (3.1), (4.1), (5.2) должны остаться в полном возврате | Карта и отрицательный контроль дёшевы; новый знак пока не оплачен. Высокая сила против удаления любого из двух остатков. Не назначать (7.2) новым готовым supplier |
| Вернуться к **известной cofinal-развилке положительных спектральных моментов** исходного источника | Оценивать среднее не матриц, а неотрицательной величины, например \(\operatorname{Tr}((P_mA_mP_m)_+^2)\), по исходным ячейкам | Проверка квантора — короткий PAPER gate; независимая арифметика момента трудна и отсутствует. Среднее матриц и отдельные знаковые traces не проходят. Никакой production scan не разрешается этим предложением |

Для второго кандидата точный sufficient quantifier таков. Если при фиксированном \(\epsilon\), \(\theta\ge0\), независимо доказано для неограниченно больших \(X\)
\[
\frac1{\#\mathcal I_X}\sum_{m\in\mathcal I_X}
 \operatorname{Tr}\big((P_mA_mP_m)_+^2\big)
 \le C_\epsilon X^{2\theta(\epsilon)},
\quad \mathcal I_X=\mathbb Z\cap[X,2X], \tag{7.3 CONDITIONAL}
\]
то хотя бы одна исходная ячейка в каждом таком блоке имеет
\(\lambda_{\max}(P_mA_mP_m)\le\sqrt{C_\epsilon}X^{\theta(\epsilon)}\).
Это даёт cofinal direct upper без множителя размерности, поскольку размерность уже включена в trace. Полный показатель после short-return — \(\max\{\theta,2\epsilon\}\).

Это **проверка достаточности разрешённого квантора**, не новый bound: (7.3) не установлена. Замена положительной части на среднюю матрицу незаконна; замена на \(\operatorname{Tr}(A^2)\) — более сильный sufficient input, а не равенство. S7 уже указывал такую раннюю развилку, поэтому она не объявляется открытием Q56.

Именно эта cofinal-развилка — документированное место следующего поиска после двух последовательных no-gain продолжений: она требует **неотрицательного скалярного контроля по ячейкам**, а не ещё одного uniform norm completion внутри каждой ячейки. До нового арифметического входа писать эквивалентный момент как прогресс нельзя.

Применимость к receiver не предполагается молча: если существовал бы фиксированный off-critical zero с \(\delta>0\), S13 даёт отрицательный сигнал \(-c m^\delta/L^{2\delta}\) в **каждой** достаточно поздней ячейке. Поэтому cofinal lower-floor с показателем \(<\delta\) уже противоречит ему. Для семейства \(\eta(\epsilon)\to0\) сначала выбирается фиксированное \(\epsilon\) с \(\eta(\epsilon)<\delta\), затем cofinal \(m\); \(\epsilon\) не меняется по \(m\). Никакой такой новый floor в Q56 не доказан.

## 8. Ledger, прогнозы и один gate

### 8.1. Ledger

| Claim | Scope | Verifier | Область принятия |
|---|---|---|---|
| (2.2)–(2.5): finite amplification и односторонний сертификат | FINITE_CELL | PAPER | Собственный вывод, actual \(\mu\), все границы и остатки |
| (3.1)–(3.6): точный original-P свидетель и overlap lower | COFINAL_FAMILY | PAPER | Собственный вывод; \(M\ge2,L\ge4\pi\); без проекционной ошибки |
| (4.3)–(4.6): цена главного абсолютного/Cauchy-канала | COFINAL_FAMILY | PAPER | Не взвешенные наборы с 2; арифметическая squarefree-оценка, без PNT |
| (5.5): цена absolute remainder для всех коротких весов | COFINAL_FAMILY | PAPER | Любые \(a_p\ge0\) до \(m/4\); использован inherited Q55 scalar input |
| (6.2)–(6.4): слабый полный trial | COFINAL_FAMILY | PAPER | Inherited full-log bound из S8; показатель \(1/2+\epsilon\) |
| (6.5): сохранённый итог | COFINAL_FAMILY | PAPER | Q55/fallback наследуются; показатель \(1/2\) |
| (7.2), (7.3): возможные достаточные входы | COFINAL_FAMILY | CONDITIONAL | Не доказаны и не использованы как факты |
| Новые executable controls | FINITE_CELL | PAPER | Точная алгебра, не физический cofinal-сертификат |

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_SIGNED_T_UPPER_AND_DIRECT_K_FLOOR
ACTUAL_CONSUMER_REQUIREMENT: a_sufficient_eventual_or_cofinal_original_P_bound_with_eta_epsilon_to_zero
ORIGINAL_REQUESTED_OBJECT: eventual_all_P_full_signed_source_upper
ORIGINAL_OBJECT_IS: NOT_NECESSARY
NECESSITY_QUALIFICATION: owner_explicitly_allows_a_proved_weaker_cofinal_quantifier
TESTED_AUXILIARY_OBJECT: independent_nonnegative_amplifier_certificate_2_5
TESTED_AUXILIARY_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - direct_cofinal_A_upper_returns_T_and_K_with_single_short_and_arch_fees
  - signed_remainder_payment_is_weaker_than_its_absolute_payment_but_not_supplied
  - nonnegative_positive_spectral_moment_bound_7_3_would_supply_a_cofinal_cell
KILL_SCOPE: THEOREM_SHAPE
KILL_CLASSES:
  - unweighted_auxiliary_prime_sets_containing_2_for_the_norm_paid_main_channel
  - arbitrary_nonnegative_prime_weights_supported_at_p_le_m_over_4_for_absolute_remainder_payment
KILL_EVIDENCE: exact_original_P_family_3_1_and_negative_upper_envelope_5_7
ACTUAL_SOURCE_FAILURE_TYPE: NO_DERIVATION
ACTUAL_SOURCE_EPISTEMIC_STATUS: RESEARCH_DEBT
REOPEN_TRIGGER: independent_signed_arithmetic_compensation_or_a_paid_cofinal_positive_spectral_moment
NOVELTY_AXIS: source_specific_test_of_finite_Mobius_prime_amplification_prices_not_a_new_source_identity
ROUTE_SCORE: 4_for_scoped_falsification_only
CONSUMER_PROGRESS: NO_PROGRESS
```

**DISCRIMINATOR.** Для настоящего source budget \(s_m\) остаётся \(s_m\|c\|^2-c^*P_mA_mP_mc\): PASS требует lower envelope \(\ge0\), отрицательное заключение о данном budget — upper envelope \(<0\) на допустимом векторе. Здесь такой отрицательный source verdict **не получен**. Отдельный certificate discriminator (5.7) строго отрицателен на cofinal семье и потому действительно исключает названные достаточные завершения. Нулесогласованных численных результатов нет.

### 8.2. Судьба зарегистрированных прогнозов

Регистрация записана после чтения и предварительного PAPER-расчёта, **до новых исполняемых математических тестов**. Она не выдаётся за регистрацию до поиска идеи.

| ID | Прогноз | Итог |
|---|---|---|
| P1 | Обязательная prime-square correction и полный source return | Подтверждён (2.2)–(2.4), exact finite controls |
| P2 | Пяти-модовый профиль точно принадлежит исходному \(P\) | Подтверждён (3.2)–(3.4); rational-frequency controls лишь проверяют алгебру |
| P3 | Главная Cauchy-плата сохраняет half-power для наборов с 2 | Подтверждён PAPER (4.3)–(4.6); не численным спектром |
| P4 | Короткие произвольные веса не спасают absolute remainder | Подтверждён PAPER (5.2)–(5.5), с явно inherited scalar input |
| P5 | Нет переноса certificate lower на CCM; retained power остаётся \(1/2\) | Соблюдено в §§5–7; \(\eta\to0\) не объявлено |

В ходе исполнения математические assertions checker не менялись; первый запуск прошёл. Никакого независимого субагента или независимого PAPER-аудита здесь не было.

```yaml
MEMORY_ENTRY:
  iteration: Q56_ACTUAL_JOINT_ARITHMETIC
  target: full_original_P_signed_arithmetic_upper
  status: OPEN
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  tested_strategy: prime_dilation_amplification_then_independent_nonnegative_payments
  local_result: two_precise_certificate_classes_refuted_by_one_original_P_family
  invariant_learned: joint_prime_channels_can_remain_coherent_after_all_inner_k_sums_are_preserved
  forbidden_future_move: treat_small_pairwise_correlations_or_retuning_prime_weights_as_a_paid_signed_source_gain
  smallest_unpaid_input: arithmetic_compensation_before_mu_sign_and_remainder_sign_are_discarded
  rollback: original_full_source_before_prime_amplification; existing_cofinal_positive_moment_fork
  next_decisive_test: bounded_independent_PAPER_audit_of_the_certificate_lower_and_its_scope
  route_death: NOT_ESTABLISHED
```

## 9. Источники и воспроизведение

### 9.1. Источники

**[S1–S14]** — неизменённые source bodies канонического Q56 TXT. Для основных зависимостей: S1–S2 — статус и scalar input Q55; S8 — полный inner-log upper \(40+16\Omega\); S13 — conditional sparse receiver и original-P return; S14 — определения исходной формы и полный \(\Psi\)-crosswalk. Размеры и SHA-256 каждого тела находятся в `q56_checks.json`. Другие source bodies использованы для анти-повторного экрана, не как новые арифметические предпосылки.

**[E1]** J. Bourgain, P. Sarnak, T. Ziegler, *Disjointness of Mobius from Horocycle Flows*, авторский PDF на IAS, Theorem 2 и Notes 1–2, печатная с. 2; начало §2, с. 3. Проверены текст и изображения этих страниц. Использован принцип prime-dilation arithmetic, а не недоказанный для нашей меняющейся семьи quantitative supplier. Ни теорема о horocycle flows, ни Ratner input здесь не применяются.

**[E2]** NIST DLMF §27.5, особенно 27.5.2 и 27.5.5: инверсия Мёбиуса и \(\Lambda=\mu*\log\). Этот исходный crosswalk не считается новым.

```text
E1: https://publications.ias.edu/sites/default/files/disjointness%20b-s-z%20oct.pdf
E2: https://dlmf.nist.gov/27.5
```

### 9.2. Что действительно запущено

Новый checker использует только стандартную библиотеку Python и `Fraction`. Выполнены 128 formal-log coefficient checks для \(\Lambda\), 1408 точных проверок \(\mu(pr)\), 12 полных finite amplifier returns и 12 Cauchy inequalities. Дополнительно — пять rational-frequency contact controls, точная свёртка endpoint-полинома, 28 integer-endpoint controls и восемь конечных squarefree count controls.

Контроли обнаруживают удаление prime-square correction, обратный знак main term, замену \(\mu\) модулем, квадрат до сборки простых каналов, неверную proper-power кратность и нарушение контактов. Они не доказывают PAPER-асимптотику и не создают production-ячейку. Рациональный параметр \(a\) в contact tests — формальный: не утверждается, что \(m=e^{2\pi/a}\) является целой исходной ячейкой. Малые \(m\) в integer controls проверяют только границы; их спектры не вычисляются.

Ни floating-point математики, ни Arb, ни Lean, ни установки пакетов, ни исполнения исторического кода не было. Новые приложения и результаты ниже полные.

Сохрани `replay_q56.py` из его блока и запусти из каталога с оригиналами:

```bash
python3 replay_q56.py \
  PROSHKA_CCM_Q56_PRIME_DILATION_VERDICT_2026-10-27.md \
  PROSHKA_CCM_ACTUAL_JOINT_ARITHMETIC_Q56_2026-10-27.txt \
  q56_replay
```

Первый аргумент — этот Markdown, второй — канонический TXT с указанным SHA-256, третий — создаваемый каталог результатов. При другом расположении меняются только пути. Replayer проверяет четыре новых asset frames, исполняет только новый checker и требует **побайтного** совпадения exact JSON. Исторические вложения не извлекаются для исполнения.

BEGIN_ASSET registration_q56.json
BYTES: 1987
SHA256: 710cc69a6f1cdfa0563c9b1b4a176530ed8a3a6a128090a24f561f02d55d5617
```json
{
  "historical_programs_executed": false,
  "installations": false,
  "operator": "COUNTEREXAMPLE_HUNT",
  "packet_sha256": "b3a5f4823019bd3e9464973b3457e7d3e9497241be81e49b0cccbc08099b270a",
  "planned_controls": [
    "omitted prime-square correction",
    "reversed amplified main sign",
    "mu replaced by abs(mu)",
    "wrong coefficient at a proper prime power",
    "removed endpoint or exponential contact",
    "square before summing linked prime channels"
  ],
  "predictions": {
    "P1": "Exact mu(p*r)=-mu(r)+1_(p|r)*mu(r) produces a nonzero prime-square correction. The finite amplifier returns the original full source.",
    "P2": "The normalized (d^2/dt^2-1/4) sin^4(pi*t/L) belongs exactly to the original three-contact band when M>=2, with no projection error.",
    "P3": "For this witness and unweighted auxiliary prime sets containing 2, the joint-Cauchy price alone is bounded below by c*sqrt(m)/log(m)^10 eventually, irrespective of additional primes.",
    "P4": "For arbitrary nonnegative auxiliary prime weights supported at p<=m/4, absolute payment of the amplifier remainder costs at least c*sqrt(m)/log(m)^10, using the inherited Q55 zero-frequency estimate to count actual primes.",
    "P5": "These are lower bounds on specified sufficient-certificate prices, not on A, T or K. The retained source exponent is 1/2 and no vanishing-exponent supplier is derived."
  },
  "repository_writes": false,
  "scope": "Exact finite algebra controls only. Cofinal witness estimates are PAPER; no production cell, interval, Lean or independent audit is certified.",
  "stage": "After complete supplied-source reading and preliminary paper calculations; before new executable mathematical tests. This is not a registration preceding idea selection.",
  "task": "Q56_ACTUAL_JOINT_ARITHMETIC",
  "tested_method": "Finite prime-divisor amplification of the complete recombined Mobius-log source, followed by a single joint Cauchy estimate; no scalar Fourier maxima."
}
```
END_ASSET

BEGIN_ASSET check_q56.py
BYTES: 9161
SHA256: 79e5a9e12c32af75e8095e233d8216ea996d49dd70926b877887adf46108dc52
```python
#!/usr/bin/env python3
"""Q56: new exact finite controls; Python 3.9+, standard library only.
Usage: python3 check_q56.py PACKET.txt [RESULT.json]
No historical code is executed. Formal rational controls are not production
CCM spectra, interval certificates, or an independent PAPER audit.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from math import factorial, isqrt
import hashlib
import json
import re
import sys

SHA = 'b3a5f4823019bd3e9464973b3457e7d3e9497241be81e49b0cccbc08099b270a'


def require(ok: bool, text: str) -> None:
    if not ok:
        raise ValueError(text)


def verify_packet(raw: bytes) -> dict:
    require(hashlib.sha256(raw).hexdigest() == SHA, 'packet SHA256')
    require(len(raw) == 160453 and raw.count(b'\n') == 2597, 'packet bytes/LF')
    raw.decode('utf-8')
    head = raw[:raw.index(b'BEGIN S1 ')]
    rx = rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$'
    rows = []
    for i, h in enumerate(re.finditer(rx, head, re.M), 1):
        sid, name, size, lf, sha = h.groups()
        require(int(sid) == i, 'source order')
        op = b'BEGIN S'+sid+b' '+name+b'\n'
        start = raw.index(op)+len(op)
        end = start+int(size)
        body = raw[start:end]
        require(len(body) == int(size) and body.count(b'\n') == int(lf), 'source size/LF')
        require(hashlib.sha256(body).hexdigest().encode() == sha, 'source SHA256')
        require(raw[end:].startswith(b'\nEND S'+sid+b'\n'), 'source closing frame')
        rows.append(dict(id='S'+sid.decode(), name=name.decode(), bytes=len(body),
                         lf=int(lf), sha256=sha.decode()))
    require(len(rows) == 14, 'source count')
    return dict(bytes=len(raw), lf=raw.count(b'\n'), sha256=SHA, sources=rows)


def factor(n: int) -> dict[int, int]:
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def mu(n: int) -> int:
    a = factor(n)
    return 0 if any(k >= 2 for k in a.values()) else (-1)**len(a)


def primes(n: int) -> list[int]:
    return [p for p in range(2, n+1) if factor(p) == {p: 1}]


def addlog(a: dict, b: dict, weight=F(1)) -> dict:
    c = dict(a)
    for p, x in b.items():
        c[p] = c.get(p, F(0))+weight*x
    return {p: x for p, x in c.items() if x}


def arithmetic_controls() -> dict:
    coeff_count = 0
    for n in range(1, 129):
        got = {}
        for d in range(1, n+1):
            if n % d == 0:
                got = addlog(got, factor(n//d), F(mu(d)))
        fn = factor(n)
        want = {next(iter(fn)): F(1)} if len(fn) == 1 else {}
        require(got == want, 'all-power Lambda convolution')
        coeff_count += 1
    local_count = 0
    for p in primes(31):
        for r in range(1, 129):
            require(mu(p*r) == -mu(r)+int(r % p == 0)*mu(r), 'prime-square correction')
            local_count += 1
    amp_count = 0
    detectors = dict(omit_square_correction=False, reverse_main_sign=False,
                     replace_mu_by_absolute=False, square_before_prime_sum=False)
    for N in (8, 17, 32, 65):
        plist = primes(N)
        for mode in (0, 1, 2):
            selected = plist[:min(len(plist), (2, 4, 7)[mode])]
            weights = {p: F((p % 5)+1, p+mode+1) for p in selected}
            H = sum((a/F(p) for p, a in weights.items()), F(0))
            b = {n: F(((-1)**n)*(n*n+3*n+1), n+2) for n in range(1, N+1)}
            omega = {n: sum((a for p, a in weights.items() if n % p == 0), F(0))
                     for n in range(1, N+1)}
            rmax = N//min(selected)
            G = {r: sum((a*b[p*r] for p, a in weights.items() if p*r <= N), F(0))
                 for r in range(1, rmax+1)}
            S = sum((F(mu(n))*b[n] for n in b), F(0))
            main = -sum((F(mu(r))*G[r] for r in G), F(0))
            E = sum((a*mu(r)*b[p*r] for p, a in weights.items()
                     for r in range(1, N//p+1) if r % p == 0), F(0))
            R = sum((mu(n)*(H-omega[n])*b[n] for n in b), F(0))
            require(H*S == main+E+R, 'full amplifier return')
            Q = sum(mu(r)**2 for r in G)
            GG = sum((g*g for g in G.values()), F(0))
            require(main*main <= Q*GG, 'exact Cauchy inequality')
            Ea = sum((a*abs(mu(r)*b[p*r]) for p, a in weights.items()
                      for r in range(1, N//p+1) if r % p == 0), F(0))
            Ra = sum((abs(mu(n)*(H-omega[n])*b[n]) for n in b), F(0))
            deficit = H*S-Ea-Ra
            require(deficit <= 0 or deficit*deficit <= Q*GG, 'one-sided certificate')
            detectors['omit_square_correction'] |= H*S != main+R
            detectors['reverse_main_sign'] |= H*S != -main+E+R
            detectors['replace_mu_by_absolute'] |= S != sum(abs(mu(n))*b[n] for n in b)
            wrongG = sum((a*a*b[p*r]**2 for r in G for p, a in weights.items()
                          if p*r <= N), F(0))
            detectors['square_before_prime_sum'] |= GG != wrongG
            amp_count += 1
    require(all(detectors.values()), 'missed amplifier mutation')
    require(factor(8) != {2: 1}, 'prime-power negative control')
    return dict(lambda_formal_log_cases=coeff_count, prime_square_cases=local_count,
                full_amplifier_cases=amp_count, cauchy_inequalities=amp_count,
                detected=detectors, proper_power_control=True,
                scope='actual mu and formal log(p); arbitrary rational full observables, not physical CCM cells')


def gaussian_add(x, y):
    return (x[0]+y[0], x[1]+y[1])


def contact_controls() -> dict:
    rows = []
    missing = dict(endpoint=False, exponential=False)
    for a in (F(1, 2), F(1, 4), F(1, 8), F(1, 16), F(1, 32)):
        A0 = -F(3, 32)
        A1 = (a*a+F(1, 4))/2
        A2 = -(4*a*a+F(1, 4))/8
        coeff = {0: A0, 1: A1/2, -1: A1/2, 2: A2/2, -2: A2/2}
        require(sum(coeff.values()) == 0, 'endpoint contact')
        for sigma in (F(1, 2), -F(1, 2)):
            z = (F(0), F(0))
            for j, c in coeff.items():
                den = sigma*sigma+j*j*a*a
                z = gaussian_add(z, (c*sigma/den, -c*j*a/den))
            require(z == (0, 0), 'exponential contact rational function')
        norm = A0*A0+(A1*A1+A2*A2)/2
        require(norm > 0, 'positive normalization')
        bad = dict(coeff)
        bad[0] += F(1, 7)
        missing['endpoint'] |= sum(bad.values()) != 0
        sigma = F(1, 2)
        badmoment = sum((c*sigma/(sigma*sigma+j*j*a*a) for j,c in bad.items()), F(0))
        missing['exponential'] |= badmoment != 0
        rows.append(dict(formal_angular_step=str(a), norm_square_divided_by_L=str(norm)))
    require(all(missing.values()), 'missed contact mutation')
    # Exact convolution of the endpoint polynomial q(t)=12*t^2-t^4/4.
    q = {2: F(12), 4: -F(1, 4)}
    J = {}
    for i, a in q.items():
        for j, b in q.items():
            deg = i+j+1
            J[deg] = J.get(deg, F(0))+a*b*F(factorial(i)*factorial(j), factorial(deg))
    require(J == {5: F(24, 5), 7: -F(2, 35), 9: F(1, 10080)}, 'endpoint polynomial')
    require(F(9,1024)+(F(1,64)+F(1,1024))/2 == F(35,2048), 'limiting norm')
    return dict(formal_frequency_cases=rows, endpoint_polynomial={str(k):str(v) for k,v in J.items()},
                limiting_norm_square_divided_by_L='35/2048', mutations_detected=missing,
                scope='formal rational frequencies only; no m=e^(2*pi/a) is asserted to be an integer production cell')


def interval_controls() -> dict:
    count = 0
    for m in (112, 113, 224, 997):
        for r in range((m+7)//8, m//7+1):
            require(F(m,4) <= 2*r <= F(2*m,7), 'two-dilation interval')
            require(F(3*m,8) <= 3*r <= F(3*m,7), 'three-dilation interval')
            require(5*r > F(m,2), 'all higher prime channels vanish')
            require(4*r <= F(4*m,7), 'positive k=2 witness interval')
            count += 1
        for N in (m//4, m//2):
            sqfree = sum(mu(n)**2 for n in range(1,N+1))
            require(4*sqfree >= N, 'squarefree lower control')
    return dict(integer_interval_points=count, squarefree_count_cases=8,
                scope='integer endpoint arithmetic only, not a sparse-band production test')


def main() -> None:
    if len(sys.argv) not in (2, 3):
        raise SystemExit('usage: python3 check_q56.py PACKET.txt [RESULT.json]')
    raw = Path(sys.argv[1]).read_bytes()
    ans = dict(packet=verify_packet(raw), arithmetic=arithmetic_controls(),
               contacts=contact_controls(), endpoints=interval_controls(),
               historical_programs_executed=False, floating_point_mathematics=False,
               lean=False, arb=False, independent_audit=False, production_spectrum=False,
               cofinal_claim_certified_by_computation=False)
    text = json.dumps(ans, ensure_ascii=False, sort_keys=True, indent=2)+'\n'
    out = Path(sys.argv[2] if len(sys.argv) == 3 else 'q56_checks.json')
    out.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
```
END_ASSET

BEGIN_ASSET q56_checks.json
BYTES: 5001
SHA256: e8eff74ff20423442d7947c2f7ba68e10b9290d295b6b10d4355f77faec16f18
```json
{
  "arb": false,
  "arithmetic": {
    "cauchy_inequalities": 12,
    "detected": {
      "omit_square_correction": true,
      "replace_mu_by_absolute": true,
      "reverse_main_sign": true,
      "square_before_prime_sum": true
    },
    "full_amplifier_cases": 12,
    "lambda_formal_log_cases": 128,
    "prime_square_cases": 1408,
    "proper_power_control": true,
    "scope": "actual mu and formal log(p); arbitrary rational full observables, not physical CCM cells"
  },
  "cofinal_claim_certified_by_computation": false,
  "contacts": {
    "endpoint_polynomial": {
      "5": "24/5",
      "7": "-2/35",
      "9": "1/10080"
    },
    "formal_frequency_cases": [
      {
        "formal_angular_step": "1/2",
        "norm_square_divided_by_L": "107/2048"
      },
      {
        "formal_angular_step": "1/4",
        "norm_square_divided_by_L": "47/2048"
      },
      {
        "formal_angular_step": "1/8",
        "norm_square_divided_by_L": "301/16384"
      },
      {
        "formal_angular_step": "1/16",
        "norm_square_divided_by_L": "4561/262144"
      },
      {
        "formal_angular_step": "1/32",
        "norm_square_divided_by_L": "72001/4194304"
      }
    ],
    "limiting_norm_square_divided_by_L": "35/2048",
    "mutations_detected": {
      "endpoint": true,
      "exponential": true
    },
    "scope": "formal rational frequencies only; no m=e^(2*pi/a) is asserted to be an integer production cell"
  },
  "endpoints": {
    "integer_interval_points": 28,
    "scope": "integer endpoint arithmetic only, not a sparse-band production test",
    "squarefree_count_cases": 8
  },
  "floating_point_mathematics": false,
  "historical_programs_executed": false,
  "independent_audit": false,
  "lean": false,
  "packet": {
    "bytes": 160453,
    "lf": 2597,
    "sha256": "b3a5f4823019bd3e9464973b3457e7d3e9497241be81e49b0cccbc08099b270a",
    "sources": [
      {
        "bytes": 4060,
        "id": "S1",
        "lf": 70,
        "name": "CCM_Q55_CONCLUSION.md",
        "sha256": "e8448afbfa7451e4c25bd621d60e3bf8d412b4c158801033427bf9dd1407a5ee"
      },
      {
        "bytes": 1931,
        "id": "S2",
        "lf": 16,
        "name": "CCM_Q55_REVIEW.md",
        "sha256": "77b48b68f858e932ae4b4e406840bb893d5d95c4d7a464783460cf8dfba95d46"
      },
      {
        "bytes": 2415,
        "id": "S3",
        "lf": 38,
        "name": "CCM_POST_Q55_AFFINE_SYMBOL_RETURN.md",
        "sha256": "1a7a2f1edeba63265788df4d66abe5549c331a3096536237a9f45a9694c602c4"
      },
      {
        "bytes": 4273,
        "id": "S4",
        "lf": 74,
        "name": "CCM_POST_Q55_BMO_SUPPLIER_TEST.md",
        "sha256": "a137fe3aaae89edc1f9b1291e8c74244fa375210a3a84ea6f10abaad332a4906"
      },
      {
        "bytes": 2660,
        "id": "S5",
        "lf": 44,
        "name": "CCM_POST_Q55_EXTREMAL_MAP_SCREEN.md",
        "sha256": "4e4a2c79b5589ccf54997699e50b081d315aa3ab8fb04459d2ed4a5685c16bfc"
      },
      {
        "bytes": 2757,
        "id": "S6",
        "lf": 44,
        "name": "CCM_Q07_DISPLACEMENT_PREFLIGHT.md",
        "sha256": "d983a2be3ec1025ce56725bb3a32e021e7e0f4cd3f1625e2f952d9059e83048c"
      },
      {
        "bytes": 9657,
        "id": "S7",
        "lf": 187,
        "name": "CCM_POST_Q52_INNER_KERNEL_PREFLIGHT.md",
        "sha256": "262e9a26b34efc7fc9b412be8916fbbaa47e67a847197b4693344d2a21d23e73"
      },
      {
        "bytes": 7127,
        "id": "S8",
        "lf": 139,
        "name": "CCM_Q15_VAUGHAN_JOINT_BUDGET.md",
        "sha256": "1e13f0487d1a3362817e34112c11953a7296c18bd3500b31995aa221d540bf41"
      },
      {
        "bytes": 10197,
        "id": "S9",
        "lf": 190,
        "name": "CCM_Q20_SELBERG_PAIR_ATTEMPT.md",
        "sha256": "4e4ea8dd3107c7ce9bd1e3d829bc46dfc3406b2f61153bf06a33bd69e3cd977f"
      },
      {
        "bytes": 3927,
        "id": "S10",
        "lf": 70,
        "name": "CCM_POST_Q53_WEIGHTED_CARRIER_PREFLIGHT.md",
        "sha256": "88f78b706bdf435c06c0ca7545b01173cfe407197fd3e84cd6495d0c548212f3"
      },
      {
        "bytes": 3462,
        "id": "S11",
        "lf": 71,
        "name": "CCM_Q09_ATTAINABLE_DENSITY.md",
        "sha256": "24c1f65cc44ef0b0db431f21cd30404946fe5f831f71c4d79ecaad1237dcbf23"
      },
      {
        "bytes": 3796,
        "id": "S12",
        "lf": 66,
        "name": "CCM_POST_Q35_FOURIER_CONCENTRATION_PREFLIGHT.md",
        "sha256": "4756f3d41d128e0ba6dcc784ebfb35ca3cf919c0a62296cb673d4d0e726d85ae"
      },
      {
        "bytes": 6174,
        "id": "S13",
        "lf": 69,
        "name": "CCM_SPARSE_BAND_RECEIVER.md",
        "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06"
      },
      {
        "bytes": 88239,
        "id": "S14",
        "lf": 1377,
        "name": "PROSHKA_CCM_Q55_DIRECT_HILBERT_PERRON_VERDICT_2026-10-27.md",
        "sha256": "03808c77aeb5a79d1a2ad46d479d0e016527e6061c2439601a752e5179d5586a"
      }
    ]
  },
  "production_spectrum": false
}
```
END_ASSET

BEGIN_ASSET replay_q56.py
BYTES: 2822
SHA256: 6f1cfdbea409c40fc91b14b6e67632295cbefe9612b42ef9f8d05286ec5e0555
```python
#!/usr/bin/env python3
"""Replay the four NEW Q56 assets, never historical programs.
Usage: python3 replay_q56.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]
Python 3.9+, standard library only. Exact JSON must match byte for byte.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HEADER = re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n', re.M)
EXPECTED = {'registration_q56.json', 'check_q56.py', 'q56_checks.json', 'replay_q56.py'}


def extract(raw: bytes) -> dict:
    out = {}
    pos = 0
    while True:
        h = HEADER.search(raw, pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name not in EXPECTED or name in out:
            raise ValueError('unexpected or duplicate asset: '+name)
        start, end = h.end(), h.end()+int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]) or hashlib.sha256(body).hexdigest() != h[3].decode():
            raise ValueError('asset bytes/hash: '+name)
        closing = b'```\nEND_ASSET\n'
        if raw[end:end+len(closing)] != closing:
            raise ValueError('asset closing frame: '+name)
        body.decode('utf-8')
        out[name] = body
        pos = end+len(closing)
    if set(out) != EXPECTED:
        raise ValueError('missing asset')
    return out


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q56.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]')
    verdict, packet = (Path(s).resolve() for s in sys.argv[1:3])
    directory = Path(sys.argv[3] if len(sys.argv) == 4 else 'q56_replay').resolve()
    assets = extract(verdict.read_bytes())
    directory.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = directory/name
        if target.resolve() in (verdict, packet):
            raise ValueError('refusing to overwrite an input')
        target.write_bytes(body)
    result = directory/'q56_replayed.json'
    run = subprocess.run([sys.executable, str(directory/'check_q56.py'), str(packet), str(result)],
                         capture_output=True, check=True)
    (directory/'check_q56.stdout').write_bytes(run.stdout)
    if result.read_bytes() != assets['q56_checks.json']:
        raise ValueError('exact replay differs from embedded JSON')
    print(json.dumps(dict(asset_count=4, all_asset_hashes_match=True,
                          new_checker_executed=True, json_byte_identical=True,
                          historical_programs_executed=False,
                          independent_audit=False, production_spectrum=False,
                          interval_certificate=False), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
```
END_ASSET

## 10. Фактический replay и окончательная граница

Все четыре новых приложения извлечены из собранного Markdown с проверкой bytes/SHA-256. Извлечённый новый checker повторно исполнен на неизменённом каноническом Q56 TXT; exact JSON совпал побайтно:

```json
{
  "all_asset_hashes_match": true,
  "asset_count": 4,
  "historical_programs_executed": false,
  "independent_audit": false,
  "interval_certificate": false,
  "json_byte_identical": true,
  "new_checker_executed": true,
  "production_spectrum": false
}
```

Этот replay проверяет доставку и конечные алгебраические контроли, **не** заменяет независимый PAPER-аудит §§3–5 и не сертифицирует cofinal-квантор численным запуском.

**Итог:** нужный full signed upper не получен. Один арифметический ход доведён до полного возврата и до проверяемого опровержения двух его достаточных завершений. Существующая оценка Q55 не улучшена и не ухудшена; RH, исходный all-P bound и возможность другого знакового аргумента остаются открыты.

## Одна CODEX DIRECTIVE

Выполнить **один bounded независимый PAPER-аудит §§2–6 и один replay новых приложений**. Проверять в порядке: полная внутренняя сумма (1.2) и точный край D; знак и prime-square correction (2.2)–(2.4); один и тот же комплексный источник во всех G; принадлежность нормированного пяти-модового профиля исходному P; явный overlap lower (3.6); отсутствие отрицательных активных каналов на I_m; локальный squarefree count и нижнюю оценку полной Cauchy-цены; uniform по неотрицательным весам остаточную плату (5.5), включая её благоприятный исходный знак и расход именно scalar Q55 input; weak trial (6.2), единственные short/arch fees и дополнительную 4 только при переводе A-upper в Psi-return.

Gate успеха: принять **только** finite amplifier identity/inequality, original-P witness и два ровно сформулированных certificate-class obstructions, если материальных ошибок нет; `FULL_SOURCE_GAIN=NONE`, `RETAINED_FULL_POWER=1/2`, `RH=OPEN`. При finding вернуть первую неверную формулу, контррасчёт и минимальный ремонт. Не переносить lower вспомогательной цены на A/T/K, не объявлять все формы BSZ или весь маршрут математически мёртвыми. Затем выполнить указанную выше команду replay и отдельно сообщить `json_byte_identical`. Не запускать следующий вопрос, новые production scans, установку пакетов или запись в репозиторий автоматически. Независимый аудит в данном ответе не выполнялся.
