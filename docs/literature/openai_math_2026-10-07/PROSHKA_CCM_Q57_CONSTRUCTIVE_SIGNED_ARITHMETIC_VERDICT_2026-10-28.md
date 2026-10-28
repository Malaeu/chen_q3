# STATUS: TRY_CCM_Q57_DIRECT_SHORT_INTERVAL_ARITHMETIC
```yaml
OPERATIVE_CLASS: TRY_CCM_Q57_DIRECT_SHORT_INTERVAL_ARITHMETIC
REQUEST_ID: Q57_CONSTRUCTIVE_SIGNED_ARITHMETIC_BEFORE_CAUCHY
DATE: 2026-10-28
LANGUAGE: ru
BASE_COMMIT_AS_DECLARED_IN_PACKET: 1a5e7b2e
PACKET_SHA256: 9325fefed57bfae1b3431c6cce374044d487e14c269176571017185dcffbb047
PACKET_BYTES: 151894
PACKET_LF: 2493
SOURCE_BODIES: 14
MANIFEST: VERIFIED
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_P
SCHEDULE: N=m; L=log(m); M=R=floor(m^epsilon); fixed_0<epsilon<1/32
COGNITIVE_OPERATOR: LITERATURE_BRIDGE
TESTED_INGREDIENT: ACTUAL_MOBIUS_MAXIMAL_SHORT_INTERVAL_CANCELLATION
RESULT: NO_DERIVATION
RESULT_SCOPE: NO_NEW_UPPER_IMPROVING_THE_COMPLETE_RETAINED_BUDGET
WEAK_TRIAL: PAPER_DERIVED_BUT_ASYMPTOTICALLY_DOMINATED_BY_Q55
WEAK_TRIAL_BOUND: 2*(40+16*Omega)*R + C_epsilon_B*sqrt(m)/(log(m))^B
WEAK_TRIAL_QUANTIFIER: EACH_FIXED_B_POSITIVE; ALL_SUFFICIENTLY_LATE_m; ALL_ORIGINAL_P_TESTS
LOCAL_PROGRESS_CLASS: NO_PROGRESS
CONSUMER_PROGRESS: NO_PROGRESS
NEW_USEFUL_PARTIAL_RESULT: NONE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
CERTIFICATE_EXCLUSIONS: NONE
IMPOSSIBILITY_CLAIM: NONE
RETAINED_FULL_POWER: 1/2
ETA_EPSILON_TO_ZERO: NOT_DERIVED
RH: OPEN
PX_RH_CLAIM: NOT_MADE
CF22_PYSR: PARKED
ZF78_GRH_RH_PREMISES: NOT_USED
VERIFIER: PAPER_OWN_DERIVATION_WITH_EXTERNAL_THEOREM_E1_AND_INHERITED_FULL_INNER_BOUND
INDEPENDENT_NEW_AUDIT: NOT_RUN
MATHEMATICAL_COMPUTATION: NOT_RUN
LEAN: NOT_RUN
ARB_INTERVAL: NOT_RUN
PRODUCTION_SPECTRUM: NOT_RUN
HISTORICAL_PROGRAMS_EXECUTED: false
INSTALLATIONS: NONE
REPOSITORY_WRITES: NONE
```

Ы. **Запрошенного улучшения полной знаковой формы нет: `NO_DERIVATION`.** Выполнена одна конструктивная попытка: применить доказанное сокращение **настоящей функции Мёбиуса на коротких интервалах** непосредственно к полной внутренней сумме, не усиливая её простыми и не применяя арифметическую Cauchy-оценку.

Полный перенос удаётся, но даёт только
\[
 \boxed{|A_m[f]|\le s_{\rm SI}(m)\|f\|_2^2,\qquad
 s_{\rm SI}(m)=2(40+16\Omega)R+
 C_{\epsilon,B}\frac{\sqrt m}{(\log m)^B}}
 \tag{0.1}
\]
для **каждого фиксированного** \(B>0\), всех достаточно больших \(m\) и всех исходных \(f\). Все части источника здесь оплачены. Однако (0.1) **асимптотически слабее принятой оценки Q55**, при любом фиксированном \(B\). Поэтому это не полезный partial result в смысле задания и не продвижение потребителя. Ниже — полный расчёт этой попытки и точная неоплаченная строка; новых исключений сертификатов нет.

## 1. Источник и ограниченная проверка отличия от прежних ходов

**[FINITE_CELL | PAPER — проверка доставки].** Прочитан текущий запрос и все S1–S14, включая исторический код как текст. Внешние bytes/LF/SHA-256 и все 14 размерно фиксированных тел совпали. Bootstrap прочитан через GitHub connector из `Malaeu/chen_q3`, ветка `rh_clean`, путь `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`; обе части имеют указанный в заголовке blob. Другие запросы и очереди не выбирались. Репозиторий не изменялся.

Из S1–S4 приняты ровно существующие ограничения: singleton-2 Cauchy не ремонтируется одним знаковым возвратом остатков; это не утверждение о величине полной формы. S5–S9 уже содержат prime-dilation, Vaughan, Selberg, Buchstab и Heath–Brown. S10–S11 не дают арифметической оценки положительного спектрального момента. Их тождества и отрицательные тесты здесь не воспроизводятся как результат.

Отличающийся вход данной проверки — **количественное неравенство для линейных сумм фактической \(\mu\)** из [E1], а не положительность вспомогательной энергии. Тождество \(\Lambda=\mu*\log\) и оценка короткой головы остаются наследуемыми. В предоставленных 14 телах не найдено изложенного ниже короткоинтервального переноса; это ограниченная сверка пакета, **не заявление мировой новизны или отсутствия такого расчёта во всём репозитории**. Проверка [E2] и [E1] — одна короткоинтервальная ветка, не два новых математических опыта.

**[COFINAL_FAMILY | PAPER — исходные определения].** Фиксируем
\[
 0<\epsilon<1/32,\quad L=\log m,\quad M=R=\lfloor m^\epsilon\rfloor,
 \quad \Omega=\frac{2\pi M}{L}.
\]
При \(c=Pc\) берём
\[
 f(t)=L^{-1/2}\sum_{|j|\le M}c_j e^{2\pi ijt/L},\qquad 0\le t\le L,
\]
с **физическим нулевым продолжением**. Все три исходных контакта сохранены. Сначала \(\|f\|_2=1\); общий случай возвращается однородностью. Обозначим
\[
 q_f(s)=2\Re\int_{\mathbb R}\overline{f(t)}f(t+s)\,dt,
 \qquad
 b_f(d)=\sum_{dk\le m}\frac{\log k}{\sqrt{dk}}q_f(\log(dk)).
 \tag{1.1}
\]
Используется существующая точная карта
\[
 A_m[f]=\sum_{d\le m}\mu(d)b_f(d)
       =\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}q_f(\log n).
 \tag{1.2}
\]
Никакие степени простых не удалены. Один и тот же комплексный \(c\) входит во все члены через полную \(q_f\).

## 2. Единственный внешний арифметический вход и его перенос

### 2.1. Точная расходуемая специализация

**[COFINAL_FAMILY | PAPER — внешний theorem import].** Из [E1, Theorem 1.1(i)] при постоянной nilsequence \(F\equiv1\) следует: для каждого фиксированного \(a>0\), при достаточно большом \(D\), \(H=\lfloor\sqrt D\rfloor\), существует измеримое множество \(E_D\subset[D/2,2D]\) такое, что
\[
 |E_D|\le C_aD(\log D)^{-a},                                    \tag{2.1}
\]
а для \(x\in[D/2,2D]\setminus E_D\) и любого интервала последовательных целых \(J\subset(x,x+H]\)
\[
 \left|\sum_{n\in J}\mu(n)\right|
 \le C_aH(\log D)^{-a}.                                       \tag{2.2}
\]
Здесь применена теорема на двух масштабах \(X=D/2,D\). Её параметр диапазона можно фиксировать равным \(1/12\): условие \(X^{5/12}\le H\le X^{11/12}\) выполнено в конечном счёте. Максимальная сумма в теореме берётся по арифметическим прогрессиям внутри окна; последовательные целые и любые их начальные отрезки входят в этот класс. \(F\equiv1\) имеет фиксированную сложность: это **не** исходный меняющийся тест \(f\).

Проверены опубликованное утверждение и определение maximal sum (1.4). Доказательство всей внешней статьи заново не аудировалось. Никакой RH-предпосылки в этот импорт не добавлено.

### 2.2. Взвешенный блок: исключительные интервалы оплачены, а не выброшены

**[ABSTRACT | PAPER — собственный вывод из (2.1)–(2.2)].** Пусть \(w\) абсолютно непрерывна на \([D,2D]\),
\[
 |w|\le W,\qquad |w'|\le K\quad\text{почти всюду}.
\]
Тогда
\[
 \boxed{
 \left|\sum_{D<n\le2D}\mu(n)w(n)\right|
 \le C_aD(\log D)^{-a}(W+HK).}
 \tag{2.3}
\]
Константа в (2.3) может быть увеличена относительно (2.1). Это оценка линейного знакового спаривания, не квадрат его Cauchy-цены.

**Доказательство.** Возьмём сдвинутую сетку
\[
 x_j=D+r+jH,\qquad 0\le r<H,
\]
и окна \((x_j,x_j+H]\), пересекающие \((D,2D]\). Их начала лежат в \((D-H,2D)\subset[D/2,2D]\) для больших \(D\). Число плохих начал обозначим \(N_E(r)\). Перестановка конечной суммы и интеграла даёт
\[
 \int_0^H N_E(r)\,dr
 =|E_D\cap(D-H,2D)|\le |E_D|.
 \tag{2.4}
\]
Следовательно, можно выбрать \(r\) с \(N_E(r)\le |E_D|/H\). Выбор зависит только от \(\mu,D,E_D\), **не от \(w\), \(f\) или экстремального вектора**. Одна такая сетка годится сразу для всех весов с выписанными bounds.

Пересечение каждого окна с \((D,2D]\) — отрезок последовательных целых. В хорошем окне все его частичные суммы \(\mu\) ограничены (2.2). Конечное суммирование Абеля поэтому даёт
\[
 \left|\sum_{n\in J}\mu(n)w(n)\right|
 \le C_aH(\log D)^{-a}\bigl(W+\operatorname{Var}_{\mathrm{hull}(J)}w\bigr)
 \le C_aH(\log D)^{-a}(W+HK).
 \tag{2.5}
\]
В плохом окне используется только \(|\mu(n)|\le1\): его вклад не больше \(HW\). Здесь \(H\) целое, поэтому полуоткрытое окно длины \(H\) содержит ровно \(H\) целых до ограничения на \(J\).

Всего окон не больше \(D/H+2\). Сумма хороших вкладов ограничена \(C_a(D+2H)(\log D)^{-a}(W+HK)\), плохих —
\[
 HN_E(r)W\le |E_D|W\le C_aD(\log D)^{-a}W.
\]

Подставляя \(H\le D\) и увеличивая константу, получаем (2.3). Первое и последнее неполные окна уже учтены: maximal estimate применяется и к их отрезкам. Дополнительного неоплаченного \(HW\) на краях нет. □

**Граница этого шага.** (2.3) не устанавливает благоприятный знак плохих окон. Их полный расход включён. Но главное сокращение в хороших окнах — доказанное арифметическое сокращение настоящей \(\mu\), полученное **до** взятия модулей отдельных арифметических атомов. Никаких независимых фаз или меток вместо \(\mu\) нет.

## 3. Полный исходный вес: оба края и внутренний cutoff

**[COFINAL_FAMILY | PAPER — собственный расчёт на исходных тестах].** Endpoint-контакт делает нулевое продолжение \(f\) элементом \(H^1(\mathbb R)\). Поэтому
\[
 |q_f(s)|\le2,\qquad |q_f'(s)|\le2\|f'\|_2\le2\Omega,
 \qquad q_f(s)=0\quad(s\ge L).
 \tag{3.1}
\]
Это стандартные геометрические bounds автокорреляции. **Cauchy к арифметическому спариванию \(\sum\mu(d)b_f(d)\) здесь не применяется.** Межмодовые члены остаются внутри \(q_f\).

Для вещественного \(u\ge1\) положим
\[
 h_f(u)=
 \begin{cases}
 u^{-1/2}q_f(\log u),&1\le u\le m,\\
 0,&u>m.
 \end{cases}
\]
Поскольку \(q_f(L)=0\), функция непрерывна в \(m\), локально абсолютно непрерывна и
\[
 |h_f'(u)|\le(1+2\Omega)u^{-3/2}
 \quad(1<u<m),\qquad h_f'=0\quad(u>m).
 \tag{3.2}
\]
Продлим **весь внутренний вес**, не исходные арифметические коэффициенты:
\[
 b_f(x)=\sum_{k=2}^{\lfloor m\rfloor}(\log k)h_f(xk),\qquad x\ge1.
 \tag{3.3}
\]
При целых \(x=d\) это ровно (1.1). Сумма конечная; при пересечении \(x=m/k\) соответствующий член равен нулю, поэтому **скачка веса и дельта-вклада в его первую производную нет**. Почти всюду
\[
 b_f'(x)=\sum_{k\le m/x}(\log k)\,k\,h_f'(xk).
 \tag{3.4}
\]
Множитель \(k\) в (3.4) обязателен.

Из \(\sum_{k\le y}k^{-1/2}\le2\sqrt y\) и \(\log k\le L\) получаем
\[
 \boxed{|b_f(x)|\le\frac{4\sqrt m\,L}{x},\qquad
 |b_f'(x)|\le\frac{2(1+2\Omega)\sqrt m\,L}{x^2}.}
 \tag{3.5}
\]
Имеем также \(b_f(x)=0\) при \(x\ge m/2\): при равенстве единственный возможный \(k=2\) даёт верхний нулевой overlap. \(k=1\) всюду имеет коэффициент \(\log1=0\).

Применяя (2.3) к **этому целому \(b_f\)**, на блоке \((D,2D]\) получаем
\[
 \left|\sum_{D<d\le2D}\mu(d)b_f(d)\right|
 \le C_a\frac{\sqrt m\,L}{(\log D)^a}
 \left(1+\frac{(1+2\Omega)H}{D}\right).
 \tag{3.6}
\]
Никакой внутренний \(k\), собственная степень простого или комплексное смешанное слагаемое не удалены из оцениваемой формы.

## 4. Вся сумма и полная цена попытки

### 4.1. Короткая голова уже оплачена существующим входом

**[COFINAL_FAMILY | PAPER — наследуемый S14 §6.1].** На исходном \(P\) имеется
\[
 |b_f(d)|\le\frac{B_m}{\sqrt d},\qquad B_m=40+16\Omega.
 \tag{4.1}
\]
Это старый full-inner-log bound, не новый результат. Введём только для разбиения суммы вспомогательный порог \(D_0=R^2\). Он **не меняет** production \(N=m\), исходные \(M,R\) или проектор. Тогда
\[
 \left|\sum_{d\le R^2}\mu(d)b_f(d)\right|
 \le B_m\sum_{d\le R^2}d^{-1/2}\le2B_mR.
 \tag{4.2}
\]

### 4.2. Длинная часть: без платы числом мод

При достаточно большом \(m\), одновременно \(L\ge8\pi\), \(R\ge2\), и
\[
 1+2\Omega=1+\frac{4\pi R}{L}\le R.
\]

Следовательно, для \(D\ge R^2\) и \(H=\lfloor\sqrt D\rfloor\)
\[
 \frac{(1+2\Omega)H}{D}\le1.
 \tag{4.3}
\]
Разобьём \(d>R^2\) на блоки \((D_j,2D_j]\), \(D_j=2^jR^2\), пока они пересекают \((R^2,m/2)\). Последний блок может выйти за \(m/2\): добавленные члены **точно нулевые** по (3.3), а не отброшены по норме.

Блоков \(O(L)\). При фиксированном \(\epsilon\), в конечном счёте
\(\log D_j\ge2\log R\ge\epsilon L\). Поэтому из (3.6)–(4.3)
\[
 \left|\sum_{R^2<d\le m}\mu(d)b_f(d)\right|
 \le C_{\epsilon,a}\sqrt m\,L^{2-a}.
 \tag{4.4}
\]
Выбираем **фиксированное** \(a=B+2\). С (4.2) это доказывает (0.1), равномерно по всем исходным \(c=Pc\). Начало асимптотики может зависеть от \(\epsilon,B\) и включает onset внешней теоремы. Нет зависимости константы от выбранного \(f\).

Таким образом, попытка действительно оценивает полный источник, а не только преобразованную энергию. Но арифметический результат импорта имеет логарифмическую точность, и она осталась в полном бюджете.

### 4.3. Сравнение с Q55: никакого нового выигрыша

**[COFINAL_FAMILY | PAPER — сравнение доказанных оболочек, не lower источника].** Наследуемая S12 оценка имеет вид
\[
 s_{55}(m)=C\sqrt m\exp\!\left[-c
 \left(\frac{L}{\log(e+L)}\right)^{1/3}\right],
 \qquad A_m\preceq s_{55}P.
 \tag{4.5}
\]
При любом фиксированном \(B>0\)
\[
 \frac{\sqrt m\,L^{-B}}{s_{55}(m)}
 =C^{-1}\exp\!\left[c\left(\frac{L}{\log(e+L)}\right)^{1/3}
                  -B\log L\right]\longrightarrow\infty.
 \tag{4.6}
\]
Кроме того,
\[
 2B_mR=O_\epsilon(m^\epsilon+m^{2\epsilon}/L)=o(s_{55}(m)).
 \tag{4.7}
\]
Следовательно, **именно выписанная** цена (0.1) не улучшает Q55. Из (4.6) не следует нижней оценки \(A_m\), непригодности всех способов использовать [E1] или запрета нужного знака.

Квантор «для каждого фиксированного \(B\)» нельзя заменить \(B=B(m)\) без контроля констант \(C_{\epsilon,B}\) и начала асимптотики. Такой контроль здесь не получен. Обещание произвольной фиксированной логарифмической степени не есть \(m^{o(1)}\) для полной цены с множителем \(\sqrt m\).

## 5. Возврат к T, K и совместному остатку

**[COFINAL_FAMILY | PAPER — наследуемая карта, полный новый trial].** Положим
\[
 b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\]
Для попытки (0.1) все возвраты таковы:
\[
 \boxed{T_{>R}\preceq(s_{\rm SI}+b_{\rm div})P,\qquad
 PK_mP\succeq-(s_{\rm SI}+50L+8)P.}
 \tag{5.1}
\]
Цена головы \(d\le R^2\) **уже внутри** \(s_{\rm SI}\). Дополнительный \(b_{\rm div}\) возникает только при переходе от полного \(A_m\) к исходному \(T_{>R}\), ровно один раз. В direct \(K_m\) его нет. Archimedean fee \(50L+8\) оплачена один раз. Нет новой контурной платы, платы за подъём носителя или второго удаления proper powers.

Если возвращать этот **A-upper** к существующей \(\Psi\)-семье, нужно \(+4\), поскольку он не был доказан сразу для \(A-A_{\rm cont}\):
\[
 R_\tau^\Psi[f]-\Psi_\tau[f]
 \le\left[\frac\tau2(s_{\rm SI}+4)-\tau h_m-1\right]\|f\|_2^2,
 \quad h_m=\sum_{n\le m}\frac{\Lambda(n)}n,\quad\tau>0.
 \tag{5.2}
\]
Все совместные члены остаются внутри точного исходного возврата. (5.2) — не новое тождество и не новый результат о малости кривизны.

**Сохраняется не trial, а прежний лучший бюджет.** Пусть \(s_0=6\sqrt m+6m^{1/4}\). На eventual области Q55 можно взять
\[
 s_{\rm keep}^{A}=\min\{s_{55},s_0\},\qquad
 \boxed{T_{>R}\preceq(s_{\rm keep}^{A}+b_{\rm div})P,
 \quad PK_mP\succeq-(s_{\rm keep}^{A}+50L+8)P.}
 \tag{5.3}
\]
К нему **не прибавляются** расходы этой попытки. Для прямого Q55 bound на \(A-A_{\rm cont}\) дополнительная 4 не нужна; при выборе между ним и fallback допустима цена \(\min\{s_{55},s_0+4\}\) в соответствующем \(\Psi\)-возврате.

Полный показатель остаётся \(1/2\). Неизвестные численные константы/onset ни Q55, ни (0.1) не превращены в finite-cell сертификат. Для отдельно заданной ячейки новый исполняемый upper не поставлен.

## 6. Первая неоплаченная строка и остановка

**[COFINAL_FAMILY | CONDITIONAL — не доказано и не принято как предпосылка].** После законно оплаченной головы (4.2) необходимый для этой попытки новый вход остаётся буквально таким:
\[
 \boxed{
 \sum_{R^2<d\le m}\mu(d)
   \sum_{dk\le m}\frac{\log k}{\sqrt{dk}}q_f(\log(dk))
 \ \stackrel{?}{\le}\ C_\epsilon m^{\theta(\epsilon)}\|f\|_2^2,
 \qquad \theta(\epsilon)\longrightarrow0.}
 \tag{6.1 — UNPAID}
\]
Квантор: каждый фиксированный \(\epsilon\in(0,1/32)\), все достаточно большие **исходные** целые \(m\), все комплексные \(c=Pc\), один и тот же \(f\) во всех членах. Достаточен только верхний знак, не абсолютная норма.

При независимом доказательстве (6.1) голова (4.2), short-return и arch дали бы, например, полный показатель \(\max\{\theta(\epsilon),2\epsilon\}\to0\). Но реально доказана только (4.4), с половинной степенью. **(6.1) — обозначение места остановки, не новая поставленная лемма и не уменьшение математического долга.**

Причина остановки относится к выполненному выводу: арифметическое сокращение в каждом хорошем окне известно лишь с фиксированной логарифмической точностью; плохие окна оплачены на той же точности. Знак между всеми этими вкладами не дал дополнительной оценки. Продолжать менять длину окон, считать новые подпункты или оптимизировать \(B\) без нового количественного входа оснований нет.

Сильнейшее возражение к ответу: «Получен другой полный upper, но он хуже имеющегося». **Верно. Поэтому итог — `NO_DERIVATION`, `NO_PROGRESS`, без полезного partial result.** Это не доказательство невозможности конструктивного арифметического шага и не очередной `KILL` достаточного сертификата.

Документированный возврат — к исходной знаковой форме **до** замены сумм по окнам независимыми модулями. К singleton-2, расширению набора простых и старым положительным энергиям возврата нет.

## 7. Ledger, зависимость и проверяемая граница

| Утверждение | Scope | Verifier | Ровно что заявлено |
|---|---|---|---|
| Целостность Q57 и S1–S14 | FINITE_CELL | PAPER | Байтовая проверка доставки, не проверка математики |
| (2.1)–(2.2) | COFINAL_FAMILY | PAPER | Специализация опубликованной Theorem 1.1(i), [E1] |
| Взвешенный перенос (2.3) | ABSTRACT | PAPER | Собственный вывод; исключения и края оплачены |
| (3.1)–(3.6) | COFINAL_FAMILY | PAPER | Полный исходный вес, общий комплексный тест, без скачка в \(m/k\) |
| Голова (4.2) | COFINAL_FAMILY | PAPER | Расход наследуемого full-inner bound, не новая арифметика |
| (0.1), (5.1)–(5.2) | COFINAL_FAMILY | PAPER | Собственный слабый полный trial; независимого аудита нет |
| Сохранённый (5.3) | COFINAL_FAMILY | PAPER | Наследуемый Q55/fallback, без нового продвижения |
| (6.1) и достаточный cofinal вариант | COFINAL_FAMILY | CONDITIONAL | Не доказаны; не используются как факты |

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_T_UPPER_AND_DIRECT_K_FLOOR
ACTUAL_CONSUMER_REQUIREMENT: eventual_or_proved_sufficient_cofinal_original_P_upper_with_eta_epsilon_to_zero
ORIGINAL_REQUESTED_OBJECT: constructive_full_signed_arithmetic_upper_before_Cauchy
ORIGINAL_OBJECT_IS: NOT_NECESSARY
NECESSITY_QUALIFICATION: uniform_eventual_bound_is_stronger_than_the_owner_allowed_cofinal_variant
METHOD_IS_NECESSARY: false
KNOWN_WEAKER_INTERFACES:
  - direct_A_upper_s_returns_T_upper_s_plus_bdiv_and_K_floor_minus_s_minus_50L_minus_8
  - direct_B_upper_s_for_B_equals_A_minus_Acont_returns_A_upper_s_without_plus_four
  - independently_paid_positive_spectral_moment_can_supply_a_cofinal_cell;_no_such_moment_bound_is_derived
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: bounded_check_of_direct_actual_Mobius_short_interval_arithmetic;_not_global_novelty
CLOSES_AT_REQUESTED_STRENGTH: NONE
OPENS_AS_MANDATORY_NEW_SUPPLIERS: NONE
KILL_SCOPE: NONE
IMPOSSIBILITY_EVIDENCE: NONE
MINIMAL_MISSING_IDENTITY: no_new_identity_required;_the_unpaid_directed_inequality_is_6_1
REOPEN_TRIGGER: independent_signed_arithmetic_control_improving_the_complete_Q55_budget_with_all_complements_paid
ROUTE_SCORE: 2
CONSUMER_PROGRESS: NO_PROGRESS
```

**Две репрезентации при незакрытом результате — без нового задания и без заявления новизны.**

| Представление | Что должно изменить решение | Цена / сила проверки |
|---|---|---|
| Исходное полное \(\sum\mu(d)b_f(d)\), либо его уже оплаченная голова и знаковый хвост (6.1) | Самостоятельная направленная арифметическая оценка, более сильная, чем (4.4) | Карта бесплатна; проверка сохранения коэффициентов дешева, новый знак пока отсутствует. Сильная проверка потери \(k\)-cutoff и общей \(q_f\) |
| Ранее записанный положительный спектральный момент исходных матриц, S10 | Новая арифметическая оценка **всего** положительного момента с движущимся \(P_m\) | Проверка квантора дешева, арифметический вход не оплачен; отсеивает незаконную замену средним матриц или долей ранга |

Это не две выполненные попытки. Никаких больших вычислений ими не разрешается. Связь с другим разделом математики в этом ответе — односторонний перенос короткоинтервальной multiplicative uniformity в (2.3); исчезающего тождества для полного остатка не получено. Объект, который закрыл бы потребителя, остаётся направленной оценкой (6.1), а не ещё одним именем положительной энергии.

**DISCRIMINATOR.** Для заданного бюджета \(s_m\) сохраняется исходный зазор
\[
 \mathcal D_{m,s}(c)=s_m\|c\|^2-A_m[f_c],\qquad c=Pc.
\]
Для PASS нужна нижняя оболочка \(\mathcal D_{m,s}\ge0\) на требуемой семье; для отрицательного заключения о конкретном бюджете — верхняя оболочка \(<0\) на допустимом свидетеле и соответствующий квантор. Новых отрицательных или нулесогласованных численных заключений здесь нет. (0.1) даёт собственный PAPER-upper только на явно указанной слабой шкале.

### Прогнозы и closeout

Регистрация сделана **после чтения источников и предварительных PAPER-оценок, до проверки переноса**; не выдаётся за preregistration поиска идеи. Исполняемых математических тестов не было.

| ID | Прогноз | Судьба |
|---|---|---|
| P1 | Одна арифметическая сетка годится для всех исходных тестов | Подтверждён собственным PAPER-расчётом (2.4); сетка не зависит от \(f\) |
| P2 | Полный inner weight не имеет скачка на \(m/k\); chain-rule factor \(k\) обязателен | Проверено в (3.2)–(3.4) |
| P3 | От данного fixed-log-power входа получаем выписанную цену (0.1), не новый показатель | Выведено в §4. Это не lower цены и не невозможность иных применений [E1] |
| P4 | Полный Q55 budget не улучшен | Проверено сравнением оболочек (4.6), без переноса lower на источник |

Что стало меньше: **ничего на требуемой арифметической шкале**. Что исключено: **ничего нового**. Что не повторять: выдавать фиксированные логарифмические выигрыши, paid transfer или удачную проверку доставки за улучшение Q55. Прежние прогнозы Q56 принимаются только в области S2–S4; нового независимого аудита этих результатов здесь нет.

```yaml
MEMORY_ENTRY:
  iteration: Q57_CONSTRUCTIVE_SIGNED_ARITHMETIC_BEFORE_CAUCHY
  status: OPEN
  cognitive_operator_used: LITERATURE_BRIDGE
  tested_strategy: actual_Mobius_short_interval_cancellation_transferred_to_full_inner_weight
  result: complete_but_dominated_weak_upper
  consumer_progress: NO_PROGRESS
  invariant_learned: exceptional_start_selection_can_be_common_to_all_original_tests_without_a_rank_fee
  smallest_unpaid_input: directed_original_signed_tail_6_1_at_a_useful_scale
  forbidden_future_move: optimize_fixed_log_exponents_as_if_they_improved_Q55_or_claim_a_new_certificate_exclusion
  next_decisive_test: bounded_independent_audit_of_the_transfer_and_its_no_gain_classification
  source_or_route_death: NOT_ESTABLISHED
```

## 8. Источники, вычислительная граница и воспроизведение

**[S1–S14]** — именно тела канонического Q57 TXT, не одноимённые живые файлы неизвестной версии. Для запроса и анти-повторного экрана использованы raw строки 1–111; для существующей singleton-2 границы — S4, строки 198–270; для full-inner bound — S14 §6.1, строки 1702–1732; для Q55 — S12, строки 1140–1209; для receiver — S13, строки 1214–1282. Полные имена, размеры, SHA-256 и raw диапазоны остальных тел приведены в `q57_transport.json` ниже.

**[E1]** Kaisa Matomäki, Maksym Radziwiłł, Xuancheng Shao, Terence Tao, Joni Teräväinen, *Higher uniformity of arithmetic functions in short intervals II. Almost all intervals*, **Inventiones mathematicae 244 (2026), 967–1091**, DOI `10.1007/s00222-026-01408-6`. Расходуется только Theorem 1.1(i), специализация \(F\equiv1\), и определение (1.4). Проверен первичный опубликованный HTML. Никакая степенная оценка для другой арифметической функции не переносится на \(\mu\).

**[E2]** Kaisa Matomäki, Maksym Radziwiłł, *Multiplicative functions in short intervals*, **Annals of Mathematics 183 (2016), 1015–1056**, DOI `10.4007/annals.2016.183.3.6`. Просмотрены Theorems 1–2 на печатных страницах 1015–1016, включая изображения страниц PDF. Это начальный источник при проверке короткоинтервальной ветки; в доказательстве (0.1) расходуется более удобный maximal input [E1], а не неявное усиление [E2].

```text
E1: https://link.springer.com/article/10.1007/s00222-026-01408-6
E2: https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf
```

**Исполнение.** Запущена только новая стандартно-библиотечная проверка bytes/LF/SHA-256 и рамок исходного пакета. Она не вычисляет \(\mu\), source spectrum, знаковые суммы, интервальные bounds или нули. Исторические программы не исполнялись. Нет установки пакетов, Lean, Arb, независимого PAPER-аудита или подтверждённого нового finite-cell результата.

Ниже весь новый исполняемый код и его полный детерминированный вывод, а также точная регистрация. Чтобы повторить **только проверку доставки**, сохрани `verify_q57_transport.py` из блока и запусти:

```bash
python3 verify_q57_transport.py \
  PROSHKA_CCM_CONSTRUCTIVE_SIGNED_ARITHMETIC_Q57_2026-10-28.txt \
  q57_transport.json
```

Первый аргумент — неизменённый исходный TXT; второй — создаваемый JSON. При другом расположении замени только путь, например `./requests/PROSHKA_CCM_CONSTRUCTIVE_SIGNED_ARITHMETIC_Q57_2026-10-28.txt`. Никакого математического PASS из успешного выполнения этой команды не следует.


BEGIN_ASSET registration_q57.json
BYTES: 1401
SHA256: 1f4c30401d8916cad313b5051ddc7eba37120f1c84b353a5459fc24b72f04c52
```json
{
  "candidate": "Actual Mobius short-interval maximal cancellation, shifted-partition selection independent of the source test, full inner log-sum weight retained",
  "historical_programs_executed": false,
  "independent_audit": false,
  "mathematical_computation_planned": false,
  "operator": "LITERATURE_BRIDGE",
  "packet_sha256": "9325fefed57bfae1b3431c6cce374044d487e14c269176571017185dcffbb047",
  "predictions": {
    "P1": "A single arithmetic-dependent shifted partition controls all original source tests; no eigenvector-dependent exceptional-set selection is needed.",
    "P2": "The moving hyperbolic edge contributes no jump to the full inner weight because the physical top overlap is zero; its derivative still carries the chain-rule factor k.",
    "P3": "The complete imported fixed-log-power input returns at best the derived allowance 2*(40+16*Omega)*R + C_epsilon_B*sqrt(m)/(log m)^B for every fixed B>0, not a new power saving.",
    "P4": "That allowance does not improve the inherited Q55 envelope; no useful partial result or source/certificate impossibility is to be claimed."
  },
  "repository_writes": false,
  "stage": "After complete packet reading, external statement verification and preliminary PAPER estimates; before validation of the weighted-block transfer. Not preregistration of idea discovery.",
  "task": "Q57_CONSTRUCTIVE_SIGNED_ARITHMETIC_BEFORE_CAUCHY"
}
```
END_ASSET

BEGIN_ASSET verify_q57_transport.py
BYTES: 3344
SHA256: b4f48e01f5c2b8cc429b4135dbcd8f9ef60733070738bd6f830ee521ec5b90a7
```python
#!/usr/bin/env python3
"""Verify Q57 request bytes and its 14 source frames; no mathematical code.
Usage: python3 verify_q57_transport.py PACKET.txt [OUTPUT.json]
Python 3.9+ standard library only. Does not execute any embedded source.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

SHA = '9325fefed57bfae1b3431c6cce374044d487e14c269176571017185dcffbb047'
SIZE, LF = 151894, 2493
NAME = 'PROSHKA_CCM_CONSTRUCTIVE_SIGNED_ARITHMETIC_Q57_2026-10-28.txt'
HEADER = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify(raw: bytes) -> dict:
    require(len(raw) == SIZE, 'outer size')
    require(raw.count(b'\n') == LF, 'outer LF')
    require(hashlib.sha256(raw).hexdigest() == SHA, 'outer SHA256')
    raw.decode('utf-8')
    require(b'\r' not in raw, 'unexpected CR')
    require(raw.startswith(b'REQUEST_ID: Q57_CONSTRUCTIVE_SIGNED_ARITHMETIC_BEFORE_CAUCHY\n'), 'request ID')
    pos = raw.index(b'BEGIN S1 ')
    headers = list(HEADER.finditer(raw[:pos]))
    require(len(headers) == 14, 'source count')
    rows = []
    for number, match in enumerate(headers, 1):
        sid, name, size, lf, sha = match.groups()
        require(int(sid) == number, 'source order')
        opening = b'BEGIN S' + sid + b' ' + name + b'\n'
        require(raw[pos:pos+len(opening)] == opening, 'source opening')
        start = pos + len(opening)
        end = start + int(size)
        body = raw[start:end]
        body.decode('utf-8')
        require(len(body) == int(size), 'source size')
        require(body.count(b'\n') == int(lf), 'source LF')
        require(hashlib.sha256(body).hexdigest().encode() == sha, 'source SHA256')
        closing = b'\nEND S' + sid + b'\n'
        require(raw[end:end+len(closing)] == closing, 'source closing')
        rows.append(dict(id='S'+sid.decode(), name=name.decode(), bytes=len(body),
                         lf=int(lf), sha256=sha.decode(),
                         start_line=raw[:start].count(b'\n')+1,
                         end_line=raw[:end].count(b'\n')))
        pos = end + len(closing)
        if number < len(headers):
            require(raw[pos:pos+1] == b'\n', 'inter-frame separator')
            pos += 1
    require(pos == len(raw), 'trailing bytes')
    return dict(packet=NAME, bytes=SIZE, lf=LF, sha256=SHA,
                source_count=len(rows), all_frames_verified=True, sources=rows,
                historical_programs_executed=False,
                mathematical_computation=False, independent_audit=False,
                lean=False, arb_interval=False, production_spectrum=False)


def main() -> None:
    if len(sys.argv) not in (2, 3):
        raise SystemExit('usage: python3 verify_q57_transport.py PACKET.txt [OUTPUT.json]')
    packet = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2] if len(sys.argv) == 3 else 'q57_transport.json').resolve()
    require(packet != output, 'refusing to overwrite the input')
    result = verify(packet.read_bytes())
    text = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2)+'\n'
    output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
```
END_ASSET

BEGIN_ASSET q57_transport.json
BYTES: 3930
SHA256: e85d67741477b7fe3479bbde02da143551e9f9fb1415ffbee23588b63e0b2c6a
```json
{
  "all_frames_verified": true,
  "arb_interval": false,
  "bytes": 151894,
  "historical_programs_executed": false,
  "independent_audit": false,
  "lean": false,
  "lf": 2493,
  "mathematical_computation": false,
  "packet": "PROSHKA_CCM_CONSTRUCTIVE_SIGNED_ARITHMETIC_Q57_2026-10-28.txt",
  "production_spectrum": false,
  "sha256": "9325fefed57bfae1b3431c6cce374044d487e14c269176571017185dcffbb047",
  "source_count": 14,
  "sources": [
    {
      "bytes": 3616,
      "end_line": 111,
      "id": "S1",
      "lf": 57,
      "name": "CCM_POST_Q56_CONSTRUCTIVE_PREFLIGHT.md",
      "sha256": "d67aa589d8c36971c7e6fe4fd65c028d01ac36c581575c3174e4d552c98be35a",
      "start_line": 55
    },
    {
      "bytes": 3777,
      "end_line": 174,
      "id": "S2",
      "lf": 59,
      "name": "CCM_Q56_CONCLUSION.md",
      "sha256": "d0ff17dde15453377584efb502f462e803d8f631a0b8b46f3a7054be9015770c",
      "start_line": 116
    },
    {
      "bytes": 1463,
      "end_line": 193,
      "id": "S3",
      "lf": 15,
      "name": "CCM_Q56_REVIEW.md",
      "sha256": "55754cd6c7ee738f33b2b72699f213b3b421044eeea8af484dc1c57ceeda7d12",
      "start_line": 179
    },
    {
      "bytes": 4017,
      "end_line": 270,
      "id": "S4",
      "lf": 73,
      "name": "CCM_POST_Q56_SIGNED_RESIDUAL_TEST.md",
      "sha256": "7d77c6f1d377bd54a31a3fe3cf4898096a3db510a71db1205adca184dd94f9f0",
      "start_line": 198
    },
    {
      "bytes": 4706,
      "end_line": 363,
      "id": "S5",
      "lf": 89,
      "name": "CCM_Q39_CONCLUSION.md",
      "sha256": "bd1f0d1c19b4a461a6e87a11b0a882be0f8641d6c4284c59e697a4c9dcd53f72",
      "start_line": 275
    },
    {
      "bytes": 7127,
      "end_line": 506,
      "id": "S6",
      "lf": 139,
      "name": "CCM_Q15_VAUGHAN_JOINT_BUDGET.md",
      "sha256": "1e13f0487d1a3362817e34112c11953a7296c18bd3500b31995aa221d540bf41",
      "start_line": 368
    },
    {
      "bytes": 10197,
      "end_line": 700,
      "id": "S7",
      "lf": 190,
      "name": "CCM_Q20_SELBERG_PAIR_ATTEMPT.md",
      "sha256": "4e4ea8dd3107c7ce9bd1e3d829bc46dfc3406b2f61153bf06a33bd69e3cd977f",
      "start_line": 511
    },
    {
      "bytes": 3118,
      "end_line": 761,
      "id": "S8",
      "lf": 57,
      "name": "CCM_POST_Q42_MULTISCALE_SCREEN.md",
      "sha256": "4cb686fe44063d054d1a872b730a36270e200a75be16f63b8868dfa833d871bb",
      "start_line": 705
    },
    {
      "bytes": 3775,
      "end_line": 827,
      "id": "S9",
      "lf": 62,
      "name": "CCM_Q49_CONCLUSION.md",
      "sha256": "9ae098f310c8a1f82fe425e9f5a5d526614d6458d6918147850bc22e15a0bafe",
      "start_line": 766
    },
    {
      "bytes": 5138,
      "end_line": 944,
      "id": "S10",
      "lf": 113,
      "name": "CCM_COFINAL_MOMENT_BUDGET_2026-10-20.md",
      "sha256": "7a5589467f088ddfdf7ba2f3fdbf4ce24da1d5108233f68f6d6e991819e824e7",
      "start_line": 832
    },
    {
      "bytes": 9657,
      "end_line": 1135,
      "id": "S11",
      "lf": 187,
      "name": "CCM_POST_Q52_INNER_KERNEL_PREFLIGHT.md",
      "sha256": "262e9a26b34efc7fc9b412be8916fbbaa47e67a847197b4693344d2a21d23e73",
      "start_line": 949
    },
    {
      "bytes": 4060,
      "end_line": 1209,
      "id": "S12",
      "lf": 70,
      "name": "CCM_Q55_CONCLUSION.md",
      "sha256": "e8448afbfa7451e4c25bd621d60e3bf8d412b4c158801033427bf9dd1407a5ee",
      "start_line": 1140
    },
    {
      "bytes": 6174,
      "end_line": 1282,
      "id": "S13",
      "lf": 69,
      "name": "CCM_SPARSE_BAND_RECEIVER.md",
      "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
      "start_line": 1214
    },
    {
      "bytes": 77096,
      "end_line": 2491,
      "id": "S14",
      "lf": 1205,
      "name": "PROSHKA_CCM_Q56_PRIME_DILATION_VERDICT_2026-10-27.md",
      "sha256": "31013fd008dca72c607b7d8c6c8cf803f5656ada048555eecdcbbfb2b265b4b1",
      "start_line": 1287
    }
  ]
}
```
END_ASSET

## 9. Граница воспроизведения

Три встроенных приложения проверены по размерам и SHA-256 после сборки Markdown. Извлечённый `verify_q57_transport.py` повторно выполнен только на исходном Q57 TXT; его JSON совпал со встроенным **побайтно**. Это проверяет **доставку и неизменность источников**, а не (2.3), (0.1), асимптотический знак или импорт [E1]. Математического replay в этом ответе нет, потому что численные математические тесты не проводились.

**Окончательный вывод:** (0.1) — законченная собственная PAPER-попытка с внешним арифметическим входом и полным возвратом. Она не улучшает сохранённый budget. Запрошенный новый конструктивный результат не получен: **`NO_DERIVATION`**. RH и исходная знаковая задача остаются открыты; независимого аудита нового расчёта ещё нет.

## Одна CODEX DIRECTIVE

Выполнить один ограниченный независимый PAPER-аудит §§2–5, **без автоматического следующего опыта**. Проверить специализацию [E1, Theorem 1.1(i)] на двух масштабах и maximal-prefix квантор; интегральный выбор сдвига (2.4), независимый от исходного теста; оплату всех плохих и обоих неполных окон; непрерывность полного веса на каждом \(m/k\), множитель \(k\) в (3.4); обе константы (3.5); порог \(R^2\), неизменность production schedule и полную цену (0.1). Затем проверить сравнение именно оболочек (4.6), single short/arch return и \(+4\) только в trial A-to-Psi. При необходимости выполнить только приведённую транспортную команду; исторические программы не запускать.

Gate: вернуть `WEAK_TRIAL_VALID` либо первую `MATERIAL_FINDING` с минимальным ремонтом. При отсутствии ошибки принять **только более слабый полный upper**, сохранив `REQUESTED_RESULT=NO_DERIVATION`, `CONSUMER_PROGRESS=NO_PROGRESS`, `RETAINED_FULL_POWER=1/2`, `RH=OPEN`. Успешный аудит или hash-check не повышает этот ответ до полезного partial result. Не создавать новый обязательный supplier из (6.1), не считать проверку двух первичных публикаций двумя новыми механизмами, не расширять singleton-2 obstruction, не запускать production spectrum, установку пакетов или репозиторную запись.
