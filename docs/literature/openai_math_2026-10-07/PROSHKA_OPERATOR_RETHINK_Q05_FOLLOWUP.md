# STATUS: TRY_Q05_MOBIUS_ANNIHILATOR_AND_SOURCE_NULL_CORRECTION
```yaml
OPERATIVE_CLASS: TRY_Q05_MOBIUS_ANNIHILATOR_AND_SOURCE_NULL_CORRECTION
ARTIFACT_KIND: STRATEGIC_MATHEMATICAL_FOLLOWUP
QUESTION_INDEX: Q05_FOLLOWUP_NOT_Q06
REQUEST_BASIS: PROSHKA_RATIONAL_HIGH_VALUES_Q05.txt
REQUEST_SHA256: 04569d150a39475d0e16dcc5a08e61fda25e1b338d9b76cf5ce58c6424902581
FOLLOWUP: "Искать нужно оператор, который заставляет настоящие коэффициенты сокращаться совместно"
PROTOCOL_REPOSITORY: Malaeu/chen_q3
PROTOCOL_BRANCH: rh_clean
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
route_id: RH_SOURCE_ARITHMETIC
front_id: COMPENSATED_JOINT_LOW_PROBE
source_object_family_id: OPENAI_003_COMPLETE_CUBIC_THETA_PROBE
terminal_consumer_id: COMMON_SIGNAL_ZERO_FREE_TO_CRITICAL_LINE
honesty_state: CHALLENGER_NOT_RH
convention_lock_id: OPENAI_ADC7F124_FIXED_DATA_ALL_ZERO_MASKS
PRIMARY_FINDING: EXACT_SOURCE_ANNIHILATORS_EXIST_BUT_QUANTITATIVE_CORRECTOR_NOT_CONSTRUCTED
EXACT_OPERATOR: "A_p = valuation_p + convolution_by_all_positive_p_powers"
EXACT_SOURCE_RELATION: A_p_mu_EQUALS_ZERO
JOINT_CORRECTOR: SUM_p_OF_A_p_ADJOINT_Y_p_PLUS_Y_p_ADJOINT_A_p
JOINT_CORRECTOR_SOURCE_ENERGY: EXACTLY_ZERO
LONG_j_C_RELATION: INHOMOGENEOUS_CUTOFF_COMMUTATOR_NOT_ZERO
WORKED_MULTIPLIER: MINUS_ONE_HALF_D_DAGGER_G
WORKED_MULTIPLIER_OUTCOME: EXACT_PRIME_POWER_DESCENT_WITH_NO_PROVED_GAIN
FIRST_UNPAID_TERM: SOURCE_WEIGHTED_JOINT_DESCENT_GRAM_OR_EQUIVALENT_PSD_REMAINDER
FULL_Q05_BOUND_PROVED: false
MB34_PROVED: false
NEW_INVERSE_POWER_GAIN_PROVED: false
NEW_HIGH_POWER_GAIN_PROVED: false
SOURCE_P_M_R_AND_HIGH_TRANSPORT: CONDITIONAL_UNCHANGED
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PROGRESS_SCOPE: EXPLICIT_SOURCE_CONSTRAINTS_AND_EXACT_ADJOINT_CORRECTION_ONLY
FULL_CONSUMER_PROGRESS: NO_NEW_POWER_GAIN
COGNITIVE_OPERATOR: DUALIZE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
ROUTE_SCORE: 3
ROUTE_FAMILY_KILL: NONE
TARGET_COUNTEREXAMPLE: NONE
RH: OPEN
SP: OPEN
PX_RH_CLAIM: NOT_MADE
REPOSITORY_WRITES: NONE
LEAN_ARB_COMPARATOR_RUNS: NONE
```

## 1. Что изменено в предыдущем предложении

**Само выражение «два эйлеровых канала» ещё не задаёт механизма выигрыша.** Разность двух произведений на грубой подсемье описывает некоторые коэффициенты, но не оценивает полный исходный функционал. Поэтому здесь не продолжается рассуждение «домножить рациональный вес и считать, что сокращение получено».

Различаются три операции:

1. **Аннулировать арифметический источник:** найти явное линейное соотношение между настоящими коэффициентами. Такое соотношение ниже действительно выписано.
2. **Сохранить исходную энергию:** использовать это соотношение как нулевую квадратичную поправку, а не заменять целевую энергию энергией преобразованного вектора без обратного контроля.
3. **Получить количественную верхнюю оценку:** построить поправку с доказанным положительным остатком в нужном бюджете. Это третье действие здесь не выполнено.

**Результат:** есть точные операторы, которые одновременно учитывают знак Мёбиуса, все простые степени и все исходные фазы. Для простейшего выбранного корректора выполнен расчёт; он возвращает совместную простостепенную корреляцию, не новый показатель. Полная оценка Q5/MB.34 остаётся открытой. Это не контрпример к цели.

Данный текст — математическое уточнение пользовательского предложения после Q5, не новый вопрос 6/10 и не замена авторитетного TXT.

## 2. Источники и неизменённая задача

**[ABSTRACT; PAPER — фиксация данных].** Основание — первые 37 строк `PROSHKA_RATIONAL_HIGH_VALUES_Q05.txt`, SHA-256 в заголовке. Проверен локальный файл запроса. Из прежнего ответа Q5 использованы его заявленная граница доказанности и разложение RF.1–RF.2, а не предполагаемая новая оценка RF.20. Локальная копия этого ответа имеет SHA-256 `c159b3ccc916550143032db58dbaeac2bbc3941dd8f1f71534d52c4d5dd531fe`.

Протокол получен заново через GitHub-коннектор. Никаких репозиторных изменений нет. Не утверждается новый полный аудит аналитических доказательств вложенного манускрипта.

Стандартная основа — **делительная свёртка** и обращение Мёбиуса: NIST DLMF §27.5, формулы 27.5.1–27.5.2; область обычного эйлерова произведения и обратного ряда — §27.4, формулы 27.4.3–27.4.5. Ниже переход к хорошим идеалам и все конечные операторные равенства доказываются непосредственно. Внешний источник не используется как поставщик моментной оценки.

Сохраняются
\[
 r\in[28/25,113/100],\quad c_0=1/10000,\quad
 D=U^r,\quad H=D^{1+c_0},\quad
 p=\frac{r(1+c_0)-1}{6},\quad P=U^p,
\]
\[
 DU^{-1/100}\le L\le D,\qquad \eta=1/200.
\]

Работаем непосредственно с исходным **Мёбиусовым полиномом**
\[
 M_u^{[a]}(L;W)=L^{-1/2}\sum_{n\ \mathrm{good}}
 \mu(n)\nu(n)\chi_n(u)^{\varepsilon_\chi}
 1_{(n,a)=1}W(q_n/L).
 \tag{O.1}
\]

Его полная положительная энергия
\[
 \mathcal E_M=\sum_{\substack{a\ \mathrm{good}\\q_a\le P}}
 \sum_{u^{(6)}}\rho(q_u/U)|M_u^{[a]}(L;W)|^2
 \tag{O.2}
\]
является допустимым прямым входом для прежнего MB.34. Это **обход вспомогательного рационального представления**, разрешённый Q5, а не подстановка \(M\) вместо \(J_C\) внутри определения \(Q_b\).

Все элементные строки, шесть единиц, S-показатели, общие простые \(u,a\), оба направления символа и все нулевые ветви остаются. Аналитические цены P/M/R и высокий перенос остаются **[COFINAL_FAMILY; CONDITIONAL]**.

## 3. Явный локальный аннулятор настоящего Мёбиуса

### 3.1. Конечная область, замкнутая относительно делителей

**[ABSTRACT; PAPER].** Пусть \(\operatorname{supp}W\subset[\alpha,\beta]\Subset(0,\infty)\). Возьмём \(X\ge\beta D\) и конечное множество хороших идеалов
\[
 \mathcal I_X=\{n:q_n\le X\}.
\]
Оно содержит каждый делитель каждого своего элемента. Вектор
\(\boldsymbol\mu=(\mu(n))_{n\in\mathcal I_X}\) включает координаты простых квадратов и всех более высоких степеней. Их нулевые значения не означают удаления соответствующих координат.

Для хорошего простого идеала \(\mathfrak p\) определим
\[
 (\mathcal D_{\mathfrak p}f)(n)=v_{\mathfrak p}(n)f(n),
 \qquad
 (\mathcal B_{\mathfrak p}f)(n)=
 \sum_{k=1}^{v_{\mathfrak p}(n)} f(n/\mathfrak p^k),
\]
\[
 \boxed{\mathcal A_{\mathfrak p}=\mathcal D_{\mathfrak p}+\mathcal B_{\mathfrak p}.}
 \tag{O.3}
\]

Первый член учитывает кратность простого. Второй суммирует **все положительные простые степени**, делящие текущую колонку.

### 3.2. Точное сокращение

\[
 \boxed{\mathcal A_{\mathfrak p}\boldsymbol\mu=0
 \quad\text{для каждого хорошего }\mathfrak p.}
 \tag{O.4}
\]

**Доказательство.** Пишем \(n=\mathfrak p^a m\), \((m,\mathfrak p)=1\).

При \(a=0\) оба члена нулевые. При \(a=1\) имеем
\(\mu(\mathfrak p m)+\mu(m)=0\).
При \(a\ge2\) первый член нулевой; в сумме возможны только последние два ненулевых члена
\(\mu(\mathfrak p m)+\mu(m)=0\). Если \(m\) сам не бесквадратен, оба они также нулевые. Это покрывает все идеалы. ∎

Например,
\[
 (\mathcal A_{\mathfrak p}\mu)(\mathfrak p\mathfrak q)=1-1=0,
\]
\[
 (\mathcal A_{\mathfrak p}\mu)(\mathfrak p^2\mathfrak q)
 =0+1-1=0.
\]
Удаление \(k\ge2\) уже при \(n=\mathfrak p^2\) даёт \(-1\), а не нуль.

Это классическое арифметическое соотношение, записанное в нужной операторной форме; оно **не объявляется новым открытием**.

### 3.3. Фазы и нули сохраняются без деления на характер

Для фактической строки и маски положим
\[
 \psi_{u,a}(n)=\nu(n)\chi_n(u)^{\varepsilon_\chi}1_{(n,a)=1},
 \qquad f_{u,a}(n)=\mu(n)\psi_{u,a}(n).
\]
Тогда
\[
 (\mathcal A_{\mathfrak p}^{u,a}f)(n)=
 v_{\mathfrak p}(n)f(n)+
 \sum_{k=1}^{v_{\mathfrak p}(n)}
       \psi_{u,a}(\mathfrak p)^k f(n/\mathfrak p^k)
\]
удовлетворяет
\[
 \boxed{\mathcal A_{\mathfrak p}^{u,a}f_{u,a}=0.}
 \tag{O.5}
\]
Действительно, полная мультипликативность с нулевыми ветвями выносит в каждом слагаемом один и тот же \(\psi_{u,a}(n)\), после чего действует (O.4). При \(\psi_{u,a}(\mathfrak p)=0\) формула тоже верна. Обратный символ не вводится.

### 3.4. Эти соотношения действительно выделяют источник

Операторы разных простых коммутируют: изменение показателя \(\mathfrak q\ne\mathfrak p\) не меняет \(v_{\mathfrak p}\), а соответствующие делительные сдвиги коммутируют.

Более существенно,
\[
 \bigcap_{q_{\mathfrak p}\le X}\ker\mathcal A_{\mathfrak p}
 =\operatorname{span}\{\boldsymbol\mu\}.
 \tag{O.6}
\]
Чтобы это проверить, сложим (O.3) с положительными весами \(\log q_{\mathfrak p}\). Получится
\[
 \mathcal A=\mathcal D+\mathcal C_\Lambda,
\]
\[
 (\mathcal Df)(n)=\log q_n\,f(n),\quad
 (\mathcal C_\Lambda f)(n)=\sum_{d\mid n}\Lambda_F(d)f(n/d),
\]
где \(\Lambda_F(\mathfrak p^k)=\log q_{\mathfrak p}\) при \(k\ge1\), а на остальных идеалах она равна нулю. После значения \(f(1)\) уравнение \(\mathcal Af=0\) последовательно определяет каждую координату \(q_n>1\), поскольку её диагональный коэффициент \(\log q_n\) положителен. Вектор \(f(1)\boldsymbol\mu\) удовлетворяет системе, значит, решение единственно. ∎

Следовательно, это не условие для свободного коэффициентного вектора: вместе с \(\mu(1)=1\) система задаёт именно исходный Мёбиус.

## 4. Почему тот же оператор нельзя молча применить к длинному j_C

**[ABSTRACT; PAPER].** Положим \(\mu_2=\mu*\mu\), а \(\mathcal P_C\) пусть означает умножение коэффициента на \(1_{q_n\le C}\). Тогда
\[
 j_C=\mu-(\mathcal P_C\mu_2)*\mathbf1.
\]
Здесь \(\mathbf1(n)=1\); это не единичный вектор \(e_1\).

Точное равенство имеет вид
\[
 \boxed{
 \mathcal A_{\mathfrak p}j_C
 =-2\bigl([\mathcal B_{\mathfrak p},\mathcal P_C]\mu_2\bigr)*\mathbf1,
 \qquad [B,P]=BP-PB.
 }
 \tag{O.7}
\]

**Доказательство.** Делительная свёртка удовлетворяет правилу
\(\mathcal D_{\mathfrak p}(f*g)=(\mathcal D_{\mathfrak p}f)*g+f*(\mathcal D_{\mathfrak p}g)\).
Из (O.4) и \(\mu_2=\mu*\mu\) получаем
\(\mathcal D_{\mathfrak p}\mu_2=-2\mathcal B_{\mathfrak p}\mu_2\).
Кроме того, \(\mathcal D_{\mathfrak p}\mathbf1=\mathcal B_{\mathfrak p}\mathbf1\), а \(\mathcal D_{\mathfrak p}\) коммутирует с \(\mathcal P_C\). Поэтому
\[
 \mathcal A_{\mathfrak p}((\mathcal P_C\mu_2)*\mathbf1)
 =2\bigl((\mathcal B_{\mathfrak p}\mathcal P_C-
           \mathcal P_C\mathcal B_{\mathfrak p})\mu_2\bigr)*\mathbf1.
\]
Вычитаем это из (O.4). ∎

Сам граничный коэффициент равен
\[
 ([\mathcal B_{\mathfrak p},\mathcal P_C]\mu_2)(n)
 =\sum_{k=1}^{v_{\mathfrak p}(n)}\mu_2(n/\mathfrak p^k)
 \left(1_{q_n/q_{\mathfrak p}^k\le C}-1_{q_n\le C}\right).
 \tag{O.8}
\]
Он поддержан на переходах через настоящий отсекатель, сохраняет равенство \(q_n=C\) в короткой части и все степени \(k\).

При \(q_{\mathfrak p}>C\ge1\)
\[
 j_C(1)=0,\quad j_C(\mathfrak p)=-2,\quad
 j_C(\mathfrak p^2)=-1,
\]
\[
 (\mathcal A_{\mathfrak p}j_C)(\mathfrak p)=-2,\qquad
 (\mathcal A_{\mathfrak p}j_C)(\mathfrak p^2)=-4.
\]
Поэтому объявление \(\mathcal A_{\mathfrak p}j_C=0\) неверно. Оплаченная прежняя энергия короткого полинома сама по себе не оплачивает его образ под новым оператором: такой ограниченности не доказано.

Это конкретная причина предпочесть здесь прямую исходную (O.2), а не насильно переносить аннулятор на вспомогательный \(j_C\).

## 5. Как применить аннулятор именно к совместной энергии

### 5.1. Одна общая матрица со всеми строками и усилителями

Определим
\[
 t_{u,a}(n)=L^{-1/2}\nu(n)\chi_n(u)^{\varepsilon_\chi}
             1_{(n,a)=1}W(q_n/L),
\]
\[
 G_{n,m}=\sum_{\substack{a\ \mathrm{good}\\q_a\le P}}
         \sum_{u^{(6)}}\rho(q_u/U)
                    \overline{t_{u,a}(n)}t_{u,a}(m).
 \tag{O.9}
\]
Это **матрица Грама** — матрица попарных произведений истинных колонок. Точно
\[
 G\succeq0,\qquad
 \boxed{\mathcal E_M=\boldsymbol\mu^*G\boldsymbol\mu.}
 \tag{O.10}
\]

Раскрытая версия сохраняет исходный арифметический множитель:
\[
 G_{n,m}=\frac{\overline{\nu(n)W(q_n/L)}\nu(m)W(q_m/L)}L
 w_P(nm)\sum_{u^{(6)}}\rho(q_u/U)
          \overline{\chi_n(u)^{\varepsilon_\chi}}
                         \chi_m(u)^{\varepsilon_\chi},
\]
\[
 w_P(nm)=\#\{a\ \mathrm{good}:q_a\le P,\ (a,nm)=1\}.
 \tag{O.11}
\]

Здесь \(w_P\) — точный счёт исходных усилителей, не заменённый плотностью. Это не сжатый \(w_{P,Y}(b)\) Q5; мы вернулись к исходным \((u,a)\) без потери какой-либо кратности. В частности, никакого \((u,a)=1\) нет.

### 5.2. Нулевая операторная поправка

Для любых конечных матриц \(Y_{\mathfrak p}\) положим
\[
 \mathcal N_Y=\sum_{q_{\mathfrak p}\le X}
 \left(\mathcal A_{\mathfrak p}^*Y_{\mathfrak p}
       +Y_{\mathfrak p}^*\mathcal A_{\mathfrak p}\right).
 \tag{O.12}
\]
Тогда **ровно на исходном коэффициенте**
\[
 \boxed{
 \boldsymbol\mu^*\mathcal N_Y\boldsymbol\mu=0,
 \qquad
 \mathcal E_M=\boldsymbol\mu^*(G+\mathcal N_Y)\boldsymbol\mu.
 }
 \tag{O.13}
\]

Это и есть допустимый способ менять операторную запись, не меняя целевой функционал. Действуют обе стороны пары колонок одновременно. Никакое значение \(\mathcal E_M\) не умножено на неизвестный строковый знаменатель.

Матрица \(\mathcal N_Y\) не обязана быть положительной: используется точное равенство её квадратичной формы нулю, а не произвольное удаление знаковых членов.

### 5.3. Что означал бы действительно работающий корректор

Пусть \(e_1\) — координатный вектор **единичного идеала колонки**, и
\[
 \mathcal B=C_{\epsilon,\mathcal A,\mathcal F}
              HU^{-\eta+\epsilon}(1+T_1)^A.
\]
Достаточный **двойственный сертификат** — явная конструкция \(Y_{\mathfrak p}\), для которой
\[
 \boxed{
 S:=\mathcal B e_1e_1^*-G-\mathcal N_Y\succeq0.
 }
 \tag{O.14}
\]
Тогда из \(\mu(1)=1\) и (O.13)
\[
 \mathcal B-\mathcal E_M=\boldsymbol\mu^*S\boldsymbol\mu\ge0.
 \tag{O.15}
\]

Знак проверен: требуется **нижняя** огибающая положительного остатка. Малость нормы \(\mathcal A\mu\), равной нулю, не является заменой (O.14).

Это не требование оценить исходный \(G\) на всех произвольных коэффициентах. Для постороннего вектора поправка (O.12) обычно ненулевая; равенство (O.13) использует специальную арифметическую систему (O.4).

**Однако свободное существование неизвестных \(Y_{\mathfrak p}\) не является прогрессом.** Нельзя определить их через уже неизвестную целевую энергию, скрыть её в решении плотной конечной задачи или предъявить численный сертификат одной ячейки вместо формулы, равномерной по U, L и общим профилям. Нужен реально выводимый выбор операторов и самостоятельное доказательство (O.14). Здесь такого выбора с нужным бюджетом нет. Этот сертификат — достаточный кандидат, не объявленная необходимость для всех подходов.

## 6. Выполненная попытка: простейший логарифмический корректор

### 6.1. Точный выбор, а не только неизвестная Y

Возьмём \(\mathcal A=\mathcal D+\mathcal C_\Lambda\) из §3.4 и
\[
 \mathcal D^\dagger_{n,n}=\begin{cases}0,&n=1,\\1/\log q_n,&n\ne1,\end{cases}
 \qquad \mathsf P=\mathcal D^\dagger\mathcal C_\Lambda.
\]
Для \(n\ne1\)
\[
 (\mathsf Pf)(n)=\sum_{\mathfrak p^k\mid n}
       \frac{\log q_{\mathfrak p}}{\log q_n}f(n/\mathfrak p^k),
 \quad (\mathsf Pf)(1)=0.
 \tag{O.16}
\]
Все коэффициенты неотрицательны, а их сумма в каждой неединичной строке равна единице, поскольку
\(\sum_{\mathfrak p^k\mid n}\log q_{\mathfrak p}=\log q_n\).
Тем не менее это не сокращение нужной энергетической нормы. Точно
\[
 \mathsf P\boldsymbol\mu=e_1-\boldsymbol\mu.
 \tag{O.17}
\]

На достаточно поздней верхней полосе \(W(1/L)=0\), поэтому \(Ge_1=e_1^*G=0\). **Это пустая единичная колонка по поддержке W, не удаление единичных элементных строк или главных характеров.**

Теперь выберем
\[
 Y=-\tfrac12\mathcal D^\dagger G
\]
для агрегированного аннулятора. Это разрешённая частная форма (O.12), поскольку \(\mathcal A\) есть линейная комбинация локальных \(\mathcal A_{\mathfrak p}\). Прямое умножение даёт
\[
 \boxed{
 G+\mathcal A^*Y+Y^*\mathcal A
 =-\tfrac12(\mathsf P^*G+G\mathsf P).
 }
 \tag{O.18}
\]

Исходный G действительно убран из явно стоящего слагаемого. **Но вместо него получены перекрёстные корреляции с простостепенным спуском, а не положительно контролируемый остаток.**

Более того, из (O.17) и \(Ge_1=0\)
\[
 \boxed{
 \mathcal E_M
 =-\operatorname{Re}\boldsymbol\mu^*G\mathsf P\boldsymbol\mu
 =\boldsymbol\mu^*\mathsf P^*G\mathsf P\boldsymbol\mu.
 }
 \tag{O.19}
\]
Таким образом, этот первый корректор имеет точный коэффициент возврата один. Он не доказал нового выигрыша.

### 6.2. Что осталось после реального вычисления

Открывая (O.19), получаем совместную энергию полиномов
\[
 \mathcal B_{u,a}(L)=\frac1{\sqrt L}
 \sum_{\mathfrak p,k\ge1}\sum_{m\ \mathrm{good}}
 \frac{\log q_{\mathfrak p}}{\log(q_{\mathfrak p}^kq_m)}
 \mu(m)\psi_{u,a}(\mathfrak p)^k\psi_{u,a}(m)
 W(q_{\mathfrak p}^kq_m/L).
 \tag{O.20}
\]
Сумма локально конечна по настоящему W. В ней нет деления на нулевой символ, а члены с \(m=1\) сохранены. Все \(k\), включая \(k\ge2\), необходимы. Точно \(\mathcal B_{u,a}=-M_u^{[a]}\) на этой полосе.

Первый неоплаченный объект этой выполненной попытки —
\[
 \sum_{q_a\le P}\sum_{u^{(6)}}\rho(q_u/U)
 \left|\sum_{\mathfrak p,k,m}\text{буквальный член (O.20)}\right|^2,
 \tag{O.21}
\]
либо, до второго квадрата, знаковое среднее в середине (O.19). Две суммы по простым степеням и один общий набор строк остаются совместными.

### 6.3. Цена испытанного раздельного оценивания

**[COFINAL_FAMILY; CONDITIONAL на прежнем масочном M].** На аннулярной поддержке \(\log(q_{\mathfrak p}^kq_m)\asymp\log L\). Нормированный профиль
\(W(y)\log L/\log(Ly)\) имеет равномерно ограниченные фиксированные семинормы при достаточно большом L; это используется только для оценки данного неудачного раздельного шага, не для объявления нового входа.

Прежний момент и Минковский дают для фиксированного a не лучше
\[
 \|\mathcal B_{u,a}\|_{2,\rho}
 \ll\frac{U^\epsilon(1+T_1)^A}{\log L}
 \left\{U^{1/2}\sum_{q_d\le\beta L}\frac{\Lambda_F(d)}{q_d^{1/2}}
 +U^{1/12}L^{5/12}\sum_{q_d\le\beta L}\frac{\Lambda_F(d)}{q_d^{11/12}}
 \right\}.
\]
Достаточно даже \(\Lambda_F(d)\le\log q_d\) и фиксированного счёта идеалов, чтобы ограничить суммы соответственно
\(\ll L^{1/2}\log L\), \(\ll L^{1/12}\log L\). Получается лишь
\[
 \sum_{q_a\le P}\|\mathcal B_{u,a}\|_{2,\rho}^2
 \ll PUL\,U^\epsilon(1+T_1)^A.
 \tag{O.22}
\]
На \(L=U^\ell\) дефицит этого бюджета относительно \(HU^{-1/200}\) равен
\(\ell-5p+1/200\); минимум на всей заданной области — \(38059/37500>1\).

Это **провал конкретного раздельного оценивания**, а не нижняя оценка настоящего (O.21). Лучший прежний момент остаётся лучше (O.22); полученную слабую границу нельзя принимать за новое продвижение.

Следующий осмысленный корректор должен работать с перекрёстными простостепенными блоками вместе с фактическим G, не повторять (O.22). Одного утверждения «у оператора стохастические строки» недостаточно: мера и норма в (O.2) не являются его инвариантной мерой.

## 7. Точная цена окна: второй способ увидеть ту же обязанность

**[ABSTRACT; PAPER].** Пусть \(\mathcal W_L f(n)=W(q_n/L)f(n)\). Поскольку \(\mathcal D_{\mathfrak p}\) коммутирует с \(\mathcal W_L\),
\[
 \boxed{
 \mathcal A_{\mathfrak p}(\mathcal W_L\mu)
 =[\mathcal A_{\mathfrak p},\mathcal W_L]\mu,
 }
 \tag{O.23}
\]
\[
 ([\mathcal A_{\mathfrak p},\mathcal W_L]\mu)(n)
 =\sum_{k=1}^{v_{\mathfrak p}(n)}
 \left\{W\!\left(\frac{q_n}{q_{\mathfrak p}^kL}\right)
            -W\!\left(\frac{q_n}{L}\right)\right\}\mu(n/\mathfrak p^k).
 \tag{O.24}
\]

Это **коммутатор** — разность двух порядков действий. Здесь она буквально показывает, что оператор сокращения сдвигает колонку относительно исходного окна. При фазах добавляется \(\psi_{u,a}(\mathfrak p)^k\), как в (O.5).

Фиксированная гладкость W не делает эту разность автоматически \(U^{-\eta}\)-малой: сдвиг нормы \(q_{\mathfrak p}^k\) не является малым приращением. Даже для самого малого хорошего простого нормы 7 аргументы отличаются множителем семь. Можно оценивать эту совместную граничную форму иначе; её новая достаточная оценка здесь не доказана.

## 8. Почему аннулирование не разрешает уничтожить настоящий ответ

Для двух простых исходные соотношения дают
\(\mu(\mathfrak p)+\mu(1)=0\) и \(\mu(\mathfrak q)+\mu(1)=0\).
Для произвольных комплексных координат существует точное равенство
\[
 \overline{x_{\mathfrak p}}x_{\mathfrak q}-|x_1|^2
 =\overline{x_{\mathfrak p}+x_1}\,x_{\mathfrak q}
       -\overline{x_1}(x_{\mathfrak q}+x_1).
 \tag{O.25}
\]
Правая сторона обнуляется на Мёбиусе. Поэтому соответствующий перекрёстный член можно перенести в единичную координату — **но его арифметический коэффициент при этом остаётся**. Это не бесплатная малость.

Так же обстоит дело с (O.14): главный риск — незаметно перенести весь прежний большой бюджет в коэффициент при \(e_1e_1^*\), а затем назвать перенос сокращением. Именно этого не позволяет проверка размера \(\mathcal B\).

## 9. Полный возврат и количественный критерий успеха

Если для всей области и каждого исходного общего производного профиля будет доказан (O.14) с \(\eta=1/200\), то (O.15) даёт **полную положительную** энергию (O.2). Отсюда немедленно следует первоначальный эксцесс MF.38; обход через J, Q и рациональный знаменатель не нужен.

Прежний MB-возврат остаётся
\[
 \mathfrak D_{\rm off}=\mathcal E_M-\lambda\mathcal R_H-
                         \mathfrak D_{\rm diag},\qquad
 \mathfrak C_G=\mathfrak D_{\rm off}+\mathcal R_{\rm paid}.
\]
Не удаляются сравнительный сырой момент, главные/фиксированные сырые строки, масочная диагональ, нижние масштабы, внешний общий делитель и его граница, оба конца верхней полосы и прежние двухсдвиговые возвраты.

Положительный Соболев применяется только после оценки полной энергии и сначала ко всем общим профилям. Конечное обращение сохраняется в буквальном виде
\[
 M_u(D;W)=\sum_{d\mid\operatorname{rad}a}
     \frac{\mu(d)\psi_u(d)}{\sqrt{q_d}}M_{ua^6}(D/q_d;W).
\]

Условный конечный результат был бы
\[
 \sum_u^{(6)}|M_u(U^r;W_{\sigma_u,t_u})|^2
 \ll \frac HP U^{-\eta+\epsilon}(1+T_1)^A,
\]
с обратным выигрышем \(\eta-5rc_0/6\). При \(\eta=1/200\) его минимум — \(5887/1200000\); для выбора \(\theta=1/250\) все потери вместе должны быть меньше \(1087/1200000\). Меньшая \(\eta\) должна превышать \(113/1200000\) плюс фактические потери.

**Это импликация с недоказанным входом (O.14), не полученный показатель.** Никакой новый RH-, SP- или высокий вывод не зачислен.

## 10. Прогнозы, конечные проверки и два следующих представления

Перед запуском конечной диагностики зарегистрированы пять проверяемых ожиданий: полный \(\mathcal A_p\) обнуляет \(\mu\); удаление старших степеней ломает закон; нулевые ветви твиста сохраняются; \(j_C\) имеет источник (O.7), а не нуль; квадратичный корректор имеет нулевое значение, но сам не доказывает верхнего бюджета.

Все пять алгебраических ожиданий подтверждены. Проверки выполнены на свободном моноиде трёх помеченных хороших простых идеалов норм 7, 13, 19 с показателями 0,…,3, со всеми локальными шестыми корнями единицы и нулевыми ветвями. Это **не весь исходный набор идеалов данной длины**, не исходная строковая выборка и не проверка софинального момента. Он используется только как конечный контроль доказанных локальных равенств.

Два отрицательных контроля: удаление старших степеней даёт \(-1\) при \(p^2\), изменение истинного \(\mu(pq)\) с 1 на 0 даёт \(-1\) в соответствующей строке аннулятора. Диагностический прибор, таким образом, реагирует на заявленные ошибки. Нулевые алгебраические результаты не интерпретируются как малая исходная энергия.

**Два допустимых представления для следующего шага:**

| Представление | Что должно быть доказано | Решающая сила / стоимость / риск |
|---|---|---|
| **Сопряжённая нулевая поправка к настоящему G**, (O.12)–(O.14) | Явная семейная формула для корректоров и доказанная положительность остатка с полным бюджетом | 5/5 / 4/5. Риск: коэффициент при единичной колонке получает весь старый долг или конструкция просто кодирует неизвестную энергию. |
| **Оконный коммутатор полного локального аннулятора**, (O.23)–(O.24) | Совместный контроль действительных оконных разностей и ограниченный возврат к (O.2) | 5/5 / 4/5. Риск: снова получить исходную энергию с коэффициентом один либо потерять общую сумму по простым степеням. |

Числа — относительные оценки решающей силы и труда, не вероятности успеха. Из этих вариантов выбран первый: **двойственная поправка**, сохранившая всю исходную арифметическую матрицу.

**Один следующий математический тест:** построить и раскрыть локально заданный смешанный двухпростой корректор к настоящему (O.11), не к матрице независимых случайных характеров; после добавления его нулевой формы предъявить точный остаток и проверить его односторонний бюджет. Не запускать большой SDP по одной ячейке и не считать получение ещё одной матрицы доказательством.

**DISCRIMINATOR:** для предлагаемой явной конструкции
\[
 S(U,L,W)=\mathcal B e_1e_1^*-G(U,L,W)-\mathcal N_Y(U,L,W).
\]
Для сертификата требуется бумажная нижняя огибающая \(S\succeq0\) на всей области. Отрицательная верхняя огибающая значения \(z^*Sz\) на одном явном z опровергает только данный сертификат, не исходный момент. Для самой цели различающая величина — \(\mathcal B-\mathcal E_M\), с полными исходными строками.

## 11. Зависимости и закрытие итерации

```yaml
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: COMMON_SIGNAL_ZERO_FREE_TO_CRITICAL_LINE
  ACTUAL_CONSUMER_REQUIREMENT: ORIGINAL_POSITIVE_M_ENERGY_WITH_ALL_SCALE_PROFILE_MASK_RETURNS
  ORIGINAL_REQUESTED_OBJECT: OPERATOR_FOR_JOINT_ACTUAL_COEFFICIENT_CANCELLATION
  ORIGINAL_OBJECT_IS: UNKNOWN
  ORIGINAL_OBJECT_NOTE: >-
    The particular PSD-corrector interface is sufficient, not known
    necessary for all ways of proving MB34.
  KNOWN_WEAKER_INTERFACES:
    - DIRECT_MB34_WITH_PAID_COMPARISON_AND_DIAGONAL
    - ORIGINAL_SPARSE_HIGH_VALUE_EXCESS_MF38
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: >-
    Source-annihilator constraints placed on both sides of the exact
    original Gram form; explicit cutoff forcing and worked log descent.
  REOPEN_TRIGGER: EXPLICIT_CORRECTOR_WITH_PROVED_UNIFORM_BUDGET_OR_DIRECT_JOINT_ESTIMATE
  IMPOSSIBILITY_EVIDENCE_FOR_TARGET: NONE
  SOURCE_INPUTS_CERTIFIED: false
  KILL_SCOPE_FOR_NEGATIVE_CONTROLS: THEOREM_SHAPE_ONLY
  NEGATIVE_CONTROL_STATEMENTS:
    - OMITTING_HIGHER_PRIME_POWERS_STILL_PRESERVES_A_p_MU_ZERO
    - THE_SAME_HOMOGENEOUS_ANNIHILATOR_KILLS_j_C
  NEGATIVE_CONTROL_EVIDENCE: O4_O7_O8_AND_EXACT_APPENDIX
  NEGATIVE_CONTROL_UPPER_ENVELOPES:
    omitted_power_identity_slack: -1
    rough_prime_j_C_zero_identity_slack: -2
META_CLOSEOUT:
  WHAT_BECAME_SMALLER: >-
    The vague operator request now distinguishes exact source cancellation
    from the still unpaid positive-return certificate.
  WHAT_WAS_KILLED: ONLY_THE_EXPLICIT_FALSE_LOCAL_SHORTCUTS
  WHAT_NOT_TO_REPEAT: >-
    Two Euler channels as a claimed gain; annihilation as a bound;
    scalar denominator multiplication; all-power deletion; separated PUL.
  CURRENT_SMALLEST_GAP: EXPLICIT_SOURCE_NULL_CORRECTOR_WITH_POSITIVE_BUDGETED_REMAINDER
  PROOF_PROGRESS_ON_MAIN_TARGET: NONE
  PREDICTION_FATE: FIVE_ALGEBRAIC_PREDICTIONS_CONFIRMED_NO_POWER_GAIN_PREDICTED_OR_PROVED
  MEMORY_ENTRY:
    target: JOINT_ACTUAL_COEFFICIENT_OPERATOR
    status: OPEN
    cognitive_operator_used: DUALIZE
    invariant_learned: >-
      Exact source annihilation can enter the energy only with its
      boundary/normalization retained; the cutoff j_C is inhomogeneous.
    forbidden_future_move: TREAT_TRANSFORMED_ZERO_AS_SMALL_ORIGINAL_ENERGY
    next_decisive_test: MIXED_PRIME_ACTUAL_GRAM_CORRECTOR_AND_ITS_FULL_REMAINDER
```

## Приложение A. Точная локальная диагностика

Код запускается Python 3 без дополнительных пакетов. Он проверяет только указанные конечные алгебраические равенства. Параметры `P` и `E` в коде задают диагностические нормы трёх помеченных простых и набор показателей; это не исходный усилитель P. Например, `E = product(range(4), repeat=3)` означает показатели 0,1,2,3 у каждого из трёх простых.

```python
from itertools import product
from fractions import Fraction as F
from pathlib import Path
import hashlib, json

# Exact checks on the free ideal monoid generated by three good prime ideals.
# This is a local-algebra diagnostic, not a test of the cofinal row-energy bound.
P=(7,13,19)
E=list(product(range(4), repeat=3))
N={e: 7**e[0]*13**e[1]*19**e[2] for e in E}
E.sort(key=lambda e:N[e])
unit=(0,0,0)
mu={e: (-1)**sum(e) if max(e)<=1 else 0 for e in E}
mu2={e: ((-2)**sum(v==1 for v in e)) if max(e)<=2 else 0 for e in E}
divs={e:list(product(*(range(v+1) for v in e))) for e in E}
sub=lambda a,b:tuple(x-y for x,y in zip(a,b))

def conv(a,b):
    return {e:sum(a[d]*b[sub(e,d)] for d in divs[e]) for e in E}
def cp(f,i):
    return {e:sum(f[tuple(e[t]-(k if t==i else 0) for t in range(3))]
                  for k in range(1,e[i]+1)) for e in E}
def ap(f,i):
    c=cp(f,i)
    return {e:e[i]*f[e]+c[e] for e in E}

checks={}
def check(group,ok):
    assert ok,group
    checks[group]=checks.get(group,0)+1

one={e:1 for e in E}
for e,v in conv(mu,one).items(): check('mobius_inversion',v==int(e==unit))
for i in range(3):
    for e,v in ap(mu,i).items(): check('all_power_annihilator',v==0)

# Formal sixth roots in Z[z]/(z^2-z+1), including zero branches.
def mul(x,y):
    a,b=x;c,d=y
    return (a*c-b*d,a*d+b*c+b*d)
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def smul(k,x): return (k*x[0],k*x[1])
def power(z,k):
    out=(1,0)
    for _ in range(k): out=mul(out,z)
    return out
roots=[power((0,1),k) for k in range(6)]
for vals in product([(0,0)]+roots, repeat=3):
    psi={e:mul(mul(power(vals[0],e[0]),power(vals[1],e[1])),power(vals[2],e[2])) for e in E}
    f={e:smul(mu[e],psi[e]) for e in E}
    for i in range(3):
        for e in E:
            out=smul(e[i],f[e])
            for k in range(1,e[i]+1):
                d=tuple(e[t]-(k if t==i else 0) for t in range(3))
                out=add(out,mul(power(vals[i],k),f[d]))
            check('twists_and_zero_branches',out==(0,0))

# Exact inhomogeneous equation for j_C = mu - (mu2 1_{N<=C})*1.
for C in (1,7,13,49,91,200):
    trunc={e:mu2[e]*int(N[e]<=C) for e in E}
    short=conv(trunc,one)
    j={e:mu[e]-short[e] for e in E}
    for i in range(3):
        cm=cp(mu2,i);ct=cp(trunc,i)
        boundary={e:ct[e]-int(N[e]<=C)*cm[e] for e in E}
        rhs=conv(boundary,one)
        lhs=ap(j,i)
        for e in E: check('cutoff_forcing',lhs[e]==-2*rhs[e])

# Window commutator. A_p(W*mu)=[A_p,W]mu, pointwise product.
W={e:F((N[e]%11)-5,11) if 7<=N[e]<=10000 else F(0) for e in E}
f={e:W[e]*mu[e] for e in E}
for i in range(3):
    lhs=ap(f,i)
    for e in E:
        rhs=F(0)
        for k in range(1,e[i]+1):
            d=tuple(e[t]-(k if t==i else 0) for t in range(3))
            rhs+=(W[d]-W[e])*mu[d]
        check('window_commutator',lhs[e]==rhs)

# Finite exact Hermitian-null-form checks without assuming anything about G.
# y is a generic integer matrix; <mu,(A^T y+y^T A)mu>=0 follows directly.
for i in range(3):
    am=ap(mu,i)
    ym={e:sum((((N[e]+3*N[d])%17)-8)*mu[d] for d in E) for e in E}
    check('quadratic_null_form',2*sum(am[e]*ym[e] for e in E)==0)

# Planted failures: removing higher prime powers or perturbing true mu.
p2=(2,0,0)
truncated_at_k1=2*mu[p2]+mu[(1,0,0)]
check('negative_controls',truncated_at_k1==-1)
wrong=mu.copy();wrong[(1,1,0)]=0
perturbed=ap(wrong,0)[(1,1,0)]
check('negative_controls',perturbed==-1)

out={
    'scope':'FINITE_CELL', 'verifier':'PAPER',
    'algebra_domain':'three labelled prime ideals, each exponent 0..3',
    'checks':checks,'total':sum(checks.values()),
    'negative_controls':{'omit_higher_powers':truncated_at_k1,'perturb_mu_pq':perturbed},
    'cofinal_energy_bound_verified':False,
    'source_P_M_R_certified':False
}
print(json.dumps(out,ensure_ascii=False,indent=2))
Path('/mnt/data/operator_rethink_check_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
```

Фактический вывод запуска:

```json
{
  "scope": "FINITE_CELL",
  "verifier": "PAPER",
  "algebra_domain": "three labelled prime ideals, each exponent 0..3",
  "checks": {
    "mobius_inversion": 64,
    "all_power_annihilator": 192,
    "twists_and_zero_branches": 65856,
    "cutoff_forcing": 1152,
    "window_commutator": 192,
    "quadratic_null_form": 3,
    "negative_controls": 2
  },
  "total": 67461,
  "negative_controls": {
    "omit_higher_powers": -1,
    "perturb_mu_pq": -1
  },
  "cofinal_energy_bound_verified": false,
  "source_P_M_R_certified": false
}
```

Полная проверка направлений и оценок в основной части — бумажный вывод, а не следствие количества этих диагностик. Финальный исходный момент по-прежнему не оценён требуемой новой степенью.
