# STATUS: TRY_CCM_JOINT_LOW_RESIDUE_Q51
```yaml
OPERATIVE_CLASS: TRY_CCM_JOINT_LOW_RESIDUE_Q51
REQUEST_ID: Q51_JOINT_LOW_RESIDUE
DATE: 2026-10-27
LANGUAGE: ru
SOURCE_OBJECT: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
BASE_COMMIT: 54e4ad569ec7dc46994ebf4f9cc15e9d99624314
PACKET_BYTES: 51031
PACKET_LF: 849
PACKET_SHA256: 5c34576e47a0b1b23a94cda5c381d29402355613e20e734846104f2eb919d61d
SOURCE_BODIES: 8
MANIFEST: VERIFIED
CONSUMER_PROGRESS: NO_PROGRESS
INDEPENDENT_LOW_RESIDUE_FLOOR: NOT_DERIVED
NEW_CONSUMER_EXPONENT: NOT_PROVED
CHOSEN_MECHANISM: WHOLE_LOW_ZERO_DIVISOR_LOG_DERIVATIVE_WITH_EXACT_ENTIRE_FACTOR_RETURN
COMPLETION_TESTED: SCALAR_POSITIVE_REAL_TO_PROJECTED_MATRIX_POSITIVE_REAL
SCALAR_COMPLETION: EQUIVALENT_TO_EXCLUSION_OF_THE_SELECTED_LOW_ZEROS
MATRIX_COMPLETION: REFUTED_ON_ACTUAL_ORIGINAL_P
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: EXACT_ACTUAL_SOURCE_NEGATIVE_QUADRATIC_FORM
KILL_EVIDENCE_REFERENCE: SECTION_6_EQ_6_7
KILL_DOES_NOT_APPLY_TO: JOINT_RESIDUE_FLOOR_OR_CCM_OR_RH
FAILURE_TYPE: NO_DERIVATION
COMPLETION_FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: RESEARCH_DEBT
EPISTEMIC_SCOPE: ORIGINAL_CCM_CONSUMER
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
VERIFIER: PAPER
AUXILIARY_RESULTS:
  - FINITE_LOW_HIGH_ENTIRE_FACTOR_RETURN_ON_THE_SAME_COMMON_CONTOUR
  - ORIGINAL_P_EXPLICIT_FIVE_MODE_POLAR_VISIBILITY
  - ACTUAL_JOINT_LOG_DERIVATIVE_DOES_NOT_MAKE_THE_ANALYTIC_TRANSFER_POSITIVE_REAL
  - BOUNDARY_LOGARITHM_WINDING_CORNER_HAS_PAID_POWER_MINUS_7_OVER_24
FIRST_UNPAID_STEP: SIGNED_BOUNDARY_PAIRING_OF_THE_WHOLE_ACTUAL_LOW_DIVISOR
RH: OPEN_NOT_CLAIMED
PX_RH_CLAIM: NOT_MADE
ALL_P_GOAL: OPEN
CONDITIONAL_ZF78: NOT_USED_NOT_UPGRADED
CF22_PYSR: PARKED_REOPENABLE
INDEPENDENT_NEW_AUDIT: NOT_RUN
LEAN: NOT_RUN
ARB: NOT_RUN
PRODUCTION_CCM_SPECTRUM: NOT_RUN
NUMERIC_OFF_LINE_ZERO_ASSIGNMENT: NONE
REPOSITORY_WRITES: NONE
PACKAGE_INSTALLATIONS: NONE
NEXT_QUESTION_DISPATCH: NONE
```

Ы. **Независимую нижнюю оценку полной \(\mathcal R_{\rm low}\) нужной силы я не получил.** Проверен конкретный предложенный ход: собрать весь настоящий низковысотный делитель в один конечный множитель \(\xi\), вернуть его логарифмическую производную вместе с оставшимся целым множителем и испытать положительно-вещественное завершение на достижимых резольвентных направлениях.

Есть два различных вывода.

**Первый:** требование, чтобы логарифмическая производная низкого множителя была голоморфной положительно-вещественной функцией в нужной полуплоскости, уже исключает все нули, входящие в \(\mathcal R_{\rm low}\). На кофинальной семье такое требование эквивалентно RH. Это не доказанный поставщик из функционального уравнения.

**Второй — фактический scoped отказ:** даже там, где полная настоящая логарифмическая производная низкого множителя положительна, её произведение с исходным аналитическим матричным transfer имеет **оба знака на исходном \(P\)**. Два направления предъявлены явно, всего на пяти исходных модах, без ошибки проекции и без назначения внепрямого нуля. Следовательно, положительность скалярного множителя не переносится на этот матричный интегранд.

**Это не знак контурного интеграла.** Нельзя перенести данный отказ на \(\mathcal R_{\rm low}\), на спектр CCM или на возможность иной совместной компенсации.

Оставшийся entire factor возвращён полностью. После удаления только low-нулей его вклад **не нулевой**: это high-residue, уже оплаченный в S4. Выполненный более ранний откат — к непрерывной ветви логарифма на общем контуре, до её дифференцирования; обязательная монодромная поправка получила явный \(o(1)\)-бюджет. Благоприятная оценка оставшегося знакового интеграла не доказана.

## 1. Source lock, чтение и границы проверки

Прочитан весь канонический TXT и все восемь полных тел S1–S8. Проверены 51 031 байт, 849 LF, общий SHA-256, порядок тел, их собственные bytes/LF/SHA-256, открывающие и закрывающие строки и один разделительный LF вне каждого тела. Манифест с точными byte-offsets приведён ниже и в исполняемом приложении.

Из GitHub-коннектора заново прочитан протокол `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, ветка `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Единственное поручение — root Q51. Исторические команды не исполнялись. S1–S2 рассматриваются как включённые локальные заметки, а не как заявленные committed/admitted результаты.

| Вход | Как используется | Что из него не импортируется |
|---|---|---|
| S1 | граница count/signature, цена полного Frobenius, условие witness-survival | magnitude из rank/count; независимая оценка negative part |
| S2 | ограничение moving single-atom packet | запрет широких пакетов или signed comparisons |
| S3 | точная all-\(P\) контурная карта и её бюджет | положительный знак всей матрицы вычетов |
| S4 | уже оплаченный полный high-tail | lower для low из zero density |
| S5 | область translated actual-witness receiver | бесплатное размножение отрицательного ранга |
| S6 | итог Q50, fallback, исходная отражательная геометрия | знак Hankel/parity с разрешённой растущей поправкой |
| S7 | отдельный sparse-band conditional receiver | уже доказанная арифметическая оценка или full-SP |
| S8 | необходимость полного знакового спаривания | перенос pointwise negative-part цены на actual форму |

Статусы upstream не повышены. Внешняя сверка ограничена классическими определениями \(\xi\), симметриями её нулей и теоремой о вычетах; локальные выводы ниже доказываются непосредственно. Ни infinite Hadamard factorization, ни новый zero-free theorem, ни RH-strength variance не нужны.

## 2. Неизменный источник и оплаченный интерфейс

**[COFINAL_FAMILY | PAPER: inherited S3, S4, S6, S7].** Фиксируем до предела
\[
0<\epsilon<1/32,\quad N=m,\quad L=\log m,\quad
M=R=\lfloor m^\epsilon\rfloor,\quad
\omega_j=\frac{2\pi j}{L},\quad \Omega=\frac{2\pi M}{L}.
\tag{2.1}
\]
\(P\) — исходный трёхконтактный проектор в полосе \(|j|\le M\), с дополнением нулями в исходный carrier. Для всех векторов одной ячейки сохраняются одни и те же \(P,u,H\).

На \(\operatorname{ran}P\):
\[
A=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\,P Q_M(\log n)P,
\qquad C^0=A+H_P,\qquad0\preceq H_P\preceq4P.
\tag{2.2}
\]
Все степени простых входят в \(\Lambda\) с настоящими весами. В этом ответе новые разложения \(\mu*\log\) не вводятся и никакие делительные маски не меняются.

Положим
\[
v_\pm(z)_j=(z\pm i\omega_j)^{-1},\qquad
\mathsf S_P(z)=\frac1L P\bigl[v_+(z)v_+(z)^{\mathsf T}
                         +v_-(z)v_-(z)^{\mathsf T}\bigr]P,
\tag{2.3}
\]
\[
\mathsf K_m(z)=m^z\mathsf S_P(z),\qquad
\operatorname{He}X=\frac{X+X^*}{2}.
\tag{2.4}
\]
В (2.3) стоит **транспонирование**, а не adjoint. Обе временные стороны и все межмодовые произведения остаются внутри одной матрицы.

Принятый общий контур имеет
\[
u\in[1/L,2/L],\quad H\in[Y,Y+1],\quad
Y=\max\{4\Omega+10,16,m^{1/4+\epsilon}\}.
\tag{2.5}
\]
Он избегает нулей. Для кодирования конечной суммы возьмём положительно ориентированный прямоугольник
\[
\Gamma_m=\partial\{z:u<\Re z<b_m,\ |\Im z|<H\},
\qquad b_m=\frac12+\frac1L.
\tag{2.6}
\]
Это не новый prime-inversion contour: (2.6) лишь представляет уже определённую конечную сумму вычетов. Все нетривиальные нули имеют \(|\Re(\rho-1/2)|<1/2\), поэтому правая сторона охватывает ровно нужные нули. Полюса \(\mathsf S_P\) находятся на мнимой оси, вне прямоугольника.

По S3,
\[
A=-H_P+\mathcal V-\mathcal R_{\rm sign}+\mathcal E,
\qquad \|\mathcal V\|\le B_m,\quad\|\mathcal E\|\le e_m,
\tag{2.7}
\]
\[
\begin{aligned}
B_m&=2^{20}C_*L(1+\Omega)\log(12L)\log(20+\Omega),\\
e_m&=V_2\left[
\frac{32\sqrt m L}{Y^3}
+\frac{2^{20}C_*\log(12L)\log(Y+10)}{Y^3}
+\frac{2^{10}C_*^2\sqrt m\log^2(Y+10)}{LY^4}\right],\\
V_2&=\frac1L\sum_{|j|\le M}\omega_j^2
=\frac{4\pi^2M(M+1)(2M+1)}{3L^3}.
\end{aligned}
\tag{2.8}
\]
Здесь \(C_*\) — тот же фиксированный классический constant из S3, не новый source supplier.

С \(G=m^\kappa,\ \kappa=5/24+\epsilon\),
\[
\mathcal R_{\rm sign}=\mathcal R_{\rm low}+\mathcal R_{\rm high},
\qquad \|\mathcal R_{\rm high}\|\le t_m,
\tag{2.9}
\]
\[
t_m=C_{\rm tail}\frac{\sqrt m\,V_2\log(G+2)}{G^3}
=O_\epsilon(m^{-1/8}/L^2).
\tag{2.10}
\]
\(C_{\rm tail}\) — фиксированная константа уже принятого local zero-count/tail bound. В (2.9) low включает \(|\gamma|=G\), high — строго \(G<|\gamma|<H\). Нули, кратности и common contour не меняются.

## 3. Полная конечная факторизация настоящей \(\xi\)

**[FINITE_CELL | PAPER].** Обозначим
\[
F(z)=\xi(1/2+z).
\tag{3.1}
\]
Используются действительные симметрии \(F(-z)=F(z)\), \(F(\bar z)=\overline{F(z)}\), целость \(F\) и соответствие её нулей нетривиальным нулям \(\zeta\) с теми же кратностями. Определение и функциональное уравнение сверены по [E1], расположение и симметрии нулей — по [E2].

Пусть \(w=\rho-1/2\), а \(r_w\) — его кратность. Строим **весь**, а не только правый, конечный делитель:
\[
D_G(z)=\prod_{|\Im w|\le G}(z-w)^{r_w},\qquad
D_H(z)=\prod_{|\Im w|<H}(z-w)^{r_w}.
\tag{3.2}
\]
При пустом наборе произведение равно 1. Оба полинома вещественны и чётны; постоянная нормировка не влияет на логарифмическую производную. Их определение использует настоящие нули, но не утверждает, что их координаты здесь вычислены.

Положим
\[
D_{G,H}=D_H/D_G,\qquad E_H=F/D_H.
\tag{3.3}
\]
\(E_H\) — целая функция, не имеющая нулей в полосе \(|\Im z|<H\), **по определению удалённого делителя**. Это не утверждение об отсутствии нулей у исходного \(F\). Высокие нули \(F\) остаются нулями \(E_H\) вне этой полосы.

Точное равенство:
\[
\boxed{\frac{F'}F=
\frac{D_G'}{D_G}+\frac{D_{G,H}'}{D_{G,H}}+\frac{E_H'}{E_H}.}
\tag{3.4}
\]
Каждый полюс первой и второй дроби имеет вычет \(r_w\), независимо от величины кратности. Внутри \(\Gamma_m\) третья дробь голоморфна. Поэтому по обычной теореме о вычетах [E3], применённой к каждой записи матрицы,
\[
\boxed{
\mathcal R_{\rm low}
=\operatorname{He}\frac1{2\pi i}
\oint_{\Gamma_m}\mathsf K_m(z)\frac{D_G'(z)}{D_G(z)}\,dz,}
\tag{3.5}
\]
\[
\boxed{
\mathcal R_{\rm high}
=\operatorname{He}\frac1{2\pi i}
\oint_{\Gamma_m}\mathsf K_m(z)\frac{D_{G,H}'(z)}{D_{G,H}(z)}\,dz,}
\tag{3.6}
\]
\[
\boxed{
\oint_{\Gamma_m}\mathsf K_m(z)\frac{E_H'(z)}{E_H(z)}\,dz=0.}
\tag{3.7}
\]

Таким образом, **цена полного оставшегося entire factor после удаления только low равна уже оплаченной high-цене**:
\[
\operatorname{He}\frac1{2\pi i}
\oint_{\Gamma_m}\mathsf K_m(z)\frac{(F/D_G)'(z)}{(F/D_G)(z)}\,dz
=\mathcal R_{\rm high},\qquad \|\cdot\|\le t_m.
\tag{3.8}
\]
Называть левую часть нулём лишь потому, что \(F/D_G\) entire, было бы ошибкой: у entire-функции могут быть нули, а у её логарифмической производной — полюса.

### Все четыре стороны, а не «хорошая вертикаль»

Ноль (3.7) относится к **целому замкнутому интегралу**. Его правую вертикаль, левую вертикаль или горизонтали по отдельности нулевыми не считаем. Никакие пределы при \(H\to\infty\) в этой формуле не берутся. На исходном tall-контуре вычеты высоких нулей (3.6) сохранены, и за них ровно один раз начисляется (2.10).

В (3.5) левые партнёры и нули с \(\Re w\le u\) присутствуют в полиноме, но находятся вне правого прямоугольника. Их вклад в этот конкретный замкнутый интеграл равен нулю по голоморфности, а не по предположению об их знаке. Они не добавлены к физической форме как новые слагаемые. В частности, \(m^w\) не заменяется на \((m^w+m^{-w})/2\).

Представление через \(F'/F\) кодирует **сумму вычетов**, а не незаметно заменяет исходный \(-\zeta'/\zeta\)-интегранд в (2.7). Его pole/arch/continuous accounting остаётся унаследованным из S3. У \(F\) нет полюса в \(z=1/2\); новый полюс основного члена туда не вставляется.

## 4. Что действительно можно доказать о высоком множителе

Эта вспомогательная проверка отделяет законный знак entire-factor return от недоказанного знака low. Она **не уменьшает** уже оплаченный основной долг.

**[COFINAL_FAMILY | PAPER: классический count из S3–S4].** Выберем фиксированную \(C_N\) так, чтобы полное число нулей с кратностями удовлетворяло
\[
N_0(T)\le C_N T\log(T+2),\qquad T\ge2.
\tag{4.1}
\]
Это следствие принятой локальной оценки \(O(\log(t+2))\), не zero-density улучшение.

Для \(w=\delta+i\gamma\) и функционального партнёра \(-\bar w=-\delta+i\gamma\), при \(z=x+it\),
\[
\Re\left(\frac1{z-w}+\frac1{z+\bar w}\right)
=
\frac{2x\,[x^2+(t-\gamma)^2-\delta^2]}
 {[(x-\delta)^2+(t-\gamma)^2][(x+\delta)^2+(t-\gamma)^2]}.
\tag{4.2}
\]
Все \(|\delta|<1/2\). Поэтому, после совместной сборки каждой настоящей пары,
\[
\boxed{
\Re\frac{D_{G,H}'(x+it)}{D_{G,H}(x+it)}\ge0,
\quad x>0,\quad |t|\le G-1/2.}
\tag{4.3}
\]
Нули с \(\delta=0\) дают отдельно \(x/[x^2+(t-\gamma)^2]>0\); их не удваиваем искусственно. Кратности функциональных партнёров совпадают.

**Область существенна:** у низкого нуля возможно \(|t-\gamma|<|\delta|\); тогда числитель (4.2) не имеет нужного знака. Оценка (4.3) не переносится в окрестности низких полюсов.

Есть также равномерная оценка целого высокого логарифмического канала. Группируя \(w,-w\),
\[
\frac1{z-w}+\frac1{z+w}=\frac{2z}{z^2-w^2}.
\tag{4.4}
\]
При \(|z|\le G/2\) знаменатель имеет модуль не меньше \(3|w|^2/4\). Диадическое суммирование (4.1) даёт
\[
\sum_{G<|\Im w|<H}\frac{r_w}{|w|^2}
\le\frac{8C_N\log(G+2)}G.
\tag{4.5}
\]
Действительно, \(k\)-я оболочка стоит не более
\(2C_N2^{-k}[\log(G+2)+(k+1)\log2]/G\); используются
\(\sum2^{-k}=2\) и \(\sum(k+1)2^{-k}=4\).

Следовательно,
\[
\boxed{
\left|\frac{D_{G,H}'(z)}{D_{G,H}(z)}\right|
\le\frac{16C_N|z|\log(G+2)}G,
\qquad |z|\le G/2.}
\tag{4.6}
\]
Это оценка **конечного** высокого делителя; никакая бесконечная факторизация \(\xi\) не предположена.

Например, на части исходной левой вертикали \(z=u+it\), \(|t|\le2\Omega\), для поздних ячеек \(\Omega\ge1\), \(G\ge8\Omega\), \(u\le1\), из S3 и (4.6):
\[
\left\|\frac1{2\pi}
\int_{-2\Omega}^{2\Omega}\mathsf K_m(u+it)
\frac{D_{G,H}'(u+it)}{D_{G,H}(u+it)}\,dt\right\|
\le\frac{288e^2 C_N}{\pi}
\frac{L\Omega^2\log(G+2)}G
=O_\epsilon(m^{-5/24+\epsilon}).
\tag{4.7}
\]
Здесь \(m^u\le e^2\), \(\|\mathsf S_P\|\le3L\), \(|u+it|\le3\Omega\). **Это лишь одна часть уже дешёвого высокого канала**. Она не оплачивает low, не заменяет полный contour return и не прибавляется к (2.10) как новая независимая плата.

## 5. Скалярный positive-real тест: точное недоказанное условие

**[FINITE_CELL | PAPER].** Пусть
\[
\ell_G(z)=D_G'(z)/D_G(z)=\sum_{|\Im w|\le G}\frac{r_w}{z-w}.
\tag{5.1}
\]
Рассмотрим ровно такое completion:
\[
\ell_G\text{ голоморфна в }\Re z>u,
\qquad \Re\ell_G(z)\ge0\text{ там}.
\tag{PR}
\]
Это определение положительно-вещественного свойства. После поворота
\(h(\zeta)=i\ell_G(u-i\zeta)\) оно становится свойством Herglotz:
голоморфность при \(\Im\zeta>0\) и \(\Im h\ge0\).

### Лемма

Для этого конечного делителя
\[
\boxed{(PR)\quad\Longleftrightarrow\quad
D_G\text{ не имеет нулей в }\Re z>u.}
\tag{5.2}
\]

**Доказательство.** При отсутствии таких нулей для каждого слагаемого
\[
\Re\frac{r_w}{x+it-w}
=\frac{r_w(x-\Re w)}{(x-\Re w)^2+(t-\Im w)^2}>0
\quad(x>u),
\tag{5.3}
\]
если делитель непуст. Для пустого делителя \(\ell_G=0\). Обратно, нуль \(w\) с \(\Re w>u\) порождает простой полюс \(r_w/(z-w)\). Другие различные нули регулярны в его окрестности; положительная кратность не сокращается. Голоморфность (PR) невозможна. □

Следовательно, в данном опыте (PR) не является более слабым установленным supplier: оно заставляет \(\mathcal R_{\rm low}=0\). Даже его голоморфная часть уже исключает выбранные нули.

**[COFINAL_FAMILY | PAPER: импликация, не использование RH].** Если (PR) доказано на неограниченной последовательности исходных \(m\) для любого одного фиксированного \(\epsilon>0\), то каждый фиксированный нуль с \(\delta=\Re w>0\) в конце концов попадает в \(|\Im w|\le G\), \(\delta>u\), что противоречит (5.2). Функциональная симметрия затем исключает и \(\delta<0\). Обратно, при RH все корни конечного делителя имеют \(\Re w=0\), и (5.3) доказывает (PR). Таким образом, **кофинальное (PR) эквивалентно RH**, а не предоставлено функциональным уравнением.

Это не означает, что такой путь нельзя независимо доказать. Оно означает только, что в текущем расчёте нельзя вставить (PR) как уже известную гипотезу. Никакой внепрямой нуль здесь не объявлен существующим; (PR) для actual source не объявлено ложным.

### Отрицательный контроль ровно общей импликации

Вещественный чётный полином
\[
D(z)=\bigl((z-1/4)^2+1\bigr)\bigl((z+1/4)^2+1\bigr)
\tag{5.4}
\]
положителен на вещественной оси и имеет обе стандартные симметрии. Но при \(z=6/25+i\)
\[
\Re D'(z)/D(z)
=-\frac{8131799049600}{83108037649}<-90.
\tag{5.5}
\]
Это **не модель нулей \(\zeta\)**. Контроль исключает только правило «real entire + even + real-axis positivity автоматически дают (PR)».

Оставшийся entire factor не убирает полюс низкой логарифмической производной: около каждого удалённого низкого нуля \((F/D_G)'/(F/D_G)\) голоморфна. Нельзя скрыть запрещённый полюс неизвестной аналитической добавкой.

## 6. Проверка на ИСХОДНОМ \(P\): полная лог-производная не исправляет матричный знак

Здесь не используется generic diagonal toy, full-\(\Pi\) атомный пример или неизвестное положение нуля. Проверяется именно достижимый transfer из (2.3).

### 6.1. Два точных контактных направления

**[FINITE_CELL | PAPER].** Обозначим
\[
a_0=1/2,\qquad \Delta=2\pi/L,\qquad
r_j(z)=\frac{z}{z^2+\omega_j^2},\quad
s_j(z)=\frac{\omega_j}{z^2+\omega_j^2}.
\tag{6.1}
\]
Не путать \(r_j\) с кратностью \(r_w\). Контактное пространство равно
\(\operatorname{span}_{\mathbb C}\{\mathbf1,r(a_0),s(a_0)\}\), поскольку исходные экспоненциальные столбцы пропорциональны \((a_0\mp i\omega_j)^{-1}\).

При \(M\ge2\) зададим два вещественных вектора, нулевых вне \(j=0,\pm1,\pm2\):
\[
\begin{array}{c|ccccc}
j&-2&-1&0&1&2\\\hline
e_j&a_0^2+4\Delta^2&-4(a_0^2+\Delta^2)&6a_0^2&-4(a_0^2+\Delta^2)&a_0^2+4\Delta^2\\
o_j&a_0^2+4\Delta^2&-2(a_0^2+\Delta^2)&0&2(a_0^2+\Delta^2)&-(a_0^2+4\Delta^2)
\end{array}
\tag{6.2}
\]
Прямое сложение даёт
\[
\mathbf1^Te=\mathbf1^To=0,
\quad e^Tr(a_0)=0,\quad o^Ts(a_0)=0.
\tag{6.3}
\]
Остальные два pairing равны нулю по чётности. Значит, **\(Pe=e\), \(Po=o\) точно**. Это допустимые векторы прежней полосы, не новый проектор и не приближение compact profile. Цена их возврата в исходный carrier равна нулю.

### 6.2. Полные аналитические contractions

\(P\) сохраняет чётность по индексу. Из \(v_+=r-is\), \(v_-=r+is\):
\[
\mathsf S_P(z)=\frac2L\bigl[(Pr(z))(Pr(z))^T-(Ps(z))(Ps(z))^T\bigr].
\tag{6.4}
\]
Совместная сборка обеих ориентаций выполнена **до** назначения знака.

Точно:
\[
E(z):=e^Tr(z)
=\frac{24\Delta^4(a_0^2-z^2)}
 {z(z^2+\Delta^2)(z^2+4\Delta^2)},
\tag{6.5a}
\]
\[
O(z):=o^Ts(z)
=\frac{12\Delta^3(a_0^2-z^2)}
 {(z^2+\Delta^2)(z^2+4\Delta^2)}.
\tag{6.5b}
\]
Например, для (6.5a) после общего знаменателя коэффициент при \((z^2)^2\) равен нулю, а оставшийся числитель равен \(24\Delta^4(a_0^2-z^2)\). Поэтому
\[
e^T\mathsf S_P(z)e=\frac2L E(z)^2,
\qquad o^T\mathsf S_P(z)o=-\frac2L O(z)^2,
\qquad e^T\mathsf S_P(z)o=0.
\tag{6.6}
\]
Это **аналитические квадраты**, не модули. На \(\Re z>0\), \(z\ne a_0\), обе правые части ненулевые. В точке \(a_0\) они зануляются исходными экспоненциальными контактами.

### 6.3. Фактический отказ matrix-positive-real completion

**[COFINAL_FAMILY | PAPER].** На каждой достаточно поздней ячейке \(M\ge2\), а \(D_G\) непуст: \(G\to\infty\) и у настоящей \(\zeta\) есть нетривиальные нули. При вещественном \(b_m>1/2\) полный настоящий \(\ell_G(b_m)\) веществен и строго положителен. Действительно, сопряжённая пара даёт
\[
\frac{r_w}{b_m-\delta-i\gamma}+
\frac{r_w}{b_m-\delta+i\gamma}
=\frac{2r_w(b_m-\delta)}{(b_m-\delta)^2+\gamma^2}>0.
\]
Здесь использована только доказанная полоса \(|\delta|<1/2\), не RH.

Пусть \(c_e=e/\|e\|\), \(c_o=o/\|o\|\), и рассмотрим **весь** предложенный интегранд
\[
\mathcal M_G(z)=\mathsf K_m(z)\ell_G(z).
\]
Из (6.6):
\[
\boxed{
 c_o^*\operatorname{He}\mathcal M_G(b_m)c_o
 =-\frac{2m^{b_m}\ell_G(b_m)}{L\|o\|^2}
 \left[\frac{12\Delta^3(a_0^2-b_m^2)}
 {(b_m^2+\Delta^2)(b_m^2+4\Delta^2)}\right]^2<0,}
\tag{6.7}
\]
\[
\boxed{
 c_e^*\operatorname{He}\mathcal M_G(b_m)c_e
 =\frac{2m^{b_m}\ell_G(b_m)}{L\|e\|^2}
 \left[\frac{24\Delta^4(a_0^2-b_m^2)}
 {b_m(b_m^2+\Delta^2)(b_m^2+4\Delta^2)}\right]^2>0.}
\tag{6.8}
\]
Таким образом, ни \(\mathcal M_G\), ни \(-\mathcal M_G\) не являются матричными positive-real функциями на нужной полуплоскости. Отказ уже происходит на безопасной вещественной точке, где вся настоящая скалярная лог-производная имеет благоприятный знак.

В (6.7) дан **точный отрицательный верх** для проверяемой PSD-гипотезы. Не требуется float-знак или придуманная координата actual zero. Неопределённость самого аналитического transfer была известна ранее; новое ограниченное действие здесь — проверить, исправляет ли её **совместный полный actual low-divisor**, а не один свободный множитель. Не исправляет в этом конкретном pointwise completion.

**Scope:** (6.7) опровергает только
\[
\operatorname{He}[m^z\mathsf S_P(z)D_G'(z)/D_G(z)]\succeq0
\quad\text{на всей }\Re z>u,
\tag{MR}
\]
и вариант с противоположным общим знаком. Оно **не опровергает** нижний bound контурного интеграла (3.5). Даже если все low-нули лежат на критической линии и (3.5) равен нулю, интегранд на правой стороне всё равно имеет оба знака. Следовательно, pointwise PSD не является необходимым условием успеха.

### 6.4. Проекция не скрывает возможный запрещённый полюс

**[FINITE_CELL | PAPER; применение к actual zero условно на его существование].** Из (6.5) следует, что при \(\Re w>0\), \(w\ne1/2\), оба \(Pr(w),Ps(w)\) ненулевые. Они лежат в разных чётностных блоках. Поэтому
\[
\operatorname{rank}_{\mathbb C}\mathsf S_P(w)=2.
\tag{6.9}
\]
Это ранг аналитической матрицы, **не** её Hermitian part и не ранг всей суммы вычетов.

Если бы существовал actual zero \(w\) с \(\Re w>u\), \(|\Im w|\le G\), то
\[
\operatorname*{Res}_{z=w}\mathcal M_G(z)
=r_w m^w\mathsf S_P(w)\ne0.
\tag{6.10}
\]
У настоящего такого нуля \(w\ne1/2\), поскольку \(\xi(1)\ne0\). Аналитическая часть entire factor не отменяет (6.10). Поэтому нельзя сначала объявить projected meromorphic function голоморфной Herglotz-функцией, а затем сослаться на контакты как на бесплатное удаление её полюсов.

Это не новый adverse zero witness и не lower масштаба \(m^\delta\) для всей \(\mathcal R_{\rm low}\): разные вычеты и контурные участки остаются связанными. Условный (6.10) проверяет лишь точную область предполагаемого holomorphic completion.

## 7. Первая неоплаченная строка и полный бюджет

После (3.5) первая действительно неоплаченная строка остаётся
\[
\boxed{
\Re\frac1{2\pi i}\oint_{\Gamma_m}
 m^z\,[c^*\mathsf S_P(z)c]\,\ell_G(z)\,dz
\ge-C_\epsilon m^{\theta(\epsilon)}\|c\|^2,
\quad c=Pc,\quad\theta(\epsilon)\to0.}
\tag{7.1 OPEN}
\]
В (7.1) один и тот же \(c\) используется на всех сторонах и для всего низкого делителя. Эквивалентно можно использовать один \(W=PWP\succeq0\), \(\operatorname{Tr}W=1\). Ни (5.3), ни (4.3) не превращают комплексный аналитический вес в положительную меру на контуре. Знак (7.1) не следует из real-entire symmetry.

Чтобы не скрыть цену возврата, положим
\[
p_m=B_m+e_m+t_m.
\]
Из (2.7)–(2.9) **точно**
\[
C^0=\mathcal V+\mathcal E-\mathcal R_{\rm high}-\mathcal R_{\rm low}.
\tag{7.2}
\]
Если независимо доказать \(\mathcal R_{\rm low}\succeq-s_mP\), то
\[
T_{>R}\preceq[s_m+p_m+b_{\rm div}]P-H_P,
\tag{7.3}
\]
\[
PK_mP\succeq H_P-[s_m+p_m+50L+8]P,
\tag{7.4}
\]
\[
b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\tag{7.5}
\]

| Компонент | Полная цена | Статус |
|---|---:|---|
| конечная low/high факторизация | 0 | точное равенство |
| whole \(E_H'/E_H\)-контур | 0 | голоморфность внутри общего прямоугольника |
| whole \((F/D_G)'/(F/D_G)\)-контур | \(t_m=O_\epsilon(m^{-1/8}/L^2)\) | это high, не ноль |
| исходная левая вертикаль | \(B_m=O_\epsilon(m^\epsilon L\log L)\) | inherited |
| оба вертикальных хвоста и обе горизонтали source inversion | \(e_m=O_\epsilon(m^{-1/4}/L^2)\) | inherited |
| short divisor | \(O_\epsilon(m^{3\epsilon/2}/L+m^{\epsilon/2}+L^2)\) | только в (7.3) |
| arch | \(50L+8\) | только один раз в direct \(K\) |
| исходные векторы (6.2) | 0 | точная принадлежность прежнему \(P\) |
| whole low floor | \(s_m\) | **не доказан в требуемом масштабе** |

Для \(s_m=C_\epsilon m^{\theta(\epsilon)}\) полная итоговая степень была бы
\[
\eta(\epsilon)=\max\{\theta(\epsilon),2\epsilon\}\longrightarrow0.
\tag{7.6}
\]
Это проверенная импликация, не доказательство premise (7.1).

**Фактически:** из принятого one-sided \(A\preceq s_{\rm keep}P\), \(H_P\preceq4P\), следует только
\[
\mathcal R_{\rm low}\succeq-[s_{\rm keep}+4+p_m]P.
\tag{7.7}
\]
Это уже известная половинная цена, выведенная из исходного верхнего bound. Возвращать (7.7) обратно как новый supplier — круговой bookkeeping с лишними затратами.

Поэтому окончательный безусловный результат **не ухудшаем**:
\[
s_{\rm keep}=W_<(m)+W(\lfloor\sqrt m\rfloor)
\le6\sqrt m+6m^{1/4},
\tag{7.8}
\]
\[
\boxed{
T_{>R}\preceq(s_{\rm keep}+b_{\rm div})P,
\qquad
PK_mP\succeq-[s_{\rm keep}+50L+8]P.}
\tag{7.9}
\]
Ни \(H_P\), ни prime powers не оплачиваются заново. Не начисляем \(p_m\) поверх независимо доказанного direct fallback. Условные результаты с ZF78 остаются условными; ZF78 в этой попытке не используется.

## 8. Обоснованный более ранний откат: логарифм до дифференцирования

Здесь не предлагается снова «доказать Herglotz» или заменить low его абсолютной нормой. Отступаем **до логарифмической производной**, сохраняя весь низкий делитель, непрерывную ветвь его логарифма на том же контуре и её реальную монодромию.

**[FINITE_CELL | PAPER].** Начнём положительный обход \(\Gamma_m\) в
\[
z_0=b_m+iH.
\]
На параметризованном обходе существует единственная непрерывная ветвь
\[
\mathfrak l_m(z)=\log\frac{D_G(z)}{D_G(z_0)},\qquad
\mathfrak l_m(z_0\text{ в начале})=0.
\tag{8.1}
\]
Она не обязана иметь одинаковое значение в начале и конце. Пусть \(\nu_m\) — число low-нулей **внутри** прямоугольника с кратностями. Тогда
\[
\mathfrak l_m(z_0\text{ в конце})=2\pi i\nu_m.
\tag{8.2}
\]
Это обычный argument principle [E3]. Все неизвестные нули сохраняются; \(\nu_m\) не подменяется нулём.

Интегрирование по частям вдоль **полного параметризованного пути** даёт
\[
\boxed{
\mathcal R_{\rm low}
=\mathfrak M_m-\mathfrak J_m,}
\tag{8.3}
\]
\[
\mathfrak M_m=\operatorname{He}\,[\nu_m\mathsf K_m(z_0)],
\qquad
\mathfrak J_m=\operatorname{He}\frac1{2\pi i}
\oint_{\Gamma_m}\mathsf K_m'(z)\mathfrak l_m(z)\,dz.
\tag{8.4}
\]
Это уже не некорректное интегрирование «глобального однозначного логарифма» через нули. Угловые значения на всех четырёх сторонах сокращаются попарно; остаётся ровно монодромный член в \(z_0\).

### Один проверенный количественный вход этой развилки

Используя только \(\nu_m\le N_0(G)\), \(m^{b_m}=e\sqrt m\) и **уже доказанное** убывание четвёртого порядка исходного \(\mathsf S_P\) при \(H\ge2\Omega\), получаем
\[
\boxed{
\|\mathfrak M_m\|
\le j_m:=\frac{8eC_N\sqrt m\,V_2 G\log(G+2)}{H^4}
=O_\epsilon(m^{-7/24}/L^2).}
\tag{8.5}
\]
Проверка степени без скрытых потерь:
\[
\frac12+3\epsilon+(5/24+\epsilon)-4(1/4+\epsilon)=-7/24.
\tag{8.6}
\]
Это законное использование count **только для малого углового члена**. Оно не повторяет ошибку S1 «count \(\Rightarrow\) magnitude всего residue». Все прочие части \(\mathfrak J_m\) ещё остаются вместе.

Из (8.3) условный budget становится
\[
\mathfrak J_m\preceq t_{m,\epsilon}P
\ \Longrightarrow\
\mathcal R_{\rm low}\succeq-(t_{m,\epsilon}+j_m)P,
\tag{8.7}
\]
с дальнейшим возвратом (7.3)–(7.4). Дополнительная плата \(j_m=o(1)\).

**Граница результата:** (8.5) — доказанный аналитический вход, не самостоятельный арифметический знак. Оценка \(\mathfrak J_m\preceq C_\epsilon m^{\theta(\epsilon)}P\) не поставлена. По (8.3), с точностью до (8.5), она эквивалентна прежнему low-floor. Я **не называю её новой независимой леммой-поставщиком**. Дополнительного нетавтологичного арифметического неравенства для этой ветви логарифма я не вывел.

Различающий тест для дальнейшего использования этой записи: supplier должен работать с **всем непрерывным branch** в (8.1), включая его меняющийся аргумент, и реально уменьшать one-sided budget (8.7). Upper для \(|\log D_G|\), удаление winding, generic positivity или только real-axis рост не проходят этот тест. Повтор (8.3) тоже не будет новой попыткой.

### Две сохранённые репрезентации и граница следующего действия

| Представление | Что проверяет | Цена карты / диагностическая сила |
|---|---|---|
| boundary logarithm (8.1)–(8.4), до производной | совместную фазу всей низкой части; обязательную монодромию | карта точна, corner \(o(1)\); дешёвый algebra check обнаруживает потерянную ветвь; новый арифметический знак не получен |
| исходная первая \(C^0\) до нулевого делителя | сохраняет реальные \(\Lambda\) и signed continuum без дополнительной positive-real гипотезы | по (7.2) \(C^0+\mathcal R_{\rm low}\) имеет норму \(\le p_m\); этот известный возврат сам не supplier |

Это не список двух успехов и не разрешение на автоматический Q52. Проверяемое новое ограничение текущего цикла — (MR) нельзя использовать даже после полного low-sum; следующий поставщик обязан обходиться без этой неверной импликации.

## 9. Самая сильная атака на результат и проверки границ

**Возражение:** «Требовался one-sided lower интеграла, а ты проверил более сильную positive-real гипотезу». Возражение верно. Именно поэтому (6.7) классифицирован только как `THEOREM_SHAPE`, а основная задача — `NO_DERIVATION`. Нельзя объявлять low-floor невозможным по провалу (PR)/(MR).

Дополнительные границы:

* Ненулевой analytic residue (6.10) не задаёт знак его Hermitian part и тем более суммы разных нулей. Не назначен никакой actual off-line zero.
* Два пяти-модовых направления используются только для отказа (MR). Они не заменяют весь \(P\) в достаточном потребителе. All-\(P\) оценка остаётся открытой.
* Низкие критические нули и левые партнёры не отбрасываются из делителя. Они просто не пересекаются правым контуром. Условие \(\Re w=u\) исключено выбором общего контура, а не vector-dependent сдвигом.
* Верхняя граница \(|\gamma|=G\) целиком относится к low; \(|\gamma|=H\) не содержит нулей. Новых неучтённых высотных полос нет.
* Исходный атом \(n=m\), prime powers, обе временные стороны и leakage \(n>m\) остаются в принятом (2.7)–(2.8). В этой попытке физическая мера вообще не меняется. Никакого intermediate \(P\) между causal factors не вставлено.
* Непрерывный контроль остаётся \(A[dx]=-H_P\), \(C^0[dx]=0\) до модулей. Нельзя заменить только prime source на continuum, но оставить его старую \(\xi\)-factorization: после такой замены низкий zeta-divisor уже не является представлением изменённого источника. В источниковой карте меняется весь источник, и ноль восстанавливается точно.
* Симметрия не заменяет транспонирование на adjoint. При такой подмене отрицательная строка (6.6) стала бы положительной и представляла бы другую матрицу.
* Отдельные высокие \(o(1)\)-цены (4.7), (8.5) не удаляют большой signed low. Они не названы новым показателем полной CCM.

## 10. Ledger, зависимости и closeout

| Утверждение | Scope | Verifier | Результат |
|---|---|---|---|
| Канонический TXT и восемь тел | FINITE_CELL | PAPER: byte-check | sizes/LF/hash/framing совпали |
| All-\(P\) contour и high-tail S3–S4 | COFINAL_FAMILY | PAPER: inherited | использованы в исходной области |
| Finite whole-low/high/entire split (3.4)–(3.8) | FINITE_CELL | PAPER | полная карта, high сохранён |
| High-factor strip sign и (4.6) | COFINAL_FAMILY | PAPER | доказаны; не low-floor |
| Positive-real equivalence (5.2) | FINITE_CELL | PAPER | отсутствие правых low-нулей — необходимая гипотеза |
| Cofinal (PR) \(\Leftrightarrow\) RH | COFINAL_FAMILY | PAPER | импликация, не premise результата |
| Исходные five-mode contacts и (6.5) | ABSTRACT | PAPER | точная алгебра для всех \(L>0,M\ge2\) |
| Actual matrix-positive-real completion | COFINAL_FAMILY | PAPER | опровергнуто (6.7)–(6.8), только указанная форма |
| Actual low pole survives \(P\) | FINITE_CELL | CONDITIONAL | при существовании такого нуля; sign/magnitude всей суммы не выводятся |
| Branch-log return и winding budget | COFINAL_FAMILY | PAPER | (8.3)–(8.6), corner \(o(1)\) |
| Independent \(\mathcal R_{\rm low}\) floor | COFINAL_FAMILY | CONDITIONAL: OPEN | не выведен |
| Исходный CCM upper / RH | COFINAL_FAMILY | CONDITIONAL: OPEN | не закрыты |
| Exact code controls | FINITE_CELL | PAPER | рациональная алгебра, не actual spectra |

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_ONE_SIDED_T_GT_R
ACTUAL_CONSUMER_REQUIREMENT: eventual_or_common_cofinal_upper_with_eta_epsilon_to_zero
ORIGINAL_REQUESTED_OBJECT: complete_joint_low_residue_lower_on_original_P
ORIGINAL_OBJECT_IS: PROVED_NECESSARY
NECESSITY_SCOPE: vanishing_exponent_family_up_to_the_inherited_paid_contour_fees
KNOWN_WEAKER_INTERFACES:
  - independently proved lower on the complete true witness with all receiver fees; not supplied here
  - direct original A upper with one short-divisor and one archimedean return
METHOD_IS_NECESSARY: false
REJECTED_COMPLETION: He[m^z S_P(z) D_Gprime(z)/D_G(z)] is positive semidefinite throughout Re z>u
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: ACTUAL_SOURCE_PAPER_COUNTEREXAMPLE_FAMILY
PINNED_EVIDENCE: Q51_SECTION_6_EQ_6_7_AND_6_8_WITH_S3_KERNEL_AND_ORIGINAL_CONTACTS
ACTUAL_LOW_FLOOR_FAILURE_TYPE: NO_DERIVATION
ACTUAL_LOW_FLOOR_EPISTEMIC_STATUS: RESEARCH_DEBT
REOPEN_TRIGGER: independent signed integral comparison that does not assume zero exclusion or pointwise matrix positivity
IMPOSSIBILITY_EVIDENCE_FOR_CCM: NONE
NOVELTY_AXIS: actual whole-low multiplier tested on exact original-P resolvent directions; full entire and branch returns retained
LOOP_DETECTED: cheap analytic representation is again at risk of being mistaken for a signed arithmetic supplier
FORBIDDEN_FUTURE_MOVE: infer positive-real matrix order from real-entire symmetry or scalar positive-real log derivative
CONSUMER_PROGRESS: NO_PROGRESS
LOCAL_RESULT_CLASS: FALSIFICATION_PROGRESS_FOR_THE_SPECIFIED_COMPLETION
CURRENT_MINIMAL_MISSING_LINE: Q51_EQ_7_1
NEXT_QUESTION_DISPATCH: NONE
```

**Три мостовых проверки, не три независимые арифметические попытки.** (i) Теорема о вычетах даёт точную карту, но не positive quadrature. (ii) Functional equation задаёт целые орбиты, но не зануляет selected-right divisor. (iii) Positive-real/Herglotz мог бы дать знак только при его реальных гипотезах; скалярная гипотеза содержит zero exclusion, а буквальная матричная (MR) ложна. Это аудит одного предложенного completion.

**Что стало меньше:** неопределённость о допустимости данного positive-real импорта и его entire/branch accounting. **Что не стало меньше:** независимый арифметический upper исходной CCM. **Что отвергнуто:** только (MR) и автоматические переходы к нему. **Что нельзя повторять:** называть (3.5), (8.3), малый high-tail или число локальных проверок доказанным low-floor.

### Зарегистрированные прогнозы

Регистрация сохранена до executable mathematical controls, но после чтения и предварительного PAPER-вывода. Она не выдаётся за прогноз, сделанный до рассуждения. P1 подтверждён точной factor map; P2 — леммой (5.2) и ограниченным отрицательным контролем; P3 — формулами (6.2)–(6.6); P4 — (4.2)–(4.7); P5 — (8.3)–(8.6). P6 — честный closeout: независимая искомая оценка не получена. Код не является доказательством P6 или универсальных асимптотических утверждений.

Совместное следствие (6.7)–(6.8) сформулировано при окончательном PAPER-аудите из уже проверенных скалярного знака и двух контактных contractions; отдельного первоначального предсказания нового favorable sign не было.

Одна архивная директива: независимо проверить (3.5)–(3.8), (5.2), фактический scope (6.7) и стоимость winding в (8.5), затем воспроизвести приложения. Не повышать статус CCM по результату такого аудита. Никаких репозиторных записей или автоматической следующей отправки.

### Запись стратегии

```yaml
MEMORY_ENTRY:
  iteration: Q51_JOINT_LOW_RESIDUE
  target: signed_low_residue_floor_on_original_P
  status: OPEN
  failed_strategy: scalar_positive_real_log_derivative_as_a_free_matrix_order_supplier
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: analytic_transpose_and_contour_phase_survive_whole_divisor_grouping
  forbidden_future_move: drop_high_zeros_of_entire_quotient_or_boundary_log_winding
  smallest_unpaid_input: Q51_EQ_7_1_OR_EQUIVALENT_WHOLE_BRANCH_PAIRING
  next_decisive_test: independent_PAPER_audit_of_the_actual_P_completion_counterexample_and_full_return
  consumer_progress: NO_PROGRESS
  route_score: 2
  local_completion_result: FALSIFICATION_PROGRESS
  mathematical_route_death: NOT_ESTABLISHED
```

## 11. Внешние источники: точные использованные утверждения

[E1] NIST DLMF 25.4.3–25.4.4: определение завершённой \(\xi\) и \(\xi(s)=\xi(1-s)\). Используются только для (3.1), симметрии и нормировки нулей.

[E2] NIST DLMF 25.10(i): все нетривиальные нули лежат в \(0<\Re\rho<1\), симметричны относительно критической прямой и вещественной оси; таких нулей бесконечно много. Никакие проценты, компьютерные высоты или RH из этой страницы не используются.

[E3] NIST DLMF 1.10.8–1.10.9: обычная residue theorem для положительно ориентированного контура и argument principle с кратностями. Применение к конечным произведениям в (3.5)–(3.8), (8.2)–(8.4) выписано здесь. Гипотезы голоморфности и отсутствие нулей на контуре проверены отдельно.

```text
[E1] https://dlmf.nist.gov/25.4#E3
     https://dlmf.nist.gov/25.4#E4
[E2] https://dlmf.nist.gov/25.10#i
[E3] https://dlmf.nist.gov/1.10#E8
     https://dlmf.nist.gov/1.10#E9
```

В этой ограниченной проверке внешний theorem о favorable signed residue не установлен и не принят; отсутствие такого результата в литературе не утверждается. Все дополнительные неравенства этого ответа выведены выше; их мировой приоритет не заявляется.

## 12. Манифест и воспроизводимость

Приложения используют только стандартную библиотеку Python. Все комплексные алгебраические знаки в тестах вычисляются в поле гауссовых рациональных чисел; float, численная квадратура и подставленные zeta zeros не используются. Рациональные \(\Delta\) в проверках — специализации тождества для произвольного \(\Delta>0\), **не** реальные производственные ячейки \(\Delta=2\pi/\log m\).

Код проверяет конечные log-derivative коэффициенты и кратности, symmetry, три контакта, обе временные ориентации, analytic squares, separated-height formula, monodromy и рациональные степени. Его негативные контроли относятся ровно к указанным алгебраическим импликациям. В частности, контроль \(\epsilon=1/32\) — только проверка полиномиальной формулы для показателя на границе, не расширение допустимой области source theorem.

**Независимый новый аудит, Lean, Arb и production-спектральные расчёты не запускались.** Исторические scripts из исходников не исполнялись. Полные code/results находятся ниже; размер тестовой панели не считается прогрессом доказательства.

### Проверенный source manifest

Диапазоны строк ниже относятся к **raw TXT**, а не к пагинации retrieval-инструмента. Byte-диапазоны имеют вид `[start,end)`; разделительный LF не входит в тело.

| ID | Полное имя тела | Bytes / LF | SHA-256 | Raw строки | Byte-диапазон |
|---|---|---:|---|---:|---:|
| S1 | `CCM_POST_Q50_COUNT_TO_MAGNITUDE_SCREEN.md` | 6798 / 124 | `c08d09ff440f982fc346724e506e53da20ba9290b78dab07e229b3d73c60a44a` | 32–155 | [6362,13160) |
| S2 | `CCM_POST_Q50_MOVING_ATOM_RESOLUTION.md` | 3881 / 71 | `e5a55028deb5d2cec7ca5da1d8d031eb2075c88a2ce36a486e8ca77da7e75eb8` | 160–230 | [13217,17098) |
| S3 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 / 123 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` | 235–357 | [17151,22784) |
| S4 | `CCM_POST_Q27_DENSITY_BUDGET.md` | 4636 / 93 | `87c3faa5a652ca4d205e82674553ad0f5f5a1c24735c43a09d98d4560c3dc166` | 362–454 | [22833,27469) |
| S5 | `CCM_POST_Q20_TRANSLATED_WITNESS_RANK.md` | 9722 / 179 | `f9e686ef665bd7aa788933b68fb8c2c6ece133ad4c6f4e9817d0673221227fa2` | 459–637 | [27527,37249) |
| S6 | `CCM_Q50_CONCLUSION.md` | 3569 / 63 | `76cd92d7f349ce2ba1e7992103bb85f13d1982c17d48b3e2b3ac425c61c9f5e9` | 642–704 | [37289,40858) |
| S7 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 / 69 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` | 709–777 | [40904,47078) |
| S8 | `CCM_Q19_CONCLUSION.md` | 3904 / 65 | `a4e083fab0eba1d57dda5ce4b1253163e4da0e6715bc8c0b65af510f5f2f36ec` | 782–846 | [47118,51022) |

### Как воспроизвести именно эти проверки

Сохрани тело приложения `replay_q51.py` в отдельный файл. Из каталога с ответом и исходным TXT выполни:

```bash
python3 replay_q51.py \
  PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_VERDICT_2026-10-27.md \
  PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_2026-10-27.txt \
  q51_replay
```

Первый аргумент — этот Markdown; второй — канонический TXT, **без редактирования байтов**; третий — каталог извлечённых приложений. При другом размещении замени только пути. Например, первый аргумент может быть `./archive/PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_VERDICT_2026-10-27.md`. Python 3.9+ со стандартной библиотекой достаточен; установка пакетов не требуется.

Replayer проверяет byte-count/SHA каждого из четырёх приложений, извлекает их, запускает только новый `check_q51.py` и сравнивает JSON побайтно. Ни одного исторического source script он не выполняет. Код не подставляет численные координаты нулей настоящей ζ.

### Полные приложения

BEGIN_ASSET registration_q51.json
BYTES: 1623
SHA256: 3b10c463dd5abd71ad37868c2cfcb5df424b81d434890ba9422d7d2a5f3e49c3
```json
{
  "task": "Q51_JOINT_LOW_RESIDUE",
  "stage": "After full packet reading and preliminary PAPER derivation; before executable mathematical controls",
  "mechanism": "Finite whole-low zero divisor with full entire quotient, tested positive-real completion and exact original-P pole visibility",
  "predictions": {
    "P1": "The quotient after removing only zeros up to G retains the high zeros up to H; removing all zeros up to H leaves zero full contour contribution, not zero boundary integrand.",
    "P2": "For the finite low divisor, holomorphic positive-real logarithmic derivative on Re(z)>u is equivalent to absence of its roots in that half-plane; symmetry alone does not supply it.",
    "P3": "Explicit even and odd five-mode vectors obey the three original contacts, and their analytic quadratic contractions are nonzero for Re(z)>0 and z not equal to 1/2.",
    "P4": "The high finite divisor has nonnegative real logarithmic derivative in the height-separated inner strip; its complete contour contribution is only the already paid high tail.",
    "P5": "Integration by parts of a continuous boundary logarithm retains the winding corner; its displayed original-kernel bound has power -7/24.",
    "P6": "No full new low-residue floor follows from these controls; the only unconditional final consumer bound remains the inherited fallback."
  },
  "scope": "Finite exact algebra controls and PAPER estimates; no numeric zeta-zero assignments, production spectra or asymptotic sign certification by code",
  "historical_source_code_execution": false,
  "repository_writes": false,
  "installations": false
}
```
END_ASSET

BEGIN_ASSET check_q51.py
BYTES: 12607
SHA256: f676f6a4ea9eaceb2210868b1ce6d959c2425b0415e1b58ea15588a31cf96417
```python
#!/usr/bin/env python3
"""Q51: byte framing and exact finite algebra, NOT production CCM spectra.
Usage: python3 check_q51.py CANONICAL_Q51.txt
Only the Python standard library is required. Historical programs are not run.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re
import sys

SIZE = 51031
LF = 849
SHA = '5c34576e47a0b1b23a94cda5c381d29402355613e20e734846104f2eb919d61d'
NAME = 'PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_2026-10-27.txt'
MANIFEST = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def verify(raw: bytes, outer: bool = True) -> dict:
    if outer and (len(raw) != SIZE or raw.count(b'\n') != LF or hashlib.sha256(raw).hexdigest() != SHA):
        raise ValueError('canonical bytes/LF/SHA mismatch')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'):
        raise ValueError('newline convention')
    if not raw.startswith(b'Q51 JOINT_LOW_RESIDUE'):
        raise ValueError('wrong request')
    pos = raw.index(b'BEGIN S1 ')
    heads = list(MANIFEST.finditer(raw[:pos]))
    if len(heads) != 8:
        raise ValueError('manifest count')
    rows = []
    for expected, h in enumerate(heads, 1):
        sid = 'S' + h[1].decode()
        if sid != f'S{expected}':
            raise ValueError('source order')
        name = h[2].decode()
        begin = f'BEGIN {sid} {name}\n'.encode()
        if raw[pos:pos + len(begin)] != begin:
            raise ValueError('source opening')
        start = pos + len(begin)
        end = start + int(h[3])
        body = raw[start:end]
        if len(body) != int(h[3]) or body.count(b'\n') != int(h[4]):
            raise ValueError('source size/LF')
        if hashlib.sha256(body).hexdigest() != h[5].decode():
            raise ValueError('source SHA')
        body.decode('utf-8')
        suffix = f'\nEND {sid}\n'.encode()
        if raw[end:end + len(suffix)] != suffix:
            raise ValueError('source closing')
        rows.append(dict(id=sid, name=name, bytes=len(body), lf=body.count(b'\n'),
                         sha256=h[5].decode(), start_byte=start, end_byte=end,
                         start_line=raw[:start].count(b'\n') + 1,
                         end_line=raw[:end].count(b'\n')))
        pos = end + len(suffix)
        if pos < len(raw):
            if raw[pos:pos + 1] != b'\n':
                raise ValueError('inter-source separator')
            pos += 1
    if pos != len(raw):
        raise ValueError('trailing content')
    return dict(packet=NAME, bytes=len(raw), lf=raw.count(b'\n'),
                sha256=hashlib.sha256(raw).hexdigest(), source_count=8,
                all_frames_verified=True, sources=rows)


@dataclass(frozen=True)
class Q:
    """Gaussian rational, for exact complex algebra (no float conversion)."""
    re: F = F(0)
    im: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q) else Q(F(x))

    def __add__(self, x):
        x = Q.cast(x)
        return Q(self.re + x.re, self.im + x.im)

    __radd__ = __add__

    def __neg__(self):
        return Q(-self.re, -self.im)

    def __sub__(self, x):
        return self + (-Q.cast(x))

    def __rsub__(self, x):
        return Q.cast(x) - self

    def __mul__(self, x):
        x = Q.cast(x)
        return Q(self.re*x.re - self.im*x.im, self.re*x.im + self.im*x.re)

    __rmul__ = __mul__

    def conj(self):
        return Q(self.re, -self.im)

    def norm2(self):
        return self.re*self.re + self.im*self.im

    def inverse(self):
        n = self.norm2()
        if not n:
            raise ZeroDivisionError('zero Gaussian rational')
        return Q(self.re/n, -self.im/n)

    def __truediv__(self, x):
        return self * Q.cast(x).inverse()

    def __rtruediv__(self, x):
        return Q.cast(x) * self.inverse()

    def __pow__(self, n):
        if not isinstance(n, int):
            raise TypeError('integer exponent required')
        if n < 0:
            return self.inverse() ** (-n)
        r, a = Q(1), self
        while n:
            if n & 1:
                r = r*a
            a = a*a
            n //= 2
        return r

    def pair(self):
        return [str(self.re), str(self.im)]


I = Q(0, 1)
ZERO = Q()


def dot(a, b):
    return sum((Q.cast(x)*Q.cast(y) for x, y in zip(a, b)), ZERO)


def pmul(a, b):
    out = [ZERO] * (len(a) + len(b) - 1)
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            out[j+k] = out[j+k] + x*y
    return out


def polynomial(roots):
    p = [Q(1)]
    for w, r in roots:
        for _ in range(r):
            p = pmul(p, [-w, Q(1)])
    return p


def peval(p, z):
    r = ZERO
    for a in reversed(p):
        r = r*z + a
    return r


def deriv(p):
    return [j*p[j] for j in range(1, len(p))]


def ld(roots, z):
    return sum((r/(z-w) for w, r in roots), ZERO)


def quartet(delta, gamma, r=1):
    return [(Q(s*delta, t*gamma), r) for s in (-1, 1) for t in (-1, 1)]


def math_checks():
    counts = {}
    errors = {}
    # Synthetic symmetric divisors test algebra only. They are NOT zeta zeros.
    low = quartet(F(1,4), F(1), 2) + [(Q(0, 2), 3), (Q(0, -2), 3)]
    high = quartet(F(1,5), F(7), 1)
    pl, ph = polynomial(low), polynomial(high)
    pall = pmul(pl, ph)
    nodes = [Q(F(1,8), F(1,3)), Q(F(3,4), F(5,2)), Q(2, -3)]
    for z in nodes:
        assert peval(deriv(pl), z)/peval(pl, z) == ld(low, z)
        assert peval(deriv(pall), z)/peval(pall, z) == ld(low, z) + ld(high, z)
        assert peval(pl, -z) == peval(pl, z)
        assert peval(pl, z.conj()) == peval(pl, z).conj()
    counts['finite_divisor_nodes'] = len(nodes)
    assert all(x.im == 0 for x in pl)
    assert all(pl[j] == ZERO for j in range(1, len(pl), 2))
    errors['drop_entire_factor_high_zeros'] = ld(high, nodes[0]) != ZERO
    errors['erase_multiplicity'] = ld(low, nodes[0]) != ld([(w, 1) for w, _ in low], nodes[0])

    # Positivity in a safely zero-free right half-plane; no assertion on actual xi.
    for z in [Q(F(3,4), t) for t in (F(-4), F(0), F(3,2), F(8))]:
        assert ld(low, z).re > 0
    counts['right_halfplane_exact_controls'] = 4
    toy = quartet(F(1,4), F(1))
    zz = Q(F(6,25), F(1))
    negative = ld(toy, zz).re
    assert negative < -90
    errors['even_real_implies_positive_real'] = negative < 0

    # Real/odd contact vectors; d is a rational test parameter for omega_1.
    # The PAPER identities hold for every real d>0, including d=2pi/log(m).
    a = F(1,2)
    js = [-2, -1, 0, 1, 2]
    vector_cases = 0
    positive_even = negative_odd = None
    for d in (F(1,3), F(2,5), F(3,2)):
        q1, q2 = a*a+d*d, a*a+4*d*d
        e = [q2, -4*q1, 6*a*a, -4*q1, q2]
        o = [q2, -2*q1, F(0), 2*q1, -q2]
        assert sum(e) == 0 and sum(o) == 0
        for c in (e, o):
            for s in (-1, 1):
                assert dot(c, [1/(Q(a)+s*I*j*d) for j in js]) == ZERO
        for z in (Q(F(1,4), F(2,3)), Q(F(2,7), F(-4,5)), Q(F(1,4))):
            r = [z/(z*z+(j*d)**2) for j in js]
            t = [Q(j*d)/(z*z+(j*d)**2) for j in js]
            E = 24*d**4*(a*a-z*z)/(z*(z*z+d*d)*(z*z+4*d*d))
            O = 12*d**3*(a*a-z*z)/((z*z+d*d)*(z*z+4*d*d))
            assert dot(e, r) == E and dot(o, t) == O
            assert dot(e, t) == ZERO and dot(o, r) == ZERO
            vp = [1/(z+I*j*d) for j in js]
            vm = [1/(z-I*j*d) for j in js]
            qe = dot(e, vp)**2 + dot(e, vm)**2
            qo = dot(o, vp)**2 + dot(o, vm)**2
            assert qe == 2*E*E and qo == -2*O*O
            assert E != ZERO and O != ZERO
            assert dot(e, vp)*dot(o, vp)+dot(e, vm)*dot(o, vm) == ZERO
            vector_cases += 1
            if z.im == 0:
                assert qe.re > 0 and qo.re < 0
                positive_even, negative_odd = qe.re, qo.re
                errors['transpose_replaced_by_adjoint'] = qo.re != dot(o, vp).norm2()+dot(o, vm).norm2()
                errors['omit_one_time_orientation'] = qo != dot(o, vp)**2
        # Both contact contractions vanish at the actual contact exponent a.
        ra = [Q(a)/(a*a+(j*d)**2) for j in js]
        ta = [Q(j*d)/(a*a+(j*d)**2) for j in js]
        assert dot(e, ra) == ZERO and dot(o, ta) == ZERO
        raw0 = [F(0), F(0), F(1), F(0), F(0)]
        errors['raw_zero_mode_treated_as_contact_vector'] = dot(raw0, ra) != ZERO
    counts['five_mode_parameter_pairs'] = vector_cases

    # Exact reflected pair formula and high-divisor inner-strip sign.
    pair_cases = 0
    for delta in (F(0), F(1,4), F(2,5)):
        for x in (F(1,16), F(1,3), F(1)):
            for y in (F(-5), F(-2), F(2), F(5)):
                p = (1/Q(x-delta, y)+1/Q(x+delta, y)).re
                rhs = 2*x*(x*x+y*y-delta*delta)/(((x-delta)**2+y*y)*((x+delta)**2+y*y))
                assert p == rhs and p > 0
                pair_cases += 1
    counts['reflected_pair_controls'] = pair_cases
    near = (1/Q(F(1,8)-F(1,4), 0)+1/Q(F(1,8)+F(1,4), 0)).re
    assert near < 0
    errors['extend_separated_height_sign_to_pole_neighborhood'] = near < 0

    # Monodromy: D(z)=z^r, K polynomial, positively oriented unit circle.
    # Exact integrated formula after division by 2pi*i; no quadrature.
    for r in (1, 2, 5):
        for co in ([F(1)], [F(2), F(-3), F(4)], [F(0), F(2,3), F(-5,7), F(1)]):
            residue = r*co[0]
            corner = r*sum(co)
            primitive_integral = r*sum(co[1:])
            assert residue == corner-primitive_integral
    counts['monodromy_polynomial_controls'] = 9
    errors['drop_winding_corner'] = F(2) != F(0)  # D=z^2, K=1
    errors['reverse_winding_orientation'] = F(2) != F(-2)

    exponent_rows = []
    for eps in (F(1,128), F(1,64), F(1,100), F(1,32)):
        kap = F(5,24)+eps
        high_power = F(1,2)+3*eps-3*kap
        corner_power = F(1,2)+3*eps+kap-4*(F(1,4)+eps)
        middle_power = 2*eps-kap
        assert high_power == -F(1,8)
        assert corner_power == -F(7,24)
        assert middle_power == eps-F(5,24) < 0
        exponent_rows.append(dict(epsilon=str(eps), high=str(high_power), corner=str(corner_power), middle=str(middle_power)))
    counts['rational_budget_controls'] = len(exponent_rows)
    # Complete signed reassembly; no new spectral estimate is asserted.
    A, Hd, vert, err, rhigh = map(F, [7, 2, 3, -1, 4])
    rlow = vert+err-rhigh-A-Hd
    assert A == -Hd+vert-rlow-rhigh+err
    errors['double_continuous_charge'] = A != -2*Hd+vert-rlow-rhigh+err
    assert all(errors.values())
    return dict(
        passed=True,
        scope='Exact finite algebra and rational surrogate controls; NOT production CCM or numeric zeta zeros',
        counts=counts,
        negative_control=dict(real_logder=str(negative), upper_bound='-90', actual_zeta_data=False),
        five_mode_real_example=dict(L_scaled_even=str(positive_even), L_scaled_odd=str(negative_odd), actual_cell=False),
        exponent_rows=exponent_rows,
        planted_errors_detected=errors,
        original_P_cofinal_floor_certified_by_code=False,
        independent_arithmetic_supplier=False)


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: python3 check_q51.py CANONICAL_Q51.txt')
    raw = Path(sys.argv[1]).read_bytes()
    provenance = verify(raw)
    cases = {}
    bad = bytearray(raw)
    bad[provenance['sources'][0]['start_byte']+40] ^= 1
    for name, value, outer in (
        ('one_byte_corruption', bytes(bad), True),
        ('body_hash_without_outer_guard', bytes(bad), False),
        ('extra_separator', raw[:provenance['sources'][0]['end_byte']]+b'\n'+raw[provenance['sources'][0]['end_byte']:], False),
        ('truncated_final_frame', raw[:-2], False),
    ):
        try:
            verify(value, outer=outer)
        except (ValueError, UnicodeError):
            cases[name] = True
        else:
            raise AssertionError('missed provenance mutation '+name)
    result = dict(provenance=provenance, provenance_mutations=cases,
                  mathematics=math_checks(),
                  historical_programs_executed=False, production_spectrum=False,
                  numeric_zeta_zeros=False, lean=False, arb=False, independent_new_audit=False)
    text = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2)+'\n'
    Path('q51_checks.json').write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
```
END_ASSET

BEGIN_ASSET q51_checks.json
BYTES: 5030
SHA256: 460386d8b5ef69ea88f315bbf9337e539cac3da0cb4c35045d6c3870df4789eb
```json
{
  "arb": false,
  "historical_programs_executed": false,
  "independent_new_audit": false,
  "lean": false,
  "mathematics": {
    "counts": {
      "finite_divisor_nodes": 3,
      "five_mode_parameter_pairs": 9,
      "monodromy_polynomial_controls": 9,
      "rational_budget_controls": 4,
      "reflected_pair_controls": 36,
      "right_halfplane_exact_controls": 4
    },
    "exponent_rows": [
      {
        "corner": "-7/24",
        "epsilon": "1/128",
        "high": "-1/8",
        "middle": "-77/384"
      },
      {
        "corner": "-7/24",
        "epsilon": "1/64",
        "high": "-1/8",
        "middle": "-37/192"
      },
      {
        "corner": "-7/24",
        "epsilon": "1/100",
        "high": "-1/8",
        "middle": "-119/600"
      },
      {
        "corner": "-7/24",
        "epsilon": "1/32",
        "high": "-1/8",
        "middle": "-17/96"
      }
    ],
    "five_mode_real_example": {
      "L_scaled_even": "1088391168/28783225",
      "L_scaled_odd": "-7558272/28783225",
      "actual_cell": false
    },
    "independent_arithmetic_supplier": false,
    "negative_control": {
      "actual_zeta_data": false,
      "real_logder": "-8131799049600/83108037649",
      "upper_bound": "-90"
    },
    "original_P_cofinal_floor_certified_by_code": false,
    "passed": true,
    "planted_errors_detected": {
      "double_continuous_charge": true,
      "drop_entire_factor_high_zeros": true,
      "drop_winding_corner": true,
      "erase_multiplicity": true,
      "even_real_implies_positive_real": true,
      "extend_separated_height_sign_to_pole_neighborhood": true,
      "omit_one_time_orientation": true,
      "raw_zero_mode_treated_as_contact_vector": true,
      "reverse_winding_orientation": true,
      "transpose_replaced_by_adjoint": true
    },
    "scope": "Exact finite algebra and rational surrogate controls; NOT production CCM or numeric zeta zeros"
  },
  "numeric_zeta_zeros": false,
  "production_spectrum": false,
  "provenance": {
    "all_frames_verified": true,
    "bytes": 51031,
    "lf": 849,
    "packet": "PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_2026-10-27.txt",
    "sha256": "5c34576e47a0b1b23a94cda5c381d29402355613e20e734846104f2eb919d61d",
    "source_count": 8,
    "sources": [
      {
        "bytes": 6798,
        "end_byte": 13160,
        "end_line": 155,
        "id": "S1",
        "lf": 124,
        "name": "CCM_POST_Q50_COUNT_TO_MAGNITUDE_SCREEN.md",
        "sha256": "c08d09ff440f982fc346724e506e53da20ba9290b78dab07e229b3d73c60a44a",
        "start_byte": 6362,
        "start_line": 32
      },
      {
        "bytes": 3881,
        "end_byte": 17098,
        "end_line": 230,
        "id": "S2",
        "lf": 71,
        "name": "CCM_POST_Q50_MOVING_ATOM_RESOLUTION.md",
        "sha256": "e5a55028deb5d2cec7ca5da1d8d031eb2075c88a2ce36a486e8ca77da7e75eb8",
        "start_byte": 13217,
        "start_line": 160
      },
      {
        "bytes": 5633,
        "end_byte": 22784,
        "end_line": 357,
        "id": "S3",
        "lf": 123,
        "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
        "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2",
        "start_byte": 17151,
        "start_line": 235
      },
      {
        "bytes": 4636,
        "end_byte": 27469,
        "end_line": 454,
        "id": "S4",
        "lf": 93,
        "name": "CCM_POST_Q27_DENSITY_BUDGET.md",
        "sha256": "87c3faa5a652ca4d205e82674553ad0f5f5a1c24735c43a09d98d4560c3dc166",
        "start_byte": 22833,
        "start_line": 362
      },
      {
        "bytes": 9722,
        "end_byte": 37249,
        "end_line": 637,
        "id": "S5",
        "lf": 179,
        "name": "CCM_POST_Q20_TRANSLATED_WITNESS_RANK.md",
        "sha256": "f9e686ef665bd7aa788933b68fb8c2c6ece133ad4c6f4e9817d0673221227fa2",
        "start_byte": 27527,
        "start_line": 459
      },
      {
        "bytes": 3569,
        "end_byte": 40858,
        "end_line": 704,
        "id": "S6",
        "lf": 63,
        "name": "CCM_Q50_CONCLUSION.md",
        "sha256": "76cd92d7f349ce2ba1e7992103bb85f13d1982c17d48b3e2b3ac425c61c9f5e9",
        "start_byte": 37289,
        "start_line": 642
      },
      {
        "bytes": 6174,
        "end_byte": 47078,
        "end_line": 777,
        "id": "S7",
        "lf": 69,
        "name": "CCM_SPARSE_BAND_RECEIVER.md",
        "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
        "start_byte": 40904,
        "start_line": 709
      },
      {
        "bytes": 3904,
        "end_byte": 51022,
        "end_line": 846,
        "id": "S8",
        "lf": 65,
        "name": "CCM_Q19_CONCLUSION.md",
        "sha256": "a4e083fab0eba1d57dda5ce4b1253163e4da0e6715bc8c0b65af510f5f2f36ec",
        "start_byte": 47118,
        "start_line": 782
      }
    ]
  },
  "provenance_mutations": {
    "body_hash_without_outer_guard": true,
    "extra_separator": true,
    "one_byte_corruption": true,
    "truncated_final_frame": true
  }
}
```
END_ASSET

BEGIN_ASSET replay_q51.py
BYTES: 2877
SHA256: ba29169bead45b0bede49bfe4c3e85b2b94728e0efd0e30b4304562ee617eb6d
```python
#!/usr/bin/env python3
"""Extract and replay Q51's four new assets; never run historical source bodies.
Usage: python3 replay_q51.py VERDICT.md CANONICAL_Q51.txt [OUTPUT_DIRECTORY]
Only the standard library is required.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HEAD = re.compile(
    rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\n'
    rb'SHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n', re.M)
EXPECTED = {'registration_q51.json', 'check_q51.py',
            'q51_checks.json', 'replay_q51.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    assets = {}
    pos = 0
    while True:
        h = HEAD.search(raw, pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name in assets or name not in EXPECTED:
            raise ValueError('unexpected/duplicate asset: ' + name)
        start = h.end()
        end = start + int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]):
            raise ValueError('asset length mismatch: ' + name)
        if hashlib.sha256(body).hexdigest() != h[3].decode('ascii'):
            raise ValueError('asset SHA mismatch: ' + name)
        body.decode('utf-8')
        closing = b'```\nEND_ASSET\n'
        if raw[end:end+len(closing)] != closing:
            raise ValueError('asset frame mismatch: ' + name)
        assets[name] = body
        pos = end + len(closing)
    if set(assets) != EXPECTED:
        raise ValueError('missing asset')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q51.py VERDICT.md CANONICAL_Q51.txt [OUTPUT_DIRECTORY]')
    verdict = Path(sys.argv[1]).resolve()
    canonical = Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q51_replay').resolve()
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = out / name
        if target.resolve() in (verdict, canonical):
            raise ValueError('output would overwrite an input')
        target.write_bytes(body)
    run = subprocess.run(
        [sys.executable, str(out / 'check_q51.py'), str(canonical)],
        cwd=out, capture_output=True, check=True)
    (out / 'check_q51.stdout').write_bytes(run.stdout)
    if (out / 'q51_checks.json').read_bytes() != assets['q51_checks.json']:
        raise ValueError('replayed JSON is not byte-identical')
    result = dict(asset_count=len(assets), all_asset_hashes_match=True,
                  checker_executed=True, json_byte_identical=True,
                  historical_programs_executed=False,
                  production_spectrum=False, independent_audit=False)
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
```
END_ASSET

## 13. Фактическое воспроизведение окончательного ответа

Четыре приложения извлечены из собранного Markdown с проверкой их размеров, SHA-256 и framing. Извлечённый `check_q51.py` исполнен на каноническом Q51 TXT; результат совпал побайтно со встроенным `q51_checks.json`.

```json
{
  "all_asset_hashes_match": true,
  "asset_count": 4,
  "checker_executed": true,
  "historical_programs_executed": false,
  "independent_audit": false,
  "json_byte_identical": true,
  "production_spectrum": false
}
```

Проверяющий подтвердил конечные тождества и обнаружил **10 предусмотренных алгебраических ошибок**; отдельно обнаружены четыре нарушения provenance: повреждение байта под внешним хешем, то же повреждение при независимой проверке body-хеша, лишний разделитель и обрезанный последний frame. Это тесты чувствительности проверяющего, не 14 независимых математических прорывов.

Фактические математические группы: три узла конечной факторизации, девять пар параметров для contact/contraction identities, 36 проверок отражённых полюсных пар, четыре контроля безопасной правой полуплоскости, девять monodromy-polynomial случаев и четыре рациональные подстановки степенного бюджета. Конечная панель не заменяет PAPER-доказательства всех кванторов выше.

**Итог Q51:** исходный источник, проектор и полный бюджет сохранены. Whole-low positive-real completion проверен; его буквальный матричный вариант отвергнут на actual original-P направлениях, а скалярный вариант требует исключения выбранных нулей. Независимая направленная оценка всей низковысотной суммы не получена. Оплаченный branch-log corner — вспомогательный результат, не новая степень CCM. RH остаётся незаявленной; исходная цель открыта.

Упаковочная проверка: дополнительный наивный `count("BEGIN_ASSET ")` сначала учёл также буквальную строку внутри кода replayer и остановился. Anchored-проверка начала строк подтвердила ровно четыре приложения. Исполняемый byte-framing replayer до и после этого контроля прошёл без изменения математики, кода проверок или ожидаемого JSON.
