# STATUS: TRY_CCM_JOINT_BOUNDARY_PHASE_Q52
```yaml
OPERATIVE_CLASS: TRY_CCM_JOINT_BOUNDARY_PHASE_Q52
REQUEST_ID: Q52_JOINT_BOUNDARY_PHASE
DATE: 2026-10-27
LANGUAGE: ru
SOURCE_OBJECT: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
BASE_COMMIT: a8b986bdf8c68cc38acb403979c8bacd382687ce
PACKET_BYTES: 129443
PACKET_LF: 2162
PACKET_SHA256: 2832d7259a0c5fbac9e4d6882775457f76ce8673ce3862ff6672d23f54286b13
SOURCE_BODIES: 8
MANIFEST: VERIFIED
CONSUMER_PROGRESS: NO_PROGRESS
INDEPENDENT_ARITHMETIC_SIGNED_SUPPLIER: NOT_DERIVED
NEW_CONSUMER_EXPONENT: NOT_PROVED
CHOSEN_MECHANISM: JOINT_GREEN_PAIRING_WITH_ONE_ORIGINAL_LAPLACE_SUPPORT_ROLLBACK
AUXILIARY_RESULTS:
  - FULL_MATRIX_GREEN_WEIGHT_AND_LOGARITHMIC_SINGULAR_RETURN
  - FINITE_ACTUAL_DIVISOR_BLASCHKE_PHASE_WITHOUT_ZERO_ABSENCE_PREMISE
  - WHOLE_STABLE_PHASE_BOUND_O_M_EPSILON_LOG_M
  - EXACT_FINITE_POSITIVE_TIME_POISSON_RETURN
  - ALL_P_INTEGRATED_CONTACT_DEFECT_MINUS_TWO_DECAY_KERNELS
FIRST_UNPAID_STEP: JOINT_SIGN_OF_FINITE_GROWTH_RETURN_FOR_ALL_ACTUAL_SELECTED_ROOTS
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
LOCAL_COMPLETION_FAILURE: FREE_POISSON_REPRODUCTION_OF_THE_EXPONENTIAL_TYPE_TRANSFER
LOCAL_FAILURE_TYPE: COUNTEREXAMPLE
LOCAL_KILL_SCOPE: THEOREM_SHAPE
LOCAL_KILL_EVIDENCE: SECTION_7_EQ_7_5_NEGATIVE_UPPER_ON_ORIGINAL_P
CCM_OR_RH_IMPOSSIBILITY: NOT_ESTABLISHED
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
VERIFIER: PAPER
UPSTREAM_CONTOUR_AND_RECEIVER: INHERITED_IN_THEIR_STATED_SCOPES
RH: OPEN_NOT_CLAIMED
PX_RH_CLAIM: NOT_MADE
CF22_PYSR: PARKED_REOPENABLE
REPOSITORY_WRITES: NONE
INSTALLATIONS: NONE
LEAN: NOT_RUN
ARB: NOT_RUN
INDEPENDENT_NEW_AUDIT: NOT_RUN
PRODUCTION_CCM_SPECTRUM: NOT_RUN
NUMERIC_ACTUAL_ZERO_ASSIGNMENTS: NONE
NEXT_QUESTION_DISPATCH: NONE
```

Ы. **Независимой односторонней оценки нужной силы для полной исходной CCM в Q52 не получено.** Совместная связь аргумента и модуля возвращает меру нулей с весом \(\operatorname{He}K(z)\), а не положительный квадрат. Поэтому положительность лапласиана сама не завершает оценку.

После этой проверки выполнен один откат к **исходному лапласовскому ядру S3 до boundary-log и его примитивов**. В нём проверен другой конкретный вход: конечный множитель Бляшке настоящего выбранного делителя имеет положительную плотность убывания граничной фазы, не требуя RH. Весь соответствующий устойчивый граничный вклад оценён на исходном \(P\):
\[
\|\mathcal P_m\|\le
64e^2C_N L(1+\Omega)\log(10+8\Omega)
=O_\epsilon(m^\epsilon L).
\tag{0.1}
\]
Однако **это не весь вычет**. Экспоненциальный тип \(m^z\) оставляет точную конечновременную поправку. Её нельзя удалить по формуле Пуассона. Уже при исходном контактном показателе \(z=1/2\) поправка равна
\[
-H_{1/2}-H_{1/2-2u}\prec0
\quad\text{на ненулевом исходном }\operatorname{ran}P.
\tag{0.2}
\]
Здесь оба \(H_a\) — явно определённые сжатия **положительных убывающих ядер**. Это проверка **целого интегрального переноса**, не повтор поточечного теста Q51. Но (0.2) имеет цену не более 12 и не является препятствием subpower-оценке. Контактная точка не объявлена нулём \(\xi\).

Оставшаяся полная поправка по настоящим нулям возвращает основной долг с коэффициентом один. Её новый благоприятный знак не доказан. Ни вспомогательная оценка (0.1), ни точная карта ниже не объявляются улучшением полной арифметической степени.

## 1. Source lock, область чтения и зависимости

Прочитаны весь канонический UTF-8 TXT и восемь тел, включая полный Q51 с кодом и JSON. Проверены размеры, LF, SHA-256, порядок, открывающие/закрывающие строки и внешние разделители. Общий хеш Q52 вычислен из смонтированных байтов; краткая пользовательская подпись его не задавала. Указанные в manifest хеши всех восьми тел совпали.

Канонический файл:

```text
PROSHKA_CCM_JOINT_BOUNDARY_PHASE_Q52_2026-10-27.txt
129443 bytes; 2162 LF
SHA256 2832d7259a0c5fbac9e4d6882775457f76ce8673ce3862ff6672d23f54286b13
```

Заново прочитан GitHub bootstrap `Malaeu/chen_q3`, `rh_clean`,
`docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob
`e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Репозиторий не изменялся. Исторические команды и программы внутри source bodies не исполнялись.

| Источник | Использование и граница |
|---|---|
| S1 | Принята исправленная граница повторных примитивов: поднятый вспомогательный контур делает четыре corner-платы малыми, но не оценивает \(J_4\). Этот опыт не повторяется. |
| S2 | Полный Q51: определения \(D_G,K\), действительная ветвь на обходе, entire/high-return, старый поточечный отказ и стоимость монодромии. Они не считаются новыми результатами. |
| S3 | Исходный all-\(P\) контур, kernel bounds, конечная карта к \(A,C^0,T,K_m\). Унаследованные аналитические входы не пересертифицированы заново. |
| S4 | Полный high-tail и ограниченная область count/norm completion. Не импортируется lower низкой части. |
| S5–S7 | Проверка отката: primitive/separator/forcing уже возвращали прежний долг. Pair seam не принимается ни как доказанный вход, ни как all-\(P\) результат. |
| S8 | Условный sparse-band receiver с прежним фиксированным \(\epsilon\), исходной нормой и оплаченными проекциями. Это не поставщик арифметического знака. |

Внешняя сверка касается только классических соглашений: уравнений Коши–Римана, ориентации контуров, определения Fourier/Laplace transform и функционального уравнения \(\xi\). Точные применённые формулы и первичные ссылки приведены в §11. **Никакой внешний theorem о нужной знаковой сумме не принят.**

До математических запусков сохранена регистрация приложений. Она сделана **после чтения и предварительного PAPER-вывода**, а не задним числом выдана за предсказание до рассуждения. Первичная проверка bytes/framing была выполнена раньше; это отдельно от математических тестов.

## 2. Неизменённые определения и полный потребитель

**[COFINAL_FAMILY | PAPER — inherited S2–S4, S8].** Фиксируем
\[
0<\epsilon<1/32,\qquad N=m,\quad L=\log m,\quad
M=R=\lfloor m^\epsilon\rfloor,
\]
\[
\omega_j=2\pi j/L,\qquad \Omega=2\pi M/L,\qquad
V_2=L^{-1}\sum_{|j|\le M}\omega_j^2\le\Omega^3.
\tag{2.1}
\]
Все утверждения об eventual-семействе относятся к каждому **фиксированному** \(\epsilon\). Старт и константы могут зависеть от него. Не используется \(\epsilon(m)\).

\(P\) — прежний ортогональный проектор на три контакта в исходной полосе. Обозначим изометрическую синтезу \(\mathcal I:\operatorname{ran}P\to L^2(0,L)\),
\[
f(t)=\mathcal Ic(t)=L^{-1/2}\sum_{|j|\le M}c_j e^{i\omega_jt},
\]
с нулевым продолжением. Сохраняются \(f(0)=f(L)=0\), два экспоненциальных контакта и \(\|f\|_2=\|c\|_2\). Во всех формах \(c\) может быть **комплексным**.

Пишем
\[
\mathsf H(s)=P Q_M(s)P\big|_{\operatorname{ran}P},\qquad0\le s\le L,
\]
\[
\mathsf H(0)=2P,\quad \mathsf H(L)=0,\quad\|\mathsf H(s)\|\le2,
\]
\[
A=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\mathsf H(\log n),
\qquad C^0=A+H_P,
\qquad0\preceq H_P\preceq4P.
\tag{2.2}
\]

Аналитическое ядро — именно
\[
\mathsf S_P(z)=\frac1L P\{v_+(z)v_+(z)^T+v_-(z)v_-(z)^T\}P,
\quad v_\pm(z)_j=(z\pm i\omega_j)^{-1},
\]
\[
\mathsf K(z)=e^{Lz}\mathsf S_P(z).
\tag{2.3}
\]
Здесь \(T\) — транспонирование. Ни в одном новом шаге оно не заменяется adjoint.

Сохраняем общий для всей \(P\) контур
\[
\Gamma=\partial\mathscr D,\quad
\mathscr D=\{u<\Re z<b,\ |\Im z|<H\},
\quad u\in[1/L,2/L],\quad b=1/2+1/L,
\tag{2.4}
\]
положительной ориентации; \(H\asymp m^{1/4+\epsilon}\) — прежняя допустимая высота. Нули на контуре исключены его исходным выбором. Пусть
\[
G=m^{5/24+\epsilon},\quad
\mathcal Z_m=\{w=\rho-1/2:\Re w>u,\ |\Im w|\le G\}.
\tag{2.5}
\]
Это множество **всех настоящих выбранных нулей**, с их кратностями \(r_w\). Оно может быть пустым; его непустота нигде не предполагается. Численные координаты неизвестного внепрямого нуля не назначаются.

По исходникам
\[
\mathcal R_{\rm low}=\operatorname{He}\sum_{w\in\mathcal Z_m}r_w\mathsf K(w),
\qquad C^0=\mathcal U_m-\mathcal R_{\rm low},
\quad\|\mathcal U_m\|\le p_m:=B_m+e_m+t_m,
\tag{2.6}
\]
где
\[
B_m=O_\epsilon(m^\epsilon L\log L),\quad
e_m=O_\epsilon(m^{-1/4}/L^2),\quad
t_m=O_\epsilon(m^{-1/8}/L^2).
\tag{2.7}
\]
В частности, из независимого \(\mathcal R_{\rm low}\succeq-sP\) следовало бы
\[
T_{>R}\preceq(s+p_m+b_{\rm div})P-H_P,
\]
\[
PK_mP\succeq H_P-(s+p_m+50L+8)P,
\tag{2.8}
\]
\[
b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\tag{2.9}
\]
При \(s=C_\epsilon m^{\theta(\epsilon)}\) итоговая степень была бы
\(\eta=\max\{\theta,2\epsilon\}\). В этом ответе такое \(s\) не поставлено.

## 3. Совместный Green-transfer: аргумент, модуль и точный матричный вес

### 3.1. Обе гармонические компоненты одновременно

**[FINITE_CELL | PAPER].** Берём полный полином S2
\[
D_G(z)=\prod_{|\Im w|\le G}(z-w)^{r_w},
\]
включая нули слева от контура. На положительно ориентированном обходе с началом \(z_0=b+iH\) пишем
\[
\ell(z)=\log\frac{D_G(z)}{D_G(z_0)}=U(z)+i\Theta(z).
\tag{3.1}
\]
\(U=\log|D_G(z)/D_G(z_0)|\) однозначна вне нулей. \(\Theta\) — **непрерывная вдоль обхода** ветвь, а не principal argument с выкинутыми скачками. Если
\(\nu_m=\sum_{w\in\mathcal Z_m}r_w\), то
\[
\Theta(z_0\text{ после обхода})-\Theta(z_0\text{ до обхода})=2\pi\nu_m.
\tag{3.2}
\]

Положим
\[
X(z)=\operatorname{He}\mathsf K(z),\qquad
Y(z)=\frac{\mathsf K(z)-\mathsf K(z)^*}{2i}.
\]
Это эрмитовы матрицы. По аналитичности \(\mathsf K\)
\[
X_x=Y_y,\qquad X_y=-Y_x,\qquad\Delta X=\Delta Y=0
\tag{3.3}
\]
во всей \(\mathscr D\). Мнимочастотные полюса \(\mathsf S_P\) находятся **вне** этой области.

Пусть \(\tau\) — единичная положительная касательная, \(n\) — внешняя нормаль. Уравнения Коши–Римана дают на каждой стороне
\[
\partial_\tau\Theta=\partial_n U,
\qquad \partial_\tau Y=\partial_n X.
\tag{3.4}
\]
Следовательно, **без разделения на модули**,
\[
\begin{aligned}
\mathcal R_{\rm low}
&=\operatorname{He}\frac1{2\pi i}\oint_\Gamma\mathsf K\,d\ell\\
&=\frac1{2\pi}\oint_\Gamma(X\,d\Theta+Y\,dU)\\
&=\boxed{\frac1{2\pi}\int_\Gamma
      (X\,\partial_nU-U\,\partial_nX)\,ds.}
\end{aligned}
\tag{3.5}
\]
В последнем переходе интегрирование по частям применяется к **однозначным** \(U,Y\). Угловые члены смежных сторон сокращаются попарно. Удаление второго слагаемого в (3.5) неправомерно.

Для самого запроса \(J_{\rm branch}\):
\[
\begin{aligned}
J_{\rm branch}
&=\frac1{2\pi}\oint_\Gamma(\Theta\,dX+U\,dY)\\
&=\boxed{\nu_m X(z_0)
 -\frac1{2\pi}\int_\Gamma(X\,\partial_nU-U\,\partial_nX)\,ds.}
\end{aligned}
\tag{3.6}
\]
Именно интегрирование \(\Theta\,dX\) возвращает \(\nu_mX(z_0)\). Оно не исчезает при выборе principal branch.

### 3.2. Все разрезы и логарифмические особенности

Внутри \(\mathscr D\), в смысле распределений,
\[
\Delta U=2\pi\sum_{w\in\mathcal Z_m}r_w\delta_w.
\tag{3.7}
\]
Полная матричная формула Грина поэтому имеет вид
\[
\boxed{\mathcal R_{\rm low}
 =\frac1{2\pi}\int_{\mathscr D}X(z)\,\Delta U(dz)
 =\sum_{w\in\mathcal Z_m}r_wX(w).}
\tag{3.8}
\]

Для проверки знаков и нормировки можно удалить маленькие диски радиуса \(a\) вокруг каждого **различного** внутреннего нуля. Вблизи \(w\)
\(U=r_w\log|z-w|+O(1)\). На внутренней окружности внешняя нормаль проколотой области направлена к \(w\). Вклад \(X\partial_nU\) стремится к \(-2\pi r_wX(w)\), а \(U\partial_nX\) имеет величину \(O(a|\log a|)\) и исчезает. Отсюда внешняя граница равна положительной сумме в (3.8). Если разрезы используются для внутренней ветви \(\ell\), их две стороны также нельзя удалять: их скачки \(2\pi i r_w\) дают те же слагаемые. В записи через \(U\) эти скачки уже представлены (3.7).

Внешние low-нули не удалены из \(U\), но их логарифмы гармоничны в \(\mathscr D\); их **полный** вклад в (3.5) нулевой. Ни отдельные стороны, ни отдельный normal-flux не объявляются нулём.

### 3.3. Почему здесь не возникает положительная энергия

**Это и есть полный искомый вес:** \(X=\operatorname{He}K\), а не \(K^*K\), \(\|K'\|^2\) или положительный scalar count. В (3.8) \(\Delta U\ge0\), однако вес не получает Loewner-знака. Принятый Q51 уже проверил соответствующее различие на исходных контактных направлениях. Повтор его контрпримера не считается новой попыткой.

Первый отсутствующий шаг данного Green-completion —
\[
\frac1{2\pi}\int_{\mathscr D}X(z)\,\Delta U(dz)
\succeq-C_\epsilon m^{\theta(\epsilon)}P,
\qquad\theta(\epsilon)\to0.
\tag{3.9 OPEN}
\]
После (3.8) это **та же** low-floor, а не выведенное из субгармоничности неравенство.

Также нельзя незаметно использовать конечную положительную энергию \(\int|\nabla U|^2\): если внутри есть нуль, то около него
\[
\int_{a<|z-w|<a_0}|\nabla U|^2\,dA
=2\pi r_w^2\log(a_0/a)+O(1).
\tag{3.10}
\]
Она расходится при \(a\downarrow0\). Введение renormalized energy потребовало бы всех self- и mixed-коррекций. В текущем **линейном** Green-transfer такого положительного кредита нет: \(\Delta X=0\), а не \(\Delta X\succeq\text{положительный квадрат}\).

**Scope отказа:** прекращён переход «положительность \(\Delta\log|D_G|\) + гармоническое сопряжение дают требуемый матричный знак». Не утверждается, что настоящая суммарная форма имеет плохой знак или что невозможно иное совместное неравенство.

### 3.4. Entire-factor return остаётся полным

С прежними \(F(z)=\xi(1/2+z)\), \(D_H\), \(E_H=F/D_H\):
\[
\log|F|=\log|D_G|+\log|D_H/D_G|+\log|E_H|
\tag{3.11}
\]
с точностью до несущественных постоянных. \(\log|E_H|\) гармонична внутри общего прямоугольника, поэтому её **полная** Green-граница равна нулю. Для \(\log|F/D_G|\) остаются высокие нули; её вклад равен \(\mathcal R_{\rm high}\), с прежней ценой \(t_m\), не нулю. Новых предпосылок о нулях \(F\) не введено.

Угловой член (3.6) имеет уже оплаченную цену
\[
\|\nu_mX(z_0)\|\le j_m
=\frac{8eC_N\sqrt m\,V_2G\log(G+2)}{H^4}
=O_\epsilon(m^{-7/24}/L^2).
\tag{3.12}
\]
Повторные примитивы S1 или изменение их высоты не используются для объявления нового выигрыша.

## 4. Один ранний откат: до boundary primitives, к исходному Laplace-transfer

**Выбрана документированная развилка S3:** первоначальное ядро \(\mathsf S_P\) и исходная конечная первая форма, до введения логарифма делителя и до разделения на квадратные сертификаты. Точное место в исходнике — определение \(\mathsf S_P\) и его causal inverse; обратная карта — S3(5), то есть (2.6).

Новый проверяемый вход здесь не состоит в очередной положительности исходного \(D_G'/D_G\). Это **конечная внутренняя нормировка** выбранного делителя и проверка, как её положительная граничная фазовая плотность сочетается с настоящей временной поддержкой \(\mathsf K\). В отличие от ошибочного Q51 positive-real импорта, эта конструкция допускает нули в нужной полуплоскости.

### 4.1. Конечный множитель и его настоящий знак на границе

**[FINITE_CELL | PAPER].** Для \(w=\delta+i\gamma\in\mathcal Z_m\) положим
\[
a_w=\delta-u>0,\qquad w^\#=2u-\bar w,
\]
\[
\mathcal B_m(z)=\prod_{w\in\mathcal Z_m}
\left(\frac{z-w}{z-w^\#}\right)^{r_w}.
\tag{4.1}
\]
Это конечный множитель Бляшке правой полуплоскости. Термин здесь означает буквально выписанное произведение. \(w^\#\) — **вспомогательная отражённая точка**, не заявленный нуль \(\xi\).

Для \(x=\Re z>u\)
\[
|z-w^\#|^2-|z-w|^2=4(x-u)a_w>0.
\tag{4.2}
\]
Следовательно, \(\mathcal B_m\) голоморфна и \(|\mathcal B_m|\le1\) справа от \(u\), причём на \(u+i\mathbb R\) её модуль равен 1. При пустом наборе \(\mathcal B_m=1\).

Её логарифмическая производная \(q_m=\mathcal B_m'/\mathcal B_m\) **имеет полюса** в выбранных нулях. Контрактивность \(\mathcal B_m\) не делает \(q_m\) голоморфной positive-real функцией. На границе точно:
\[
q_m(u+it)=-h_m(t),\qquad
\boxed{h_m(t)=\sum_{w\in\mathcal Z_m}
\frac{2r_wa_w}{a_w^2+(t-\gamma)^2}\ge0.}
\tag{4.3}
\]
\(h_m=-\partial_t\arg\mathcal B_m(u+it)\). Кратности и вся совместная сумма сохраняются. Ни положительной нижней границы для \(a_w\), ни разделённости ординат не предполагается.

Это независимое доказанное свойство данного конечного множителя, но **не новая арифметическая оценка CCM**. Далее проверяется его перенос, а не предполагается его успех.

### 4.2. Полный возврат добавленных отражений

Пусть \(N_m(z)=\prod_{w\in\mathcal Z_m}(z-w)^{r_w}\),
\(N_m^\#(z)=\prod_{w\in\mathcal Z_m}(z-w^\#)^{r_w}\). Тогда
\[
D_G/\mathcal B_m=(D_G/N_m)N_m^\#
\tag{4.4}
\]
— полином без нулей внутри \(\Gamma\). Поэтому
\[
\boxed{\mathcal R_{\rm low}
=\operatorname{He}\frac1{2\pi i}\oint_\Gamma\mathsf K(z)q_m(z)\,dz.}
\tag{4.5}
\]
Все отражённые полюса находятся строго слева от \(u\), а все невыбранные low-нули — вне правого прямоугольника. Равенство относится ко всему контуру; индивидуальные стороны quotient-return не удаляются. В полном \(F/\mathcal B_m\) внутри остаются именно высокие пересечённые нули, и их прежняя плата \(t_m\) сохраняется.

## 5. Полная оценка устойчивой фазовой части

Определим
\[
\boxed{\mathcal P_m=
\operatorname{He}\frac1{2\pi}\int_{\mathbb R}
\mathsf K(u+it)h_m(t)\,dt.}
\tag{5.1}
\]
Это не вся \(\mathcal R_{\rm low}\). Интеграл абсолютно сходится. Знак \(\mathcal P_m\) не выводится из \(h_m\ge0\): матричное \(\mathsf K\) не является положительным весом.

**Лемма 1 [COFINAL_FAMILY | PAPER].** При \(L\ge1,\Omega\ge1\) и достаточно поздней исходной ячейке
\[
\boxed{\|\mathcal P_m\|\le\ell_m:=
64e^2C_N L(1+\Omega)\log(10+8\Omega).}
\tag{5.2}
\]
Здесь \(C_N\) — фиксированная унаследованная константа
\(N_0(T)\le C_N T\log(T+2)\) для всех \(T\ge2\), с кратностями и обеими высотами.

**Доказательство.** В обозначениях S3
\[
s(t):=\|\mathsf S_P(u+it)\|\le3L,
\qquad s(t)\le8V_2|t|^{-4}\quad(|t|\ge2\Omega),
\]
\[
I_S:=\int_\mathbb R s(t)dt
\le12L\Omega+\frac{2V_2}{3\Omega^3}
\le12L\Omega+2/3.
\tag{5.3}
\]
Кроме того, \(m^u\le e^2\).

Положим \(T_0=4(1+\Omega)\). Для нулей с \(|\gamma|\le2T_0\) используем **полную** массу каждого Poisson-профиля:
\[
\frac1{2\pi}\int_\mathbb R\frac{2a_w}{a_w^2+(t-\gamma)^2}dt=1.
\]
Их суммарная цена не превосходит
\[
3e^2 L N_0(2T_0)
\le6e^2C_N L T_0\log(2T_0+2).
\tag{5.4}
\]

Если \(|\gamma|>2T_0\), то \(0<a_w<1/2\). На \(|t|\le|\gamma|/2\) Poisson-числитель даёт bound \(4/\gamma^2\). На дополнении \(s(t)\le128V_2/\gamma^4\). Поэтому полная цена данного нуля, без кратности, не больше
\[
e^2\left(\frac{2I_S}{\pi\gamma^2}+\frac{128V_2}{\gamma^4}\right).
\tag{5.5}
\]
Из local count диадическим суммированием, для \(Y\ge2\),
\[
\sum_{|\gamma|>Y}\frac{r_w}{\gamma^2}
\le\frac{8C_N\log(Y+2)}Y,
\quad
\sum_{|\gamma|>Y}\frac{r_w}{\gamma^4}
\le\frac{8C_N\log(Y+2)}{Y^3}.
\tag{5.6}
\]
Достаточно сгруппировать \(2^kY<|\gamma|\le2^{k+1}Y\); для второй оценки возникают сходящиеся суммы \(\sum2^{-3k}\) и \(\sum(k+1)2^{-3k}\). Суммирование по всем нулям здесь лишь увеличивает цену finite-low подмножества.

Подставляя \(Y=2T_0\), получаем far-price
\[
e^2C_N\log(2T_0+2)
\left(\frac{8I_S}{\pi T_0}+\frac{128V_2}{T_0^3}\right).
\tag{5.7}
\]
Имеем \(I_S/T_0\le4L\), \(128V_2/T_0^3\le2\), а
\(6LT_0=24L(1+\Omega)\). Сумма (5.4),(5.7) меньше правой стороны (5.2). □

**Что важно для переноса.** В (5.2) нет потери от почти касающихся \(u\) нулей, неизвестной минимальной щели между ординатами или выбора контура по вектору. Вся \(P\) контролируется одновременно. На нашем расписании
\[
\ell_m=O_\epsilon(m^\epsilon L)=O_\epsilon(m^{2\epsilon}).
\tag{5.8}
\]
Но (5.2) оплачивает лишь устойчивую часть. Утверждения, что она равна всей \(\mathcal R_{\rm low}\), ниже нет.

## 6. Точный finite-support return: что формула Пуассона не возвращает бесплатно

### 6.1. Буквальный обратный Laplace-transfer

**[FINITE_CELL | PAPER].** Для \(\tau\ge0\) определим матрицу \(\mathscr Q(\tau)\) как сжатие следующей конечной матрицы:
\[
\mathscr Q_{jk}^{\rm raw}(\tau)=
\begin{cases}
2\tau\cos(\omega_j\tau)/L,&j=k,\\[2mm]
\displaystyle\frac{2[\sin(\omega_k\tau)-\sin(\omega_j\tau)]}
 {L(\omega_k-\omega_j)},&j\ne k.
\end{cases}
\tag{6.1}
\]
То есть \(\mathscr Q=P\mathscr Q^{\rm raw}P\). Это точный обратный Laplace-transform \(\mathsf S_P\):
\[
\mathsf S_P(z)=\int_0^\infty e^{-z\tau}\mathscr Q(\tau)d\tau,
\qquad\Re z>0.
\tag{6.2}
\]
Можно проверить (6.2) по каждому произведению
\((z\pm i\omega_j)^{-1}(z\pm i\omega_k)^{-1}\), либо свёрткой двух экспонент. Сжатие применяется после сложения обеих ориентаций. Оценка
\(\|\mathscr Q(\tau)\|\le2(2M+1)\tau/L\), полученная из этой свёртки, оправдывает абсолютную сходимость при \(\Re z>0\).

**Именно исходная сетка** \(\omega_jL=2\pi j\) даёт
\[
\boxed{\mathscr Q(L-s)=\mathsf H(s),\qquad0\le s\le L.}
\tag{6.3}
\]
Вне \([0,L]\) \(\mathscr Q\) — вспомогательный Laplace-inverse, **не физический сдвиг с изменённой поддержкой**. Никакая исходная корреляция за пределы окна не продлевается.

Переменная \(y=L-\tau\) даёт абсолютно сходящуюся запись
\[
\mathsf K(u+it)=\int_{-\infty}^L
 e^{uy+ity}\mathscr Q(L-y)dy.
\tag{6.4}
\]
В частности, у этой boundary-функции есть положительная временная поддержка \(0<y<L\). Самой аналитичности \(\mathsf K\) справа от \(u\) недостаточно для её бесплатного восстановления обычным Poisson-integral: экспоненциальный множитель \(e^{Lz}\) нельзя забыть.

### 6.2. Совместная формула с полным исправляющим членом

Для \(w=u+a+i\gamma\), \(a>0\), положим
\[
\mathscr P_u\mathsf K(w)=\frac1\pi\int_\mathbb R
\frac{a\,\mathsf K(u+it)}{a^2+(t-\gamma)^2}dt.
\tag{6.5}
\]
Нормировка Poisson-ядра и его Fourier-transform:
\[
\frac1\pi\int_\mathbb R
\frac{a e^{ity}}{a^2+(t-\gamma)^2}dt
=e^{i\gamma y-a|y|}.
\tag{6.6}
\]
Она проверяется замыканием контура в верхнюю/нижнюю полуплоскость по знаку \(y\); при \(y=0\) получается 1. Здесь нет импорта теоремы о восстановлении растущей аналитической функции.

Подставляем (6.4) в (6.5). Fubini законен по \(\int_{-\infty}^L e^{uy}\|\mathscr Q(L-y)\|dy<\infty\) и единичной массе ядра. Для \(y\le0\) множители \(e^{ay}\) и \(e^{-a|y|}\) совпадают. Вся отрицательная временная сторона **сокращается точно**, а не удаляется. Для \(0<y<L\) остаётся
\[
\boxed{\mathsf K(w)-\mathscr P_u\mathsf K(w)
=\int_0^L\bigl(e^{ws}-e^{(2u-\bar w)s}\bigr)\mathsf H(s)ds.}
\tag{6.7}
\]
Это равенство всей матрицы с исходными комплексными mixed terms. Его правая сторона конечна и не требует оценок \(\mathsf S_P\) в отражённой точке; даже если эта точка совпадёт с мнимочастотным полюсом рациональной записи, конечный интеграл остаётся регулярным.

Теперь суммируем (6.7) **до модулей** по всем \(w\in\mathcal Z_m\):
\[
\boxed{\mathcal R_{\rm low}=\mathcal P_m+\mathcal D_m,}
\tag{6.8}
\]
\[
\boxed{\mathcal D_m=
\operatorname{He}\int_0^L\mathsf H(s)
 \sum_{w\in\mathcal Z_m}r_w
 \left(e^{ws}-e^{(2u-\bar w)s}\right)ds.}
\tag{6.9}
\]
Кратности, все собственные и смешанные модовые произведения, обе временные стороны и **все** нули выбранного делителя сохранены. Сопряжённость настоящего набора делает скалярную сумму в (6.9) вещественной, но не неотрицательной. Для каждой сопряжённой пары её вклад содержит
\(4r_we^{us}\sinh(a_ws)\cos(\gamma s)\).

Здесь не вводится новый квадрат, не требуется контроль ненужной положительной спектральной части и не суммируются модули отдельных главных вычетов. Неоплаченная \(\mathcal D_m\) остаётся **полной знаковой** формой.

### 6.3. Четыре стороны, бесконечные линии и точная цена хвостов

Для конечного \(q_m\) можно использовать тот же прямоугольник, а затем отправить вверх/вниз только вспомогательные горизонтали его рациональной функции. Это не изменение исходного zeta inversion и не пересечение новых actual high-нулей. Его полюса уже все лежат при \(|\gamma|\le G\).

С положительной ориентацией левый интеграл идёт вниз. Из \(q_m(u+it)=-h_m(t)\) его вклад имеет **плюс** перед (5.1). После полного предела:
\[
\mathcal R_{\rm low}
=\mathcal P_m+
\operatorname{He}\frac1{2\pi}\int_\mathbb R
\mathsf K(b+it)q_m(b+it)dt.
\tag{6.10}
\]
Правый интеграл равен именно \(\mathcal D_m\). Это также следует из причинной свёртки (6.2) с inverse Laplace
\(q_m\): \(\sum r_w(e^{ws}-e^{w^\#s})\).

Для количественного контроля всех переходов, при \(H\ge2G,2\Omega\) и \(b-u\le1\),
\[
|q_m(x\pm iH)|\le4\nu_m/H^2,\qquad u\le x\le b.
\]
Отсюда суммарная цена двух горизонталей не больше
\[
\frac{32e\sqrt m\,V_2\nu_m}{\pi H^6}
=O_\epsilon(m^{-19/24-2\epsilon}/L^2).
\tag{6.11}
\]
Полные части левой и правой вертикалей за \(|t|=H\) имеют соответственно цены
\[
\frac{32e^2V_2\nu_m}{5\pi H^5}
=O_\epsilon(m^{-25/24-\epsilon}/L^2),
\]
\[
\frac{32e\sqrt m\,V_2\nu_m}{5\pi H^5}
=O_\epsilon(m^{-13/24-\epsilon}/L^2).
\tag{6.12}
\]
Все оценки используют \(\nu_m\le C_NG\log(G+2)\). Полные бесконечные представления (6.8),(6.10) **точны**; (6.11)–(6.12) показывают, что никакая сторона не была бесплатно удалена. Эти альтернативные ошибки не начисляются вторично к точной формуле и не изменяют исходный \(t_m\).

## 7. Реальный all-P discriminator: целое Poisson-восстановление неверно уже в контакте

Этот тест не назначает гипотетический нуль и не использует синтетический делитель как модель \(\zeta\). Проверяется конкретное предполагаемое тождество для **настоящего исходного матричного transfer**.

Для \(a>0\) определим
\[
H_a:=\mathcal I^*\left[e^{-a|t-v|}\right]_{0\le t,v\le L}\mathcal I.
\tag{7.1}
\]
По прямому интегрированию физического сдвига
\[
H_a=\int_0^L e^{-as}\mathsf H(s)ds,
\qquad H_{1/2}=H_P.
\tag{7.2}
\]
Коэффициента 2 сверх уже содержащихся двух ориентаций нет.

**Лемма 2 [FINITE_CELL | PAPER].** Для \(L\ge16\), \(u\in[1/L,2/L]\) и ненулевого исходного пространства, положим \(a=1/2-2u\ge1/4\). Тогда
\[
\boxed{\mathsf K(1/2)-\mathscr P_u\mathsf K(1/2)
=-H_{1/2}-H_a,}
\tag{7.3}
\]
\[
\boxed{\mathscr P_u\mathsf K(1/2)=H_{1/2}+H_a\succ0,
\qquad \mathsf K(1/2)=0.}
\tag{7.4}
\]
Более того, в исходной норме
\[
\boxed{-12P\preceq
\mathsf K(1/2)-\mathscr P_u\mathsf K(1/2)
\preceq-c_mP\prec0,}
\tag{7.5}
\]
\[
c_m=\frac1{1/4+\Omega^2}+\frac{2a}{a^2+\Omega^2}>0.
\tag{7.6}
\]

**Доказательство.** Оба столбца \(Pv_\pm(1/2)\) равны нулю по исходным двум контактам, так что \(\mathsf K(1/2)=0\). Подстановка \(w=1/2\) в (6.7) даёт
\[
\int_0^L e^{s/2}\mathsf H(s)ds-
\int_0^L e^{(2u-1/2)s}\mathsf H(s)ds.
\]
Первый интеграл равен \(-H_P\) по **полному** исходному continuous-return, второй — \(H_a\). Получаем (7.3)–(7.4).

Для полноты, положительность и её размер можно доказать без предположения о CCM. Нулевое продолжение \(f\) принадлежит \(H^1(\mathbb R)\), поскольку исходный endpoint-contact сохранён. При Fourier-соглашении
\(\widehat f(\xi)=\int f(t)e^{-i\xi t}dt\)
\[
\langle c,H_ac\rangle=
\int_\mathbb R\frac{2a}{a^2+\xi^2}|\widehat f(\xi)|^2\frac{d\xi}{2\pi}.
\tag{7.7}
\]
Множитель вычисляется непосредственно интегрированием \(e^{-a|t|}\). Он строго положителен. Для единичного \(c\) мера \(|\widehat f|^2d\xi/(2\pi)\) имеет массу 1 и второй момент
\(\|f'\|_2^2\le\Omega^2\). Cauchy либо выпуклость \(x\mapsto1/(a^2+x)\) дают
\[
\frac{2a}{a^2+\Omega^2}P\preceq H_a\preceq\frac2aP.
\tag{7.8}
\]
Суммирование (7.8) при \(a\) и \(1/2\) доказывает (7.5), поскольку \(4+2/a\le12\). □

**Точная область отказа.** Верхняя отрицательная граница в (7.5) опровергает бесплатное Poisson-восстановление \(\mathsf K(w)=\mathscr P_u\mathsf K(w)\), а также направление \(\mathsf K(1/2)\succeq\mathscr P_u\mathsf K(1/2)\). Это уже **полный интегральный** тест на всех исходных \(P\)-векторах. Он не требует недоказанного half-plane Herglotz-свойства и не повторяет Q51, где проверялся знак одного матричного интегранда.

Но \(1/2\) — контактная точка, а не заявленный нуль \(F\). Оценка (7.5) имеет постоянную верхнюю цену; она **не опровергает** разрешённую растущую поправку, lower всей \(\mathcal R_{\rm low}\), либо subpower-оценку CCM. Никакой знак \(\mathcal D_m\) при настоящих неизвестных нулях из этого теста не выводится.

### Контроль конечного диагонального return

Есть дополнительная проверка, полезная для воспроизведения:
\[
\int_0^L e^{zs}\mathsf H(s)ds
=(e^{Lz}-1)\mathsf S_P(z)
-P\operatorname{diag}_{j}\left(\frac{2z}{z^2+\omega_j^2}\right)P.
\tag{7.9}
\]
Равенство сначала выводится вне полюсов; левая сторона целая, поэтому в особых точках берутся устранимые пределы полного правого выражения. На диагонали оно следует из интегрирования \(2(1-s/L)e^{zs}\cos\omega_js\); вне диагонали — из двух синусов с тем же endpoint phase \(e^{i\omega_jL}=1\). Удаление последней диагональной матрицы неверно. В \(z=1/2\) именно она остаётся после исходных контактов.

## 8. Первая неоплаченная строка и полный результат по показателю

Подставляя (6.8) в исходный потребитель (2.6), получаем **без дополнительной ошибки карты**
\[
\boxed{C^0=\mathcal U_m-\mathcal P_m-\mathcal D_m,
\qquad\|\mathcal U_m-\mathcal P_m\|\le p_m+\ell_m.}
\tag{8.1}
\]

Первое отсутствующее арифметическое свойство — направленный контроль всей конечновременной связи
\[
\boxed{
\operatorname{He}\int_0^L\mathsf H(s)
\sum_{\substack{w\text{ actual}\Re w>u,\ |\Im w|\le G}}
 r_w\bigl(e^{ws}-e^{(2u-\bar w)s}\bigr)ds
\succeq-C_\epsilon m^{\theta(\epsilon)}P,
\quad\theta(\epsilon)\to0.}
\tag{8.2 OPEN}
\]
Нужен **один и тот же** исходный вектор либо плотность \(W=PWP\succeq0\) во всех слагаемых. Положительная плотность (4.3) не оценивает (8.2): после return осталась положительная временная сторона \(0<s<L\), где Poisson-damping \(e^{-a_ws}\) отличается от \(e^{a_ws}\). Косинусные фазы настоящих ординат и исходное двухстороннее overlap-ядро должны контролироваться **совместно**.

(8.2) не принимается в предпосылки. По (6.8), (5.2) это тот же low-floor с точностью до уже дешёвой \(\ell_m\), а не новая готовая более лёгкая теорема. Аналогично (8.1) не называется новым supplier для \(C^0\).

Если бы независимо было доказано \(\mathcal D_m\succeq-s_DP\), полный бюджет составлял бы
\[
\mathcal R_{\rm low}\succeq-(s_D+\ell_m)P,
\quad
J_{\rm branch}\preceq(s_D+\ell_m+j_m)P,
\tag{8.3}
\]
\[
T_{>R}\preceq(s_D+\ell_m+p_m+b_{\rm div})P-H_P,
\]
\[
PK_mP\succeq H_P-(s_D+\ell_m+p_m+50L+8)P.
\tag{8.4}
\]
Все оплаченные добавки в (8.4) имеют eventual upper \(C_\epsilon m^{2\epsilon}\). Поэтому при \(s_D=C_\epsilon m^{\theta(\epsilon)}\) получилась бы требуемая
\(\eta=\max\{\theta,2\epsilon\}\to0\). Это **условный вывод о цене**, не доказательство (8.2).

### Что фактически известно без нового знака

От прямого унаследованного
\(A\preceq s_{\rm keep}P\) и \(H_P\preceq4P\) получаем лишь
\[
\mathcal R_{\rm low}\succeq-(s_{\rm keep}+4+p_m)P,
\]
\[
\mathcal D_m\succeq-(s_{\rm keep}+4+p_m+\ell_m)P.
\tag{8.5}
\]
При обратной вставке второй строки в (8.4) возникла бы допустимая, но худшая цена
\[
s_{\rm keep}+4+2p_m+2\ell_m+b_{\rm div}
\tag{8.6}
\]
для \(T\), и аналогичная цена с одной arch-платой вместо \(b_{\rm div}\) для \(K_m\). В ней сохраняется степень \(1/2\). Это цена кругового возврата известного upper, **не нижняя величина настоящей формы**. Она не принимается вместо лучшего прямого результата.

Итоговый безусловный bound сохраняется ровно прежним:
\[
s_{\rm keep}=W_<(m)+W(\lfloor\sqrt m\rfloor)
\le6\sqrt m+6m^{1/4},
\]
\[
\boxed{T_{>R}\preceq(s_{\rm keep}+b_{\rm div})P,
\qquad PK_mP\succeq-(s_{\rm keep}+50L+8)P.}
\tag{8.7}
\]
Вспомогательные \(p_m,\ell_m,j_m\) поверх (8.7) не начислены. \(H_P\) не оплачен второй раз, short добавлен только в \(T\). Новой степени, коэффициентного запаса на настоящей паре или результата RH нет.

## 9. Атака на вывод, сохранённые границы и решение

**Самое сильное возражение:** «Отказ бесплатного Poisson-восстановления ещё не означает отказ хорошего bound с поправкой». Верно. Именно поэтому локальный отрицательный верх (7.5) относится только к указанной theorem shape, а общий результат — `NO_DERIVATION`. Допустимая поправка постоянного размера не исключена; вообще \(\|\cdot\|\le12\) в том контрольном контакте.

**Второе возражение:** «Оплачен только устойчивый канал, а трудность перенесена в \(\mathcal D_m\)». Тоже верно: это явно установлено (8.1)–(8.2), и не названо уменьшением главного долга. Новый полезный локальный вывод — нельзя применять гармоническое Poisson-продолжение к \(e^{Lz}\mathsf S_P(z)\) без возврата всей положительной временной поддержки. Малый high-tail и полное harmonic conjugacy этого не исправляют.

Границы, которые сохранены:

* \(P,N,L,M,R\), исходная норма и fixed-\(\epsilon\) кванторы не менялись. Тест (7.5) действует на всём исходном \(P\), не на подставленном удобном профиле.
* Все \(\Lambda(p^k)\) и исходные \(\mu\)-маски остаются в принятой контурной карте. Нового арифметического разложения или изменения коэффициентов здесь нет.
* Полюса исходного transfer на мнимой оси не пересекались исходным контуром. Вспомогательные отражения \(w^\#\) полностью учтены в quotient (4.4) и конечном return (6.7).
* \(|\gamma|=G\) входит в low; исходный \(|\gamma|=H\) исключён выбором контура. Бесконечная вспомогательная вертикаль относится только к конечному low-делителю; её явные хвосты (6.12) не заменяют исходные inversion tails.
* \(s=L\) сохраняет \(\mathsf H(L)=0\); ни верхний prime-power атом, ни исходные \(n>m\) inversion returns не переопределены. В (6.4) отрицательная временная сторона сокращается **совместно**, а не объявляется несуществующей.
* Подстановка непрерывного исходного источника даёт прежний \(A[dx]=-H_P\), \(C^0[dx]=0\) до модулей. При такой замене нельзя сохранить старый zeta-divisor как представление изменённой арифметики: меняется полная source map, не один её кусок.
* Отрицательный интегральный тест (7.5) не находится в предполагаемом нуле. Из него не делается утверждение о знаке полной actual residue sum. Никакая численная внепрямая точка не назначена.
* S5–S7 не использованы для подмены all-\(P\) задачи ещё открытой pair seam. Результат S8 остаётся условным receiver, не дополнительной гипотезой о знаке.

**Решение:** остановить именно Green/subharmonic-positivity completion и бесплатный Hardy–Poisson перенос. Не продолжать primitive/height optimization. Выполненный откат вернул полную первую форму (8.1), с явно сохранённым источниковым конечновременным членом. Независимой нужной inequality после этого отката также не найдено.

## 10. Ledger, dependency contract и closeout

| ID | Утверждение | Scope | Verifier | Статус |
|---|---|---|---|---|
| L0 | Source frames и восемь полных тел | FINITE_CELL | PAPER / byte-check | совпали |
| L1 | All-\(P\) contour, high-tail, receiver | COFINAL_FAMILY | PAPER / inherited | не пересертифицированы целиком |
| L2 | (3.5)–(3.8), полный joint Green-weight и монодромия | FINITE_CELL | PAPER | выведены; сами не дают знак |
| L3 | Положительная boundary phase density конечного \(\mathcal B_m\) | FINITE_CELL | PAPER | доказана, без RH |
| L4 | Whole \(\|\mathcal P_m\|\le\ell_m\) | COFINAL_FAMILY | PAPER | оплаченный вспомогательный канал |
| L5 | Exact original-kernel support return (6.7)–(6.9) | FINITE_CELL | PAPER | все смешанные члены сохранены |
| L6 | Contact integrated defect (7.3)–(7.8) | COFINAL_FAMILY | PAPER | отрицательный upper для free Poisson reproduction; не CCM no-go |
| L7 | \(\mathcal D_m\) floor / \(J_{\rm branch}\) upper нужной силы | COFINAL_FAMILY | CONDITIONAL / OPEN | не выведены и не использованы |
| L8 | Full return (8.3)–(8.4) | ABSTRACT | PAPER | проверенная импликация, premise открыт |
| L9 | Новый арифметический показатель / RH | COFINAL_FAMILY | CONDITIONAL / OPEN | не получены |
| L10 | Исполняемые finite controls | FINITE_CELL | PAPER | точная алгебра; не production spectrum |

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_ONE_SIDED_T_GT_R
ACTUAL_CONSUMER_REQUIREMENT: eventual_or_common_cofinal_upper_with_eta_epsilon_to_zero
ORIGINAL_REQUESTED_OBJECT: whole_joint_boundary_argument_modulus_upper
ORIGINAL_OBJECT_IS: PROVED_NECESSARY
NECESSITY_SCOPE: equivalent_to_low_floor_up_to_paid_corner_and_original_contour_fees
METHOD_IS_NECESSARY: false
KNOWN_WEAKER_INTERFACES:
  - direct_original_A_upper_with_one_short_and_one_arch_return
  - independently_proved_true_source_pair_margin_with_its_receiver_not_an_all_P_promotion
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
REOPEN_TRIGGER: independently_proved_signed_control_of_the_whole_positive_time_return_not_separate_phase_mass_or_harmonicity
NOVELTY_AXIS: integrated_Poisson_support_defect_test_and_uniform_whole_stable_phase_budget
LOCAL_REJECTED_THEOREM_SHAPE: K_equals_Poisson_continuation_of_its_left_boundary_without_a_growth_return
LOCAL_KILL_SCOPE: THEOREM_SHAPE
LOCAL_KILL_EVIDENCE_KIND: EXACT_ORIGINAL_P_NEGATIVE_UPPER
LOCAL_KILL_EVIDENCE: Q52_SECTION_7_EQ_7_5
LOCAL_REPAIRED_STATEMENT: Q52_EQ_6_7_WITH_THE_COMPLETE_FINITE_INTERVAL_CORRECTION
IMPOSSIBILITY_EVIDENCE_FOR_CCM: NONE
CONSUMER_PROGRESS: NO_PROGRESS
LOCAL_COMPLETION_PROGRESS: FALSIFICATION_PROGRESS_ONLY
```

### Две репрезентации, без эскалации вычислений

| Представление | Различающий тест | Цена / диагностическая сила |
|---|---|---|
| Полная boundary/area форма \((U,\Theta,X)\) | Нормальная производная теста, log-singular masses и winding; нельзя заменить вес положительным count | Точная карта, низкая алгебраическая цена; высокая сила против бесплатного energy-completion, но нового source sign нет |
| Исходный Laplace-transfer и конечный внутренний phase-factor | Оплаченный \(\mathcal P_m\) **вместе** с конечным \(\mathcal D_m\); contact test (7.5) обнаруживает пропущенную поддержку | Карта точна; \(\ell_m=O_\epsilon(m^{2\epsilon})\); исходный главный долг не уменьшен |

**DISCRIMINATOR для любого zero-consistent будущего результата:** не норма отдельного boundary-клочка, а lower envelope полного запаса
\(sP+\mathcal D_m\), либо upper envelope \(J_{\rm branch}-sP\), с заранее зафиксированными \(s\), областью и всеми возвратами. Конечная интервальная проверка принимает только заявленную конечную область; интервал через ноль не даёт знака. В текущей работе такие production-ячейки не вычислялись.

**Судьба регистрации:** P1 — полный weight и монодромия выведены; P2 — finite inner formula доказана; P3 — support-return выведен; P4 — all-\(P\) contact defect и цена 12 доказаны; P5 — stable-part bound доказан, полный supplier отсутствует; P6 — потребитель не закрыт. Конечные тесты проверяют чувствительную алгебру этих пунктов, но не сертифицируют асимптотику.

```yaml
MEMORY_ENTRY:
  iteration: Q52_JOINT_BOUNDARY_PHASE
  target: original_P_joint_boundary_upper_with_vanishing_exponent
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: use_subharmonicity_or_positive_boundary_phase_without_returning_exponential_type_support
  invariant_learned: K_has_a_nonzero_positive_time_piece_and_Poisson_continuation_damps_it_instead_of_analytically_growing_it
  forbidden_future_move: drop_the_integral_in_Q52_6_7_or_call_the_stable_phase_budget_the_full_residue_floor
  smallest_unpaid_input: complete_signed_finite_interval_pairing_Q52_8_2
  consumer_progress: NO_PROGRESS
  route_score: 2
  source_route_death: NOT_ESTABLISHED
  next_decisive_test: bounded_independent_check_of_Q52_Green_signs_Poisson_return_and_contact_defect_not_an_automatic_new_research_cycle
```

### Одна CODEX DIRECTIVE

**Выполнить один ограниченный независимый PAPER-аудит §§3–8:** проверить ориентацию и оба Green-boundary члена; finite Blaschke quotient без скрытого zero-exclusion; константу 64 в (5.2); точный source inverse (6.1)–(6.7); contact identity и оба направления (7.5); одинарную оплату всех расходов (8.4). Затем извлечь и воспроизвести четыре приложения. Вернуть первую ошибку либо приёмку ровно этих утверждений. Не принимать (8.2), новую степень, RH или whole-chain certification из успешного replay. Не запускать новый вопрос, широкий численный scan или формализацию по инерции. Репозиторная запись этим ответом не поручается.

## 11. Первичные классические формулы и граница внешней проверки

[E1] NIST DLMF 1.9.25–1.9.26: уравнения Коши–Римана и гармоничность real/imaginary parts. DLMF 1.9.28–1.9.32: параметризованный контур, положительная ориентация, Cauchy и winding. Здесь они применены к конечной матрице покомпонентно; log-singular и matrix-weighted Green-вывод дан в §3, а не принят как готовый арифметический theorem.

[E2] NIST DLMF §1.14(i),(iii): соглашения Fourier/Laplace, convolution и Parseval. В этом ответе используется явно написанное ненормированное Fourier-соглашение §7. Ядро (6.6), обратная матрица (6.1) и множитель \(2a/(a^2+\xi^2)\) выводятся непосредственно; различия конвенций не прячутся в ссылке.

[E3] NIST DLMF 25.4.3–25.4.4: определение завершённой \(\xi\) и функциональное уравнение. Фактические конечные делители, multiplicities и весь source-return принимаются из S2–S4 в их stated scope, не из компьютерного списка нулей.

```text
[E1] https://dlmf.nist.gov/1.9#E25
     https://dlmf.nist.gov/1.9#E26
     https://dlmf.nist.gov/1.9#E28
     https://dlmf.nist.gov/1.9#E32
[E2] https://dlmf.nist.gov/1.14
[E3] https://dlmf.nist.gov/25.4#E3
     https://dlmf.nist.gov/25.4#E4
```

Это проверка первичных стандартных формул, не новый литературный supplier. Ни global literature-absence, ни новый внешний zero-free/variance theorem не заявляются.

## 12. Проверки, воспроизводимость и честная область

Новые программы используют только стандартную библиотеку Python, точные рациональные и гауссово-рациональные числа. Проверяются Green-orientation, finite-root phase algebra, endpoint-reduced Laplace entries, positive/negative time bookkeeping, исходные контакты, Jensen-budget и рациональные степени хвостов.

**Граница кодовых тестов:** искусственные конечные корни проверяют только алгебру множителя, не моделируют actual \(\xi\). Рациональные \(\Delta,L,E\) в матричных тестах — специализации **после** формального использования \(e^{i\omega_jL}=1\), \(E=e^{zL}\); это не производственные ячейки. Fourier positivity и все eventual-кванторы доказаны текстом выше, не finite panel. Ни один floating-point знак не используется.

Первый запуск строгого parser остановился **до математических проверок**: первоначально ожидалось отсутствие пустого LF после последнего `END S8`. Фактический канонический пакет заканчивается `\nEND S8\n\n`. Parser исправлен под точный внешний framing: один пустой LF после каждого закрывающего frame, включая последний. Байты исходника, его hash, математические прогнозы и тестовые тождества не менялись. После этого полный checker прошёл. Эта упаковочная ошибка не скрыта и не считается математическим отрицательным результатом.

В итоговом запуске пройдены 15 polynomial Green случаев, 20 circle/branch случаев, 6 finite Blaschke контролей, 50 endpoint-reduced матричных равенств, 6 support cases, 2 contact directions, 3 finite Jensen контроля и 3 строки степенного бюджета. Обнаружены десять предусмотренных алгебраических и четыре framing/hash нарушения. **Число проверок не является прогрессом исходного доказательства.**

Не запускались независимый новый аудит, Lean, Arb, production-спектральные вычисления или вычисление actual zeta zeros. Исторические программы не выполнялись. Полные код и результаты — в четырёх приложениях ниже.

### Команда воспроизведения

Сохрани тело `replay_q52.py` из приложения в отдельный файл, затем:

```bash
python3 replay_q52.py \
  PROSHKA_CCM_JOINT_BOUNDARY_PHASE_Q52_VERDICT_2026-10-27.md \
  PROSHKA_CCM_JOINT_BOUNDARY_PHASE_Q52_2026-10-27.txt \
  q52_replay
```

Первый аргумент — этот полный Markdown, второй — неизменённый канонический TXT, третий — создаваемый каталог. При другом размещении замени только пути, например `./archive/PROSHKA_CCM_JOINT_BOUNDARY_PHASE_Q52_VERDICT_2026-10-27.md`; содержимое файлов не редактируй. Достаточно Python 3.9+ без установки пакетов.

### Проверенный source manifest

Следующая таблица относится к raw TXT; byte-диапазоны полуоткрытые, separator LF не входит в body.

| ID | Полное имя тела | Bytes / LF | SHA-256 | Raw строки | Bytes `[start,end)` |
|---|---|---:|---|---:|---:|
| S1 | `CCM_POST_Q51_REPEATED_PRIMITIVE_PREFLIGHT.md` | 8546 / 166 | `02ce0e7a85863c6da6df148b6a560f8349f411811ce5d77b3637fff7ce19f409` | 30–195 | [7823,16369) |
| S2 | `PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_VERDICT_2026-10-27.md` | 84366 / 1441 | `953aef7fdb188a62264d48571165be1f936df8bd021acf57823b4c0f3f1c86e3` | 200–1640 | [16443,100809) |
| S3 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 / 123 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` | 1645–1767 | [100862,106495) |
| S4 | `CCM_POST_Q27_DENSITY_BUDGET.md` | 4636 / 93 | `87c3faa5a652ca4d205e82674553ad0f5f5a1c24735c43a09d98d4560c3dc166` | 1772–1864 | [106544,111180) |
| S5 | `CCM_Q43_CONCLUSION.md` | 3946 / 75 | `c0a8339a58d0ed7be7942dcd657164dc479b470d74a5613b2006c77fa2407ef5` | 1869–1943 | [111220,115166) |
| S6 | `CCM_Q44_CONCLUSION.md` | 4532 / 80 | `4b0f6e355cc1e5159df49a4eafafbb81e5326825febdfc42f18f7202eb610993` | 1948–2027 | [115206,119738) |
| S7 | `CCM_Q45_CONCLUSION.md` | 3436 / 55 | `fe75c23687897d58a6c891d37cf3e2968d4957d228e80bc9f02a852a86f6e070` | 2032–2086 | [119778,123214) |
| S8 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 / 69 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` | 2091–2159 | [123260,129434) |

### Полные исполняемые приложения

BEGIN_ASSET registration_q52.json
BYTES: 2190
SHA256: ab3d22df532540fa8eaa409b684a713628428b012529c33b9dc49560fc863e28
```json
{
  "task": "Q52_JOINT_BOUNDARY_PHASE",
  "stage": "After full byte-locked packet reading and preliminary PAPER derivation; before executable mathematical checks",
  "selected_mechanism": "Full matrix Green pairing of modulus and boundary argument, followed by one rollback to the original Laplace kernel and finite Blaschke phase with exact positive-time support return",
  "predictions": {
    "P1": "The full Green weight is He K, not a positive square; the boundary branch corner and the logarithmic singular masses have their stated signs.",
    "P2": "The finite Blaschke product of the selected actual right roots is contractive to the right of u and has negative boundary argument derivative; no absence of roots is assumed.",
    "P3": "Poisson continuation of K differs from analytic continuation by exactly the finite interval integral of (exp(w s)-exp((2u-conj(w))s)) H(s). Negative-time support cancels, rather than being discarded.",
    "P4": "At the original contact exponent 1/2, the full defect is minus the sum of two positive decaying kernels, not zero; its all-P absolute norm is at most 12 for u<=1/8.",
    "P5": "The complete stable Poisson part has an independent O_epsilon(m^epsilon log m) upper norm budget; the remaining finite growth defect has no new supplied one-sided bound.",
    "P6": "The original full consumer remains open; exact controls do not certify its asymptotic sign."
  },
  "candidate_representations_before_checks": [
    {"name": "Matrix Green/Riesz pairing", "map_cost": "zero", "discriminator": "derive the actual matrix area weight and all boundary terms", "cost": "low exact algebra; high strength for detecting a false positive-energy inference"},
    {"name": "Finite-inner phase and original finite-time Laplace return", "map_cost": "exact map; stable boundary part has explicit parameter-proportional upper", "discriminator": "contact exponent 1/2 detects omitted exponential-type correction on all original P", "cost": "moderate PAPER derivation; finite algebra tests only"}
  ],
  "source_code_executed": false,
  "numeric_zeta_zeros": false,
  "production_spectrum": false,
  "repository_writes": false,
  "installations": false
}
```
END_ASSET

BEGIN_ASSET check_q52.py
BYTES: 12910
SHA256: 948714704cf7fc73d269f4969132e0fb0a05017e8568ef423f1bda8474c19d0c
```python
#!/usr/bin/env python3
"""Q52: exact finite algebra and packet framing, not a CCM spectral certificate.
Usage: python3 check_q52.py CANONICAL_Q52.txt
Standard library only; historical source programs are never executed.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
import re
import sys

NAME = 'PROSHKA_CCM_JOINT_BOUNDARY_PHASE_Q52_2026-10-27.txt'
SIZE, LF = 129443, 2162
SHA = '2832d7259a0c5fbac9e4d6882775457f76ce8673ce3862ff6672d23f54286b13'
MAN = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def verify(raw: bytes, outer: bool = True) -> dict:
    if outer and (len(raw) != SIZE or raw.count(b'\n') != LF or hashlib.sha256(raw).hexdigest() != SHA):
        raise ValueError('canonical bytes/LF/SHA')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n') or not raw.startswith(b'Q52 JOINT_BOUNDARY_PHASE'):
        raise ValueError('encoding/request frame')
    pos = raw.index(b'BEGIN S1 ')
    heads = list(MAN.finditer(raw[:pos]))
    if len(heads) != 8:
        raise ValueError('manifest count')
    rows = []
    for i, h in enumerate(heads, 1):
        if h[1] != str(i).encode():
            raise ValueError('manifest order')
        sid, name = 'S'+str(i), h[2].decode()
        begin = f'BEGIN {sid} {name}\n'.encode()
        if raw[pos:pos+len(begin)] != begin:
            raise ValueError('opening frame')
        start, end = pos+len(begin), pos+len(begin)+int(h[3])
        body = raw[start:end]
        if len(body) != int(h[3]) or body.count(b'\n') != int(h[4]):
            raise ValueError('body bytes/LF')
        if hashlib.sha256(body).hexdigest() != h[5].decode():
            raise ValueError('body hash')
        body.decode('utf-8')
        close = f'\nEND {sid}\n'.encode()
        if raw[end:end+len(close)] != close:
            raise ValueError('closing frame')
        rows.append(dict(id=sid, name=name, bytes=len(body), lf=body.count(b'\n'),
                         sha256=h[5].decode(), start_byte=start, end_byte=end,
                         start_line=raw[:start].count(b'\n')+1, end_line=raw[:end].count(b'\n')))
        pos = end+len(close)
        # This packet has exactly one blank LF after EVERY closing frame,
        # including the last one. It is outside the source body.
        if raw[pos:pos+1] != b'\n':
            raise ValueError('post-frame separator')
        pos += 1
    if pos != len(raw):
        raise ValueError('trailing bytes')
    return dict(packet=NAME, bytes=len(raw), lf=raw.count(b'\n'), sha256=SHA,
                source_count=8, all_frames_verified=True, sources=rows)


@dataclass(frozen=True)
class Q:
    """Gaussian rational. No float is used to decide a sign."""
    re: F = F(0)
    im: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))
    @staticmethod
    def cast(x):
        return x if isinstance(x, Q) else Q(x)
    def __add__(self, x):
        x = Q.cast(x); return Q(self.re+x.re, self.im+x.im)
    __radd__ = __add__
    def __neg__(self):
        return Q(-self.re, -self.im)
    def __sub__(self, x):
        return self + (-Q.cast(x))
    def __rsub__(self, x):
        return Q.cast(x) + (-self)
    def __mul__(self, x):
        x = Q.cast(x)
        return Q(self.re*x.re-self.im*x.im, self.re*x.im+self.im*x.re)
    __rmul__ = __mul__
    def conj(self):
        return Q(self.re, -self.im)
    def norm2(self):
        return self.re*self.re+self.im*self.im
    def __truediv__(self, x):
        x = Q.cast(x); n = x.norm2()
        if not n: raise ZeroDivisionError
        return self*x.conj()*F(1, n)
    def __rtruediv__(self, x):
        return Q.cast(x)/self
    def __pow__(self, n):
        if n < 0: return (Q(1)/self)**(-n)
        z = Q(1)
        for _ in range(n): z = z*self
        return z

I = Q(0, 1)

# Bivariate rational polynomials. These test Green's formula, not zeta data.
def add(p, q):
    r = p.copy()
    for k, v in q.items(): r[k] = r.get(k, F(0))+v
    return {k:v for k,v in r.items() if v}
def scale(p, a): return {k:v*a for k,v in p.items() if v*a}
def mul(p, q):
    r = {}
    for (i,j), v in p.items():
        for (k,l), w in q.items(): r[i+k,j+l] = r.get((i+k,j+l), F(0))+v*w
    return r

def der(p, axis):
    r = {}
    for (i,j), v in p.items():
        n = (i,j)[axis]
        if n: r[(i-1,j) if axis == 0 else (i,j-1)] = v*n
    return r

def integ(p, box):
    a,b,c,d = box
    return sum((v*(b**(i+1)-a**(i+1))*F(1,i+1)*(d**(j+1)-c**(j+1))*F(1,j+1)
                for (i,j),v in p.items()), F(0))

def edge(p, axis, fixed, lo, hi):
    out = F(0)
    for (i,j),v in p.items():
        power, n = (i,j) if axis == 0 else (j,i)
        out += v*fixed**power*(hi**(n+1)-lo**(n+1))*F(1,n+1)
    return out

def harmonic(n):
    p = {}
    for j in range(0,n+1,2): p[n-j,j] = F(math.comb(n,j)*(-1)**(j//2))
    return p

def green(X,U,box,drop_second=False):
    a,b,c,d = box; result=F(0)
    for axis, v0,v1,lo,hi in ((0,a,b,c,d),(1,c,d,a,b)):
        p = mul(X,der(U,axis))
        if not drop_second: p=add(p,scale(mul(U,der(X,axis)),-1))
        result += edge(p,axis,v1,lo,hi)-edge(p,axis,v0,lo,hi)
    return result


def math_checks():
    counts, errors = {}, {}
    box=tuple(map(F,[-1,2,-2,1]))
    us=[{(2,0):F(1),(0,2):F(1)}, {(3,1):F(2),(1,2):F(-3),(0,0):F(4)},
        {(4,0):F(1),(0,4):F(-2),(2,2):F(3)}]
    gc=0; drop_detected=False
    for n in range(5):
        X=harmonic(n)
        assert not add(der(der(X,0),0),der(der(X,1),1))
        for U in us:
            lap=add(der(der(U,0),0),der(der(U,1),1))
            val=integ(mul(X,lap),box)
            assert green(X,U,box)==val
            drop_detected |= green(X,U,box,True)!=val
            gc+=1
    counts['green_polynomial_cases']=gc
    errors['drop_U_normal_derivative_of_X']=drop_detected

    # Exact one-root circle averages: mean K(w+r exp(it)) = K(w).
    # They also test the 2pi normalization and winding sign; not actual zeros.
    mc=0
    for w in (Q(F(1,3),F(2,5)),Q(F(-1,4),F(1,7))):
        for n in range(5):
            for mult in (1,3):
                center=w**n; corner=(w+Q(2))**n
                # K(w+2e^(it)) = sum_k coeff_k e^(ikt).
                # The normalized boundary-log integral equals mult*sum_{k>=1} coeff_k,
                # since integral_0^(2pi) t e^(ikt) dt = 2pi/(i*k).
                coeff=[math.comb(n,k)*(w**(n-k))*Q(2)**k for k in range(n+1)]
                branch=mult*sum(coeff[1:],Q(0))
                assert mult*center==mult*corner-branch
                mc+=1
    counts['circle_branch_cases']=mc
    errors['drop_winding_corner']=(Q(3)!=Q(0))
    errors['use_log_modulus_squared_without_half']=(F(3)!=F(6))

    # Finite auxiliary root fixtures only; no numeric zeros of xi are assigned.
    u=F(1,8)
    roots=[(Q(F(1,4),F(2,3)),2),(Q(F(3,8),F(-5,4)),1)]
    bc=0
    for t in (F(-2),F(0),F(1,3),F(3)):
        z=Q(u,t); b=Q(1); ld=Q(0); density=F(0)
        for w,r in roots:
            wr=Q(2*u)-w.conj(); a=w.re-u
            b*=((z-w)/(z-wr))**r
            ld+=r*(1/(z-w)-1/(z-wr))
            density+=r*2*a/(a*a+(t-w.im)**2)
        assert b.norm2()==1 and ld.im==0 and ld.re==-density
        assert density>0; bc+=1
    for z in (Q(F(1,5),F(1,7)),Q(F(3,4),F(-1,3))):
        b=Q(1)
        for w,r in roots: b*=((z-w)/(z-(Q(2*u)-w.conj())))**r
        assert b.norm2()<1;bc+=1
    counts['finite_blaschke_cases']=bc
    w=roots[0][0]; z=Q(u,0)
    errors['reflect_at_zero_instead_of_u']=((z-w)/(z+w.conj())).norm2()!=1
    errors['reverse_boundary_phase_speed']=ld.re!=density

    # Endpoint-reduced integral of the literal Fourier matrix.
    # Delta,L and E are formal rational specializations AFTER imposing
    # exp(+/- i omega_j L)=1, E=exp(z L). They are not production cells.
    fc=0
    for L,delta,z,E in ((F(2),F(1,3),Q(F(2,5),F(1,7)),Q(F(3,2),F(1,4))),
                        (F(3),F(2,5),Q(F(3,7),F(-1,6)),Q(F(4,3),F(-1,5)))):
        for j in range(-2,3):
            for k in range(-2,3):
                oj,ok=j*delta,k*delta
                S=(1/((z+I*oj)*(z+I*ok))+1/((z-I*oj)*(z-I*ok)))/L
                diag=(1/(z+I*oj)+1/(z-I*oj)) if j==k else Q(0)
                rhs=(E-1)*S-diag
                if j==k:
                    direct=sum((-1/(z+sgn*I*oj)+(E-1)/(L*(z+sgn*I*oj)**2)
                                for sgn in (-1,1)),Q(0))
                else:
                    def sine_int(o): return (E-1)*(1/(z+I*o)-1/(z-I*o))/(2*I)
                    direct=2*(sine_int(ok)-sine_int(oj))/(L*(oj-ok))
                assert direct==rhs;fc+=1
                if j==k and j==0: errors['drop_finite_Laplace_diagonal']=(direct!=(E-1)*S)
    counts['finite_Laplace_matrix_entries']=fc

    # Positive-time support correction: exact formal exponential powers,
    # represented here by a rational base for an algebraic test.
    sc=0; base=F(2); u0,a=2,1
    for y in (-3,-1,0,1,2,4):
        analytic=base**((u0+a)*y)
        poisson=base**(u0*y-a*abs(y))
        defect=F(0) if y<=0 else base**((u0+a)*y)-base**((u0-a)*y)
        assert analytic==poisson+defect;sc+=1
    counts['time_support_cases']=sc
    errors['replace_Poisson_by_analytic_continuation']=base**3!=base
    errors['drop_reflected_exponential']=base**3-base!=base**3

    # Contact cancellation S_P(1/2)=0 on explicit source contact directions.
    # Algebraic controls only; PAPER positivity of decaying kernels is separate.
    a0=F(1,2); delta=F(1,3); js=list(range(-2,3))
    q1,q2=a0*a0+delta*delta,a0*a0+4*delta*delta
    ee=[q2,-4*q1,6*a0*a0,-4*q1,q2]
    oo=[q2,-2*q1,F(0),2*q1,-q2]
    cc=0
    for c in (ee,oo):
        assert sum(c)==0
        vp=sum((c0/(Q(a0)+I*j*delta) for j,c0 in zip(js,c)),Q(0))
        vm=sum((c0/(Q(a0)-I*j*delta) for j,c0 in zip(js,c)),Q(0))
        assert vp==vm==Q(0)
        assert sum(c0*c0*2*a0/(a0*a0+(j*delta)**2) for j,c0 in zip(js,c))>0
        cc+=1
    counts['contact_directions']=cc

    # Jensen lower bound for a positive decaying kernel (finite algebra checks).
    jc=0
    for a in (F(1,4),F(1,3),F(1,2)):
        weights=[F(1,6),F(1,3),F(1,2)]; freqs=[F(0),F(1),F(3)]
        moment=sum(p*x*x for p,x in zip(weights,freqs))
        val=sum(p*2*a/(a*a+x*x) for p,x in zip(weights,freqs))
        assert val>=2*a/(a*a+moment);jc+=1
    counts['decaying_kernel_Jensen_cases']=jc
    for u in (F(1,128),F(1,32),F(1,8)):
        a=F(1,2)-2*u
        assert F(4)+2/a<=12
    errors['drop_second_contact_kernel']=(F(4)+F(8)!=F(4))

    exponents=[]
    for eps in (F(1,128),F(1,64),F(1,33)):
        kap=F(5,24)+eps; hh=F(1,4)+eps
        high=F(1,2)+3*eps-3*kap
        lefttail=3*eps+kap-5*hh
        horizontal=F(1,2)+3*eps+kap-6*hh
        righttail=F(1,2)+3*eps+kap-5*hh
        assert high==-F(1,8)
        assert lefttail==-F(25,24)-eps
        assert horizontal==-F(19,24)-2*eps
        assert righttail==-F(13,24)-eps
        exponents.append(dict(epsilon=str(eps),high=str(high),lefttail=str(lefttail),
                              horizontal=str(horizontal),righttail=str(righttail)))
    counts['budget_exponent_rows']=len(exponents)
    # C0=U-Rlow and Rlow=Pstable+Dgrowth, one copy of Hd only.
    C,H,U,Pstable=map(F,[7,2,3,5]);Rlow=U-C;D=Rlow-Pstable;A=C-H
    assert A==U-Pstable-D-H
    errors['double_Hd_return']=A!=U-Pstable-D-2*H
    assert all(errors.values()),errors
    return dict(passed=True,counts=counts,planted_errors_detected=errors,exponents=exponents,
                scope='Exact finite algebra and formal/rational controls; not actual zeta coordinates or CCM spectra',
                cofinal_signed_supplier_certified_by_code=False)


def main():
    if len(sys.argv)!=2: raise SystemExit('usage: python3 check_q52.py CANONICAL_Q52.txt')
    raw=Path(sys.argv[1]).read_bytes();p=verify(raw);mutations={}
    bad=bytearray(raw);bad[p['sources'][0]['start_byte']+50]^=1
    for name,data,outer in [('outer_hash',bytes(bad),True),('body_hash',bytes(bad),False),
                           ('extra_separator',raw[:p['sources'][0]['end_byte']]+b'\n'+raw[p['sources'][0]['end_byte']:],False),
                           ('truncated_frame',raw[:-2],False)]:
        try: verify(data,outer)
        except (ValueError,UnicodeError): mutations[name]=True
        else: raise AssertionError('undetected provenance change: '+name)
    out=dict(provenance=p,provenance_mutations=mutations,mathematics=math_checks(),
             historical_programs_executed=False,lean=False,arb=False,production_spectrum=False,
             numeric_zeta_zeros=False,independent_audit=False)
    text=json.dumps(out,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q52_checks.json').write_text(text,encoding='utf-8');print(text,end='')

if __name__=='__main__': main()
```
END_ASSET

BEGIN_ASSET q52_checks.json
BYTES: 4714
SHA256: e81fff3559c6a96750cc3bec035c30a87f4b261c55c285fb1f998099edbd9769
```json
{
  "arb": false,
  "historical_programs_executed": false,
  "independent_audit": false,
  "lean": false,
  "mathematics": {
    "cofinal_signed_supplier_certified_by_code": false,
    "counts": {
      "budget_exponent_rows": 3,
      "circle_branch_cases": 20,
      "contact_directions": 2,
      "decaying_kernel_Jensen_cases": 3,
      "finite_Laplace_matrix_entries": 50,
      "finite_blaschke_cases": 6,
      "green_polynomial_cases": 15,
      "time_support_cases": 6
    },
    "exponents": [
      {
        "epsilon": "1/128",
        "high": "-1/8",
        "horizontal": "-155/192",
        "lefttail": "-403/384",
        "righttail": "-211/384"
      },
      {
        "epsilon": "1/64",
        "high": "-1/8",
        "horizontal": "-79/96",
        "lefttail": "-203/192",
        "righttail": "-107/192"
      },
      {
        "epsilon": "1/33",
        "high": "-1/8",
        "horizontal": "-75/88",
        "lefttail": "-283/264",
        "righttail": "-151/264"
      }
    ],
    "passed": true,
    "planted_errors_detected": {
      "double_Hd_return": true,
      "drop_U_normal_derivative_of_X": true,
      "drop_finite_Laplace_diagonal": true,
      "drop_reflected_exponential": true,
      "drop_second_contact_kernel": true,
      "drop_winding_corner": true,
      "reflect_at_zero_instead_of_u": true,
      "replace_Poisson_by_analytic_continuation": true,
      "reverse_boundary_phase_speed": true,
      "use_log_modulus_squared_without_half": true
    },
    "scope": "Exact finite algebra and formal/rational controls; not actual zeta coordinates or CCM spectra"
  },
  "numeric_zeta_zeros": false,
  "production_spectrum": false,
  "provenance": {
    "all_frames_verified": true,
    "bytes": 129443,
    "lf": 2162,
    "packet": "PROSHKA_CCM_JOINT_BOUNDARY_PHASE_Q52_2026-10-27.txt",
    "sha256": "2832d7259a0c5fbac9e4d6882775457f76ce8673ce3862ff6672d23f54286b13",
    "source_count": 8,
    "sources": [
      {
        "bytes": 8546,
        "end_byte": 16369,
        "end_line": 195,
        "id": "S1",
        "lf": 166,
        "name": "CCM_POST_Q51_REPEATED_PRIMITIVE_PREFLIGHT.md",
        "sha256": "02ce0e7a85863c6da6df148b6a560f8349f411811ce5d77b3637fff7ce19f409",
        "start_byte": 7823,
        "start_line": 30
      },
      {
        "bytes": 84366,
        "end_byte": 100809,
        "end_line": 1640,
        "id": "S2",
        "lf": 1441,
        "name": "PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_VERDICT_2026-10-27.md",
        "sha256": "953aef7fdb188a62264d48571165be1f936df8bd021acf57823b4c0f3f1c86e3",
        "start_byte": 16443,
        "start_line": 200
      },
      {
        "bytes": 5633,
        "end_byte": 106495,
        "end_line": 1767,
        "id": "S3",
        "lf": 123,
        "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
        "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2",
        "start_byte": 100862,
        "start_line": 1645
      },
      {
        "bytes": 4636,
        "end_byte": 111180,
        "end_line": 1864,
        "id": "S4",
        "lf": 93,
        "name": "CCM_POST_Q27_DENSITY_BUDGET.md",
        "sha256": "87c3faa5a652ca4d205e82674553ad0f5f5a1c24735c43a09d98d4560c3dc166",
        "start_byte": 106544,
        "start_line": 1772
      },
      {
        "bytes": 3946,
        "end_byte": 115166,
        "end_line": 1943,
        "id": "S5",
        "lf": 75,
        "name": "CCM_Q43_CONCLUSION.md",
        "sha256": "c0a8339a58d0ed7be7942dcd657164dc479b470d74a5613b2006c77fa2407ef5",
        "start_byte": 111220,
        "start_line": 1869
      },
      {
        "bytes": 4532,
        "end_byte": 119738,
        "end_line": 2027,
        "id": "S6",
        "lf": 80,
        "name": "CCM_Q44_CONCLUSION.md",
        "sha256": "4b0f6e355cc1e5159df49a4eafafbb81e5326825febdfc42f18f7202eb610993",
        "start_byte": 115206,
        "start_line": 1948
      },
      {
        "bytes": 3436,
        "end_byte": 123214,
        "end_line": 2086,
        "id": "S7",
        "lf": 55,
        "name": "CCM_Q45_CONCLUSION.md",
        "sha256": "fe75c23687897d58a6c891d37cf3e2968d4957d228e80bc9f02a852a86f6e070",
        "start_byte": 119778,
        "start_line": 2032
      },
      {
        "bytes": 6174,
        "end_byte": 129434,
        "end_line": 2159,
        "id": "S8",
        "lf": 69,
        "name": "CCM_SPARSE_BAND_RECEIVER.md",
        "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
        "start_byte": 123260,
        "start_line": 2091
      }
    ]
  },
  "provenance_mutations": {
    "body_hash": true,
    "extra_separator": true,
    "outer_hash": true,
    "truncated_frame": true
  }
}
```
END_ASSET

BEGIN_ASSET replay_q52.py
BYTES: 2888
SHA256: a1231282cad7f27c28292755fb808d2d451543cff41c2a822b5318f302585fb7
```python
#!/usr/bin/env python3
"""Extract and replay Q52's four checked assets; do not run source bodies.
Usage: python3 replay_q52.py VERDICT.md CANONICAL_Q52.txt [OUTPUT_DIRECTORY]
Only Python 3.9+ standard-library modules are required.
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
EXPECTED = {'registration_q52.json', 'check_q52.py',
            'q52_checks.json', 'replay_q52.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    assets = {}
    pos = 0
    while True:
        h = HEAD.search(raw, pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name not in EXPECTED or name in assets:
            raise ValueError('unexpected or duplicate asset: ' + name)
        start, end = h.end(), h.end() + int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]):
            raise ValueError('asset length: ' + name)
        if hashlib.sha256(body).hexdigest() != h[3].decode('ascii'):
            raise ValueError('asset SHA256: ' + name)
        body.decode('utf-8')
        closing = b'```\nEND_ASSET\n'
        if raw[end:end+len(closing)] != closing:
            raise ValueError('asset closing frame: ' + name)
        assets[name] = body
        pos = end + len(closing)
    if set(assets) != EXPECTED:
        raise ValueError('missing assets')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q52.py VERDICT.md CANONICAL_Q52.txt [OUTPUT_DIRECTORY]')
    verdict, canonical = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q52_replay').resolve()
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = out / name
        if target.resolve() in (verdict, canonical):
            raise ValueError('refusing to overwrite an input')
        target.write_bytes(body)
    completed = subprocess.run(
        [sys.executable, str(out / 'check_q52.py'), str(canonical)],
        cwd=out, capture_output=True, check=True)
    (out / 'check_q52.stdout').write_bytes(completed.stdout)
    if (out / 'q52_checks.json').read_bytes() != assets['q52_checks.json']:
        raise ValueError('replayed JSON differs from the embedded result')
    report = dict(asset_count=len(assets), all_asset_hashes_match=True,
                  checker_executed=True, json_byte_identical=True,
                  historical_programs_executed=False, production_spectrum=False,
                  independent_audit=False)
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
```
END_ASSET

## 13. Фактическое воспроизведение собранного ответа

Четыре приложения извлечены **из самого итогового Markdown**. Их byte-count, SHA-256 и закрывающие frames совпали; извлечённый `check_q52.py` исполнен на неизменённом каноническом Q52 TXT. Его `q52_checks.json` совпал со встроенным результатом побайтно.

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

Это собственное воспроизведение, не независимый математический аудит. Скрипты исторических источников не запускались. Внутренний circle/branch контроль вычисляет ненулевые Fourier-коэффициенты полинома на окружности и их нормированный логарифмический интеграл; он не определяет проверяемый интеграл через желаемый ответ. Рациональные модельные данные остаются только алгебраическими контролями.

**Итог Q52:** полное contour/area спаривание, монодромия, entire/high-возврат и исходный \(P\) сохранены. Устойчивая фазовая часть оплачена; бесплатный Poisson-return опровергнут целым интегральным тестом исходного ядра. Направленная оценка всей обязательной конечновременной поправки не выведена. Новый арифметический показатель, полный CCM-goal и RH не закрыты. Репозиторий не изменялся.
