# STATUS: TRY_CCM_JOINT_SIGNED_ARITHMETIC_Q03
```yaml
OPERATIVE_CLASS: TRY_CCM_JOINT_SIGNED_ARITHMETIC_Q03
VERDICT_CODE: REFLECTED_WEIL_PAIRING_REFINES_FULL_FIXED_STRIP_LOG_FEE_ARITHMETIC_POWER_OPEN
DATE: 2026-10-20
REQUEST_FILE: PROSHKA_CCM_JOINT_SIGNED_ARITHMETIC_Q03_2026-10-20.txt
REQUEST_BYTES: 101698
REQUEST_LF_COUNT: 1619
REQUEST_SHA256: 664df558b602e914457885c6ba519c016ba8b35c0066c194430e6e0570490ac8
REQUEST_HASH_AND_SIZE: MATCH
REQUEST_READ: COMPLETE_INCLUDING_ALL_EIGHT_EMBEDDED_SOURCE_BLOCKS
SOURCE_BASELINE: b41c9a3a2e744e7a2ea6c2d3037a74e0b6bb5d49
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: ORIGINAL_FULL_CCM_N_EQUALS_M_WITH_ORIGINAL_THREE_CONSTRAINT_SPARSE_BAND
TERMINAL_CONSUMER: SEPARATE_SPARSE_BAND_OFF_CRITICAL_WITNESS_RECEIVER
SCHEDULE: M=R=floor(m^epsilon), 0<epsilon<1/32 fixed before m grows
CHOSEN_MECHANISM: EXACT_MOBIUS_RECOMBINATION_AND_REFLECTED_WEIL_PAIRING_WITH_DAMPED_LAPLACE_SAMPLING
ADJUDICATION: INCONCLUSIVE_FOR_NEW_FULL_ARITHMETIC_POWER
NEW_FULL_POWER_BELOW_THREE_EIGHTHS: NOT_OBTAINED
NEW_ETA_EPSILON_TENDING_TO_ZERO: NOT_OBTAINED
NEW_COFINAL_POWER_GAIN: NOT_OBTAINED
NEW_COMPLETE_CONDITIONAL_ENVELOPE: "T_gtR <= [E_a(m,M)+50 log(m)+8+b_small]P; under inherited ZF78, E_a=O(m^(3/8) log(5+2pi M/log m))"
NEW_DIRECT_RESTRICTED_FLOOR: "P K_m P >= -E_a(m,M)P; a=3/8 remains conditional on ZF78"
FINITE_ENVELOPE: "E_a=2^18 C_z log(5+Omega) [m^a+m^(1/8)(1+log m)^2], L>=4, 1/8<=a<=1/2, all right-half zeros have Re(rho)-1/2<=a"
NEW_QUANTITATIVE_SCOPE: COMPLETE_FIXED_STRIP_LOGARITHMIC_PRICE_ONLY
OLD_COMPLETE_ENVELOPE: O(m^(3/8) (log m)^2 log(3 log m)), conditional on ZF78
ZF78_USE: USED_AS_THE_SAME_NAMED_CONDITIONAL_INPUT_NOT_REPROVED
OTHER_MATHEMATICAL_INPUTS: ACCEPTED_CCM_WEIL_DICTIONARY_AND_CLASSICAL_LOCAL_ZERO_COUNT
UNPAID_STEP: SIGNED_COUPLING_OF_REFLECTED_EVALUATIONS_WITH_CRITICAL_LINE_POSITIVE_MASS
FIRST_SIGN_LOSS: "2 Re(A conjugate(B)) >= -|A|^2-|B|^2, followed by m^delta<=m^a"
C_PLUS_E_SLOW: RETAINED_THROUGH_EXACT_T_RECOMBINATION; Q02_RETURN_NOT_SPENT_AS_POSITIVE_CREDIT
ACTUAL_MOBIUS_COEFFICIENTS: RETAINED_BY_EXACT_LAMBDA_EQUALS_MU_CONVOLVED_WITH_LOG
ALL_PRIME_POWERS: RETAINED
ACTUAL_W_AND_MIXED_TERMS: RETAINED_UNTIL_EXPLICIT_PROVED_INEQUALITY
RH_OR_MERTENS_STRENGTH_INPUT: NOT_ASSUMED
RH: NOT_PROVED
FULL_SP: OPEN_NOT_CLAIMED
G1_G3: OPEN_NOT_CLAIMED
CF22_PYSR: PARKED_REOPENABLE
PX_RH_CLAIM: NOT_MADE
REPOSITORY_WRITES: NONE
LEAN_RUNS: 0
ARB_RUNS: 0
ACTUAL_CCM_SPECTRAL_RUNS: 0
EXACT_LOCAL_CONTROLS: 2536
EXACT_CONTROL_STATUS: PASS
TRANSFORM_DIAGNOSTICS: 9_BINARY64_CASES_NOT_INTERVAL_CERTIFICATES
HIGH_PRECISION_DIAGNOSTIC_ATTEMPT: TIME_LIMIT_NO_COMPLETED_RESULT_NOT_COUNTED_AS_PASS
INDEPENDENT_REVIEW: NOT_RUN
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: UNIVERSAL_SAMPLING_LEMMA_AND_COMPLETE_CONDITIONAL_LOG_FEE_ONLY
CONSUMER_POWER_PROGRESS: NONE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
ACTUAL_ROUTE_KILL_SCOPE: NONE
ROUTE_SCORE: 3
```

Ы. **Нового арифметического показателя в Q03 не получено.** Выполнен один другой количественный ход: вернуться от `C+E_slow` к полной исходной сумме, собрать настоящую свёртку Мёбиуса до модулей и оценивать **полную форму Вейля через отражённые пары**, не через максимум скалярных префиксов. Получена полная условная оболочка с меньшей логарифмической ценой:

\[
 T_{>R}\preceq
 \left[C\,m^{3/8}\log(5+\Omega_M)+b_{\rm small}+50\log m+8\right]P
 \quad\text{eventually},
 \qquad \Omega_M=2\pi M/\log m.
\]

**Зависимость от ZF78 та же, что у принятого Q10.** При фиксированном `epsilon` это `O_epsilon(m^(3/8) log m)`, вместо записанного `O(m^(3/8) log^2(m) log(3 log m))`. Это не меньшая фиксированная степень и не `eta(epsilon)->0`. Нового независимого арифметического факта о расположении знаков μ здесь не поставлено. Ниже выполнены полный перенос, самокритика и точная локализация первой потери знака.

## 0. Источники и граница задачи

**[ABSTRACT | PAPER — происхождение].** Прочитан весь смонтированный UTF-8 Q03: 101698 байт, 1619 LF; SHA-256 совпадает с указанным владельцем. Восемь встроенных файлов включают три собственных теста, приёмку Q02, полный Q02, sparse-band receiver, continuous log-density identity и старый Selberg-аудит. Верхние строки 1–58 — действующее задание; старые директивы внутри приложений не исполнялись.

Повторно прочитан bootstrap через GitHub. Для проверки источниковой нормировки открыт только прямо упомянутый sparse receiver-ом файл `docs/literature/openai_math_2026-10-07/CCM_RESTRICTED_PRIME_RECEIVER.md` на baseline `b41c9a3a2e744e7a2ea6c2d3037a74e0b6bb5d49`, blob `897a92716a746ce8b9a36adb77e66c83b19bdf59`. Новое состояние HEAD, Comparator и транзитивные Lean-зависимости не проверялись.

Внешние первичные материалы использованы только для двух классических входов: нормировки полной Weil-дистрибуции и локального числа нулей с кратностями. Их формулировки, использование и URLs приведены в §13. Источниковое отождествление этой дистрибуции с **настоящей** CCM принимается из пакета, а не выводится из сходства названий операторов.

Собственные результаты пакета сохраняются:

* `-a_c'` меняет знак: односторонний scalar cumulative bound не применяется как положительное ядро.
* Полный верхний край Q неопределён: отрицательный кубический член не заменяет весь оператор.
* Два affine log moments уже оплачены; их повторное вычитание не считается новым выигрышем.
* Q02 оплачивает `T-V`, но не V.

Ни один из этих обходов не используется как новая предпосылка. Контур через неизвестные нули не сдвигается: используется полная, абсолютно сходящаяся при данном тесте zero-формула, со всеми членами.

### Зарегистрированное ожидание

До новых локальных проверок зафиксировано: точная μ-сборка; отражённая билинейная, а не модульно-квадратная форма; сохранение компенсации пары при all-pass множителе; точность finite-Fourier/Laplace нормировки. Ожидалось возможное уменьшение **логарифмической платы**, но не новый показатель ниже `3/8`. Регистрация и фактические результаты воспроизводятся в приложениях.

## 1. Неизменённые определения и какой откат выполнен

**[FINITE_CELL | PAPER — источник Q03:469–513].** Пусть
\[
 L=\log m,\quad \omega_j=2\pi j/L,\quad \Omega=2\pi M/L,
 \qquad Fe_j(t)=L^{-1/2}e^{i\omega_jt}\mathbf1_{[0,L]}(t).
\]
В формулах ниже `L>=4`, `1<=M<=m`, `2<=R<m`. Целевое расписание остаётся
\[
 M=R=\lfloor m^\epsilon\rfloor,\qquad0<\epsilon<1/32
 \quad\text{фиксировано до }m\to\infty.
\]
Проектор `P` — исходное ортогональное сжатие на
\[
 b^*c=v_+^*c=v_-^*c=0.
\]
Нулевое дополнение помещает коэффициенты в исходный полный носитель `|j|<=m`. Частоты не заменяются на `2pi j/log M`. При фиксированном m проектор не дифференцируется и не подстраивается под нуль или выбранный вектор.

\[
 Q_M(s)_{jk}=\begin{cases}
 2(1-s/L)\cos(\omega_js),&j=k,\\
 [\sin(\omega_ks)-\sin(\omega_js)]/[\pi(j-k)],&j\ne k,
 \end{cases}\quad 0\le s\le L,
\]
\[
 A_m(t)=t^{-1/2}P Q_M(\log t)P,
 \qquad
 T_{>R}=\sum_{\substack{d>R\\dk\le m}}\mu(d)\log k\,A_m(dk).
 \tag{1}
\]
Все d,k — обычные целые; все произведения и степени простых сохраняются. `k=1` имеет вес ноль, `dk=m` имеет исходное `Q_M(L)=0`.

Для каждого `c in ran P`, `f=Fc`, имеем
\[
 \|f\|_2=\|c\|_2,\quad f(0)=f(L)=0,\quad
 \int_0^L e^{t/2}f(t)\,dt=\int_0^L e^{-t/2}f(t)\,dt=0.
 \tag{2}
\]
В частности, нулевое продолжение f принадлежит `H^1(R)`; используемые граничные условия следуют из настоящего b, а не вводятся заново.

### 1.1. Совместная μ-сборка до всякого модуля

**[FINITE_CELL | PAPER].** Для каждого целого n:
\[
 \sum_{d\mid n}\mu(d)\log(n/d)=\Lambda(n).
 \tag{3}
\]
Доказательство: при `n=p^a` остаётся `a log p-(a-1)log p=log p`; при двух или более различных простых группировка коэффициентов каждого `log p` содержит множитель `sum_{d|N}mu(d)=0` по другому простому. При n=1 обе стороны нулевые.

Следовательно, точно
\[
 T_{\le R}+T_{>R}=\mathcal A_m,
 \qquad
 \mathcal A_m=\sum_{2\le n\le m}\Lambda(n)A_m(n).
 \tag{4}
\]
Это использование **именно настоящих μ**. Оно не является новым тождеством и не заявляется арифметическим выигрышем: это законный откат к полному source-объекту перед нормами. В (4) не теряется ни короткая часть, ни квадратные/высшие степени простых.

Положим
\[
 D_m=P(A_{\rm arch}-c_AI)P.
\]
Принятый CCM crosswalk и цена из Q03:1000–1014,1497–1506:
\[
 \boxed{PK_mP=D_m-T_{\le R}-T_{>R}},
 \qquad \|D_m\|\le50L+8,
 \tag{5}
\]
\[
 \|T_{\le R}\|\le b_{\rm small}:=
 (56+32\Omega)\sqrt R+12(1+\log R)^2.
 \tag{6}
\]

## 2. Полная signed Weil-формула, а не положительный суррогат

**[ABSTRACT | PAPER — классическая формула и принятый source map].** Используем
\[
 \mathcal F_f(w)=\int_0^L f(t)e^{wt}\,dt.
\]
Для нетривиального нуля `rho` положим
\[
 w_\rho=\rho-\tfrac12=\delta_\rho+i\gamma_\rho,
 \qquad w_\rho^\dagger=-\overline{w_\rho}.
\]
Пусть `n_rho` — кратность. Полная форма на исходном тесте равна
\[
 \boxed{
 \langle c,K_mc\rangle
 =\mathcal W(f)
 =\sum_\rho n_\rho
 \mathcal F_f(w_\rho)
 \overline{\mathcal F_f(w_\rho^\dagger)}.
 }
 \tag{7}
\]
Сумма по различным нулям с явной кратностью эквивалентна сумме по нулям с повторениями. Нетривиальные нули здесь — нули xi, а trivial-zero/gamma и pole terms находятся в исходной арифметической форме. Исходные два экспоненциальных условия оплачивают её pole-моменты; они не разрешают удалить какие-либо нетривиальные нули.

Нормировка (7) проверяется источниковым сепаратором: значения `+e^{delta h}` и `-e^{delta h}` на отражённой паре дают ровно `-2r e^{2delta h}`, как в принятом adverse witness. Подстановка `|F(w)|^2` вместо отражённого произведения изменила бы этот знак и саму форму.

### 2.1. Законность формулы для наших конечных Fourier-тестов

Для гладких компактных тестов (7) — стандартная Weil-дистрибуция. Для f из (2) её можно получить плотностью в `H^1_0(0,L)` при **фиксированной** ячейке. Действительно, после интегрирования по частям для `|gamma|>=1` и `|delta|<=1/2`
\[
 |\mathcal F_f(\delta+i\gamma)|
 \le e^{L/2}\|f'\|_1/|\delta+i\gamma|.
\]
Такая же граница действует для `H^1_0`-аппроксимантов с равномерно ограниченной `H^1`-нормой. Произведения в (7) имеют суммируемый `O_{m,f}((1+|gamma|)^{-2})` конверт по классическому локальному числу нулей. Переход с гладких тестов допустим по dominated convergence. Арифметическая сторона непрерывна в принятой fixed-window form-норме; `H^1`-сходимость и одномерное вложение в `C^0` её обеспечивают. Здесь константа может зависеть от фиксированного m; **равномерные** оценки выводятся отдельно ниже, из явной Fourier-формулы.

Можно также использовать источник Suzuki, §4.2, где периодически-гладкий тест, обрезанный на конечном интервале, входит в класс `K(a)`. Это проверка класса тестов, не импорт положительности.

### 2.2. Отражённые пары сохраняются целиком

Функциональные симметрии xi сохраняют кратности. Обозначим через `Z_+` нули с `delta>0`, а через `Z_0` — нули на критической прямой. Тогда
\[
 \mathcal W(f)=\mathcal Z_0(f)+
 2\Re\sum_{\rho\in Z_+}n_\rho
 \mathcal F_f(w_\rho)
 \overline{\mathcal F_f(w_\rho^\dagger)},
 \tag{8}
\]
\[
 \mathcal Z_0(f)=\sum_{\rho\in Z_0}n_\rho
 |\mathcal F_f(i\gamma_\rho)|^2\ge0.
\]
Каждый right-half нуль спаривается с левым нулём той же высоты, а не с его обычным комплексным сопряжением. Вся right-half совокупность включает обе высоты ±gamma; четырёхчленные симметрии не посчитаны дважды.

Введём обычное отражение `f^r(t)=f(L-t)` и два Laplace-преобразования
\[
 H_f(z)=\int_0^L f(t)e^{-zt}\,dt,
 \qquad H_{f^r}(z)=\int_0^L f(L-t)e^{-zt}\,dt.
\]
Оба — преобразования исходных Fourier-полиномов с той же полосой, поскольку `e^{i omega_j L}=1`. Их L2-нормы равны. Точно
\[
 \mathcal F_f(w)=e^{wL}H_{f^r}(w),
 \qquad
 \mathcal F_f(w^\dagger)=H_f(\bar w).

\]

Итак,
\[
 \boxed{
 \mathcal W(f)=\mathcal Z_0(f)+
 2\Re\sum_{\rho\in Z_+}n_\rho m^{\delta_\rho+i\gamma_\rho}
 H_{f^r}(\delta_\rho+i\gamma_\rho)
 \overline{H_f(\delta_\rho-i\gamma_\rho)}.
 }
 \tag{9}
\]
Все source-смешанные члены содержатся в этом выражении. Правая сторона не является суммой модулей квадратов.

## 3. Новый количественный инструмент: weighted Laplace sampling без платы за размерность

Здесь доказывается новый для данной попытки конверт. В нём нет предположения о малости Мёбиуса, RH, простоте или разделённости нулей.

### Лемма A. Полный частотный интеграл

**[ABSTRACT | PAPER].** Пусть `L>=4`, `M>=1`,
\[
 f(t)=L^{-1/2}\sum_{|j|\le M}c_j e^{2\pi ijt/L},
 \quad0\le t\le L,
 \qquad\Omega=2\pi M/L.
\]
Для каждого `sigma>=0`:
\[
 \boxed{
 \int_{\mathbb R}\log(5+|y|)|H_f(\sigma+iy)|^2\,dy
 \le64\log(5+\Omega)\|f\|_2^2.
 }
 \tag{10}
\]
Для `sigma>=-1/(1+L)` достаточно заменить 64 на 512.

**Доказательство.** Интегрирование каждого исходного Fourier-монома даёт точное
\[
 H_f(z)=\frac{1-e^{-zL}}{\sqrt L}
 \sum_{|j|\le M}\frac{c_j}{z-i\omega_j}.
 \tag{11}
\]
В точках `z=i omega_j` выражение понимается по устранимому пределу. На правой/левой стороне никакой новый pole не создан; `H_f` целая.

Положим
\[
 T=2\Omega+2,\quad d=2M+1,\quad E=\max(1,e^{-\sigma L}).
\]
Из Plancherel в конвенции без `2pi` в экспоненте:
\[
 \int_{\mathbb R}|H_f(\sigma+iy)|^2dy
 =2\pi\int_0^L e^{-2\sigma t}|f(t)|^2dt
 \le2\pi E^2\|f\|_2^2.
 \tag{12}
\]
Для `|y|>=T` каждый знаменатель (11) имеет модуль не меньше `|y|/2`, а `|1-e^{-zL}|<=2E`. По Cauchy:
\[
 |H_f(\sigma+iy)|^2
 \le\frac{16E^2d}{Ly^2}\|f\|_2^2.
 \tag{13}
\]
Это только оценка **хвоста преобразования**, а не Cauchy по настоящим μ или по блокам матрицы. Число d будет полностью оплачено шириной tail-области:
\[
 \frac d{LT}\le\frac{3M}{4\pi M+2L}\le\frac3{4\pi}.
\]
Кроме того,
\[
 \int_T^\infty\frac{\log(5+y)}{y^2}dy
 =\frac{\log(5+T)}T+\int_T^\infty\frac{dy}{y(y+5)}
 \le\frac{2\log(5+T)}T.
\]
Следовательно, central и две tail-части стоят вместе не больше
\[
 \left(2\pi+\frac{48}{\pi}\right)E^2\log(5+T)\|f\|_2^2
 <64E^2\log(5+\Omega)\|f\|_2^2,
\]
так как `log(5+T)=log(7+2Omega)<=2log(5+Omega)`. При `sigma>=0` имеем E=1. При `sigma>=-1/(1+L)`, `E^2<=e^2<8`, и получается 512. ∎

В частности, в (10) нет скрытого множителя `M`, `L` или `2M+1`. Отрицательная sigma в малой полосе оплачена множителем `e^2`, не перенормировкой исходного теста.

### 3.1. Единственный input о количестве нулей

**[ABSTRACT | PAPER — классический вход].** Фиксируем конечную константу `C_z>=1`, такую что
\[
 \sum_{\substack{\rho:\Re\rho\ge1/2\\|\Im\rho-y|\le2}}n_\rho
 \le C_z\log(5+|y|),\qquad y\in\mathbb R.
 \tag{14}
\]
Это Proposition 16 в Tao, *254A, Notes 2*, при фиксированном source-параметре `varepsilon=1/2`, после конечного покрытия окна и увеличения абсолютной константы. Кратности включены. Физическая `epsilon` не участвует в этой константе. Никакой zero-free region не следует из (14).

### Лемма B. Значения в точках нулей, отделённых от критической прямой

**[ABSTRACT | PAPER].** Суммируя только по реальным нетривиальным нулям с `1/8<=delta_rho<=1/2`, получаем
\[
 \boxed{
 \sum n_\rho|H_f(\delta_\rho+i\gamma_\rho)|^2
 \le2^{16}C_z\log(5+\Omega)\|f\|_2^2.
 }
 \tag{15}
\]
Та же граница верна со знаком `-gamma` и с `f^r`.

**Доказательство.** Возьмём диски радиуса `r_0=1/32` вокруг каждой точки `delta+i gamma`. По среднему для субгармонической функции `|H_f|^2`:
\[
 |H_f(z_\rho)|^2\le\frac1{\pi r_0^2}
 \iint_{|z-z_\rho|<r_0}|H_f(z)|^2dA(z).
\]
Эта disk-оценка получается из Cauchy и Cauchy–Schwarz на каждом круге, затем интегрированием по радиусу. Положительность подынтегральных функций оправдывает перестановку всех сумм.

Для фиксированного `z=sigma+iy` число покрывающих его центров, с кратностями, не больше (14). Все диски лежат в
\[
 3/32\le\sigma\le17/32.
\]
По (10), ширине этой полосы меньше 1 и (14), сумма не больше
\[
 \frac{64}{\pi r_0^2}C_z\log(5+\Omega)\|f\|^2
 \le2^{16}C_z\log(5+\Omega)\|f\|^2.
\]
Высоты не предполагаются различными или разделёнными. ∎

### Лемма C. Нули в узкой полосе возле критической прямой

**[ABSTRACT | PAPER].** Для `0<delta_rho<1/8`:
\[
 \boxed{
 \sum n_\rho|H_f(\delta_\rho+i\gamma_\rho)|^2
 \le512C_z(1+L)^2\log(5+\Omega)\|f\|_2^2.
 }
 \tag{16}
\]

**Доказательство.** Теперь радиус disk-оценки `r_L=1/(1+L)`. Все диски лежат в
\[
 -r_L<\sigma<1/8+r_L,
\]
полоса имеет ширину меньше 1 при `L>=4`. Используем вторую часть леммы A с константой 512. Плата `r_L^{-2}` выставлена явно, это `(1+L)^2`. Никакого предположения об отсутствии нулей в этой полосе нет. ∎

Отделение (15) от (16) важно: применение disk-радиуса `1/L` ко всем нулям снова создало бы лишнюю логарифмическую плату на главном `m^{3/8}` члене. Здесь малая плата умножается только на `m^{1/8}`.

## 4. Полный односторонний результат, включая все нули

Обозначим через `STRIP(a)` только следующее явно названное предположение:
\[
 0<\Re\rho-1/2\le a
 \quad\text{для каждого правого нетривиального нуля},
 \qquad1/8\le a\le1/2.
 \tag{17}
\]
`a=1/2` разрешено классической критической полосой. `a=3/8` — ровно сохранённая ZF78, здесь **условный** вход. Никакого предположения `a=O(epsilon)` не принимается.

### Теорема D. Source-preserving lower floor

**[COFINAL_FAMILY | CONDITIONAL для a=3/8; PAPER для a=1/2, при принятом CCM dictionary].** При `L>=4`:
\[
 \boxed{
 PK_mP\succeq-\mathfrak E_a(m,M)P,
 }
 \tag{18}
\]
где можно взять
\[
 \boxed{
 \mathfrak E_a(m,M)=
 2^{18}C_z\log(5+\Omega)
 \left[m^a+m^{1/8}(1+L)^2\right].
 }
 \tag{19}
\]
Здесь весь исходный источник и все исходные межмодовые связи сохраняются.

**Доказательство.** Рассмотрим произвольный `c in ran P`. Для каждого правого нуля положим
\[
 U_\rho=m^{\delta_\rho/2}e^{i\gamma_\rho L}H_{f^r}(w_\rho),
 \qquad V_\rho=m^{\delta_\rho/2}H_f(\bar w_\rho).
\]
Точная пара из (9) равна `2 Re(U_rho conjugate(V_rho))`. Используем только верное
\[
 2\Re(U_\rho\overline{V_\rho})
 \ge-|U_\rho|^2-|V_\rho|^2,
 \tag{20}
\]
причём положительное `Z_0(f)` можно оставить или отбросить при **нижней** оценке W.

В секторе `delta>=1/8` множитель `m^delta<=m^a`; (15) применяется отдельно к двум, но настоящим, endpoint-преобразованиям. Цена не больше
\[
 2^{17}C_z m^a\log(5+\Omega)\|f\|^2.
\]
В секторе `0<delta<1/8` используется `m^delta<=m^{1/8}` и (16). Цена не больше
\[
 2^{10}C_z m^{1/8}(1+L)^2\log(5+\Omega)\|f\|^2.
\]
Их сумма не больше (19). Норма `||f||=||c||`; утверждение действует одновременно для всех c. Это доказывает операторную оценку (18), а не лишь среднее заранее выбранной формы. ∎

### 4.1. Бесконечный zero-tail не пропущен

Для `Y>=2Omega+2`, (13) и (14) дают, с консервативной константой,
\[
 \sum_{\substack{\rho\in Z_+\\|\gamma_\rho|>Y}}
 n_\rho\gamma_\rho^{-2}
 \le24C_z\frac{\log(5+Y)}Y.
\]
С учётом двух endpoint-преобразований и critical-line части, абсолютный хвост (7) ограничен
\[
 \boxed{
 2048C_z\,m^a\frac{(2M+1)\log(5+Y)}{LY}\|f\|^2.
 }
 \tag{21}
\]
Для проверки этого коэффициента достаточно разбить высоты на единичные интервалы: при `K=floor Y>=Y/2` сумма `sum_{j>=K}log(6+j)/j^2` не больше `12log(5+Y)/Y`. Обе высотные стороны и обе отражённые функции включены; 2048 оставляет запас.

Это не вычисление нулей до Y. Формула нужна для явной проверки абсолютной сходимости и цены возможного усечения. При `Y=m^2` и исходной полосе её степень `a+epsilon-2` отрицательна. Точные near-zero evaluations не заменялись усреднением по высоте.

### 4.2. Что это даёт при унаследованной ZF78

Полагая `a=3/8`, имеем
\[
 \mathfrak E_{3/8}
 =O\!\left(m^{3/8}\log(5+\Omega)\right),
 \tag{22}
\]
потому что `m^{1/8}(1+L)^2=o(m^{3/8})`. В конечной формуле (19) этот меньший член оставлен полностью; утверждение (22) имеет обычный достаточно поздний старт.

При `M=floor(m^epsilon)`:
\[
 \log(5+\Omega)=O(1+\epsilon L),
\]
поэтому (22) имеет цену `O_epsilon(m^(3/8)L)`. Она **не** имеет показателя, стремящегося к нулю.

Без ZF78 можно поставить `a=1/2`; это даёт полный bound со степенью `1/2`, а не безусловное получение (22). Никакая информация о нулях не была улучшена этой работой.

## 5. Возврат к T, к V и к исходной CCM без двойного счёта

**[COFINAL_FAMILY | CONDITIONAL, те же inputs].** Из (5),(18) получаем более точную, чем scalar envelope, запись:
\[
 \boxed{
 T_{>R}\preceq\mathfrak E_a P+D_m-T_{\le R}.
 }
 \tag{23}
\]
В частности,
\[
 \boxed{
 T_{>R}\preceq
 [\mathfrak E_a+b_{\rm small}+50L+8]P.
 }
 \tag{24}
\]
Это полная матрица, не только fast-sector, не один diagonal block и не выдуманный zero-free supplier. Для каждого actual `W=PWP>=0, Tr W=1` берётся след того же неравенства. Коммутирование W с отдельными слагаемыми не предполагается.

### 5.1. Почему малые делители не надо дважды кредитовать или дважды терять

Если вернуть scalar envelope (24) через грубую (5), получится допустимый, но худший floor
\[
 PK_mP\succeq-[\mathfrak E_a+2b_{\rm small}+2(50L+8)]P.
\]
В настоящем доказательстве это лишнее: в (23) сохранены точные `D_m-T_{<=R}`. Их подстановка в (5) **сокращается алгебраически**, возвращая ровно (18). Это не бесплатная положительность короткого члена — он не оценивался отдельно в доказательстве (18).

Для самого scalar-контракта `T<=a_m P` цена (6) присутствует один раз в (24). Прежний `-2H_P` из другого Q10-представления не прибавляется к новой формуле как дополнительный кредит: (18) получена из полной формы, включающей её исходные continuous/archimedean terms.

### 5.2. Полный C+E и принятый Q02-return

Обозначим доказанную Q02 цену через
\[
 F_2(m,M,R)=32(1+D_1)N_D(1+2L)
 +\frac{\mathfrak K_2}{\pi^2m^{3/2}},
\]
\[
 D_1=2/L+4\Omega,
 \quad D_2=4\Omega/L+4\Omega^2,
 \quad\mathfrak K_2=16/3+20D_1/9+4D_2/9,
 \quad N_D=\lceil\log_2(m/R)\rceil.
\]
Пакет даёт точное `T=V+Delta_2`, `||Delta_2||<=F_2`, где
\[
 V=C_{>R}+E_{\rm slow}^{(m^2)}.
\]
Отсюда, если требуется формулировка именно для V,
\[
 \boxed{
 V\preceq(\mathfrak E_a+F_2)P+D_m-T_{\le R},
 }
 \tag{25}
\]
и её scalar-версия добавляет `b_small+50L+8`.

Выполненная попытка оценивает **T напрямую**, поэтому не требуется возвращать V обратно через ещё одно грубое `F_2`. В частности, исходная точная отмена `C(d)+E_d=0` при `d>m/2` сохранена в (3)–(4), а вся непустая `k=2` оболочка остаётся в полном источнике. Здесь не оценивались C и E_slow независимо.

### 5.3. Полная таблица показателей

| Компонента | Цена на исходном расписании | Статус |
|---|---|---|
| Полная zero-pair цена при ZF78 | `m^(3/8) log(5+Omega)` | Новый полный условный конверт |
| Вспомогательный near-line сектор | `m^(1/8)(1+L)^2 log(5+Omega)` | Явно включён в конечную (19), позже меньше главного |
| `b_small` в scalar T-return | `(56+32Omega)sqrt R+12(1+log R)^2` | Прежний, степень `3epsilon/2` |
| Архимедов scalar-return | `50L+8` | Прежний |
| `T-V` | `F_2=O_epsilon(m^epsilon L)` | Принятый Q02, не новый выигрыш |
| При явном zero-height cutoff `Y=m^2` | `O(m^(a+epsilon-2))` с указанными логами | Не пропущен; cutoff вообще не нужен для теоремы |

После всех возвратов сохраняется показатель `3/8`. Ни на каждой ячейке, ни на неограниченной подпоследовательности показатель `eta(epsilon)->0` не получен.

### 5.4. Сравнение с Q10 на том же объекте

Записанная прежняя цена:
\[
 C_{10}\,m^{3/8}L^2\log(3L)+b_{\rm small}.
\]
Новая (24):
\[
 C\,m^{3/8}\log(5+\Omega)+b_{\rm small}+50L+8.
\]
При фиксированном `0<epsilon<1/32` отношение новых scalar-цен к записанным старым стремится к нулю. Ведущее отношение имеет порядок `O_epsilon(1/[L log(3L)])`. Отдельная ограниченная отрицательная поправка Q10 `-2H_P` не меняет этого асимптотического сравнения.

**Не заявляется историческая оптимальность или новизна fixed-strip принципа.** Новое здесь — конкретный dimension-free возврат этой более экономной цены к literal CCM и actual W. Отсутствие нового показателя не скрыто за словом «выигрыш».

## 6. Первый неоплаченный шаг и его точная степень

В (9) все коэффициенты ещё совместны. Первое существенное ослабление — (20). Оно забывает, как расположены два endpoint-преобразования **одного и того же f**, и не использует положительную массу `Z_0(f)` для оплаты отрицательных отражённых вкладов.

Следующее ослабление:
\[
 m^{\delta_\rho}\le m^{3/8}.
\]
При желаемом `eta(epsilon)<3/8` цена нового полного конверта относительно цели содержит
\[
 \boxed{
 m^{3/8-\eta(\epsilon)}\log(5+\Omega),
 }
 \tag{26}
\]
и остаётся слишком большой. Это сравнение **верхних бюджетов**, не нижняя граница actual T и не свидетель существования внепрямого нуля.

Чтобы заменить `3/8` на меньшую степень в этой попытке, надо либо поставить более сильную независимую zero-free информацию, либо оценить **совместное signed-выражение (9)** лучше, чем (20), с сохранённым положительным `Z_0`. Ни то ни другое не поставлено. Локальный счёт нулей (14) сам этого не даёт. Не принимаются Mertens, RH, скрытая простота нулей, случайные фазы или независимость endpoint-значений.

Утверждение «все нули уже имеют delta<=O(epsilon)» немедленно сделало бы результат нужным, но это и есть непоставленное усиление, а не следствие frame-леммы. Оно не используется.

### 6.1. Оставшееся взаимодействие можно записать без потери смешанных членов

В пространстве последовательностей по фактическим правым нулям, с весами их кратностей, пусть
\[
 (\mathcal B_+f)_\rho=\sqrt{n_\rho}\,
 m^{\delta_\rho/2}e^{i\gamma_\rho L}H_{f^r}(w_\rho),
\]
\[
 (\mathcal B_-f)_\rho=\sqrt{n_\rho}\,
 m^{\delta_\rho/2}H_f(\bar w_\rho).
\]
Тогда точно
\[
 \boxed{
 \mathcal W(f)=\mathcal Z_0(f)
 +\tfrac12\|\mathcal B_+f+\mathcal B_-f\|^2
 -\tfrac12\|\mathcal B_+f-\mathcal B_-f\|^2.
 }
 \tag{27}
\]
Это равенство, не ещё одна доказанная положительность. Конкретный неоплаченный вход — верхняя оценка разности
\[
 \tfrac12\|\mathcal B_+f-\mathcal B_-f\|^2
 -\tfrac12\|\mathcal B_+f+\mathcal B_-f\|^2-\mathcal Z_0(f)
\]
на исходном source-классе с меньшей полной степенью. Форма (27) объясняет, **какой** кредит был потерян в (20), но не сжимает неизвестное одним новым обозначением. Она не назначается обязательным интерфейсом для любого доказательства.

**Основание для дальнейшего выбора:** новый supplier должен связывать два исходных endpoint-map и/или их critical-line массу. Другая оценка размера каждого map отдельно оставляет ту же фиксированную степень. При отсутствии такого supplier продолжать шлифовать константу в (15) бессмысленно для целевого показателя.

## 7. Сильнейшие проверки против ложного знака

### 7.1. Отражённая пара не есть положительный квадрат

Для контрольных значений A=1, B=-1:
\[
 2\Re(A\bar B)=-2,
 \qquad2|A|^2=2.
\]
Верная (20) достигает равенства. Это абстрактный контроль algebraic inference, не утверждение о настоящем наборе нулей. Source-негативный witness в пакете условно реализует именно противоположные значения на гипотетической off-line паре; существование такой пары не утверждается.

### 7.2. Бесплатное right-half damping отражённой пары не работает

Для вещественного `a_0>0` рассмотрим множитель
\[
 b_{a_0}(z)=\frac{z-a_0}{z+a_0}.
\]
При `Re z>0` его модуль меньше единицы, но для `z^dagger=-conjugate(z)` точно
\[
 \boxed{b_{a_0}(z)\overline{b_{a_0}(z^\dagger)}=1.}
 \tag{28}
\]
Поэтому умножение двух отражённых Mellin-значений одним таким all-pass фильтром не уменьшает их произведение: левый множитель компенсирует правый. Это верно и для конечных произведений таких факторов, вне их нулей/полюсов.

Это **только** точная проверка предполагаемого бесплатного spectral credit. Существование time-domain фильтра, сохранение support и CCM-класса отдельно не доказаны и здесь не используются. Формула (28) не запрещает другие фильтры с оплаченным возвратом и не опровергает actual cancellation.

### 7.3. Не подменять результат данными общего модельного набора

Леммы A–C работают для наборов точек, удовлетворяющих (14), но no-go из произвольного такого набора не выводится для дзета. В этой работе не строится фиктивное распределение нулей для опровержения исходной CCM. ZF78 — только сохранённая условная граница. Все усиления реального источника требуют собственной арифметики.

## 8. Обоснованный откат и два представления перед дальнейшими действиями

Откат разрешён запросом и выполнен **до** отдельной Euler-ошибки: `C+E` вновь собрано в T, затем короткая часть возвращена в точную `Lambda=mu*log` и полную Weil-форму. Потеря знака теперь видна в (20), а не скрыта в scalar-prefix supremum.

| Представление того же объекта | Что сохраняет | Диагностическая сила / цена | Чего ещё нет |
|---|---|---|---|
| **Исходный joint autocorrelation pairing** `sum mu(d)log k/sqrt(dk) q_c(log(dk))`, или `V=C+E_slow` с Q02-возвратом | Все настоящие коэффициенты, знак q, полный P, все d,k | Высокая против scalar-positive и endpoint shortcuts; низкая цена source-check, высокая цена нового арифметического знака | Верхняя оценка совместной меры на этом конусе |
| **Отражённые endpoint-map (9),(27)** | Те же prime powers через exact Weil dictionary; все zero-пары и critical positive mass | Высокая против ложной модульной замены/неоплаченного фильтра; frame-budget вычислен; новый signed supplier имеет неизвестную высокую цену | Относительное, а не отдельное нормовое сравнение map с достаточной степенью |

Это два места сохранения структуры, а не два новых предполагаемых теоремных входа и не разрешение на широкий численный запуск. **Дальнейший fixed-strip absolute-frame ход останавливается:** он уже вернул полный показатель и не породил новое арифметическое сокращение.

## 9. Дискриминаторы

**Для источниковой цели.** При заранее закреплённых `epsilon,K,eta,m0` проверяется запас
\[
 K m^\eta-\lambda_{\max}(T_{>R}|_{\operatorname{ran}P}),\qquad m\ge m_0.
\]
Нижняя интервальная граница `>=0` принимает только конечную ячейку; верхняя `<0` опровергает только этот фиксированный контракт. Интервал через ноль требует более высокой точности либо точного структурного свидетеля. Неизвестный eventual-start нельзя подгонять после опыта.

**Для нового полного fixed-strip конверта.** Проверяемая универсальная часть — (10),(15),(16),(18) и source dictionary (7). Для численного finite-height теста обязательно добавить хвост (21). Нулевой интервал truncated signed sum не является нулём бесконечной суммы.

**Для (28).** Точный rational complex product отличает сохранение пары от кажущегося damping одного значения; никаких измерений близких нулей не требуется.

## 10. Выполненные проверки, ограничения и прогнозы

**[FINITE_CELL | PAPER — exact controls, не формальный prover].** Выполнено 2536 точных проверок рациональной/целочисленной алгебры:

| Проверка | Число |
|---|---:|
| Полная μ-log сборка в Mangoldt для n<=192 | 192 |
| Все короткие/длинные атомы при R=2,3,5,8,16 | 960 |
| Степень 27 и точная граница при n=12 | 2 |
| Отражённая пара, lower-square bound и полный возврат | 1125 |
| Контроль знака critical-пары | 225 |
| Преднамеренная модульная подмена обнаружена | 1 |
| All-pass pair identity | 27 |
| Рациональная проверка показателей возврата | 4 |

Это не вычисление K_m и не доказательство location bound. Универсальные утверждения доказываются выше.

**[FINITE_CELL | PAPER — численная диагностика без интервалов].** Девять binary64 контролей сравнили явное Laplace-преобразование, прямую квадратуру, отражённую пару, устранимый резонанс и исходные экспоненциальные ограничения. Использованы настоящие odd/even/mixed профили из собственных тестов Q03, нормированные и дополненные нулями, на законных расписаниях `m=2^64,2^128,2^192`, `epsilon=1/64`, `M=R=2,4,8`. Число m велико только в аналитической нормировке: **арифметические суммы до m не вычислялись**. Максимальное расхождение равно приблизительно `1.96e-15`; это agreement, не сертификат точного знака.

Первый 70-значный mpmath-прогон превысил ограничение 45 секунд и не дал завершённого результата. Он **не** записан как PASS. После этого для дешёвой проверки конвенций выполнена отдельно обозначенная binary64-квадратура. Математические утверждения и их области из-за timeout не менялись.

Независимый reviewer, Lean, Arb и Comparator не запускались. Ветка репозитория не изменялась. Прогноз нового степенного выигрыша не регистрировался и такой выигрыш не получен.

## 11. Ledger и dependency epistemics

| ID | Утверждение | Scope | Verifier | Статус |
|---|---|---|---|---|
| S | Literal P,Q,K, full Weil source map, short/arch returns | COFINAL_FAMILY | PAPER | Принятые источниковые входы, не повторный полный аудит |
| M | Полная μ-log сборка (3)–(5) | FINITE_CELL | PAPER | Точная; не новая арифметическая оценка |
| W | Отражённая signed-формула (7)–(9) | ABSTRACT | PAPER | Классическая формула + проверенный source-return |
| A | Weighted Laplace integral (10) | ABSTRACT | PAPER | Доказан с явными константами |
| B | Damped zero sampling (15)–(16) | ABSTRACT | PAPER | Доказан из локального счёта нулей; без RH |
| D | Полный floor (18)–(19), a=1/2 | COFINAL_FAMILY | PAPER | Выведен при принятых source inputs |
| D78 | Полный floor и T-bound, a=3/8 | COFINAL_FAMILY | CONDITIONAL | Использует ровно ZF78; ожидает независимого аудита нового переноса |
| R | V/T/K return (23)–(25), полный бюджет | COFINAL_FAMILY | CONDITIONAL | Те же зависимости; нового малого показателя нет |
| C | Reflected/all-pass controls | ABSTRACT | PAPER | Точные проверки ошибочных общих выводов; не actual counterexample |
| OPEN | Новый signed power supplier / cofinal variant | COFINAL_FAMILY | CONDITIONAL | Не доказан и не использован как предпосылка |

**DOWNSTREAM_CONSUMER:** отдельный sparse-band off-critical witness receiver на исходной полной CCM. **ACTUAL_CONSUMER_REQUIREMENT:** upper bound полной T с `eta(epsilon)->0`, eventual либо законно cofinal. **ORIGINAL_REQUESTED_OBJECT:** одна совместная actual-μ попытка для V/T. **ORIGINAL_OBJECT_IS:** UNKNOWN как необходимое представление; норма endpoint-map отдельно точно не необходима. **KNOWN_WEAKER_INTERFACES:** прямой signed autocorrelation upper bound; оценка полной prime-матрицы без long split; совместная signed (9) с сохранением `Z_0` вместо (20). **FAILURE_TYPE:** NO_DERIVATION нового арифметического показателя. **EPISTEMIC_STATUS:** RESEARCH_DEBT. **REOPEN_TRIGGER:** независимый actual-source контроль coupling в (9)/(27) с меньшей полной степенью, либо другая совместная арифметическая оценка исходного q-cone, а не только новая константа sampling. **NOVELTY_AXIS:** меньшая полная логарифмическая плата fixed-strip возврата. **KILL_SCOPE:** NONE для T/V/CCM/RH. **MATHEMATICAL_IMPOSSIBILITY_EVIDENCE_FOR_ACTUAL_TARGET:** NONE.

### Closeout

**Что стало меньше:** конкретная полная fixed-strip upper-price с `L^2 log(3L)` уменьшена до `log(5+Omega)`, все source-return сохранены. **Что не стало меньше:** степенной показатель `3/8` и основной signed arithmetic debt. **Что нельзя повторять:** объявлять critical-line positivity знаком off-critical пары; заменять два endpoint-map независимыми модулями и называть это actual cancellation; считать `a=O(epsilon)` поставленным; тратить Q02 fast-bound на V целиком.

**Судьба предсказаний:** finite μ/short-long identities и reflected pair controls прошли exact-check; Laplace convention подтверждена девятью неинтервальными контролями; ожидаемое уменьшение логарифмической цены выведено в PAPER; power gain не предсказывался и не получен. Нет ретроактивного повышения fixed-strip bound до нового zero-free результата.

```yaml
MEMORY_ENTRY:
  iteration: CCM_JOINT_SIGNED_ARITHMETIC_Q03_2026_10_20
  target: ACTUAL_ONE_SIDED_LONG_DIVISOR_SPARSE_BOUND
  status: OPEN
  cognitive_operator: REPRESENTATION_SHIFT
  quantitative_result: Complete inherited-strip logarithmic fee reduced by direct reflected-pair sampling
  first_unpaid_step: Separate-square lower bound of an actual reflected pair followed by m^delta<=m^(3/8)
  actual_arithmetic_power_gain: NONE
  forbidden_future_move: Repeat frame-constant tuning as if it reduced the source exponent
  next_decisive_action: Bounded independent audit of the full new sampling-to-CCM return; no new wide search or RH premise
  full_SP_G1_G3_RH: OPEN
```

## 12. Одна CODEX DIRECTIVE

**Независимо проверить один пакет: леммы A–C и полный source-return теоремы D.** Проверить прежде всего: (i) точную нормировку полной zero-формы против принятой CCM и источникового `-2r e^{2delta h}`; (ii) отсутствие конъюгационной подмены в (9); (iii) weighted Plancherel и оплату `(2M+1)/(LT)` в (10); (iv) обе ширины disk-областей и multiplicity count в (15),(16); (v) все zero-tail terms (21); (vi) exact short/arch cancellation в (23), без повторного использования чужого `-2H_P`; (vii) сравнение **полных** условных бюджетов на исходном расписании.

Приёмка означает только новый complete fixed-strip logarithmic envelope. Не принимать новую степень, `eta(epsilon)->0`, cofinal gain, Mertens, SP или RH. Воспроизвести exact checker как контроль реализации; floating-point appendix не повышать до интервала. При дефекте вернуть первый неверный шаг и исправленную цену, не общий запрет actual cancellation. После аудита не продолжать эту absolute-frame ветвь без отдельного арифметического supplier для потерянной signed coupling.

## 13. Первичные источники и воспроизведение

Внутренний authoritative источник — Q03 с SHA-256 из заголовка. Опорные диапазоны его индексированной/сырой версии (разница возможна только в завершающей пустой строке):

* 1–58: новый контракт и запреты;
* 113–305: три собственных no-gain теста;
* 308–381: ограниченная приёмка Q02;
* 467–513: буквальные P,Q,T,C,E;
* 936–1016: полный Q02-return и inherited budget;
* 1436–1506: sparse witness и source form;
* 1509–1565: уже оплаченные smooth identities, не новый supplier;
* 1568–1619: старый product-only Selberg audit.

Дополнительно прочитан прямо указанный sparse receiver-ом `CCM_RESTRICTED_PRIME_RECEIVER.md` на source baseline; источник full Weil convention, отражённого witness и равенства (5).

Первичные внешние материалы:

```text
Masatoshi Suzuki, Aspects of the screw function corresponding to the Riemann zeta-function,
arXiv:2206.03682v4, §§3.2–3.3 (3.3)–(3.8), §4.2 test class K(a).
https://arxiv.org/html/2206.03682v4

Terence Tao, 254A, Notes 2: Complex-analytic multiplicative number theory,
9 December 2014, Proposition 16, fixed source parameter varepsilon=1/2.
https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/
```

Первый источник поставляет формулу, не её положительность без RH. Второй — локальное число нулей, не ZF78 и не малость μ. Все новые constants и mappings в тексте доказаны отдельно. Полнота поиска литературы и историческая новизна результата не утверждаются.

## Приложение A. Регистрация новых проверок

```json
{
  "request": "PROSHKA_CCM_JOINT_SIGNED_ARITHMETIC_Q03_2026-10-20.txt",
  "request_sha256": "664df558b602e914457885c6ba519c016ba8b35c0066c194430e6e0570490ac8",
  "mechanism": "Exact Mobius-to-Weil recombination followed by one-sided reflected-zero pairing and dimension-free damped-Laplace sampling",
  "registered_before_checks_below": [
    "Finite Mobius-log coefficient assembly equals the full Mangoldt coefficients minus every short-divisor term, including prime powers and both cutoffs.",
    "A reflected off-critical pair contributes 2 Re(A conjugate(B)), not 2 |A|^2; the sharp lower elementary bound is -(|A|^2+|B|^2).",
    "The rational all-pass multiplier b(z)=(z-a)/(z+a) obeys b(z) conjugate(b(-conjugate(z)))=1 away from its zeros/poles; damping one member is not damping the pair.",
    "The finite Fourier Laplace formula retains its removable resonances and matches a separately integrated original constrained profile.",
    "Under the inherited ZF78 input, the proposed full bound retains exponent 3/8 but may reduce its logarithmic fee from L^2 log(3L) to log(5+Omega)."
  ],
  "not_predicted": "No new full power below 3/8, no eta(epsilon)->0 estimate, no RH conclusion.",
  "verification_boundary": "Paper proofs plus finite exact controls and small non-interval transform diagnostics only; no source-spectrum scan, Arb, Lean or independent external review."
}
```

## Приложение B. Точный локальный проверяющий

Сохранить блок как `check_q03.py` и выполнить `python3 check_q03.py`. Подстановок переменных или путей нет; JSON записывается рядом со скриптом. Используется стандартная библиотека Python. Проверяются только указанные конечные тождества, не спектр CCM.

```python
"""Exact Q03 controls. No CCM spectral computation and no zero-location certificate."""
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
import hashlib, json


def mu(n: int) -> int:
    out, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            out = -out
            if n % p == 0:
                return 0
        p += 1
    return -out if n > 1 else out


def flog(n: int) -> dict[int, int]:
    c: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            c[p] = c.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        c[n] = c.get(n, 0) + 1
    return c


def coeff(n: int, lo: int, hi: int) -> dict[int, int]:
    out: dict[int, int] = {}
    for d in range(lo, min(hi, n)+1):
        if n % d == 0:
            for p, a in flog(n//d).items():
                out[p] = out.get(p, 0) + mu(d)*a
    return {p:a for p,a in out.items() if a}


def plus(a, b):
    z = dict(a)
    for p, t in b.items():
        z[p] = z.get(p, 0) + t
    return {p:t for p,t in z.items() if t}

# Exact Gaussian rationals (real,imaginary).
def z(x=0,y=0): return (F(x),F(y))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[0],-a[1])
def sub(a,b): return add(a,neg(b))
def conj(a): return (a[0],-a[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def norm2(a): return a[0]**2+a[1]**2
def div(a,b):
    q=norm2(b)
    if not q: raise ZeroDivisionError
    c=mul(a,conj(b))
    return (c[0]/q,c[1]/q)

stats = Counter()
for n in range(1,193):
    fs=flog(n)
    target={next(iter(fs)):1} if len(fs)==1 else {}
    assert coeff(n,1,n)==target
    stats['full_mu_log_to_mangoldt']+=1
    for R in (2,3,5,8,16):
        assert plus(coeff(n,1,R),coeff(n,R+1,n))==target
        stats['short_long_all_atom_returns']+=1
assert coeff(27,3,27)=={3:-2}
assert coeff(12,4,12)=={2:1}
stats['proper_power_and_cutoff_controls']+=2

values=[z(F(k,3),F(j,5)) for k in range(-2,3) for j in (-1,0,2)]
phases=[z(1),z(-1),z(0,1),z(0,-1),z(F(3,5),F(4,5))]
for a in values:
    for b in values:
        for phase in phases:
            ap=mul(phase,a)
            paired=2*mul(ap,conj(b))[0]
            assert paired+norm2(a)+norm2(b)==norm2(add(ap,b))
            assert paired>=-norm2(a)-norm2(b)
            stats['reflected_pair_lower_bound_and_return']+=1
        assert 2*mul(a,conj(a))[0]==2*norm2(a)
        stats['critical_pair_sign_controls']+=1

# Deliberate invalid replacement of the reflected bilinear term by a modulus.
a,b=z(1),z(-1)
assert 2*mul(a,conj(b))[0]==-2
assert 2*norm2(a)==2
stats['false_modulus_square_rejected']+=1

for a0 in (F(1,2),F(1,3),F(2,3)):
    for re in (F(1,10),F(1,4),F(3,8)):
        for im in (F(0),F(1),F(7,3)):
            w=z(re,im)
            wd=neg(conj(w))
            def bf(v): return div(sub(v,z(a0)),add(v,z(a0)))
            assert mul(bf(w),conj(bf(wd)))==z(1)
            assert norm2(bf(w))<1
            assert norm2(bf(wd))>1
            stats['allpass_pair_invariance']+=1

# Exponent bookkeeping only, not a test of any asymptotic arithmetic premise.
for eps in (F(1,10000),F(1,1000),F(1,100),F(1,33)):
    assert F(3,2)*eps<F(3,8)
    assert eps<F(3,8)
    assert F(1,8)<F(3,8)
    stats['returned_exponent_comparisons']+=1

out={'status':'PASS','counts':dict(stats),'total_checks':sum(stats.values()),
     'scope':'finite exact coefficient and signed-pair algebra; no CCM sign certificate',
     'ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```

### Фактический результат

```json
{
  "status": "PASS",
  "counts": {
    "full_mu_log_to_mangoldt": 192,
    "short_long_all_atom_returns": 960,
    "proper_power_and_cutoff_controls": 2,
    "reflected_pair_lower_bound_and_return": 1125,
    "critical_pair_sign_controls": 225,
    "false_modulus_square_rejected": 1,
    "allpass_pair_invariance": 27,
    "returned_exponent_comparisons": 4
  },
  "total_checks": 2536,
  "scope": "finite exact coefficient and signed-pair algebra; no CCM sign certificate",
  "ccm_spectral_runs": 0,
  "arb_runs": 0,
  "lean_runs": 0,
  "script_sha256": "ed4d4baf57e0e4a2a1efcc16003f5db8e6bb1747f6dccb4693d45261bff4f2df"
}
```

## Приложение C. Неинтервальная проверка конвенций преобразования

Сохранить блок как `laplace_diagnostics.py` и выполнить `python3 laplace_diagnostics.py` в среде со SciPy. Подстановок путей нет. Суммы по простым, нули дзета и спектры CCM не вычисляются. Первый более медленный 70-значный вариант не завершился в лимит; его отсутствие результата отмечено в JSON, а не выдано за успешный тест.

```python
"""Small floating-point convention checks, not interval or spectral certificates."""
from pathlib import Path
import math, cmath, hashlib, json
from scipy.integrate import quad
rows=[]

def cquad(fn, lo, hi):
    return complex(quad(lambda t:fn(t).real,lo,hi,epsabs=1e-12,epsrel=1e-12,limit=150)[0],
                   quad(lambda t:fn(t).imag,lo,hi,epsabs=1e-12,epsrel=1e-12,limit=150)[0])

for power in (64,128,192):
    L=power*math.log(2); w0=2*math.pi/L; M=2**(power//64)
    odd={1:(.25+w0*w0)*math.sqrt(L)/(2j),-1:-(.25+w0*w0)*math.sqrt(L)/(2j),
         2:-(.25+4*w0*w0)*math.sqrt(L)/(4j),-2:(.25+4*w0*w0)*math.sqrt(L)/(4j)}
    even={0:-.75*math.sqrt(L),1:(1+4*w0*w0)*math.sqrt(L)/2,-1:(1+4*w0*w0)*math.sqrt(L)/2,
          2:-(.25+4*w0*w0)*math.sqrt(L)/2,-2:-(.25+4*w0*w0)*math.sqrt(L)/2}
    for kind in ('odd','even','mixed'):
        raw=odd if kind=='odd' else even if kind=='even' else {j:even.get(j,0)+1j*odd.get(j,0) for j in range(-2,3)}
        norm=math.sqrt(sum(abs(v)**2 for v in raw.values()))
        c={j:v/norm for j,v in raw.items()}
        def f(t):return sum(v*cmath.exp(1j*j*w0*t) for j,v in c.items())/math.sqrt(L)
        def H(z):return (1-cmath.exp(-z*L))/math.sqrt(L)*sum(v/(z-1j*j*w0) for j,v in c.items())
        z=.375+1j*(1/3+1.5*w0)
        hd=cquad(lambda t:f(t)*cmath.exp(-z*t),0,L)
        hr=cquad(lambda t:f(L-t)*cmath.exp(-z*t),0,L)
        # Compare after removing the large exp(Re(z)*L) factor, not before.
        Fscaled=cquad(lambda t:f(t)*cmath.exp(z*(t-L)),0,L)
        partner=H(z.conjugate())
        a=2*(Fscaled*partner.conjugate()).real
        b=2*(hr*partner.conjugate()).real
        res=cquad(lambda t:f(t)*cmath.exp(-1j*w0*t),0,L)
        eH=abs(hd-H(z)); ePair=abs(a-b); eRes=abs(res-math.sqrt(L)*c.get(1,0))
        emom=[]
        for r in (-.5,.5):
            # Moment divided by its common exponential endpoint factor.
            emom.append(abs(sum(v/(r+1j*j*w0) for j,v in c.items())/math.sqrt(L)))
        assert eH<2e-10 and ePair<2e-10 and eRes<2e-10 and max(emom)<2e-10
        rows.append({'m':'2^'+str(power),'epsilon':'1/64','M=R':M,'profile':kind,
                     'Laplace_abs_error':eH,'scaled_pair_abs_error':ePair,
                     'removable_resonance_abs_error':eRes,'moment_coefficient_abs_error':max(emom)})
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','cases':len(rows),'precision':'binary64',
     'scope':'transform conventions on original constrained profiles at legal schedules; no primes, zeta zeros or CCM spectra evaluated',
     'prior_attempt':'A 70-digit, 9-case mpmath quadrature exceeded the 45s execution limit and produced no completed result; not counted as PASS.',
     'max_error':max(max(r['Laplace_abs_error'],r['scaled_pair_abs_error'],r['removable_resonance_abs_error'],r['moment_coefficient_abs_error']) for r in rows),
     'rows':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('laplace_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```

### Фактический результат

```json
{
  "status": "PASS_DIAGNOSTIC_NOT_INTERVAL",
  "cases": 9,
  "precision": "binary64",
  "scope": "transform conventions on original constrained profiles at legal schedules; no primes, zeta zeros or CCM spectra evaluated",
  "prior_attempt": "A 70-digit, 9-case mpmath quadrature exceeded the 45s execution limit and produced no completed result; not counted as PASS.",
  "max_error": 1.9572857118358894e-15,
  "rows": [
    {
      "m": "2^64",
      "epsilon": "1/64",
      "M=R": 2,
      "profile": "odd",
      "Laplace_abs_error": 2.6251129656189234e-17,
      "scaled_pair_abs_error": 4.336808689942018e-19,
      "removable_resonance_abs_error": 1.776671397975708e-15,
      "moment_coefficient_abs_error": 0.0
    },
    {
      "m": "2^64",
      "epsilon": "1/64",
      "M=R": 2,
      "profile": "even",
      "Laplace_abs_error": 1.1056736068366555e-17,
      "scaled_pair_abs_error": 8.470329472543003e-21,
      "removable_resonance_abs_error": 1.968427392893083e-16,
      "moment_coefficient_abs_error": 1.6668921920349325e-17
    },
    {
      "m": "2^64",
      "epsilon": "1/64",
      "M=R": 2,
      "profile": "mixed",
      "Laplace_abs_error": 7.37257477290143e-18,
      "scaled_pair_abs_error": 7.623296525288703e-21,
      "removable_resonance_abs_error": 3.403163082969598e-16,
      "moment_coefficient_abs_error": 2.6355879703905836e-17
    },
    {
      "m": "2^128",
      "epsilon": "1/64",
      "M=R": 4,
      "profile": "odd",
      "Laplace_abs_error": 6.594944350062754e-18,
      "scaled_pair_abs_error": 1.2705494208814505e-20,
      "removable_resonance_abs_error": 8.89143889457352e-16,
      "moment_coefficient_abs_error": 0.0
    },
    {
      "m": "2^128",
      "epsilon": "1/64",
      "M=R": 4,
      "profile": "even",
      "Laplace_abs_error": 6.942281208919283e-18,
      "scaled_pair_abs_error": 1.4558378780933287e-22,
      "removable_resonance_abs_error": 9.567911291176978e-16,
      "moment_coefficient_abs_error": 5.893353862474048e-18
    },
    {
      "m": "2^128",
      "epsilon": "1/64",
      "M=R": 4,
      "profile": "mixed",
      "Laplace_abs_error": 7.902413390062179e-18,
      "scaled_pair_abs_error": 5.029258124322408e-22,
      "removable_resonance_abs_error": 9.234396849835526e-16,
      "moment_coefficient_abs_error": 6.074730116030579e-18
    },
    {
      "m": "2^192",
      "epsilon": "1/64",
      "M=R": 8,
      "profile": "odd",
      "Laplace_abs_error": 9.679199334683438e-18,
      "scaled_pair_abs_error": 2.6469779601696886e-22,
      "removable_resonance_abs_error": 9.492423198367192e-16,
      "moment_coefficient_abs_error": 2.4059516394536344e-18
    },
    {
      "m": "2^192",
      "epsilon": "1/64",
      "M=R": 8,
      "profile": "even",
      "Laplace_abs_error": 3.675229789768064e-18,
      "scaled_pair_abs_error": 1.075334796318936e-23,
      "removable_resonance_abs_error": 1.9572857118358894e-15,
      "moment_coefficient_abs_error": 4.811903278907269e-18
    },
    {
      "m": "2^192",
      "epsilon": "1/64",
      "M=R": 8,
      "profile": "mixed",
      "Laplace_abs_error": 1.9679114112006266e-17,
      "scaled_pair_abs_error": 4.516406144539531e-22,
      "removable_resonance_abs_error": 5.601452482706917e-16,
      "moment_coefficient_abs_error": 4.959996369797656e-18
    }
  ],
  "script_sha256": "b4fabc9d88102e5944bbaea7dde663dd8c9d098509f0d10022f45b29a80fdcb5"
}
```
