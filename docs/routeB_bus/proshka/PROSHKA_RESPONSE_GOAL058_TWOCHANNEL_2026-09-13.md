# STATUS: RUN_NAMED_RELATIVE_REMAINDER
```yaml
OPERATIVE_CLASS: RUN_NAMED_RELATIVE_REMAINDER
REQUEST_ID: REQ-2026-09-13-TWOCHANNEL
BOUNDARY_ID: GOAL058_ACTUAL_THETA_TWOCHANNEL_RELATIVE_FORM
REQUEST_COMMIT: de2271bebae87c24ca0dfd3d02ae885de8db1b11
REQUEST_BLOB: eea7ebf0bd637925d065bd443100d11e83ad83ad
REQUEST_SHA256: 4d2193b53ba35111a7bf07f54541c6d2edc21815d2b3760d284fcbf17eb7d4d0
REQUEST_BYTES: 10054
REQUEST_LF: 127
SOURCE_BASE: 4f1d9f75e31955960d56111942b3f1c5efbb78d0
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
HONESTY_STATE: CHALLENGER_NOT_RH
CANDIDATE: GLOBAL_TWOCHANNEL_J_RELATIVE_DOMINATION
CANDIDATE_CHANGED: false
COGNITIVE_OPERATOR: DUALIZE
RESULT: FIRST_UNPAID_FULL_SOURCE_RELATIVE_BOUND
RF_PROVED: false
RF_REFUTED: false
ACTUAL_V_NEGATIVE_WITNESS: false
ACTUAL_MULTIPLE_XI_ZERO_ASSERTED: false
NEW_NECESSARY_CONDITION: RF_IMPLIES_RH_AND_SIMPLE_XI_ZEROS
NECESSARY_CONDITION_IS_NOT_A_PROOF_OF_ITS_CONCLUSION: true
FIRST_UNPAID_TRANSITION: SAME_SOURCE_SHIFT_FORM_DOMINATES_FIXED_FOUR_CHANNEL_NORM
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
SOURCE_SIGN_PROGRESS: NONE
PROOF_STATE: PAPER_DERIVATIONS_PENDING_INDEPENDENT_REVIEW
LEAN_VERIFIED: false
GLOBAL_IC: OPEN_UNCHANGED
GLOBAL_ODD2: OPEN_UNCHANGED
ALL_ORDER_SOURCE_SIGN: OPEN_UNCHANGED
PX_RH_CLAIM: NOT_MADE
PRODUCTION_ADMISSION: false
SOURCE_SIGN_NO_DELTA:
  inherited: 5
  proposed_after_independent_intake: 6
  applied_to_state: false
PUBLICATION_BRANCH: codex_mac/math-proshka-20260912
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_TWOCHANNEL_2026-09-13.md
```

AUTOPSY: dropped=COUPLING; note=The fixed carrier has a complete positive norm and passes the prescribed end tests, but no rank-independent lower comparison of the actual signed source form with that norm is proved. A stronger necessary Fourier condition, including simplicity of xi zeros under RF, is derived, not assumed satisfied or violated.

## 0. Решение

**Полный RF не доказан и не опровергнут.** Этот документ завершает один опыт с неизменным T12/T13 первым точным неоплаченным сравнением. Он не назначает автоматически другое J или вычислительную кампанию.

Получены следующие проверяемые результаты.

1. Для данного J выписана точная положительная четырёхканальная норма, включая межканальную связь. Все конечные матрицы W на различных узлах строго положительны, но их собственные числа не имеют общего положительного нижнего предела.
2. Почти зависимые семейства проверены без вычитания приближённых чисел: каждый порядок конечной разности имеет точный делённый предел. Знаменатели этих пределов положительны для всех порядков именно у T12.
3. Построено одно детерминированное семейство с неограниченным числом реальных узлов. Его относительный предел равен
   \[
   \frac{F'(\tau)^2-F(\tau)F''(\tau)}{S_W(\tau)},
   \quad F(z)=\int f(x)e^{-izx}dx,\quad S_W(\tau)>0.
   \tag{1}
   \]
   Все интегралы, хвосты и конечные суммы этого переноса оплачены ниже.
4. Поэтому RF требует не только неотрицательности V, но и **простоты всех нулей xi**: сначала принятый consumer даёт RH из RF; затем (1) запрещает кратный вещественный нуль F. Это условное следствие RF, **не утверждение RH или простоты**.

В частности, кратный вещественный нуль F, если бы он существовал, дал бы полный отказ любой delta>0 через одно и то же семейство с V[c]/W[c]->0. Существование такого нуля не установлено. Поэтому код KILL здесь был бы неверным. `[ABSTRACT][PAPER]` `[COFINAL_FAMILY][CONDITIONAL]`

## 1. Прочитанные источники и байтовая граница

R — управляющий запрос по указанному пользователем commit. Прочитан целиком. Восстановленные UTF-8 bytes дают 10054 bytes / 127 LF / final LF / CR 0, SHA-256 и Git blob из заголовка. Совпадение blob проверяет также отсутствие изменения текста при восстановлении.

S1 — `docs/Codex/REPORT_2026-09-13_TWOCHANNEL_LAPLACE_BRIDGE.md` в том же commit. Прочитан целиком, T1--T4 и заключительные receipts. Локально пересчитаны 11996 bytes / 245 LF / final LF / CR 0; SHA-256 `e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908`; Git blob `51ef75574931fde124c94a5a9df2d623460d9538`. Оба совпадают с pinned GitHub/source binding.

Следующие четыре файла получены непосредственно через GitHub в SOURCE_BASE. Их **remote Git blobs** подтверждены; ниже отдельно названа область содержательного чтения. SHA-256 и полные размеры S2/S3 в этой таблице — закреплённые контрольные данные запроса/приёмки, **не объявляются независимо пересчитанными локальными SHA-256 в этом проходе**. Для S4/S5 полные SHA-256, размеры/LF и Git blobs дополнительно пересчитаны из ранее доставленных byte-exact frames и сопоставлены с remote blobs именно текущего SOURCE_BASE. Appendix C содержит полный код и буквальный вывод; это не новое содержательное чтение рекурсивного архива.

| ID | Путь | Закреплённые bytes/LF и SHA-256 | Подтверждённый remote blob / чтение |
|---|---|---|---|
| S2 | `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_BROWNIANHODGE_2026-09-13.md` | 50817/664; `7649d7600e9ddac8407aa24a93ebf624466d1a3410e44270de70c3476595dfa9` | `cdd03e7da883835122818529b0ebe993ec27b199`; §§1--6, нужные формулы (2)--(9), (24)--(27), область и хвосты; не заявляется повторное чтение всего Appendix/архива |
| S3 | `docs/Codex/REPORT_2026-09-13_BROWNIANHODGE_INTAKE.md` | 7621/160; `74074ad94cf0c5b1cccdc0959bbf35f73833f92dcf22a66c2fe8fbf768834ca3` | `721cf810edde882840f0f51849598c21e312b6c4`; весь файл |
| S4 | `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md` | 15303/335; `1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282` | `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`; весь файл, Theorem T и его пределы |
| S5 | `docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md` | 37796/467; `14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc` | `de9578084446baecfbb2a316d7bda3da817c8c01`; §4, OD1, BP1--BP3b, BP4/BP5 и их приёмка |

S2/S3 не используются для повторного Brownian-опыта. S4 — принятый all-node/all-complex перенос, **не готовый знак**. Контроль S5 не повторялся.

Bootstrap прочитан в `rh_clean`: `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. Доставленный пользователем pinned GitHub request является текущим управляющим заданием; старый attachment-transport не восстанавливается.

P1 — Galé--Matache--Miana--Sánchez-Lajusticia, arXiv:2401.16091v1, HTML §1, (1.1) и следующая формула ядра. Непосредственно сверены norm factor 1/(2pi), ядро 1/(z+bar(w)) и его норма. Адрес: `https://arxiv.org/html/2401.16091v1`. Прочитан этот HTML-фрагмент, не весь PDF; PDF-хеш S1 не пересчитывался. В настоящих доказательствах Laplace Gram и Fourier transform sech вычисляются непосредственно. P1 не поставляет знак theta.

Новые выводы ниже имеют статус PAPER-кандидатов до независимого приёма. Никакой kernel/Lean-проверки не было. `[ABSTRACT][PAPER]`

## 2. Тот же источник и полный домен

Сохраняем
\[
Z=\int_{\mathbb R}\Phi=\xi(1/2),\quad A=\|\Phi\|_2,
\quad f=\Phi/A,
\]
\[
V(x,y)=\int_0^\infty(x+y+2t)f(x+t)f(y+t)dt,
\quad D(x)=V(x,x)>0.
\tag{2}
\]
Источник S2/S5 даёт полный, а не модово усечённый фактор
\[
f(x)=\frac{4\pi^2}{A}e^{9x/2-a_x}h(a_x),\qquad
 a_x=\pi e^{2x},\qquad 0<h(a)\le1,
\quad h(a)\ge1-\frac3{2a}.
\tag{3}
\]
При малом a последняя нижняя оценка может быть отрицательной. Она не заменяет ни h>0, ни взаимность. В (3) сохранён весь h, полученный из полной свёртки двух половин энергии в S2. Плотность p=Phi/Z не подставляется вместо f.

Из S4 §2 для каждого фиксированного k есть конечная константа C_k с
\[
|f^{(k)}(x)|\le C_k\exp[-(\pi/2)e^{2|x|}].
\tag{4}
\]
Это оплачивает все фиксированные производные, интегралы и граничные переходы ниже. Никакой оценки, равномерной по k, из (4) не извлекается.

Положим m=(x+y)/2, d=(x-y)/2. Чётность f даёт точную формулу
\[
V(x,y)=\int_{|m|}^{\infty}2u f(u+d)f(u-d)du.
\tag{5}
\]
Поэтому V(x,y)>0 **как элемент ядра**, V(-x,-y)=V(x,y), а
\[
D(x)=2\int_{|x|}^{\infty}u f(u)^2du,
\quad D'(x)=-2x f(x)^2.
\tag{6}
\]
Эти свойства не являются PSD утверждением. На каждом конечном компакте D отделена от нуля, и sqrt(D) гладка.

Все конечные комплексные линейные комбинации переводов f и t f на t>=0 принадлежат L2. Компактное интегрирование семейства по x допустимо по (4). Основным consumer остаётся принятый all-node Theorem T; новый compact-test inverse multiplier не вводится. `[ABSTRACT][PAPER]`

## 3. Неизменный J и точная норма четырёх каналов

Буквально сохраняем T12:
\[
r_x=\sqrt{x^2+4},\quad
c_x=\frac{e^{x/2}}{\sqrt{2\cosh x}},\quad
 d_x=\frac{e^{-x/2}}{\sqrt{2\cosh x}},
\]
\[
A_x=r_x^{-1/2},\quad B_x=\sqrt{1-r_x^{-1}},\quad
N_x^2=1+A_x^2c_xd_x,
\]
\[
J_x=\frac1{N_x}\left[
A_x(c_xv_{+,r_x}+d_xv_{-,r_x})
\oplus B_x(c_xw_{+,r_x}+d_xw_{-,r_x})\right].
\tag{7}
\]
A_x — скаляр канала, не физическая константа A. Здесь r_x — радиальная координата носителя, не плотность r(t) исходного закона. Векторы w состоят из двух ортогональных копий
\[
j_r(s)=\sqrt2 e^r e^{-e^{2r}s},\quad s>0,
\quad \langle j_r,j_q\rangle=\operatorname{sech}(r-q).
\tag{8}
\]
Векторы v имеют ровно K_1 из S1 T8. Не предполагается RKHS целевого V.

Пусть C(u)=sech(u), T(u)=u/sinh(u), T(0)=1. Для Fourier convention без нормирующего множителя
\[
\mu(\zeta)=\int_{\mathbb R}C(u)e^{-i\zeta u}du
=\pi\operatorname{sech}(\pi\zeta/2)>0.
\tag{9}
\]
Короткая проверка: интегрируем exp(-i zeta z)/cosh(z) по прямоугольнику высоты pi. Вертикали исчезают; верхняя сторона даёт exp(pi zeta) раз нижнюю. Единственный полюс i pi/2 имеет residue exp(pi zeta/2)/i. Отсюда (1+exp(pi zeta))mu=2pi exp(pi zeta/2), включая zeta=0. S1 T7 также даёт Fourier(T)=mu^2/2.

Для произвольных физических коэффициентов z_i положим t_i=z_i sqrt(D(x_i))/N_(x_i). Определим
\[
P_+(\zeta)=\sum_i t_i A_{x_i}c_{x_i}e^{-i\zeta r_{x_i}},\quad
P_-(\zeta)=\sum_i t_i A_{x_i}d_{x_i}e^{-i\zeta r_{x_i}},
\]
\[
R_+(\zeta)=\sum_i t_i B_{x_i}c_{x_i}e^{-i\zeta r_{x_i}},\quad
R_-(\zeta)=\sum_i t_i B_{x_i}d_{x_i}e^{-i\zeta r_{x_i}},\quad
P_s=(P_++P_-)/\sqrt2,\ P_a=(P_+-P_-)/\sqrt2.
\tag{10}
\]
Тогда **точно**
\[
\boxed{
W[z]=\frac1{2\pi}\int_{\mathbb R}\mu(\zeta)
\left[(1+\mu/4)|P_s|^2+(1-\mu/4)|P_a|^2
+|R_+|^2+|R_-|^2\right]d\zeta.}
\tag{11}
\]
Здесь W[z]=sum bar(z_i)W(x_i,x_j)z_j. Межканальный член до диагонализации равен mu^2 Re(bar(P_+)P_-)/2 под общим множителем 1/(2pi). Именно этот коэффициент следует из off-diagonal T/2; он не отброшен.

Все четыре суммы ограничены для каждого конечного ряда, mu интегрируема. Поэтому (11) — обычные абсолютно сходящиеся интегралы. Если N_0[z] обозначает ту же правую часть с двумя множителями (1+/-mu/4), заменёнными на 1, то
\[
(1-\pi/4)N_0[z]\le W[z]\le(1+\pi/4)N_0[z].
\tag{12}
\]
**Это сравнение двух функциональных норм, не нижняя граница относительно sum |z_i|^2.** Сами P/R могут почти зануляться.

Для различных реальных x_i форма W строго положительна на каждом ненулевом конечном ряду. Действительно, её независимые w-компоненты при нулевой энергии должны обе обращаться в нуль. Линейная независимость конечных различных экспонент exp(-e^(2r)s) группирует коэффициенты по r. В группе {a,-a}, a>0, остаётся матрица
\[
\begin{pmatrix}c_a&d_a\\d_a&c_a\end{pmatrix},
\quad \det=c_a^2-d_a^2=\tanh a>0.
\]
Остальные множители B, sqrt(D)/N положительны. В группе {0} коэффициент тоже обязан быть нулём. Независимость экспонент доказывается умножением на самую медленно убывающую экспоненту и последовательным пределом s->infinity. Повторные узлы сначала объединяются. `[ABSTRACT][PAPER]`

## 4. Почти зависимые ряды: точная, а не entrywise проверка

Пусть rho=V/sqrt(DD), Gamma=Ghat. Их диагонали равны 1. Физические коэффициенты z_i=b_i/sqrt(D(x_i)) дают V[z]=rho[b], W[z]=Gamma[b]. Это допустимая конечная положительная конгруэнция, не смена источника.

Для фиксированного целого m>=1 возьмём x_j=j epsilon,
\[
b_j=(-1)^{m-j}\binom mj,\quad 0\le j\le m.
\]
Повторная основная теорема анализа даёт, для K=rho либо Gamma,
\[
\epsilon^{-2m}K[b]
=\int_{[0,1]^{2m}}
K_{m,m}\left(\epsilon\sum_{j=1}^m u_j,
\epsilon\sum_{j=1}^m v_j\right)du\,dv.
\tag{13}
\]
В частности предел равен K_(m,m)(0,0). Ошибка не превосходит модуля непрерывности этой производной на квадрате [0,m epsilon]^2. Отменены все нижние степени до округления; epsilon не делит приближённый почти нуль.

Для данного Gamma **каждая конечная jet Gram-матрица**
\[
B_m=[\Gamma_{i,j}(0,0)]_{0\le i,j\le m}
\tag{14}
\]
положительно определена. Доказательство использует только w-компоненты J. После ортогонального сложения/вычитания каналов они равны
\[
\frac{B_x}{N_x}\frac{\cosh(x/2)}{\sqrt{\cosh x}}j_{r_x},\qquad
\frac{B_x}{N_x}\frac{\sinh(x/2)}{\sqrt{\cosh x}}j_{r_x}.
\]
Первая функция чётна, вторая нечётна. Разложения r_x=2+x^2/4+O(x^4) и
exp(2r_x)=e^4(1+x^2/2+O(x^4)) показывают: производная порядка 2k первого канала — exp(-e^4 s) умножить на полином степени k с ненулевым старшим коэффициентом; производная порядка 2k+1 второго канала имеет ту же степень k и ненулевой старший коэффициент. Множители при x=0 соответственно ненулевые и имеют простой нуль. Треугольность по степени доказывает независимость всех конечных наборов. Это Hilbert-производные: на компактном x-интервале любой фиксированный порядок доминируется полиномом по s, умноженным на exp(-c s), c>0.

Следовательно, Gamma[b]~epsilon^(2m) Gamma_(m,m)(0,0)>0 для каждого фиксированного m. Не существует положительного coefficient-floor, общего даже для всех двухузловых матриц. Но отсюда **не** следует, что отношение rho[b]/Gamma[b] стремится к нулю: его числитель отменяется тем же порядком. `[ABSTRACT][PAPER]`

### Первый предел проходит; следующий источник не оплачен

Введём полные исходные интегралы
\[
d_0=D(0)=2\int_0^\infty t f(t)^2dt,\quad
I_1=2\int_0^\infty t f'(t)^2dt,\quad
I_2=2\int_0^\infty t f''(t)^2dt,\quad q_0=f(0)^2.
\]
Интегрирование по частям с (4) даёт
\[
V_{11}(0,0)=I_1-q_0,\quad V_{20}(0,0)=-I_1,
\quad V_{22}(0,0)=I_2,
\]
\[
\kappa:=\rho_{11}(0,0)=\frac{I_1-q_0}{d_0}>0,
\quad \rho_{20}(0,0)=-\kappa,
\]
\[
\sigma:=\rho_{22}(0,0)
=\frac{I_2}{d_0}+\frac{q_0^2-2q_0I_1}{d_0^2},
\quad \sigma-\kappa^2=\frac{d_0I_2-I_1^2}{d_0^2}.
\tag{15}
\]
Строгость kappa использует ровно принятый S5 §4:
J_f(t)=t(f'^2-ff'')+ff'>0. Его интеграл равен I_1-q_0. Одной формальной строгой вогнутости для этой поточечной строгости не предполагаем.

У неизменного носителя непосредственное разложение T13 даёт
\[
\Gamma_{11}(0,0)=3/20,\quad \Gamma_{20}(0,0)=-3/20,
\quad \Gamma_{22}(0,0)=61/240.
\tag{16}
\]
Для независимой проверки коэффициентов можно использовать
r_x=2+x^2/4-x^4/64+O(x^6), sqrt(r_x-1)=1+x^2/8-x^4/64+O(x^6),
[((2/5)(r_x cosh x+1/2))]^(-1/2)=1-x^2/4+53x^4/960+O(x^6).
Подстановка в T13 даёт коэффициент x^2 y^2 равный 61/960. Appendix A проверяет эту точную арифметику.

Первый нечётный relative quotient стремится к 20 kappa/3>0; он не убивает никакую достаточно малую delta. На span{evaluation, first derivative} имеется положительная нижняя граница min(1,20 kappa/3). Это ограниченный jet-предел, не доказательство на всех близких парах и не новый all-node supplier.

Уже на чётном span{evaluation, second derivative} RF потребовал бы
\[
\begin{pmatrix}1&-\kappa\\-\kappa&\sigma\end{pmatrix}
\succeq\delta
\begin{pmatrix}1&-3/20\\-3/20&61/240\end{pmatrix},
\tag{17}
\]
то есть, в частности,
\[
(1-\delta)(\sigma-61\delta/240)
-(-\kappa+3\delta/20)^2\ge0.
\tag{18}
\]
Правый carrier имеет Schur complement 139/600>0. Нового бюджета (18) для самой theta здесь нет; наличие такого бюджета в каких-либо непрочитанных документах не отрицается. Проверка одного (18) также не закрыла бы всех m. Никакого sweep по m, полиномам, Hankel-матрицам или theta-узлам не выполнялось.

## 5. Полный Fourier-дискриминатор с растущим числом узлов

### 5.1. Абсолютная сходимость и точный источник

Положим M_j=int_R |x|^j f(x)dx для j=0,2. Формула (5) и Tonelli дают
\[
\boxed{\iint_{\mathbb R^2}|V(x,y)|dxdy=M_0M_2<\infty.}
\tag{19}
\]
Проверка константы: dxdy=2 dm dd; интегрирование m по [-u,u] даёт 8u^2 du dd. Замена a=u+d,b=u-d превращает это в (a+b)^2 da db на a+b>0. Чётность f делит полный интеграл пополам; нечётный первый момент равен нулю.

Если T_j(R)=int_(|x|>R)|x|^j f(x)dx, то тот же расчёт даёт **полный** хвост
\[
\iint_{\max(|x|,|y|)>R}|V(x,y)|dxdy
\le M_0T_2(R)+M_2T_0(R).
\tag{20}
\]
Действительно, |x|,|y|<=u+|d|=max(|a|,|b|) в области |m|<=u. Никакой центральный или противоположный конец не исчезает из оценки.

Из (4),(6) следуют int sqrt(D)<infinity и все её экспоненциально взвешенные L1-моменты. Так как |Gamma|<=1,
\[
|W(x,y)|\le\sqrt{D(x)D(y)},
\quad \iint|W|\le B_0^2,
\quad B_0:=\int\sqrt D.
\]
\[
\iint_{\max(|x|,|y|)>R}|W(x,y)|dxdy
\le2B_0\int_{|x|>R}\sqrt{D(x)}dx.
\tag{21}
\]
Все хвосты (20),(21) стремятся к нулю по доказанному полному источнику.

Сдвиговая производная даёт точное тождество
\[
(\partial_x+\partial_y)V(x,y)=-(x+y)f(x)f(y).
\tag{22}
\]
Это интегрирование полной t-производной исходного integrand. На бесконечности граничный член исчезает по (4); при t=0 он равен -(x+y)f(x)f(y).

Определим без нормирующих 2pi-множителей
\[
\mathscr V(\lambda,\mu)=\iint e^{-i\lambda x}V(x,y)e^{i\mu y}dxdy,
\quad F(z)=\int f(x)e^{-izx}dx.
\]
F(z)=xi(1/2-iz)/A: S4 доказывает равенство в открытой zero-free полуплоскости, а обе стороны целые; теорема тождественности распространяет его на C без RH.

Fourier-преобразование (22) даёт
\[
\boxed{\mathscr V(\lambda,\mu)=
\frac{F(\lambda)F'(\mu)-F'(\lambda)F(\mu)}{\lambda-\mu}
\quad(\lambda\ne\mu),}
\]
\[
\boxed{\mathscr V(\tau,\tau)=F'(\tau)^2-F(\tau)F''(\tau).}
\tag{23}
\]
Знаки фиксированы antilinear-first convention. Например, Fourier(xf)=iF', тогда как int yf(y)exp(i mu y)dy=-iF'(mu). Делитель после (22) равен i(lambda-mu). Равенство на диагонали — непрерывный предел; F и его производные вещественны при вещественном аргументе. Fourier-дифференцирование допустимо в смысле распределений, поскольку V и правая часть (22) принадлежат L1. Эквивалентно, гладкий cutoff даёт граничную ошибку O(R^-1)||V||_1, стремящуюся к нулю. Отдельное необоснованное интегрирование бесконечных границ не используется. При tau=0 формула даёт F(0)(-F''(0))=M_0M_2, в точности (19): это отдельная проверка знака и всех нормирующих множителей. `[ABSTRACT][PAPER]`

### 5.2. Carrier не имеет нулевой plane-wave энергии

Определим
\[
S_W(\tau)=\iint e^{-i\tau x}W(x,y)e^{i\tau y}dxdy
=\left\|\int e^{i\tau x}\sqrt{D(x)}J_x\,dx\right\|^2.
\tag{24}
\]
Bochner-интеграл существует по (21). Для **каждого** tau in R:
\[
\boxed{S_W(\tau)>0.}
\tag{25}
\]
Доказательство со строгим аналитическим дискриминатором. Возьмём лишь независимую w_+-компоненту в (7):
\[
A_\tau(s)=\int_{\mathbb R}e^{i\tau x}a(x)e^{-\ell(x)s}dx,
\quad a(x)=\sqrt{D(x)}\frac{B_xc_x}{N_x}\sqrt2e^{r_x},
\quad \ell(x)=e^{2r_x}.
\]
a ограничена и интегрируема по (4),(6). Её значение
\[
a(0)=\sqrt{2D(0)/5}\,e^2>0.
\]
Если u=r_x-2>=0, то x^2=u(u+4) и exp(2u)>=1+2u+2u^2>=1+x^2/2. Следовательно на всей R
\[
\ell(x)-e^4\ge\tfrac12e^4x^2.
\]
Подстановка x=z/sqrt(s) даёт, с одной гауссовой мажорантой на всей прямой,
\[
\boxed{\lim_{s\to\infty}\sqrt{s}\,e^{e^4s}A_\tau(s)
=2\sqrt{\pi D(0)/5}>0.}
\tag{26}
\]
В пределе exp(i tau z/sqrt(s))->1 для каждого фиксированного tau. Мажоранта — sup|a| exp(-e^4 z^2/2); это не усечение x-источника. A_tau непрерывна для s>0. Поэтому она ненулевая на интервале положительной длины при достаточно больших s, и S_W(tau)>=||A_tau||_2^2>0. Норма конечна уже по Bochner-оценке.

Это строгость для каждого tau, не единый положительный floor по всей R. В действительности S_W(tau)->0 при |tau|->infinity по Riemann--Lebesgue и W in L1. `[ABSTRACT][PAPER]`

### 5.3. Одна конкретная последовательность допустимых конечных рядов

Для фиксированного реального tau и целого N>=1 положим
\[
x_{k,N}=k/N^3,\quad -N^4\le k<N^4,
\qquad c_{k,N}=N^{-3}e^{i\tau k/N^3}.
\tag{27}
\]
Это ровно 2N^4 различных реальных узлов. Вложения J не изменяются. Докажем
\[
V[c_N]\longrightarrow\mathscr V(\tau,\tau),\qquad
W[c_N]\longrightarrow S_W(\tau)>0.
\tag{28}
\]
Полные хвосты ограничены (20),(21). На квадрате [-N,N]^2 (27) есть обычная левая Riemann-сумма с mesh N^-3. Ошибка не превосходит 8L_tau/N, если L_tau — сумма глобальных верхних границ модулей двух первых частных производных соответствующего oscillatory integrand.

Такие конечные L_tau существуют **без знака V**. Для V из исходного интеграла и Cauchy--Schwarz:
\[
\sup|\partial_xV|\le
\|f\|_2^2+\|t f'\|_2\|f\|_2+\|f'\|_2\|t f\|_2<\infty;
\]
аналогично для y и для V без производных. При этом |u|<=(|u+d|+|u-d|)/2, так что bound не зависит от x-y. Для W: ||J_x||=1 и sup||J'_x||<infinity следуют из (7), |r'_x|<=1, ограниченных скалярных коэффициентов/их производных и ||j'_r||=||v'_(sigma,r)||=1. Все эти Hilbert-производные следуют из C''(0)=-1 либо прямо из (8).

Наконец sqrt(D) и её производная ограничены. На компакте это следует из D>0. При |x|>=15 используем именно полный S2 (26):
D(x)>=|x| f(x)^2(1-3/(2a_|x|))^2/(2a_|x|).
Вместе с |(sqrt D)'|=|x|f(x)^2/sqrt D и (4) это даёт ограниченность и стремление производной к нулю. Таким образом Riemann-error O(N^-1) и оба бесконечных хвоста действительно оплачены. Никакая оценка, растущая неизвестно с размером квадрата, в (28) не спрятана.

Итак, для того же возрастающего ряда узлов
\[
\boxed{\frac{V[c_N]}{W[c_N]}\longrightarrow
\Lambda(\tau):=\frac{F'(\tau)^2-F(\tau)F''(\tau)}{S_W(\tau)}.}
\tag{29}
\]
Деление допустимо: W[c_N]>0 уже при каждом N по §3, а предельный знаменатель строго положителен. `[COFINAL_FAMILY][PAPER]`

## 6. Что RF дополнительно потребовал бы от xi

Одноузловой тест сначала требует 0<delta<=1, поскольку W(x,x)=V(x,x)=D(x)>0. Если существовала бы такая delta из запроса, (28) давало бы
\[
\boxed{F'(\tau)^2-F(\tau)F''(\tau)\ge\delta S_W(\tau)>0
\quad\text{для каждого }\tau\in\mathbb R.}
\tag{30}
\]
Следовательно
\[
\delta\le\inf_{\tau\in\mathbb R}\Lambda(\tau).
\tag{31}
\]
Знак и нижняя граница этого infimum для фактической theta **не получены**. Никакая численная выборка tau не подставляется вместо квантора.

Если бы был предоставлен вещественный кратный нуль gamma, то F(gamma)=F'(gamma)=0. Формулы (25),(29) дали бы V[c_N]/W[c_N]->0 на одном явном семействе (27). Это исключило бы **каждую** положительную delta, даже если все V[c_N] оставались неотрицательными. При RF такой gamma невозможен.

Кроме того, RF и независимо доказанное W>=0 дали бы V>=0 на всех конечных комплексных рядах. Принятый S4 Theorem T затем дал бы RH. Все нули F тогда вещественны; предыдущее рассуждение делает их простыми. Получено точное условное следствие
\[
\boxed{\text{RF}\ \Longrightarrow\ \text{RH и простота всех нетривиальных нулей xi}.}
\tag{32}
\]
**Не доказаны ни RF, ни RH, ни простота.** Наличие кратного нуля не предполагается. Это не KILL. Утверждение, что RF необходимо для исходного полного знака именно нашей theta, также не установлено: consumer S4 не требует доказанной простоты. Нельзя автоматически сделать эту более сильную coercivity обязательной для всего маршрута.

В (27) gamma может появиться только в **условном свидетеле опровержения**, если кратный нуль был бы независимо предоставлен. Он не использован для определения J или source-параметров. Фактических вычислений нулей/их производных не было. `[ABSTRACT][CONDITIONAL]`

## 7. Точный полный остаток и первый неоплаченный переход

Для исходного конечного ряда z зададим на t>=0
\[
P_z(t)=\sum_i z_i f(t+x_i),\qquad
Q_z(t)=\sum_i z_i(t+x_i)f(t+x_i).
\]
Оба принадлежат L2 по (4). Полное исходное равенство:
\[
\boxed{V[z]=2\Re\int_0^\infty\overline{P_z(t)}Q_z(t)dt.}
\tag{33}
\]
Все комплексные коэффициенты, центральные и смешанные члены сохранены. Подстановка (11) даёт первый неоплаченный источник RF в совершенно определённом виде:
\[
\boxed{2\Re\langle P_z,Q_z\rangle\ \ge\
\frac{\delta}{2\pi}\int\mu\left[
(1+\mu/4)|P_s|^2+(1-\mu/4)|P_a|^2+|R_+|^2+|R_-|^2\right],}
\tag{34}
\]
**с одной delta>0 для всех n, всех реальных x_i и всех комплексных z_i**. P_s,P_a,R_+,R_- в (34) — точно (10), вычисленные из того же ряда z, не независимо выбираемые функции.

Эквивалентно, для полного остатка Ehat=V-W,
\[
\widehat E[z]+(1-\delta)W[z]
=\frac12\left(\|P_z+Q_z\|_2^2-\|P_z-Q_z\|_2^2\right)-\delta W[z].
\tag{35}
\]
Ни положительная норма (11), ни полный BP2 не дали нижней оценки левой разности в (35). Cauchy--Schwarz даёт верхнюю абсолютную оценку, не (34). **Называть (34) новой доказанной леммой означало бы NO_PROGRESS_TAUTOLOGY.** Здесь она названа только как точный неоплаченный переход.

Даже отдельное доказательство скалярного (30) не закрыло бы (34). Для полного переноса в Fourier-координатах требуется PSD всех матриц
\[
[\mathscr V(\lambda_i,\lambda_j)-\delta\mathscr W(\lambda_i,\lambda_j)]_{i,j},
\quad \mathscr W(\lambda,\mu)=\iint e^{-i\lambda x}W(x,y)e^{i\mu y}dxdy.
\tag{36}
\]
Все mixed Fourier entries здесь существуют по (19),(21). Ни знака этой матрицы, ни uniform lower bound, ни отрицательного полного V-свидетеля в настоящем ответе нет.

## 8. Проверка сильнейших возражений и границы

**«S_W>0, значит RF опровергнут?»** Нет. Требуется реальный нуль числителя в (30), либо последовательность с неположительным предельным отношением, либо иное несовместимое следствие. Ни один такой фактический источник не предъявлен.

**«Простота — известное либо бесплатное следствие RH?»** В этом документе такое не предполагается и не утверждается. (32) — дополнительная необходимая гипотеза именно RF, установленная из явной положительности S_W. Она не является опубликованным доказательством простоты.

**«Пределы на двух концах достаточно близки?»** Входные T2/T6/T14 относятся к фиксированным сдвигам и фиксированным конечным матрицам. Семейства (13) и (27) меняют rank или conditioning. Никакой uniformity из фиксированных пределов туда не переносится.

**«У положительного block multiplier есть floor 1-pi/4?»** Да, относительно N_0, не относительно физических коэффициентов и не относительно (33). Формула (13) демонстрирует эту разницу именно для неизменного J.

**«Отрицательный Ehat исключает delta>0?»** Нет. Положительный диагональный резерв (1-delta)W в (35) остаётся. Его нельзя удалить. Даже неуспех delta=1 не исключает меньшую delta.

**«Отказ RF опроверг бы RH?»** Нет: нулевой предельный quotient из-за кратного вещественного нуля совместим с отсутствием отрицательного V. Это отдельная граница достаточного усиления.

Никакого переноса только внешней области на весь источник не заявлено. Все вновь доказанные формулы действуют на всей R, но **полного знака** они не дают. `[ABSTRACT][PAPER]`

## 9. Consumer-first ledger, две репрезентации и остановка

| Поле K8A | Значение |
|---|---|
| DOWNSTREAM_CONSUMER | S4 Theorem T, затем названный published Weil criterion |
| ACTUAL_CONSUMER_REQUIREMENT | V[x_1,...,x_n]>=0 для всех n и всех комплексных рядов |
| ORIGINAL_REQUESTED_OBJECT | RF: V>=delta W, одна delta>0, J строго T12 |
| ORIGINAL_OBJECT_IS | UNKNOWN как необходимое условие для actual source; достаточно, но необходимость не доказана |
| KNOWN_WEAKER_INTERFACES | непосредственно V>=0; точный иной положительный decomposition с полным independently-signed остатком; каждое такое Z обязано дать именно all-node V>=0 |
| FAILURE_TYPE | NO_DERIVATION |
| EPISTEMIC_STATUS | RESEARCH_DEBT, не MATHEMATICALLY_DEAD |
| NOVELTY_AXIS | явный all-rank Fourier-дискриминатор для данного J и дополнительная условная простота; общей библиографической новизны не заявлено |
| REOPEN_TRIGGER | независимый uniform bound (34), либо полный источник для inf Lambda<=0 / отрицательного relative row |
| KILL_SCOPE | NONE |

Две пригодные репрезентации **того же J**, не два новых семейства:

- **R1: Fourier plane-wave / divided-kernel test**, (23)--(31). Kill-power estimate 9/10, derivation cost 3/10. Может строго исключить всякую delta через quotient->0; не может доказать RF по одному диагональному тесту. Нынешний знак inf Lambda не вычислен.
- **R2: coupled four-channel source remainder**, (10)--(12),(33)--(36). Kill/pass-power estimate 10/10, source-bound cost 9/10. Сохраняет все ranks и phases; требует независимого источника нижней оценки, которого здесь нет.

Оценки стоимости — качественные исследовательские оценки, не результаты измерения и не сроки. Обе репрезентации перечислены для последующего выбора владельца; новая кампания и второй J не запускаются.

**DISCRIMINATOR при нуль-совместимом результате:** сертифицированные upper bounds для V[c_N]/W[c_N] с положительной нижней границей знаменателя и верхней огибающей, стремящейся к нулю. Для фиксированного tau это ровно (29); кратный вещественный нуль — достаточный условный пример. Для coalescent rows нужны полные jet upper/lower budgets в (13), а не нули округлённого определителя. Числа, согласующиеся с нулём при данной точности, отказ RF не удостоверяют.

Одна директива CODEX: независимо проверить §5, прежде всего знак и нормировку (23), строгую w_+-компоненту (26) и весь finite-node предел (28), затем классифицировать ответ только как `ACCEPT_NECESSARY_RF_FOURIER_AND_SIMPLICITY_CONDITION_ONLY` либо назвать первый неверный шаг. Appendix A воспроизвести без изменения исходника. Не повышать RF/IC/ODD2/RH, не открывать новый J и не менять очередь/реестры. Полный source-sign bound (34) остаётся на стороне следующего решения владельца, не скрытым поручением автоматически доказать RH.

## 10. Closeout и регистрация

Регистрация перед точной алгеброй сохранена в Appendix B. Первые 1026 bytes имели SHA-256 `80b87b3b15108656fd9e8d319a4e776770033b190d35ad7058a4b00a9c41a162`. Перед отдельным Fourier-тестом добавлена P5; полный файл 1519 bytes, SHA-256 `59ac4cb16e81d6902c934adfa29a0df1ac791b58538e5212fa79a4d9096597af`. Старые ставки не исправлялись.

| Prediction | Fate |
|---|---|
| P1: finite-node и all-order jet strictness carrier, без общего coefficient-floor | CONFIRMED_BY_PAPER_DERIVATION, §§3--4; independent acceptance pending |
| P2: Gamma_11=3/20 и соответствующий первый относительный предел | CONFIRMED_BY_EXACT_ALGEBRA_AND_PAPER; исходный числитель не вычислялся |
| P3: epsilon^(2m) carrier energy для любого фиксированного m | CONFIRMED_BY_PAPER; конечный код orders1--8 — только calibration |
| P4: полный source lower bound | UNRESOLVED; ни предсказание истины, ни завершённая проверка RF |
| P5: S_W(tau)>0 и conditional simplicity under RF | CONFIRMED_BY_PAPER_DERIVATION; существование кратного xi-нуля не проверялось и не утверждается |

Что стало точнее: у требуемого RF появился конкретный all-rank Fourier quotient и доказанное дополнительное следствие о кратности. Что убито: никакой actual RF и никакое source-семейство. Что не повторять: заключение из entrywise errors, совпадения диагоналей или fixed-rank end limits о нижней относительной границе.

Исторический source-sign no-delta: **5 -> 6 после независимого учёта этого одного опыта**, без сброса за carrier algebra или условное (32). Это третья construction attempt после возобновления владельцем (Villain, Brownian, Twochannel). Machine state не изменяется. Следующий опыт не запускается автоматически.

Memory entry: fixed T12 survived admissibility and two-end tests; the requested all-complex lower bound remains unpaid; its Fourier consequence forces a strictly positive Laguerre quotient and, conditionally on RF, simple xi zeros. Preserve the distinction between source sign and strict domination of this auxiliary carrier.

Ни одного theta-evaluation, quadrature, root computation, matrix sweep или Lean run не было. Арифметический код ниже вычисляет только коэффициенты **заданного** carrier, а не source/Hankel matrices. Он не является сертификатом (RF).

В GitHub публикуется только этот новый Markdown. Нет Lean-source, поэтому Lean build/axiom handoff не имитируется. Обычный scoped commit должен сохранить текущую родительскую ветку; итоговые commit SHA и точный путь возвращаются в чат. Ветки rh_clean, очередь, runtime и чужие документы не меняются.

## Appendix A. Исполненная точная алгебра

Команда: `python /mnt/data/twochannel/check_carrier.py`. Для независимого запуска сохрани блок как `check_carrier.py` и выполни `python check_carrier.py`. Имена входных параметров: N=4 — только полный Taylor degree carrier; x,y — формальные переменные. Это не cutoff theta и не размер source Hankel.

```python
"""Exact algebraic calibration of the fixed T12/T13 carrier; no theta values."""
from fractions import Fraction as Q
from math import factorial, comb

N = 4  # Total Taylor degree needed for the mixed (2,2) derivative.

def clean(a):
    return {ij: Q(v) for ij, v in a.items() if v and sum(ij) <= N}

def add(a, b):
    c = dict(a)
    for ij, v in b.items():
        c[ij] = c.get(ij, Q(0)) + v
    return clean(c)

def scale(a, q):
    return clean({ij: v * q for ij, v in a.items()})

def mul(a, b):
    c = {}
    for (i, j), v in a.items():
        for (k, l), w in b.items():
            if i + j + k + l <= N:
                ij = (i + k, j + l)
                c[ij] = c.get(ij, Q(0)) + v * w
    return clean(c)

ONE = {(0, 0): Q(1)}
X = {(1, 0): Q(1)}
Y = {(0, 1): Q(1)}

def power(a, n):
    out = ONE
    for _ in range(n):
        out = mul(out, a)
    return out

def binomial_power(a, q):
    assert a.get((0, 0), 0) == 1
    u = add(a, scale(ONE, -1))
    out, term, coeff = dict(ONE), dict(ONE), Q(1)
    for k in range(1, N + 1):
        term = mul(term, u)
        coeff *= (q - k + 1) / k
        out = add(out, scale(term, coeff))
    return out

def cosh0(a):
    assert a.get((0, 0), 0) == 0
    out = dict(ONE)
    for k in range(2, N + 1, 2):
        out = add(out, scale(power(a, k), Q(1, factorial(k))))
    return out

def radius(a):
    return scale(binomial_power(add(ONE, scale(mul(a, a), Q(1, 4))), Q(1, 2)), 2)

rx, ry = radius(X), radius(Y)
brx = binomial_power(add(rx, scale(ONE, -1)), Q(1, 2))
bry = binomial_power(add(ry, scale(ONE, -1)), Q(1, 2))

def denominator_factor(r, x):
    z = scale(add(mul(r, cosh0(x)), scale(ONE, Q(1, 2))), Q(2, 5))
    return binomial_power(z, Q(-1, 2))

gx, gy = denominator_factor(rx, X), denominator_factor(ry, Y)
z = add(rx, scale(ry, -1))
C = binomial_power(cosh0(z), Q(-1))
# z has valuation 2, so T(z)=z/sinh(z)=1-z^2/6 through total degree 4.
T = add(ONE, scale(mul(z, z), Q(-1, 6)))
term1 = mul(mul(add(ONE, mul(brx, bry)), cosh0(scale(add(X, Y), Q(1, 2)))), C)
term2 = scale(mul(cosh0(scale(add(X, scale(Y, -1)), Q(1, 2))), T), Q(1, 2))
G = scale(mul(mul(gx, gy), add(term1, term2)), Q(2, 5))

def derivative(i, j):
    return G.get((i, j), Q(0)) * factorial(i) * factorial(j)

assert derivative(0, 0) == 1
assert derivative(1, 1) == Q(3, 20)
assert derivative(2, 0) == -Q(3, 20)
assert derivative(2, 2) > Q(9, 400)
print('CARRIER_G11=' + str(derivative(1, 1)))
print('CARRIER_G20=' + str(derivative(2, 0)))
print('CARRIER_G22=' + str(derivative(2, 2)))
print('EVEN_SCHUR=' + str(derivative(2, 2) - Q(9, 400)))
# Unit diagonal and reflection are checked as exact polynomial identities.
diagonal = {}
for (i, j), value in G.items():
    diagonal[i + j] = diagonal.get(i + j, Q(0)) + value
assert diagonal[0] == 1 and all(v == 0 for n, v in diagonal.items() if n)
assert all((i + j) % 2 == 0 for i, j in G)
print('UNIT_DIAGONAL_AND_REFLECTION=PASS_TO_DEGREE_4')
for m in range(1, 9):
    for k in range(m + 1):
        s = sum(Q((-1)**(m-j) * comb(m, j)) * Q(j, 1)**k for j in range(m + 1))
        assert s == (factorial(m) if k == m else 0)
print('FINITE_DIFFERENCE_CALIBRATION_ORDERS_1_TO_8=PASS')
# A rank-one positive carrier plus arbitrarily small entrywise error does not
# certify a relative lower bound. This is a tool plant, not another theta test.
for eps in [Q(1, 10), Q(1, 1000)]:
    residual_on_difference = -2 * eps
    assert residual_on_difference < 0
print('PLANTED_POINTWISE_TO_RELATIVE_FALLACY=DETECTED')
print('THETA_EVALUATIONS=0; QUADRATURES=0; NODE_SWEEPS=0; LEAN_RUNS=0')
```

Буквальный stdout:

```text
CARRIER_G11=3/20
CARRIER_G20=-3/20
CARRIER_G22=61/240
EVEN_SCHUR=139/600
UNIT_DIAGONAL_AND_REFLECTION=PASS_TO_DEGREE_4
FINITE_DIFFERENCE_CALIBRATION_ORDERS_1_TO_8=PASS
PLANTED_POINTWISE_TO_RELATIVE_FALLACY=DETECTED
THETA_EVALUATIONS=0; QUADRATURES=0; NODE_SWEEPS=0; LEAN_RUNS=0
```

Контроль последней строки о pointwise fallacy: G=[[1,1],[1,1]], E=epsilon*[[0,1],[1,0]], b=(1,-1). Тогда G[b]=0, E[b]=-2epsilon. Это искусственный алгебраический plant, не изменённый источник и не новый кандидат J.

## Appendix B. Буквальная регистрация предсказаний

```text
REQ-2026-09-13-TWOCHANNEL
Candidate fixed: GLOBAL_TWOCHANNEL_J_RELATIVE_DOMINATION, exactly T12/T13.
Registration before any new symbolic or source computation:
P1 (0.98): the independent Laplace part makes every finite Gram matrix
at distinct real nodes strictly positive, and every finite jet Gram matrix
at zero strictly positive. This will not supply a uniform coefficient floor.
P2 (0.95): the carrier's normalized first derivative metric at zero is 3/20;
the centered two-node relative quotient tends to 20*V_11(0,0)/(3*D(0)).
P3 (0.99): for each fixed order m, the same m-th finite-difference row
has carrier energy asymptotic to epsilon^(2m)*G_mm(0,0)>0.
P4 (unresolved target, no prediction of truth): determine whether the
full source bounds the SAME four-channel norm below by a fixed delta>0.
No change of J, theta quadrature, node sweep, polynomial/Hankel sweep,
unknown xi zeros, Cholesky of V, or assumed positivity of V is authorized.
Only exact carrier Taylor coefficients and algebraic calibration will run.

Additional preregistration before the Fourier-family test:
P5 (0.85): the fixed carrier has strictly positive integrated energy on
EVERY real plane wave; the full-source Fourier diagonal is F'^2-F F''.
Consequently RF would imply simplicity of every zero after its accepted
RF=>V>=0=>RH implication. A hypothetical multiple real zero would supply
an explicit increasing-rank family with V[c]/W[c] tending to zero, not
necessarily an actual negative V witness. No multiple xi zero is assumed.
```

## Appendix C. Пересчёт доступных байтов и сопоставление pinned blobs

Команда: `python /mnt/data/twochannel/check_sources.py`. Код проверки транспортных байтов не участвует в математическом доказательстве. Переменные ROOT и WORK обозначают корень runtime и рабочую папку соответственно; для другого окружения замени эти два пути на папки с теми же исходными файлами. Например, `ROOT=Path("/tmp/source_bundle")`, `WORK=ROOT/"twochannel"`. Имена файлов внутри папок остаются буквальными. R и S1 восстановлены из полного UTF-8 вывода GitHub; S4/S5 извлекаются без текстовой правки из ранее приложенных фреймов и сверяются с текущими pinned blobs. S2/S3 не объявляются прошедшими этот локальный replay.

```python
"""Verify used local source bytes against pinned remote Git blob identifiers."""
from pathlib import Path
import hashlib

ROOT = Path('/mnt/data')
WORK = ROOT / 'twochannel'

def frame(packet, source_path, size):
    lines = packet.read_bytes().splitlines(keepends=True)
    prefix = ('===== FILE ' + source_path + ' BYTES ').encode()
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix)) + 1
    out = bytearray()
    while len(out) < size:
        line = lines[i]
        if not line.startswith(b'| '):
            raise ValueError('Invalid framed source line')
        out.extend(line[2:])
        i += 1
    if len(out) != size:
        raise ValueError('Frame byte count mismatch')
    return bytes(out)

def check(key, data, count, lf, sha256, blob):
    actual_sha = hashlib.sha256(data).hexdigest()
    actual_blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert (len(data), data.count(b'\n'), data.count(b'\r'), data.endswith(b'\n')) == (count, lf, 0, True)
    assert (actual_sha, actual_blob) == (sha256, blob)
    print(f'{key}: bytes={count}; LF={lf}; finalLF=true; CR=0; SHA256={actual_sha}; blob={actual_blob}; MATCH')

check('R', (WORK/'request.txt').read_bytes(),10054,127,
      '4d2193b53ba35111a7bf07f54541c6d2edc21815d2b3760d284fcbf17eb7d4d0',
      'eea7ebf0bd637925d065bd443100d11e83ad83ad')
check('S1',(WORK/'bridge.md').read_bytes(),11996,245,
      'e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908',
      '51ef75574931fde124c94a5a9df2d623460d9538')
s4=frame(ROOT/'PROSHKA_REQUEST_GOAL058_ODDINFINITY_2026-09-12.txt',
         'docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md',15303)
check('S4',s4,15303,335,
      '1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282',
      'b8b5a1a8739c946f75340f3115616d6f9ba5b40e')
s5=frame(ROOT/'PROSHKA_REQUEST_GOAL058_ODD2COMPACT_2026-09-12.txt',
         'docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md',37796)
check('S5',s5,37796,467,
      '14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc',
      'de9578084446baecfbb2a316d7bda3da817c8c01')
print('S2,S3: pinned GitHub blobs read; SHA256 values inherited, not locally replayed')
```

Буквальный stdout:

```text
R: bytes=10054; LF=127; finalLF=true; CR=0; SHA256=4d2193b53ba35111a7bf07f54541c6d2edc21815d2b3760d284fcbf17eb7d4d0; blob=eea7ebf0bd637925d065bd443100d11e83ad83ad; MATCH
S1: bytes=11996; LF=245; finalLF=true; CR=0; SHA256=e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908; blob=51ef75574931fde124c94a5a9df2d623460d9538; MATCH
S4: bytes=15303; LF=335; finalLF=true; CR=0; SHA256=1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282; blob=b8b5a1a8739c946f75340f3115616d6f9ba5b40e; MATCH
S5: bytes=37796; LF=467; finalLF=true; CR=0; SHA256=14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc; blob=de9578084446baecfbb2a316d7bda3da817c8c01; MATCH
S2,S3: pinned GitHub blobs read; SHA256 values inherited, not locally replayed
```
