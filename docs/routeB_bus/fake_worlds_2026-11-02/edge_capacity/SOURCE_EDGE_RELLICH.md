# STATUS: TRY_EDGE_LAW_RELLICH_MOVING_PROJECTOR

```yaml
OPERATIVE_CLASS: TRY_EDGE_LAW_RELLICH_MOVING_PROJECTOR
REQUEST_ID: EDGE_LAW_RELLICH_v1
DATE: 2026-11-02
TASK_MODE: DIRECT_OWNER_SOURCE_PINNED_MATHEMATICAL_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_BASE: 05c177921c8c3f88eef958875f949f0dab691d94
SOURCE_LEDGER_COMMIT: 8acecc1574740c5163c2a4e8ef75049f6df84313
SOURCE_VIRIAL_COMMIT: 9710787485148cb797bed49fd8d4d8d033b47e99
SOURCE_DILATION_COMMIT: d8983a2a3b05ef0368fc6f284bef1fd22b4cd50c
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: EXACT_FINITE_COMPRESSION_DILATION_IDENTITY_WITH_ALL_BOUNDARY_AND_PROJECTOR_TERMS
Q_A: EXACT_SOURCE_BOUNDARY_FUNCTIONALS_GIVEN_NO_UNIVERSAL_R_IDENTIFIED
Q_B: LOWER_ZERO_HEAD_EDGE_CROSS_AND_MOVING_CONSTRAINT_TERMS_RETAINED
Q_C: NO_COFINAL_SELECTED_VECTOR_VOLUME_SIGN_PROVED
NEW_COFINAL_SOURCE_SIGN: NONE
EDGE_LAW_R_NEAR_4: NEITHER_PROVED_NOR_REFUTED_FOR_SELECTED_ZETA_FAMILY
LOCAL_PARAMETER: L_tau=L_exp_tau_WITH_N_FIXED
DISCRETE_N_EQ_m_SEQUENCE_DERIVATIVE: NOT_ASSERTED
PRIME_POWER_THRESHOLD: EXPLICIT_ONE_SIDED_RANK_ONE_KICK
ZERO_CUTOFF_THRESHOLD: CONSTANT_ACTIVE_SET_REQUIRED_LOCALLY
EIGENVALUE_SIMPLICITY: NOT_ASSUMED_SILENTLY_DEGENERATE_SLOPES_GIVEN
MOVING_PROJECTOR_CORRECTION: EXPLICIT_AND_TESTED
LOG_LAPLACIAN_NORMALIZED_TRACE_IMPORT: NOT_USED
RH_ASSUMED: false
RH_PROVED: false
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: EXACT_FINITE_FAMILY_VARIATIONAL_TRANSFER_NOT_GLOBAL_EDGE_LAW
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
SCOPE: FINITE_CELL
VERIFIER: PAPER
EXACT_ALGEBRA_GROUPS: 7
NUMERICAL_CONTROL: ORIGINAL_m8_FULL_SOURCE_AND_TRUE_LOW_ZERO_COMPLEMENT
NUMERICAL_DPS: [40, 55]
INTERVAL_CERTIFICATE: false
NEW_LARGE_m_SPECTRA: false
INDEPENDENT_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
REPOSITORY_WRITTEN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. Выведено точное дилатационное тождество для конечного сжатия на исходное J-perp. В нём есть три существенные части: вариация полной арифметической формы, граничный член и движение evaluation-проектора. Для простой ветви нижнего уровня всё записано скалярно; для кратного уровня дана матрица односторонних скоростей. Граница при входе prime-power атома оплачена отдельно.

Универсальный коэффициент R около 4 не выведен. Точное тождество энергии содержит нижний нулевой head, endpoint-tail, его перекрёстный член и остаточную форму. На moving cutoff нельзя выбросить ни один из них. Отсутствие доказательства этого закона не является его опровержением для выбранных минимизаторов.

## 0. Короткий ответ на (a), (b), (c)

**(a)** У дилатации и у энергии разные граничные коэффициенты. Естественная source-граница дилатации есть **линейный по следу** функционал `-2 f(b) B_L[f]`. Он не является числом, умноженным только на f(b)^2. После явно выбранного постоянного lifting следа можно выделить scalar `-2 W_L f(b)^2`, но остаётся гранично-объёмный смешанный член. Для энергии точный scalar endpoint-tail coefficient `C_T` дан в (5.5)–(5.7). Универсальное отождествление этих величин с `R log(T)/(pi T)` не выведено. Для energy-coefficient C_T такое равенство требует дополнительного зануления суммы H_T+X_T+V_T; это не утверждается опровергнутым для каждой отдельной ячейки. Фазово усреднённая модель вещественного дальнего хвоста имеет ведущий коэффициент 2, а не 4; усреднение не используется как теорема.

**(b)** Нижние нули находятся в `H_T[f]` в (5.4), а их движение в координатах carrier — в `dot E` и `dot Pi`. Перекрёстный endpoint/remainder член находится в `X_T[f]`; он не имеет фиксированного знака. На J-perp нижний head НЕ зануляется: это было бы свойством J, а не его ортогонального дополнения.

**(c)** Не доказан знак объёмного члена на выбранной кофинальной семье. Общий source-вириальный volume функционал действительно имеет оба знака уже на гладких компактных чётных тестах (§7.2). Это не контрпример к специальному закону выбранных finite-CCM минимумов. Точное препятствие состоит в отсутствии **совместного, относительного к f(b)^2 log(T)/T** контроля head/cross/remainder и в неоплаченной нормированной скорости evaluation-проектора. Малость абсолютной quiet residual этого не даёт.

## 1. Источники, объект и область заявления

### 1.1. Что прочитано

- S1. `docs/routeB_bus/fake_worlds_2026-11-02/edge_law/RESULT.md`, base `05c177921c8c3f88eef958875f949f0dab691d94`, blob `f970d06bb69eab07cc09d19ad39da77cebe03066`: весь отчёт.
- S2. `edge_law/zero_side/FORMULAS.md`, тот же base, blob `34c264282cd92b4508adbca586f9d951968249c2`: весь файл, включая complex-pair и far-tail guards.
- S3. `fake_worlds_2026-11-02/ledger_diff/SOURCE_CONVENTIONS.md`, pin `8acecc1`, blob `ff1fbc285b5529fd5fd66f5bff5f83e3974e40ee`: весь файл. `ledger.csv` прочитан частично для колонок и соглашений; все его большие числовые строки заново не пересчитывались.
- S4. `proshka/PROSHKA_VERDICT_CCM_POHOZAEV_2026-11-02.md`, pin `d8983a2a3b05ef0368fc6f284bef1fd22b4cd50c`, blob `12780e227a4dc2e6e1a85c60bdad687c1f266494`: основания boundary guard и исходниковая дилатационная вариация §§1–5.
- S5. `proshka/PROSHKA_VERDICT_CCM_VIRIAL_CUTOFF_2026-11-02.md`, pin `9710787485148cb797bed49fd8d4d8d033b47e99`, blob `10713267d1719ba81e89592800f4dd681821d0fd`: глобальный h-вириал и точные конечные вариации §§1–3. Глобальная радикальность h не переносится на произвольный complement-minimizer.
- P1. Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, HTML §3, (3.2)–(3.20): исходная форма и нормировки.
- P2. arXiv:2411.15985v2: первичная страница подтверждает отзыв 26.04.2025 именно из-за существенной ошибки в Pohozaev proof. Отозванная теорема не импортируется. Отдельный неприкреплённый файл с идентификатором `KILL 8` не подменялся выдуманным источником; математическое boundary-ограничение взято из закреплённого S4 и первичной записи отзыва.

Данные S1 — floating diagnostics, не interval certificates. Три новых zeta ratios равны приблизительно 3.91936, 4.52548, 4.14317; последний source-minus-prefix — баланс исходной формы, не независимо посчитанный бесконечный хвост. Отсюда не делается кофинального вывода.

### 1.2. Точное конечное семейство

**[FINITE_CELL | PAPER; definitions.]** При заданном исходном m фиксируем N=m и L=log m, b=L/2. Используем вещественный ортонормированный базис

\[
\phi_{n,L}(x)=\frac{d_n(-1)^n}{\sqrt L}\cos(2\pi nx/L)\mathbf1_{[-b,b]}(x),
\quad d_0=1,\quad d_n=\sqrt2\ (n>0),\quad 0\le n\le N.
\tag{1.1}
\]

Здесь `A_N(L)` — **полная исходная** форма в этом базисе. При начальном L=log m,N=m это ровно A_m. В локальной дилатационной вариации N держится фиксированным:

\[
L_\tau=e^\tau L,\qquad
(\mathscr U_\tau f)(x)=e^{-\tau/2}f(e^{-\tau}x),\qquad
\mathscr U_\tau\phi_{n,L}=\phi_{n,L_\tau}.
\tag{1.2}
\]

Это локальное продолжение для вычисления производной, НЕ замена исходного расписания. Производная последовательности, в которой одновременно скачет целое N=m, не объявляется существующей.

Пусть E_tau содержит все активные value-условия ниже T_tau, в физических координатах carrier. Например T_tau=kappa*2pi N/L_tau. На локальном интервале нет пересечения нулём cutoff и ранг постоянен. Точки нулей остаются фактическими комплексными точками; двигаются базис и его значения, не нули ζ. При комплексной четверке можно использовать две вещественные строки Re/Im. Точные повторы агрегируются; при необходимости выбирается полный независимый набор строк для ТОГО ЖЕ kernel. Значения кратностей остаются в попарной метрике head-формы, а не создают независимые value-условия.

\[
J_\tau=\ker E_\tau,\quad S_\tau=J_\tau^\perp,\quad
\Pi_\tau=E_\tau^*(E_\tau E_\tau^*)^{-1}E_\tau.
\tag{1.3}
\]

Формула с обратной относится к выбранному full-row-rank представлению. При лишних строках можно эквивалентно использовать постоянного ранга Moore–Penrose projector, но не менять head-метрику без exact crosswalk.

Пусть c единичный coefficient-vector выбранного минимизатора на S=S_0:

\[
f=\sum c_n\phi_{n,L},\quad \Pi c=c,\quad
\Pi Ac=\lambda c,\quad r=(I-\Pi)Ac\in J.
\tag{1.4}
\]

В общем случае `Ac != lambda c`. Это eigenvector сжатия, не полного carrier. Для реальных исходных матриц нижний eigenvector можно выбрать вещественным; кратность не исключается.

### Claim ledger

| Claim | Scope | Verifier | Boundary |
|---|---|---|---|
| (2.2)–(2.6) полный source-вириал | FINITE_CELL | PAPER | finite N, smooth interior, обе односторонние границы |
| (3.2)–(3.7) moving-compression derivative | FINITE_CELL | PAPER | постоянный ранг и активный zero set; кратность обработана |
| (4.2)–(4.6) boundary/volume split | FINITE_CELL | PAPER | нет знака selected-volume |
| (5.4)–(5.7) полный head/edge/cross/volume | FINITE_CELL | PAPER | все комплексные нули и кратности |
| coefficient 2 in (6.2) | ABSTRACT | CONDITIONAL | real-tail plus phase-averaged density model only |
| общая двузнаковость volume §7.2 | ABSTRACT | PAPER | гладкие чётные full-window тесты, не actual selected minima |
| observed R range | FINITE_CELL | CONDITIONAL | унаследованная численная диагностика |
| cofinal EDGE_LAW and positive complement floor | COFINAL_FAMILY | CONDITIONAL | NOT_PROVED |

## 2. Полный source-вириал для конечного carrier

Положим

\[
Q_f(s)=2\int_{-b}^{b-s}f(x)f(x+s)\,dx\quad(0\le s\le L),
\quad Q_f(s)=0\ (s\ge L),
\]
\[
j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad m_j(s)=(sj(s))',
\quad a_n=\log n,\quad w_n=\frac{\Lambda(n)}{\sqrt n},
\]
\[
p(x)=\sqrt2\cosh(x/2),\quad q(x)=\sqrt2\sinh(x/2),
\quad p_f=\langle p,f\rangle,\quad t_f=\langle xq,f\rangle.
\]

Исходная чётная форма:

\[
\mathfrak k[f]=-c_*\|f\|^2+
\int_0^\infty j(s)(2\|f\|^2-Q_f(s))\,ds
-\sum_{n\ge2}w_nQ_f(a_n)+p_f^2,
\quad c_*=\gamma_E+\log(8\pi)+\pi/2.
\tag{2.1}
\]

Все степени простых остаются. Нечётный полюс равен нулю именно по чётности на всём variation path. Нельзя отдельно добавлять полюс к нулевой стороне: он уже включён в полную явную формулу.

### Теорема 1. Регулярная скорость и крайний атом

**[FINITE_CELL | PAPER.]** Вне prime-power порогов:

\[
\boxed{
\Phi_L[f]:=\left.\frac d{d\tau}\mathfrak k[\mathscr U_\tau f]\right|_0
=-\|f\|^2-\int_0^L m_j(s)Q_f(s)\,ds
+p_f^2+p_ft_f+
\sum_{a_n<L}w_na_nQ_f'(a_n).
}
\tag{2.2}
\]

Эквивалентно,

\[
\Phi_L[f]=\int_0^L sj(s)Q_f'(s)\,ds
+\sum_{a_n<L}w_na_nQ_f'(a_n)+p_f^2+p_ft_f.
\tag{2.3}
\]

Если L=log n0, то для расширения окна и его сжатия:

\[
\boxed{\Phi_L^+[f]=\Phi_L^-[f]-2w_{n_0}L f(b)^2,}
\tag{2.4}
\]

где Phi^- — правая часть (2.2) со строгим a_n<L. Если Lambda(n0)=0, разницы нет.

**Доказательство.** Из унитарной нормировки Q_{U_tau f}(s)=Q_f(e^{-tau}s). Для архимедовой части заменяем s=e^tau u до дифференцирования. Комбинация `j(u)+u j'(u)` интегрируема: сингулярность 1/(2u) сокращается, а на бесконечности есть экспоненциальное убывание. Производная равна `int m_j(2||f||²-Q_f)`. Так как `int_0^infinity m_j=-1/2`, получаем первый и второй члены (2.2). Это не предполагает производной нулевого продолжения в L2.

Для конечного cosine-carrier Q_f гладка на (0,L), поэтому на всех СТАРЫХ внутренних атомах производные существуют. Конечность локально активной prime-суммы оправдывает её дифференцирование. Pole pairing после замены переменной равен

\[
p_f(\tau)=e^{\tau/2}\int p(e^\tau x)f(x)\,dx,
\quad p_f'(0)=\tfrac12(p_f+t_f),
\]

что даёт p_f²+p_f t_f. Производная постоянного -c_*||f||² нулевая, но этот член остаётся в самой энергии.

При s=L-u, u↓0, непрерывность внутренних следов и чётность дают

\[
Q_f(L-u)=2f(b)^2u+O_f(u^2).
\tag{2.5}
\]

У cosine-профиля f'(±b)=0, поэтому можно даже получить O(u^3), но это не требуется. При tau>0 новый атом имеет u=L(1-e^{-tau})=L tau+O(tau²); при tau<0 корреляция атома тождественно нулевая. Отсюда (2.4). ∎

Поскольку (2.2) квадратична по c, поляризация определяет точные симметричные матрицы dot A^±. Пусть d_b=(d_0,...,d_N)^T/sqrt L, так что f(b)=d_b^T c. Тогда

\[
\boxed{\dot A^+-\dot A^-=-2w_{n_0}L\,d_bd_b^T.}
\tag{2.6}
\]

Это rank-one endpoint kick, а не неизвестный Pohozaev trace.

## 3. Реллих для движущегося сжатия

### Теорема 2. Простой уровень

**[FINITE_CELL | PAPER.]** На smooth постоянного ранга ветви с простым выбранным eigenvalue:

\[
\boxed{
\dot\lambda^\pm=\Phi_L^\pm[f]+2\operatorname{Re}\langle r,\dot\Pi c\rangle.
}
\tag{3.1}
\]

Точка означает d/dtau, то есть L d/dL при указанном локальном продолжении. Вне порогов знаки ± совпадают.

Обозначив W=EE*, получаем полностью явную матрицу

\[
\boxed{
\dot\Pi=(I-\Pi)\dot E^*W^{-1}E+E^*W^{-1}\dot E(I-\Pi),
\qquad
\dot\Pi c=(I-\Pi)\dot E^*W^{-1}Ec.
}
\tag{3.2}
\]

Для complex evaluation row до перехода к Re/Im координатам:

\[
\boxed{
\dot E_{\rho n}=\tfrac12\widehat\phi_{n,L}(z_\rho)
+z_\rho\widehat\phi_{n,L}'(z_\rho).
}
\tag{3.3}
\]

Активные z_rho фиксированы. Производной theta, перемещения самих нулей или предположения RH здесь нет.

**Доказательство.** Для нормированной ветви c_tau in ran Pi_tau:
`dot lambda=<c,dot A c>+2 Re<Ac,dot c>`.
Из (1.4), нормировки и дифференцирования Pi_tau c_tau=c_tau:
`Ac=lambda c+r`, `Re<c,dot c>=0`, `(I-Pi)dot c=dot Pi c`.
Получаем (3.1). Дифференцирование `E* (EE*)^-1 E` даёт (3.2); сингулярные числа или численная SVD не подставляются вместо этой формулы. Дилатационная Fourier-формула `hat(U_tau phi)(z)=e^{tau/2}hat(phi)(e^tau z)` даёт (3.3). ∎

Если Q — изометрический синтез J и delta=||AQ||, то

\[
\|r\|\le\delta,\qquad
\boxed{\left|2\operatorname{Re}\langle r,\dot\Pi c\rangle\right|
\le2\delta\,\|\dot\Pi c\|
\le\frac{2\delta\|\dot E\|}{\sigma_{\min}(E)}.}
\tag{3.4}
\]

Последнее неравенство относится к выбранным raw независимым строкам. Сам projector и его correction не меняются при обратимом row-rescaling, но в производной rescaling нужно учитывать. Малая delta сама по себе не даёт малого correction, тем более малого относительно e² log(T)/T: цена evaluation conditioning не оплачена автоматически.

### Кратность, атомы и смена ранга

Пусть W0 — изометрический синтез всего минимального eigenspace сжатия при tau=0. Тогда матрицы скоростей:

\[
\boxed{
K^\pm=W_0^*\bigl(\dot A^\pm+A\dot\Pi+\dot\Pi A\bigr)W_0.
}
\tag{3.5}
\]

Для нижней огибающей finite-dimensional ветвей:

\[
\boxed{\dot\lambda_+=\lambda_{\min}(K^+),\qquad
\dot\lambda_-=\lambda_{\max}(K^-).}
\tag{3.6}
\]

В простом случае (2.6) даёт прямо

\[
\dot\lambda_+-\dot\lambda_-=-2w_{n_0}Lf(b)^2.
\tag{3.7}
\]

При кратности надо использовать (3.5)–(3.6), а не присваивать обоим направлениям произвольно выбранный один f. Если нуль пересекает T, появляется автоматическая zero-row либо меняется rank, smooth Pi-формула не применяется через событие; считаются односторонние subspaces и их собственные значения. Если меняется N, сравниваются разные finite carriers, а не производная (3.1).

### Почему нельзя написать 0=вириал

Минимальность означает стационарность только по нормированным вариациям ВНУТРИ текущего S. Дилатация меняет окно, carrier functions и S. Даже на постоянном A, для движущейся прямой `(cos tau,sin tau)` и A=[[a,b],[b,d]] производная сжатого уровня при 0 равна 2b, а не нулю.

Кроме того, при ненулевом e=f(b):

\[
\|\mathscr U_\tau f-f\|_2^2=L e^2|\tau|+o(|\tau|).
\tag{3.8}
\]

Нулевое продолжение не имеет L2-дилатационного tangent. Нельзя без boundary layer заменить derivative формы на `2k(f,-f/2-xf')`. Точное уравнение для внутреннего дифференциального выражения имеет вид

\[
\widehat{(-f/2-xf')_{\mathrm{int}}}(z)
=\tfrac12F(z)+zF'(z)-2be\cos(bz).
\tag{3.9}
\]

Именно последний term был бы потерян в naive generator calculation. Подход через correlation и finite matrices его сохраняет.

## 4. Явный гранично-объёмный вид

**[FINITE_CELL | PAPER.]** Положим

\[
e=f(b),\qquad I_f(s)=\int_{-b}^{b-s}f(x)f'_{\mathrm{int}}(x+s)\,dx.
\]

Leibniz даёт

\[
\boxed{Q_f'(s)=2I_f(s)-2e f(b-s),\qquad0<s<L.}
\tag{4.1}
\]

Определим независимые source-функционалы

\[
\mathcal B_L[f]=\int_0^L sj(s)f(b-s)\,ds+
\sum_{a_n<L}w_na_nf(b-a_n),
\tag{4.2}
\]
\[
\mathcal W_L[f]=2\int_0^L sj(s)I_f(s)\,ds+
2\sum_{a_n<L}w_na_nI_f(a_n)+p_f^2+p_ft_f.
\tag{4.3}
\]

Соединяя (2.3), (3.1), (4.1), получаем запрошенное тождество:

\[
\boxed{
\dot\lambda_-=
\underbrace{-2e\,\mathcal B_L[f]}_{\text{boundary/interior flux}}
+\underbrace{\mathcal W_L[f]}_{\text{full source volume}}
+\underbrace{2\operatorname{Re}\langle r,\dot\Pi c\rangle}_{\text{moving compression}}.
}
\tag{4.4}
\]

При prime-power пороге для правой скорости добавить `-2w_n L e²`. В непороговой точке минус у dot lambda — только обозначение совпадающей скорости.

Никакой singular integral при s=0 не остался: sj имеет конечный предел, I_f и f(b-s) ограничены. В s=L все профили имеют односторонние пределы, а prime threshold уже обработан отдельно. Все объёмные и boundary-функционалы вычисляются по ОДНОМУ выбранному f, не по отдельным минимумам компонентов.

### Можно ли выделить коэффициент только при e²?

Можно, если явно выбрать lifting следа. Возьмём chi_L=1_{[-b,b]}, g=f-e chi_L, так что g(±b)=0. Тогда

\[
W_L=\int_0^L sj(s)\,ds+\sum_{a_n<L}w_na_n,
\quad\mathcal B_L[f]=eW_L+\mathcal B_L[g],
\]
\[
\boxed{
\dot\lambda_-=-2W_Le^2+
\bigl(\mathcal W_L[f]-2e\mathcal B_L[g]\bigr)
+2\operatorname{Re}\langle r,\dot\Pi c\rangle.
}
\tag{4.5}
\]

Таким образом, для ЭТОГО lifting

\[
\boxed{\Gamma^{\rm dil}_L=-2W_L,\qquad
\Gamma^{\rm dil,+}_L=\Gamma^{\rm dil,-}_L-2w_nL\ (L=a_n).}
\tag{4.6}
\]

Это явный отрицательный scalar для ζ, поскольку все w_n>=0. Он не равен положительному R log(T)/(pi T) из измерения энергии. Противоречия нет: речь о скорости, а не уровне, и mixed term не исчез. С другим lifting scalar перераспределяется вместе с mixed volume; инвариантен полный (4.4), а не произвольно выделенный scalar.

### Возврат к Abel-ledger, без смешения двух boundary terms

Пусть `a_z(s)=exp(-s/2)[psi(exp s)-(exp s-1)]`. Тогда точно, как в S3,

\[
S_m[f]=\int_0^L a_z(s)Q_f(s)/2\,ds
-2\int_0^L a_z(s)I_f(s)\,ds
+2e\int_0^L a_z(s)f(b-s)\,ds.
\tag{4.7}
\]

Это energy-ledger, не dot lambda. Его последний член имеет знак **плюс в S**, а в `lambda=H_++4-c_*-S` — минус. Его kernel a_z отличается от sj и атомов a_n w_n в вириале. Не следует идентифицировать эти два boundary columns. E0(1)=0, Q(L)=0 и все prime powers оплачивают оба Abel endpoints.

## 5. Точная энергия: где нижние нули и отрицательный cross

### 5.1. Endpoint subtraction не является RH-заменой

**[FINITE_CELL | PAPER.]** Для real even f положим F(z)=hat f(z),

\[
B_L(z)=\frac{2\sin(bz)}z=\widehat\chi_L(z),\qquad
R_f(z)=F(z)-eB_L(z).
\tag{5.1}
\]

Все функции целые. На nonmodal аргументах

\[
R_f(z)=\frac{2\sin(bz)}{\sqrt L z}
\sum_{n=1}^N\frac{d_nc_n\omega_n^2}{z^2-\omega_n^2}.
\tag{5.2}
\]

У finite cosine-profile f'(±b)=0, поэтому также точно

\[
R_f(z)=-z^{-2}\int_{-b}^b f''_{\mathrm{int}}(x)e^{-izx}\,dx,
\tag{5.3}
\]

с устранимым значением при z=0. Это показывает, какой внутренний derivative content находится в остатке; число ||f''|| не объявляется малым относительно e.

Используем полную source-идентичность по всем completed zeros с multiplicity. На real even f её диагональ равна `sum_rho F(z_rho)^2`, НЕ sum |F(z_rho)|². Симметрии делают сумму вещественной. Для fixed finite carrier она абсолютно сходится, поскольку F=O_m(1/|gamma|) в полосе и N(t)=O(t log t).

При strict head |gamma|<T положим

\[
H_T[f]=\sum_{|\gamma|<T}F(z_\rho)^2,
\quad C_T=\sum_{|\gamma|\ge T}B_L(z_\rho)^2,
\]
\[
X_T[f]=2e\sum_{|\gamma|\ge T}B_L(z_\rho)R_f(z_\rho),
\quad V_T[f]=\sum_{|\gamma|\ge T}R_f(z_\rho)^2.
\]

Тогда

\[
\boxed{\lambda=H_T[f]+e^2C_T+X_T[f]+V_T[f].}
\tag{5.4}
\]

Суммы понимаются симметрично по орбитам, хотя сама energy-сумма здесь абсолютно сходится. При equality |gamma|=T нуль относится к хвосту. При комплексных коэффициентах используется исходное conjugate-reflection pairing вместо real-square notation.

### 5.2. Аналитический scalar C_T через исходную арифметику

Endpoint-tail coefficient не обязательно вычислять отрезанием неизвестного infinite tail. Полная форма на chi_L даёт

\[
\boxed{C_T=\mathfrak k[\chi_L]-
\sum_{|\gamma|<T}\left(\frac{2\sin(bz_\rho)}{z_\rho}\right)^2.}
\tag{5.5}
\]

Здесь первый член полностью явен:

\[
\boxed{
\begin{aligned}
\mathfrak k[\chi_L]={}&-c_*L
+2\int_0^L sj(s)\,ds+2L\int_L^\infty j(s)\,ds\\
&-2\sum_{a_n<L}w_n(L-a_n)
+32\sinh^2(L/4).
\end{aligned}}
\tag{5.6}
\]

Доказательство: ||chi_L||²=L, Q_chi=2(L-s) на [0,L], p_chi=4sqrt2 sinh(L/4). Нет дополнительных полюсов или omitted n=m term. (5.5) — точный analytic coefficient, но он использует actual head evaluations и полный signed source, не только N(T).

Если e!=0, измеренный ratio в точности

\[
\boxed{
R_m=\frac{\pi T}{\log T}C_T+
\frac{\pi T}{e^2\log T}\bigl(H_T[f]+X_T[f]+V_T[f]\bigr).
}
\tag{5.7}
\]

Поэтому вопрос о коэффициенте R нельзя решить вычислением C_T, не оплатив второй член. Если e=0, ratio не определён, но (5.4) остаётся верной. Ненулевой след выбранной кофинальной семьи не следует из существующих конечных значений.

### 5.3. Где head в moving-compression identity

Пишем exact head `A_<T=E_full^* Jcal E_full`; при real critical rows Jcal содержит 2nu, при complex quartet — соответствующий indefinite pair block. E_full здесь хранит всю метрику, даже если для projector был выбран независимый row basis.

На локальном неизменном census Jcal постоянна, и

\[
\langle c,\dot A_{<T}c\rangle
=2\operatorname{Re}\langle E_{\rm full}c,
\mathcal J\dot E_{\rm full}c\rangle.
\tag{5.8}
\]

Это конечная сумма, её дифференцирование законно. Вдобавок head-строки определяют dot Pi. Поскольку head maps S into S,

\[
r=(I-\Pi)R_Tc,
\tag{5.9}
\]

но из этого не следует, что поправка r*dot Pi мала на edge-scale. Head не исчезает: `Ec=0` означало бы c in J; для единичного c in J-perp это невозможно.

### 5.4. Почему бесконечный differentiated zero sum требует отдельного guard

Для finite jump profile F(z)=2e sin(bz)/z+O_f(z^-2) в фиксированной полосе. В fixed-coefficient dilation

\[
\dot F(z)=\tfrac12F(z)+zF'(z).
\]

При e!=0 ведущий derivative содержит 2be cos(bz), то есть имеет порядок O_f(1), а не O_f(1/|z|). Формально продифференцированное слагаемое `2F dot F` имеет лишь O_f(1/|gamma|) envelope, не суммируемый с N(t)=O(t log t). Это не доказывает расходимость actual oscillatory series, но исключает автоматическую dominated-convergence аргументацию из energy-сходимости.

Корректное определение derivative: сначала точная finite difference полной source-формы (как в S5), затем предел. Нулевую версию можно использовать только с явной регуляризацией и доказанным обменом пределов. Нельзя потерять boundary contribution, дифференцируя неравномерный endpoint tail почленно.

## 6. Что означает коэффициент 2 и почему он не доказывает R≈4

На конечном блоке действительных положительных нулей:

\[
2\sum F(\gamma)^2
=8e^2\sum\frac{\sin^2(b\gamma)}{\gamma^2}
+8e\sum\frac{\sin(b\gamma)R_f(\gamma)}\gamma
+2\sum R_f(\gamma)^2.
\tag{6.1}
\]

У cross знак произволен. S1 уже измеряет отрицательный cross и substantial head на тех же selected vectors. Эти наблюдения не опровергают возможный будущий selected-family law, но исключают объяснение таблицы простым удалением head/cross.

**[ABSTRACT | CONDITIONAL: model only.]** Если дополнительно заменить весь релевантный tail вещественными nodes, sin² его средним 1/2, а counting measure — главной плотностью log(t/(2pi))/(2pi), то endpoint часть равна

\[
\boxed{
\frac{2e^2}{\pi T}\bigl(\log(T/(2\pi))+1\bigr).
}
\tag{6.2}
\]

Ведущий коэффициент относительно e² log(T)/(pi T) — 2. Это интегральное вычисление, а НЕ доказанное фазовое усреднение. Полная critical-line tail premise не принимается без RH; и даже при ней moving-family phase error требует самостоятельной оценки.

Для real t>Omega точный remainder bound из S2:

\[
|R_f(t)|\le\frac{2|\sin(bt)|}{t(t^2-\Omega^2)}
\sum_{n=1}^N\frac{|d_nc_n|\omega_n^2}{\sqrt L}.
\tag{6.3}
\]

При T=1.1Omega множитель Omega²/(T²-Omega²)=1/0.21, а не o(1). Более того, оценка (6.3) абсолютная и не делится безопасно на tiny e. Поэтому fixed-f far-tail expansion не даёт uniform relative edge law при m→infinity.

Точный достаточный объект для source lower edge bound с числом a>0:

\[
\boxed{
H_T[f]+X_T[f]+V_T[f]+e^2
\left(C_T-a\frac{\log T}{\pi T}\right)\ge0
}
\tag{6.4}
\]

на actual selected normalized f и неограниченной исходной семье. Это **обязательство**, не доказанный supplier; равенство (5.4) не доказывает знак (6.4).

## 7. Знак объёмной части и точное препятствие

### 7.1. Что нельзя заключать

Положительность Lambda не делает `Q_f'(log n)` или `I_f(log n)` неотрицательными. Reflection-evenness не фиксирует их знак. Билинейная радикальность глобального h даёт Phi[h]=0, но не Phi[f]=0 и не Phi[f-h]>=0. Полная eigenvalue stationary equation также не применима к arbitrary generator или к изменяющемуся S.

Нижние критические нули дают положительную head-форму, но off-line quartet даёт

\[
4\nu\bigl((\operatorname{Re}F(z))^2-(\operatorname{Im}F(z))^2\bigr).
\tag{7.1}
\]

Ту же indefinite metric нужно сохранять в tail. Подмена (7.1) на абсолютные квадраты — именно запрещённая zero-location предпосылка. В DH-данных S1 эти signed contributions измерены; они не являются изменением универсальной boundary-константы. В DH источник меняется на odd gamma kernel, signed b_D(n) и отсутствующий pole, поэтому zeta coefficients нельзя переносить туда неизменёнными.

### 7.2. Строгий отрицательный контроль общего знака volume

**[ABSTRACT | PAPER; source-exact smooth tests, NOT the original N=m selected branch.]** Выберем a=log2 и фиксированное L с a<L<log3. Пусть chi — вещественная чётная неотрицательная C_c^infinity((-L/2,L/2)) функция с `C_chi(a)=int chi(x)chi(x+a)dx>0`; такая функция существует, если её поддержка имеет длину больше a. Рассмотрим

\[
f_t(x)=\frac{\chi(x)\cos(tx)}{\|\chi\cos(t\cdot)\|_2}.
\]

У всех f_t нулевой обычный trace. Единственный ненулевой prime atom при малой dilation — n=2. Repeated integration by parts в rapidly oscillating части корреляции даёт

\[
Q_{f_t}'(a)=-\frac{2t C_\chi(a)}{\|\chi\|_2^2}\sin(ta)+O_\chi(1).
\tag{7.2}
\]

Arch-variation ограничена через `1+2||m_j||_1`; pole-variation быстро убывает по t, поскольку chi smooth compact. Поэтому

\[
\boxed{\mathcal W_L[f_t]=
-\frac{2w_2a C_\chi(a)}{\|\chi\|_2^2}t\sin(ta)+O_\chi(1).}
\tag{7.3}
\]

На последовательностях ta=pi/2+2pi k и ta=3pi/2+2pi k получаются соответственно -infinity и +infinity. Это доказывает, что общий source-volume функционал не обладает знаком из E/F/LA предпосылок. При фиксированном L гладкие тесты также можно приближать finite cosine sums в нужных derivative нормах; однако это не diagonal N=m test и не контрпример к selected cofinal EDGE_LAW. Для последнего нужен дополнительный source-specific selection argument, которого здесь нет.

### 7.3. Exact missing interface

Для закона энергии не оплачена (6.4) на масштабе e² log(T)/T. Для получения его из вириала дополнительно нужны:

- контроль moving projector term (3.4) на том же **относительном** масштабе;
- интегрирование shape derivative с начальным уровнем и событиями rank/mode/prime changes либо независимая energy identity (5.4);
- joint head/cross/remainder bound, а не отдельные unsigned bounds с потерей cancellation.

Добавление scalar cI к конечной матрице меняет lambda на c, но не меняет dot A, r или projector correction. Этот простой LA-контроль показывает, почему derivative identity сама по себе не определяет уровень. В literal source c_* известен и удержан в (5.6); его нельзя забыть при переходе от скорости к энергии.

## 8. KILL 8 и completeness границ

Финитный профиль с e!=0 не имеет конечного логарифмически нормированного следа:

\[
f(b-d)^2\log(d^{-2})\to+\infty\quad(d\downarrow0).
\]

Нельзя подставить его e² в граничный член теоремы для continuum log-Laplacian eigenfunction с исчезающим обычным trace. Даже для последнего существование нормированного trace и interchange малопорядковых пределов были отдельными неоплаченными предпосылками S4. Отозванный arXiv:2411.15985 не используется. Здесь finite shape identity доказана напрямую по source-корреляциям.

| Boundary/event | Treatment |
|---|---|
| x=±b | оба trace, чётность, Leibniz term (4.1), L2 cusp (3.8) |
| s=0 | sj→1/2, arch norm term -||f||², integrable m_j |
| s=L | Q(L)=0, expansion (2.5), one-sided endpoint atom |
| L=log n | exact rank-one kick (2.6), all prime powers |
| |gamma|=T | strict head, inclusive tail; no derivative through entry |
| automatic external sinc row/rank change | no constant-rank projector formula across event |
| removable modal poles | entire sinc continuation, not pole deletion |
| multiple compressed eigenvalue | matrix slopes (3.5)–(3.6) |
| integer N change | not part of fixed-N derivative; discrete return separate |
| e=0 | energy identity retained; ratio R not formed |
| infinite zero sum differentiated | no unjustified termwise differentiation; finite difference first |
| Fourier/prime/arch/pole truncation | full source and full arch tail retained in derivation |

## 9. E/F/Z/LA/A/I classification

Immediate dependencies are separated from remote historical proofs of imported facts.

| Ingredient | Tags | Exact meaning |
|---|---|---|
| cosine carrier, ordinary endpoint trace, dilation norm | LA,A | geometry/domain, not theta radicality |
| derivative (4.1), continuum/pole Leibniz algebra | LA,A | ordinary calculus with moving boundary |
| actual j,c_*,pole normalization | F,A | completed-zeta gamma/pole source |
| actual w_n=Lambda(n)/sqrt n and jumps | E,I | prime-power weights and integer atom locations |
| full source = conjugate-reflected zero sum | E,F,A | explicit formula; not only counts |
| E, dot E, Pi, dot Pi | LA,A | actual complex evaluation nodes; Z alone insufficient |
| compressed HF / Rellich | LA,A | finite perturbation theory and domain continuation |
| lower head/pair metric | F,A,LA | complex-pair symmetry and multiplicities |
| endpoint split F=eB+R | LA,A | integration by parts / exact rational formula |
| energy tail absolute convergence | Z,A | count growth plus fixed-strip Fourier decay |
| replacing sin² by 1/2 | NOT_AN_ACCEPTED_INPUT | separate oscillatory hypothesis, not implied by Z |
| coefficient 2 model | Z plus extra assumptions | density integral after unproved phase/real-tail substitution |
| claimed selected cofinal volume sign | OPEN | not supplied by E,F,Z,LA labels |
| global h virial from S5 | F,A; E in source crosswalk | radicality at one global test, not selected finite stationarity |

## 10. Tests, predictions, and verification scope

Predictions were written to `registration.json` before execution. Seven exact SymPy groups cover projector differentiation, moving-subspace nonstationarity, rational endpoint algebra, square expansion, negative cross control, density primitive and endpoint-atom kick. Numerical normalization uses the actual m=8 source, N=8, L=log8, and the first three real zeta zeros below 1.1Omega. It is not an abstract replacement matrix.

Two independent precision/quadrature settings were run: 40 dps, 4xGL32, finite-difference h=1e-8; and 55 dps, 4xGL48, h=1e-12. Each side rebuilds the finite source and the moving complement. New m=55..240 spectra were not computed.

| Quantity at m=8 | Value |
|---|---:|
| selected complement lambda | 1.50788342085888561035 |
| e=f(b) | -0.71751538512268324500 |
| source left virial | -6.41350285101287147391 |
| moving-projector correction | -0.81939442714179016943 |
| prime-power 8 kick | -0.52471033024688902450 |
| predicted left slope | -7.23289727815466164334 |
| predicted right slope | -7.75760760840155066784 |
| refined left absolute FD discrepancy | 1.325e-10 |
| refined right absolute FD discrepancy | 1.509e-10 |
| direct interior-integral Leibniz discrepancy | <2.0e-54 |

The original h=1e-8 discrepancies were approximately 1.325e-6 and 1.509e-6. Their four-order reduction is consistent with the first-order finite difference error. This is NOT a rigorous quadrature/eigenvalue enclosure and does not certify a new zeta zero census. The analytic proof does not use the floating values.

| Prediction | Fate |
|---|---|
| P1 moving correction required | CONFIRMED by exact LA and actual m8 diagnostic |
| P2 endpoint prime-power kick sign/coefficient | CONFIRMED exact local calculation and both FD slopes |
| P3 source boundary/volume Leibniz term | PROVED_PAPER; direct integral normalization confirmed |
| P4 averaged coefficient 2 | algebra of model CONFIRMED; phase-average premise NOT PROVED |
| P5 cross retained and not fixed sign | CONFIRMED exact square identity and negative plant |
| selected R≈4 cofinal | NOT_TESTED_AS_A_THEOREM; no prediction upgraded from finite observations |

## 11. Two representations and one next task

| Representation | Decisive object | Kill-power / cost |
|---|---|---|
| full arithmetic shape ledger | (4.4), plus independently rebuilt dot Pi and prime threshold kicks | high for false identities / low-to-moderate finite cost; no automatic cofinal sign |
| endpoint-energy Schur split inside S | endpoint representer and exact interior resolvent, avoiding a supposed universal Pohozaev constant | high for testing rank-one edge explanation / moderate finite cost, high source-gap cost |

For the second representation let beta=Pi d_b, assume beta!=0, u=beta/||beta||, and split S=span{u} plus (S cap ker boundary). Write A_S=[[a,h*],[h,D]]. If lambda not in spectrum(D) and e!=0, exactly

\[
\lambda=a-h^*(D-\lambda I)^{-1}h,\qquad
 e^2=\frac{\|\beta\|^2}{1+h^*(D-\lambda I)^{-2}h}.
\tag{11.1}
\]

These are guarded identities, not estimates: an interior gap, source sign, and the full resolvent budget cannot be invented. They identify what an actual edge-controlled eigenvector would have to satisfy without dropping a mixed block.

**CODEX DIRECTIVE — EDGE_LAW_RELLICH_MATRIX_AUDIT.** On the saved original vectors, compute the fixed-N dilation source (2.2), the boundary/volume split (4.4), and the exact evaluation-projector derivative (3.2); compare with eigenvalue finite differences while holding the active zero set fixed. At prime-power L use separate sides. In the same report compute the energy coefficient (5.5) from the constant source vector and direct low-zero head, then retain H_T, X_T, V_T rather than fit R after deleting them. First reproduce the m8 sign controls below. Require source/Gram/rank/simplicity or cluster guards, two precisions, all raw quantities on the SAME physical vector and absolute as well as e² log(T)/T-relative errors. No claim of a cofinal edge law or RH follows from finite agreement. If a normalized result is zero-consistent, the DISCRIMINATOR is a one-sided interval for the complete defect (6.4), or an exact source factorization of it; division by an uncertified tiny endpoint is forbidden.

## 12. Dependency epistemics and closeout

DOWNSTREAM_CONSUMER: source lower floor on the literal complement, with inherited quiet-space transfer.
ACTUAL_CONSUMER_REQUIREMENT: a uniform lower bound; a positive selected edge law would be stronger than necessary.
ORIGINAL_REQUESTED_OBJECT: full compressed dilation identity and analytic interpretation of edge-law coefficient.
ORIGINAL_OBJECT_IS: useful candidate representation; exact R≈4 law is NOT_NECESSARY for a constant-floor consumer.
KNOWN_WEAKER_INTERFACES: a direct joint one-sided source bound; no need for exact edge asymptotics or a positive volume term separately.
FAILURE_TYPE: NO_DERIVATION of selected cofinal volume sign / edge coefficient law.
EPISTEMIC_STATUS: RESEARCH_DEBT for that source estimate; not route death.
REOPEN_TRIGGER: relative complete-defect bound (6.4) or a source-controlled endpoint Schur budget, including all mixed terms.
NOVELTY_AXIS: finite moving-zero-complement HF/Rellich identity, explicit projector and prime-power threshold corrections; no new cofinal positivity.

What shrank: the proposed Rellich test is now a fully specified finite-family identity with no unlabelled boundary or constraint derivative. What was excluded: only the generic shortcuts `minimum => zero dilation`, `quiet residual => small projector correction`, `far-tail endpoint average => moving-family R`, and an imported finite trace Pohozaev formula. No KILL of the literal edge-law family is asserted. Strongest attack survives in explicit form: the head/cross terms and normalized constraint velocity can remain load-bearing at tiny e.

Do not retry: differentiating the discrete N=m sequence as a smooth family; replacing J-perp by J; using a continuum trace theorem on a finite profile with e!=0; treating source-minus-prefix as an independent positive infinite tail; upgrading numerical identities to a sign theorem.

Memory entry:

```yaml
iteration: EDGE_LAW_RELLICH_v1
status: PROGRESS
cognitive_operator_used: REPRESENTATION_SHIFT
invariant_learned: moving support and moving zero-complement contribute separately
forbidden_future_move: drop projector velocity or replace nonlocal boundary flux by a scalar endpoint law
minimal_missing_identity: a joint source bound for complete relative defect (6.4)
next_decisive_test: fixed-N one-sided derivative audit and exact endpoint-energy ledger
```

No repository file or route-state was changed. No Lean source was written, so a Lean axiom profile is inapplicable. This file is an author PAPER derivation with explicit exact/finite controls, not an independent audit.

### Primary public references

P1: https://arxiv.org/html/2511.22755v1 — Connes–Consani–Moscovici, §3; only the explicit form and normalization are used.

P2: https://arxiv.org/abs/2411.15985v2 — withdrawn 26 April 2025, stated error in Pohozaev proof. No result from that withdrawn proof is imported.

## Appendix A. Reproducible controls

The following code is self-contained. Install through uv as in its docstring. Parameters `MP_DPS`, `GL_ORDER`, `FD_H`, `RESULT_NAME` are optional environment overrides: for the refined run use `MP_DPS=55 GL_ORDER=48 FD_H=1e-12 RESULT_NAME=results_refined.json uv run --with mpmath --with sympy python checks.py`. All finite source terms are retained; the geometric arch tail is truncated at a level negligible for this diagnostic, not interval-certified.

```python
#!/usr/bin/env python3
"""EDGE_LAW_RELLICH_v1 normalization checks.
Run: uv run --with mpmath --with sympy python checks.py
m=8 is the original carrier size; N is held at m during local L dilation.
No finite experiment certifies a cofinal inequality or RH.
"""
from pathlib import Path
import json, time, os
import sympy as sp
import mpmath as mp
BASE=Path(__file__).resolve().parent
out={"exact":{},"numerical":{},"scope":"DIAGNOSTIC_NOT_INTERVAL"}
def exact():
    t=sp.symbols('t',real=True)
    E=sp.Matrix([[1,t,0],[0,1,t]])
    P=E.T*(E*E.T).inv()*E
    M=(E*E.T).inv()
    rhs=(sp.eye(3)-P)*sp.diff(E,t).T*M*E+E.T*M*sp.diff(E,t)*(sp.eye(3)-P)
    assert sp.simplify(sp.diff(P,t)-rhs)==sp.zeros(3)
    out['exact']['projector_derivative']=True
    a,b,d=sp.symbols('a b d',real=True)
    v=sp.Matrix([sp.cos(t),sp.sin(t)])
    AA=sp.Matrix([[a,b],[b,d]])
    deriv=sp.diff((v.T*AA*v)[0],t).subs(t,0)
    assert deriv==2*b
    out['exact']['nonstationary_moving_subspace']=str(deriv)
    z,om=sp.symbols('z om',positive=True)
    assert sp.factor(z/(z*z-om*om)-1/z-om*om/(z*(z*z-om*om)))==0
    out['exact']['rational_edge_split']=True
    X,edge=sp.symbols('X edge',real=True)
    assert sp.expand(2*(edge+X)**2-(2*edge**2+4*edge*X+2*X**2))==0
    out['exact']['edge_cross_square']=True
    assert (4*edge*X).subs({edge:1,X:-sp.Rational(1,2)})==-2
    out['exact']['negative_cross_plant']=True
    T=sp.symbols('T',positive=True)
    primitive=(sp.log(T/(2*sp.pi))+1)/T
    assert sp.simplify(sp.diff(primitive,T)+sp.log(T/(2*sp.pi))/T**2)==0
    out['exact']['phase_averaged_coefficient']=2
    tau,w=sp.symbols('tau w',real=True)
    assert sp.diff(-2*w*(1-sp.exp(-tau)),tau).subs(tau,0)==-2*w
    out['exact']['endpoint_atom_right_kick']='-2*w (unit constant trial)'
    print('EXACT 7 groups passed',flush=True)
def numeric():
    mp.mp.dps=int(os.environ.get("MP_DPS", "40"))
    gl=int(os.environ.get("GL_ORDER", "32"))
    N=8; L0=mp.log(8)
    nodes,weights=mp.gauss_quadrature(gl,'legendre')
    us=[]; ws=[]
    for k in range(4):
        for i in range(gl):
            us.append((k+(nodes[i]+1)/2)/4)
            ws.append(weights[i]/8)
    d=[mp.mpf(1)]+[mp.sqrt(2)]*N
    cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2
    zeros=[mp.im(mp.zetazero(k)) for k in range(1,4)]
    def sinc(x): return mp.sin(x)/x if x else mp.mpf(1)
    def qij(L,s,i,j):
        if s>=L:return mp.mpf(0)
        ell=L-s; oi=2*mp.pi*i/L; oj=2*mp.pi*j/L
        return d[i]*d[j]*(-1)**(i+j)*ell/L*(sinc((oi-oj)*ell/2)*mp.cos((oi+oj)*s/2)+sinc((oi+oj)*ell/2)*mp.cos((oj-oi)*s/2))
    def jj(s):return mp.exp(-s/2)/(-mp.expm1(-2*s))
    def mj(s):
        v=jj(s)
        return v+s*v*(-mp.mpf('0.5')-2/mp.expm1(2*s))
    def ap(L,n):
        om=2*mp.pi*n/L
        return mp.sqrt(2)*d[n]/mp.sqrt(L)*mp.sinh(L/4)/(mp.mpf('0.25')+om*om)
    lambdas={n:mp.log(next(iter(sp.factorint(n)))) for n in range(2,10) if len(sp.factorint(n))==1}
    def Eof(L):
        return mp.matrix([[2*d[n]*z*mp.sin(L*z/2)/(mp.sqrt(L)*(z*z-(2*mp.pi*n/L)**2)) for n in range(N+1)] for z in zeros])
    def Aof(L):
        H=mp.matrix(N+1)
        poles=[ap(L,n) for n in range(N+1)]
        tail=mp.fsum(mp.exp(-(mp.mpf('.5')+2*k)*L)/(mp.mpf('.5')+2*k) for k in range(35))
        for i in range(N+1):
            for j in range(i,N+1):
                ij=int(i==j)
                ar=L*mp.fsum(w*jj(u*L)*(2*ij-qij(L,u*L,i,j)) for u,w in zip(us,ws))+2*ij*tail
                primes=mp.fsum(v/mp.sqrt(n)*qij(L,mp.log(n),i,j) for n,v in lambdas.items() if mp.log(n)<L)
                H[i,j]=H[j,i]=-cstar*ij+ar-primes+poles[i]*poles[j]
        return H
    def select(L):
        E=Eof(L); U,R=mp.qr(E.T)
        U=U[:,:len(zeros)]
        A=Aof(L); eig,V=mp.eigsy(U.T*A*U)
        c=U*V[:,0]
        return eig[0],c,A,E
    lam,c,A,E=select(L0)
    print('NUM base source built',flush=True)
    P=E.T*(E*E.T)**-1*E
    Ed=mp.matrix([[mp.diff(lambda tau:Eof(L0*mp.exp(tau))[i,j],0) for j in range(N+1)] for i in range(len(zeros))])
    Pd=(mp.eye(N+1)-P)*Ed.T*(E*E.T)**-1*E+E.T*(E*E.T)**-1*Ed*(mp.eye(N+1)-P)
    r=(mp.eye(N+1)-P)*A*c
    corr=2*(r.T*Pd*c)[0]
    e=mp.fsum(d[i]*c[i] for i in range(N+1))/mp.sqrt(L0)
    def Q(s):return mp.fsum(c[i]*c[j]*qij(L0,s,i,j) for i in range(N+1) for j in range(N+1))
    p=mp.fsum(c[i]*ap(L0,i) for i in range(N+1))
    xpq=mp.fsum(c[i]*(2*L0*mp.diff(lambda x:ap(x,i),L0)-ap(L0,i)) for i in range(N+1))
    ar=-1-L0*mp.fsum(w*mj(u*L0)*Q(u*L0) for u,w in zip(us,ws))
    prime=mp.fsum(v/mp.sqrt(n)*mp.log(n)*mp.diff(Q,mp.log(n)) for n,v in lambdas.items() if n<8)
    virial=ar+p*p+p*xpq+prime
    kick=-2*mp.log(2)/mp.sqrt(8)*L0*e*e
    h=mp.mpf(os.environ.get('FD_H','1e-8'))
    lp,cp,Ap,Ep=select(L0*mp.exp(h))
    lm,cm,Am,Em=select(L0*mp.exp(-h))
    plus=(lp-lam)/h
    minus=(lam-lm)/h
    expected_plus=virial+corr+kick
    expected_minus=virial+corr
    errplus=abs(plus-expected_plus);errminus=abs(minus-expected_minus)
    # Independent direct interior integral checks the boundary in Q'.
    def ff(x):
        return mp.fsum(c[n]*d[n]*(-1)**n*mp.cos(2*mp.pi*n*x/L0) for n in range(N+1))/mp.sqrt(L0)
    def fp(x):
        return mp.fsum(-c[n]*d[n]*(-1)**n*(2*mp.pi*n/L0)*mp.sin(2*mp.pi*n*x/L0) for n in range(1,N+1))/mp.sqrt(L0)
    leibniz_errors=[]
    for ss in [L0/7,mp.log(2),mp.log(5),L0*mp.mpf('.95')]:
        ell=L0-ss
        integ=ell*mp.fsum(w*ff(-L0/2+u*ell)*fp(-L0/2+u*ell+ss) for u,w in zip(us,ws))
        leibniz_errors.append(abs(mp.diff(Q,ss)-(2*integ-2*e*ff(L0/2-ss))))
    out['numerical']['leibniz_max_error']=mp.nstr(max(leibniz_errors),24)
    leibniz_error=max(leibniz_errors)
    assert leibniz_error<mp.mpf('1e-24')
    vals={'m':8,'N_fixed':8,'dps':mp.mp.dps,'GL_per_panel':gl,'panels':4,'lambda':lam,'edge':e,'source_left_virial':virial,'projector_correction':corr,'prime8_kick':kick,'fd_left':minus,'pred_left':expected_minus,'fd_right':plus,'pred_right':expected_plus,'abs_error_left':errminus,'abs_error_right':errplus,'projector_rank':3,'orthogonality_error':mp.norm(P*c-c),'FD_h':h,'leibniz_max_error':leibniz_error}
    out['numerical']={k:mp.nstr(v,24) if isinstance(v,mp.mpf) else v for k,v in vals.items()}
    assert errplus<mp.mpf('1e-5') and errminus<mp.mpf('1e-5')
    assert abs(corr)>mp.mpf('1e-12')
    out['numerical']['passed']=True
exact()
started=time.monotonic()
numeric()
out['elapsed_seconds']=time.monotonic()-started
(BASE/os.environ.get('RESULT_NAME','results.json')).write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2),flush=True)
```

## Appendix B. Refined control output

```json
{
  "exact": {
    "projector_derivative": true,
    "nonstationary_moving_subspace": "2*b",
    "rational_edge_split": true,
    "edge_cross_square": true,
    "negative_cross_plant": true,
    "phase_averaged_coefficient": 2,
    "endpoint_atom_right_kick": "-2*w (unit constant trial)"
  },
  "numerical": {
    "m": 8,
    "N_fixed": 8,
    "dps": 55,
    "GL_per_panel": 48,
    "panels": 4,
    "lambda": "1.50788342085888561034695",
    "edge": "-0.717515385122683245004087",
    "source_left_virial": "-6.41350285101287147390715",
    "projector_correction": "-0.819394427141790169431397",
    "prime8_kick": "-0.524710330246889024504087",
    "fd_left": "-7.23289727802220815452587",
    "pred_left": "-7.23289727815466164333854",
    "fd_right": "-7.75760760855244400228676",
    "pred_right": "-7.75760760840155066784263",
    "abs_error_left": "1.3245348881267518928692e-10",
    "abs_error_right": "1.50893334444125036149851e-10",
    "projector_rank": 3,
    "orthogonality_error": "1.80940458995139821050778e-57",
    "FD_h": "1.0e-12",
    "leibniz_max_error": "1.95759134039955735801309e-54",
    "passed": true
  },
  "scope": "DIAGNOSTIC_NOT_INTERVAL",
  "elapsed_seconds": 3.9206725259999757
}
```