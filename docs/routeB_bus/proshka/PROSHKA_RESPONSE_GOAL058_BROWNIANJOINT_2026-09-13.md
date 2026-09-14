# STATUS: KILL_NAMED_CONDITIONAL_MECHANISM
```yaml
OPERATIVE_CLASS: KILL_NAMED_CONDITIONAL_MECHANISM
REQUEST_ID: REQ-2026-09-13-BROWNIANJOINT
BOUNDARY_ID: GOAL058_FULL_THETA_DILATION_CONDITIONAL_COVARIANCE
REQUEST_COMMIT: a17d4f7c1d95c6f274461405ea1a8ffdd29a61dc
REQUEST_BLOB: 09abce5ffe252091ccd28c9a8bc22f5f8ebcd85b
SOURCE_BASE: 9864a5052eaa23790d8719d3beb548e084eee24d
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
HONESTY_STATE: CHALLENGER_NOT_RH
SELECTED_MECHANISM: PHYSICALLY_WEIGHTED_COPY_REFLECTION_RANK_ONE_HODGE_PROJECTION
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: FULL_SOURCE_POSITIVE_INDEX_AT_LEAST_TWO_AND_NEGATIVE_PRIMITIVE_FORM
KILL_EVIDENCE_REF: "Sections 4-8; R=10^24; H_psi(F,F)<-1/9; continuation to the requested likelihood interval"
AUTOPSY_DROPPED: SIGN
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS_NAMED_MECHANISM: MATHEMATICALLY_DEAD_AT_EXACT_SCOPE_PENDING_REVIEW
EPISTEMIC_STATUS_TARGET: RESEARCH_DEBT
TARGET_PROVED: false
TARGET_REFUTED: false
ACTUAL_V_NEGATIVE_WITNESS: false
NEW_TARGET_SIGN_SUPPLIER: false
NEW_RESULT: WEIGHTED_HODGE_PRIMITIVITY_FAILS_EVEN_ON_ACTUAL_LIKELIHOOD_PRODUCT_SPAN
PROGRESS_CLASS: FALSIFICATION_PROGRESS
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROOF_STATE: PAPER_CANDIDATE_PENDING_INDEPENDENT_REVIEW
EXACT_RATIONAL_CALIBRATION_EXECUTED: true
THETA_EVALUATIONS: 0
QUADRATURES: 0
SOURCE_RANK_SWEEPS: 0
LEAN_RUNS: 0
INDEPENDENT_REVIEW_PERFORMED_BY_PRODUCER: false
GLOBAL_IC: OPEN_UNCHANGED
GLOBAL_ODD2: OPEN_UNCHANGED
ALL_ORDER_SOURCE_SIGN: OPEN_UNCHANGED
FIXED_TWOCHANNEL_RF: PREVIOUSLY_REFUTED_NOT_REOPENED
PX_RH_CLAIM: NOT_MADE
CANONICAL_ADMISSION: false
SOURCE_SIGN_NO_DELTA:
  inherited: 10
  proposed_after_independent_acceptance: 11
  state_changed: false
ATTEMPTS_SINCE_LATEST_OWNER_DIRECTION:
  inherited_completed: 1
  proposed_after_this_attempt: 2
PUBLICATION_BRANCH: codex_mac/math-proshka-20260912
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_BROWNIANJOINT_2026-09-13.md
```

AUTOPSY: dropped=SIGN; note=The physical weight and half-line cutoff destroy the one-positive-direction premise of the proposed copy-reflection Hodge argument. The failure occurs on the linear span of the actual dilation likelihoods, and also on their products from the requested interval. It does not refute the complete conditional-covariance comparison.

## 1. Итог и точная граница

**Полную оценку `E_micro >= E_loss` я не доказал и не опроверг.** Проверен один конкретный механизм: перенести прежнюю **Hodge-примитивность** на отражение двух энергий после включения именно физического веса `w` и отсечения `X>=0`.

У этого переноса ложна необходимая промежуточная гипотеза. У новой взвешенной формы имеются как минимум **два положительных направления**, уже на линейной оболочке настоящих likelihoods — отношений плотностей при масштабировании. Поэтому удаление одного положительного направления не превращает минус оставшуюся форму в положительную энергию.

Ниже дан полный источник-специфический бюджет, а не контрпример с заменённой плотностью. При явном `R=10^24` строится конечная комбинация трёх полных likelihoods, для которой
\[
\boxed{Q_\psi(1,F)=0,\qquad H_\psi(F,F)<-\frac19.} \tag{1}
\]
В физическом масштабе правая часть равна `-1/(18 A^2)`. После доказанного аналитического продолжения тот же отказ существует и на требуемом интервале `1/2<a<1`, хотя конкретные локальные узлы и коэффициенты здесь не вычислены. Отдельно доказано, что ограничение на произведения likelihoods с обоими параметрами в этом интервале также не спасает данный Hodge-шаг.

**Это отрицательная форма `H_psi`, не отрицательная `V`.** Не утверждается, что TARGET требует положительности `H_psi`: это проверяемая предпосылка только выбранной попытки переноса; её одной достаточность для TARGET также не была установлена. Специальная компенсация между микроскопической формой и полной условной ковариацией остаётся возможной и неоплаченной. `[ABSTRACT][PAPER]`

## 2. Источники и область чтения

Протокол `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` получен через GitHub из `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`; прочитан с продолжениями усечённого вывода. Управляющий запрос прочитан целиком по указанному владельцем commit. Его текущая доставка через pinned GitHub TXT определяет задачу; старые вложения не выбирают работу.

В таблице приведены **remote Git blobs**, возвращённые чтением именно закреплённых commit. Это не заявление о независимо пересчитанных локальных SHA-256 всех файлов. Полные рекурсивные архивы и старые PDF не перечитывались.

| ID | Путь от корня `Malaeu/chen_q3` | Commit | Подтверждённый Git blob; чтение |
|---|---|---|---|
| R | `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_BROWNIANJOINT_2026-09-13.txt` | `a17d4f7c1d95c6f274461405ea1a8ffdd29a61dc` | `09abce5ffe252091ccd28c9a8bc22f5f8ebcd85b`; полностью |
| D | `docs/Codex/REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md` | тот же commit R | `46d295269a62e4e951f6ab0f0b0ba2d22b537166`; полностью, §§1–6 и receipt |
| B | `docs/Codex/REPORT_2026-09-13_BROWNIANHODGE_INTAKE.md` | SOURCE_BASE | `721cf810edde882840f0f51849598c21e312b6c4`; полностью |
| H | `docs/Codex/REPORT_2026-09-13_BROWNIAN_PRIMITIVE_FORM.md` | SOURCE_BASE | `440b72e444e7a13de87fd61dc828a84bc5894cb3`; B1–B5 и исходная acceptance; последующий appended preflight не используется |
| S | `docs/Codex/REPORT_2026-09-13_BROWNIAN_SCALE_DIFFERENCE.md` | SOURCE_BASE | `95eb52bf3565c705fce2f205426303c751406af1`; полностью |
| A | `docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md` | SOURCE_BASE | `4c7b8bdbc362e1e65a41747c7cd6367430066974`; A1–A2, строки 1–108 |
| W | `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md` | SOURCE_BASE | `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`; Theorem T, §§1–2 и §10; дополнительно получены строки 276–335 |
| Z | `docs/Codex/REPORT_2026-09-13_DEFORMED_SOURCE_ZERO_WITNESS.md` | SOURCE_BASE | `0949396cb6e51c5fe830ec3b706a6065f308fea5`; Z3–Z4 и receipt, строки 75–146 |

Локаторы восстанавливаются однозначно как `https://github.com/Malaeu/chen_q3/blob/{commit}/{path}`. Например, R — буквальная ссылка владельца. Идентификатор draft SHA-256 `b5d949a29d09d52cea59acbf8a9c68ead2516e7340244fe92f0bacf4f524274f` в D относится к проверенному draft до добавления receipt; его нельзя объявлять хешем финального D. Здесь этот draft-хеш не пересчитывался.

Внешне сверены только точные theta-тождества NIST DLMF: [20.2.2, 20.2.4](https://dlmf.nist.gov/20.2), [20.7.33](https://dlmf.nist.gov/20.7#E33), включая principal-square-root convention. Они нужны в §7 для аналитичности. Они не являются теоремой о TARGET. Исходная Laplace-формула полного `nu` берётся из B/H и ниже также используется напрямую через произведение. Новая знаковая оценка не импортируется из литературы.

Ранее принятые `A1`, полный источник B, условное тождество D и Theorem T используются в своих точных областях. Новое доказательство ниже — **PAPER-кандидат**, не независимый приём и не Lean-проверка. `[ABSTRACT][PAPER]`

## 3. Тот же источник, тот же вес, обе энергии и вся ковариация

Сохраняем
\[
\alpha=\tfrac14,\quad U=\sum_{n\ge1}E_n/(\pi n^2),\quad
\nu(du)=h(u)du,\quad r=h*h,\quad C=2Z,
\]
\[
\Phi(x)=e^{5x/2}r(e^{2x}),\qquad f=\Phi/A,\quad A=\|\Phi\|_2.
\]
Ни `nu`, ни `Phi`, ни `A` не меняются. Независимую копию `U` обозначаем `U'`, чтобы не смешивать её с ядром `V`.

Входы B/D дают
\[
d\mu=C^{-1}T^{1/4}h(u)h(v)\,du\,dv,\quad T=u+v,
\quad X=\tfrac12\log T,
\]
\[
w=\mathbf1_{T\ge1}Z\Phi(X)/A^2.
\]
Следовательно **точно**
\[
\boxed{w\,d\mu=\frac1{2A^2}\psi(u+v)h(u)h(v)\,du\,dv,\qquad
\psi(t)=\mathbf1_{t\ge1}t^{3/2}r(t).} \tag{2}
\]
Степень `3/2` содержит оба исходных множителя `1/4+5/4`. Удалять `r(t)`, менять эту степень или стирать индикатор нельзя.

Пусть `a=e^{2x}` и
\[
\ell_a(u)=a h(au)/h(u),\qquad G_x=a^{1/4}\ell_a(u)\ell_a(v).
\]
При условии `T=t` закон первого аргумента — `h(u)h(t-u)du/r(t)`. Поэтому прямой заменой переменной
\[
\mathcal C G_x=a^{5/4}r(at)/r(t)=\Phi(X+x)/\Phi(X). \tag{3}
\]
Это принятый источник-fit D, не новая знаковая лемма.

Для любого исходного конечного ряда положим `a_i=e^{2x_i}` и
`F_{ij}(u)=ell_{a_i}(u)ell_{a_j}(u)`. Если
\[
Q_\eta(F,G)=\iint\eta(u+v)\overline{F(u)}G(v)h(u)h(v)\,du\,dv,
\]
то полный микроскопический член равен
\[
\boxed{
E_{\rm micro}[c]=\frac1{2A^2}\sum_{i,j}\overline{c_i}c_j(a_i a_j)^{1/4}
\left[Q_{\psi\log}(F_{ij},F_{ij})+(x_i+x_j)Q_\psi(F_{ij},F_{ij})\right].} \tag{4}
\]
В `psi log` логарифм относится к `u+v`. Ни один из двух источников `h(a_i u)` и `h(a_i v)` не заменён своим условным средним. В частности, (4) не есть произвольная положительная матрица из-за положительности её отдельных интегралов.

Обозначим
\[
m_i(t)=\mathbb E[G_{x_i}\mid T=t],\quad
\Sigma_{ij}(t)=\mathbb E[(G_{x_i}-m_i)(G_{x_j}-m_j)\mid T=t].
\]
Для вещественных likelihoods `Sigma` вещественна и симметрична. Полная ковариационная потеря имеет вид
\[
\boxed{
E_{\rm loss}[c]=\int_0^\infty f(X)^2
\sum_{i,j}\overline{c_i}c_j(2X+x_i+x_j)\Sigma_{ij}(e^{2X})\,dX.} \tag{5}
\]
Это сохраняет смешанный член `B_c^perp`, включая его знак. Из `Sigma(t)>=0` не следует знак матрицы с множителем `2X+x_i+x_j`.

Итак, непогашенный TARGET остаётся ровно
\[
E_{\rm micro}[c]-E_{\rm loss}[c]
=2\Re\langle\mathcal CG_c,\mathcal C(XG_c+B_c)\rangle_{w\mu}
=V[c]\ge0. \tag{6}
\]
Мы не вводим оператор `G_c -> B_c` на факторпространстве: обе функции по-прежнему определяются самим конечным списком. Никакое неустановленное замыкание оператора не используется. `[ABSTRACT][PAPER]`

## 4. Проверяемый Hodge-шаг и его область определения

У прежнего Q_alpha с ядром `(u+v)^alpha` была одна положительная размерность. Выбранная попытка — получить то же свойство для **Q_psi из (2)**, чтобы применить его примитивный знак к профилям из (4) и условной поправке. Проверяем именно эту промежуточную гипотезу, прежде чем объявлять перенос состоявшимся.

Положим
\[
\rho_\psi(u)=h(u)\int_0^\infty\psi(u+v)h(v)dv,\qquad
\mathcal D_\psi=L^2((0,\infty),\rho_\psi(u)du).
\]
По Cauchy–Schwarz на симметричной положительной мере в (2)
\[
|Q_\psi(F,G)|\le\|F\|_{\mathcal D_\psi}\|G\|_{\mathcal D_\psi}. \tag{7}
\]
Это корректная непрерывная Hermitian-форма; она не обязана быть положительной. Константа 1 принадлежит области, и
\[
q_*=Q_\psi(1,1)>0,
\quad H_\psi(F,G)=\frac{Q_\psi(F,1)Q_\psi(1,G)}{q_*}-Q_\psi(F,G). \tag{8}
\]
Тождество `H_psi(F,G)=-Q_psi(PF,PG)` верно для
`PF=F-Q_psi(1,F)1/q_*`. **Его знак ещё не следует из тождества.**

Полный B-источник, через `W=sum_{n>=2} E_n/(pi n^2)`, даёт
\[
h(u)=2\pi e^{-\pi u}\chi(u),\quad
\chi(u)=\tfrac12\mathbb E[e^{\pi W}\mathbf1_{W<u}],
\]
\[
0<\chi\le1,\quad
r(t)=4\pi^2e^{-\pi t}\mathcal B(t),\quad
\mathcal B(t)=\int_0^t\chi(u)\chi(t-u)du,
\]
\[
\boxed{0<\mathcal B(t)\le t,\qquad 0\le t-\mathcal B(t)\le\frac3{2\pi}<\frac12.} \tag{9}
\]
Это полный результат B, а не первая theta-мода. Например, последний бюджет следует из
`E exp(pi W)=2`, `E[W exp(pi W)]/2=3/(4pi)` и
`1-chi(u)chi(t-u) <= (1-chi(u))+(1-chi(t-u))`.

Для `0<a<=1` монотонность `chi` даёт
\[
0<\ell_a(u)\le a e^{\pi(1-a)u}. \tag{10}
\]
Из (9) следует `psi(t)<=4pi^2 t^{5/2}e^{-pi t}`. Поэтому интегранд квадрата нормы `ell_a` в (7) ограничен константой, умноженной на
\[
(u+v)^{5/2}e^{-2\pi a u-2\pi v}.
\]
Он интегрируем для каждого `a>0`. Следовательно **все `ell_a`, `0<a<=1`, лежат в D_psi**. Для произведения `ell_a ell_b` аналогичный показатель равен
`-2pi(a+b-1)u-2pi v`, так что все продукты при `a,b>1/2` также принадлежат области. Дополнительный `log(u+v)` из (4) поглощается полиномиальной мажорантой на `u+v>=1`. Концевой участок с малым `u` или `v` не исключён.

Проверяемая гипотеза выбранного механизма теперь точна:
\[
H_\psi(F,F)\ge0\quad\text{на линейной оболочке этих likelihoods/продуктов}. \tag{H}
\]
Ниже (H) опровергается. Не утверждается, что (H) необходимо для TARGET. `[ABSTRACT][PAPER]`

## 5. Полная экспоненциальная перекалибровка исходного закона

Введём действительный смешанный kernel
\[
J(a,b)=Q_\psi(\ell_a,\ell_b)
=ab\iint\psi(u+v)h(au)h(bv)\,du\,dv. \tag{11}
\]
После `s=au`, `t=bv` это `E psi(U/a+U'/b)` под исходными независимыми законами.

Пусть
\[
L(z)=\mathbb Ee^{-zU}=\prod_{n\ge1}(1+z/(\pi n^2))^{-1}
=\frac{\sqrt{\pi z}}{\sinh\sqrt{\pi z}},\quad L_a=L(\pi/a)>0.
\]
Под вероятностью `dnu_a=e^{-pi u/a}dnu/L_a` компоненты U остаются независимыми экспоненциальными величинами с увеличенными rates. Поэтому для `Y_a=U/a` эти rates **точно**
\[
\boxed{\lambda_{n,a}=\pi(1+a n^2),\quad n\ge1.} \tag{12}
\]
Проверка для бесконечного числа компонент: для любой конечной группы её совместное наклонённое преобразование факторизуется, а хвост нормировки есть сходящееся положительное Laplace-произведение. Это определяет все конечномерные законы и сохраняет почти наверное конечную сумму. Никакой конечный cutoff не подставлен вместо nu.

Из (9), (11) получаем точное равенство
\[
\boxed{
J(a,b)=4\pi^2L_aL_b\,
\mathbb E_{a,b}\!\left[\mathbf1_{Y_a+Y_b'\ge1}
(Y_a+Y_b')^{3/2}\mathcal B(Y_a+Y_b')\right].} \tag{13}
\]
Индикатор и весь `Bcal` остаются внутри ожидания. Здесь впервые используется существенная структура именно rates `pi*n^2`: она даёт (12) и следующие количественные концентрационные оценки.

### 5.1. Моменты с явным бюджетом

Зафиксируем `R>=1` и `1<=s,t<=9/8`; положим
\[
a=(Rs)^{-2},\quad b=(Rt)^{-2},\quad
Y=Y_a+Y_b',\quad Z_R=Y/R,\quad z_0=(s+t)/2.
\]
Из суммирования убывающей функции `1/(1+v^2)` по полной решётке следует
\[
Rs/2-1/\pi\le\mathbb EY_a\le Rs/2.
\]
Действительно, интеграл от нуля до бесконечности равен `pi/2`, а разность между ним и положительной правой суммой не превосходит первого прямоугольника. Отсюда
\[
0\le z_0-\mathbb EZ_R\le2/(\pi R).
\]
Для суммы экспоненциальных компонент с rates не меньше pi:
\[
\operatorname{Var}Y\le\mathbb EY/\pi,\quad
\kappa_3(Y)\le2\mathbb EY/\pi^2,
\quad\mathbb EY\le9R/8.
\]
Все суммы кумулянтов сходятся; можно сначала доказать формулы для конечных сумм и перейти по монотонной сходимости моментов. Поэтому
\[
\boxed{\mathbb E|Z_R-z_0|^2<\frac1R,\qquad \mathbb EZ_R^3<3.} \tag{14}
\]
Для первой оценки достаточно
`9/(8pi R)+4/(pi^2 R^2)<1/R`, используя `pi>3`. Для второй используем
`E Y^3=m^3+3m Var(Y)+kappa_3(Y)`; верхняя константа
`(9/8)^3+(9/8)^2+1/4=1505/512<3`.

Среднее значение производной функции `z^(5/2)` и Cauchy–Schwarz дают
\[
\left|\mathbb EZ_R^{5/2}-z_0^{5/2}\right|
\le\frac52\sqrt{\mathbb E|Z_R-z_0|^2}
\sqrt{\mathbb E(Z_R+z_0)^3}
<\frac{13}{\sqrt R}. \tag{15}
\]
Здесь `E(Z_R+z_0)^3<=4(E Z_R^3+z_0^3)<18<25`.

### 5.2. Отсечение и полный density-tail оплачены, а не забыты

Для каждого `y>0`, включая `0<y<1`, (9) даёт
\[
\left|\mathbf1_{y\ge1}y^{3/2}\mathcal B(y)-y^{5/2}\right|
\le\tfrac12y^{3/2}+1.
\]
Деление ожидания на `R^(5/2)`, (14) и Cauchy–Schwarz ограничивают эту потерю величиной `2/R`. Вместе с (13)–(15):
\[
\boxed{
\left|\frac{J((Rs)^{-2},(Rt)^{-2})}
{4\pi^2L_{(Rs)^{-2}}L_{(Rt)^{-2}}R^{5/2}}
-\left(\frac{s+t}{2}\right)^{5/2}\right|
\le\frac{15}{\sqrt R}.} \tag{16}
\]
Область: **все** `R>=1`, `s,t in [1,9/8]`. Это полная оценка интегрального остатка. Она не утверждает матричный знак, исходя лишь из поэлементной сходимости: ниже размер, коэффициенты и цена этой сходимости зафиксированы заранее.

Получился показатель `5/2`, а не прежний `alpha=1/4`: физический вес поставляет `t^(3/2)`, а полный convolution-tail r поставляет ещё `t`. Прежняя одноположительная геометрия не обязана пережить эту замену. `[COFINAL_FAMILY][PAPER]`

## 6. Две положительные размерности и отрицательный primitive-бюджет

Для одного заранее фиксированного kernel
\[
K_*(s,t)=((s+t)/2)^{5/2}
\]
возьмём узлы `s=(1,17/16,9/8)` и два коэффициентных вектора
\[
e=(1,0,0),\qquad z=(4495/16,-536,256).
\]
Второй вектор есть ровно
`(15/16)ev_1-(3/2)D_h+D_h^2`, `h=1/16`, где используются первые и вторые **прямые конечные разности**, не производные исходного theta.

Точная рациональная проверка Appendix A доказывает для ограниченной на эти два вектора матрицы M:
\[
M_{00}=1,\quad |M_{01}|<1/8,\quad 1/4<M_{11}<1.
\]
Следовательно
\[
\boxed{M\succeq\tfrac18 I_2.} \tag{17}
\]
Код не вычисляет theta: каждое `q^(5/2)` ограничено рационально как `q^2 sqrt(q)` с проверкой квадрата обоих концов. Для ручной проверки направления служит точная derivative-матрица K_* в `(1,1)`:
\[
\begin{pmatrix}
1&5/4&15/16\\
5/4&15/16&15/64\\
15/16&15/64&-15/256
\end{pmatrix}.
\]
Её determinant `-75/256`; вектор `(15/16,-3/2,1)` ортогонален первому evaluation в этой форме и имеет положительную энергию `15/32`. Но именно **конечные** узлы выше, а не незаявленный предел производных, используются в (17).

Теперь фиксируем **R=10^24**. Введём настоящие source-профили
\[
a_i=(Rs_i)^{-2},\qquad
p_i=\frac{\ell_{a_i}}{2\pi L_{a_i}R^{5/4}},
\quad f_0=p_0,\quad f_1=\sum_{i=0}^2z_i p_i.
\]
Все нормирующие множители положительны и конечны. Их очень большой размер не ограничивается условиями задачи и не вычисляется с плавающей точкой.

По (16) ошибка каждого элемента матрицы на p_i не превосходит `15/10^12`. Поскольку `sum |z_i|=17167/16<1073`, ошибка квадратичной формы на `(f_0,f_1)` по модулю не превосходит
\[
\frac{15}{10^{12}}\left(1+(17167/16)^2\right)(|b_0|^2+|b_1|^2)
<\frac1{1000}(|b_0|^2+|b_1|^2).
\]
Это следует из `(abs(b_0)+||z||_1 abs(b_1))^2 <= (1+||z||_1^2)(|b_0|^2+|b_1|^2)`, поэтому почти зависимые направления здесь не потеряны. Вместе с (17)
\[
\boxed{Q_\psi(b_0 f_0+b_1 f_1,b_0 f_0+b_1 f_1)
>\tfrac19(|b_0|^2+|b_1|^2),\quad (b_0,b_1)\ne0.} \tag{18}
\]
Так **полный** Q_psi имеет положительный индекс не меньше двух.

Для явного примитивного свидетеля определим действительные, полные source-интегралы
\[
q_j=Q_\psi(1,f_j),\quad j=0,1.
\]
`q_0>0`, поскольку `f_0>0` и мера положительна на области положительной меры. Следовательно корректно
\[
F=\frac{q_1 f_0-q_0 f_1}{\sqrt{q_0^2+q_1^2}}.
\]
Получаем `Q_psi(1,F)=0`, и (18) доказывает (1). Это **строгая верхняя огибающая отрицательного primitive-значения**, с полным интегральным источником. Неравенство не основано на неудаче достаточной оценки.

Более общо, из двумерной положительной плоскости следует отказ отрицательной примитивной части после удаления **любого одного** положительного вектора: эта плоскость пересекает его Q_psi-ортогональную гиперплоскость ненулевым вектором. Удаление большего числа направлений или другой специальный механизм этим не исключаются. `[FINITE_CELL][PAPER]`

## 7. Почему это препятствие достигает интервала задания

Параметры a_i в явном свидетеле малы, а задание использует `1/2<a<1`. Поэтому нужен отдельный перенос — одного далёкого свидетеля без него недостаточно.

### 7.1. Голоморфность полного likelihood kernel

Плотность h имеет точные представления в `Re z>0`:
\[
h(z)=2\pi\sum_{n\ge1}(-1)^{n+1}n^2e^{-\pi n^2z}
=\sum_{k\ge0}\left(\frac{\pi(2k+1)^2}{2z^{5/2}}-\frac1{z^{3/2}}\right)
e^{-\pi(2k+1)^2/(4z)}. \tag{19}
\]
Это derivative по z от `theta_4(0|iz)`; второе равенство — точное DLMF 20.7.33 с theta_2 series. Principal powers положительны на `z>0`.

Чтобы не подменить плотность одноимённой theta-функцией, проверим её Laplace-transform. Для `c>0`, обычный Gaussian integral даёт
\[
\int_0^\infty e^{-st}\frac{c}{2\sqrt\pi t^{3/2}}e^{-c^2/(4t)}dt=e^{-c\sqrt s}.
\]
Дифференцирование по c и умножение на `2 sqrt(pi)` дают transform одного члена второго ряда (19):
`2 sqrt(pi s) exp(-(2k+1)sqrt(pi s))`.
Суммирование даёт ровно `sqrt(pi s)/sinh(sqrt(pi s))=L(s)`.
Абсолютная перестановка для каждого `s>0` законна: модуль каждого члена ограничивается суммой двух положительных Gaussian-integral членов; их интегралы имеют геометрическое затухание по `2k+1`, с не более чем линейным prefactor. Laplace-uniqueness после фиксированного положительного экспоненциального наклона идентифицирует (19) с полной h из nu. Здесь нет предположения о нулях xi.

Для a в любом компакте правой полуплоскости и малого `u>0` второй ряд даёт
\[
|h(au)|\le C u^{-5/2}e^{-c/u};
\]
для `u>=1` первый ряд даёт `|h(au)|<=C e^{-cu}` с, возможно, другими положительными C,c. Оба утверждения получаются отделением половины действительного показателя для суммирования полного ряда. Вместе с `psi(u+v)<=4pi^2(u+v)^(5/2)e^{-pi(u+v)}` они дают интегрируемую локально равномерную мажоранту в (11).

Следовательно J(a,b) голоморфен в произведении двух правых полуплоскостей. То же верно для
\[
\mathcal H(a,b)=J(a,1)J(1,b)/J(1,1)-J(a,b). \tag{20}
\]
Для действительных `0<a,b<1` это в точности `H_psi(ell_a,ell_b)`.

### 7.2. Перенос отрицательного вывода — не расширение домена по желанию

Предположим, что все конечные матрицы mathcal H на `(1/2,1)` PSD. Применим принятый A1 к **этому** голоморфному kernel, реальному интервалу `(0,1)` и его открытому подинтервалу `(1/2,1)`. Тогда все конечные матрицы на `(0,1)` тоже PSD. Это противоречит явному трёхпрофильному свидетелю §6.

Значит
\[
\boxed{\exists m,\ a_1,\ldots,a_m\in(1/2,1),\ c\in\mathbb C^m:
\sum_{i,j}\overline{c_i}\mathcal H(a_i,a_j)c_j<0.} \tag{21}
\]
A1 применяется к all-rank PSD, не к одному положительному determinant. Здесь нет перехода от нескольких вычисленных матриц к универсальному знаку. Контрапозиция использует прямую теорему A1, в которой сохранены смешанные старые/новые узлы и порядок пределов.

Численный rank, узлы и коэффициенты свидетеля (21) **не вычислены**. Это существование строгого отрицательного значения для вспомогательной формы. Оно не является координатами отрицательной строки исходного V. `[ABSTRACT][PAPER]`

## 8. Ограничение на исходные двухфакторные произведения не спасает этот Hodge-шаг

В (4) встречаются продукты `F_ab=ell_a ell_b` с обоими параметрами из `(1/2,1)`. Проверим именно их, а не произвольные функции из более широкой области.

Для фиксированного `a in (1/2,1)` и `b` стремящегося к 1 снизу:
\[
\ell_a\ell_b\longrightarrow\ell_a\quad\text{в }\mathcal D_\psi. \tag{22}
\]
Поточечная сходимость следует из непрерывности h и `ell_1=1`. Для нормы выберем `b_0 in (1/2,1)` так, чтобы `a+b_0>1`. Мажоранта §4 с показателем `-2pi(a+b_0-1)u-2pi v`, вместе с мажорантой для ell_a, интегрируема. Теорема о доминированной сходимости даёт (22).

Если H_psi была бы PSD на линейной оболочке **всех** таких продуктов, применяем её к произвольному конечному набору `ell_{a_i}ell_b` и переходим `b->1-`. Непрерывность (7)–(8) дала бы PSD на всех `ell_{a_i}`, вопреки (21). Таким образом
\[
\boxed{H_\psi\text{ не PSD и на }
\operatorname{span}\{\ell_a\ell_b:1/2<a,b<1\}.} \tag{23}
\]
Это именно однофакторные профили, получающиеся при перемножении **двух полных likelihoods G** в микроскопической энергии. Параметр 1 не незаконно добавлен к исходным узлам: он используется лишь как оплаченный предел профилей с параметром строго меньше 1. Из строгого отрицательного предела следует отрицательность при некотором конечном `b<1`.

Однако коэффициенты продуктов в (4) имеют специальную структуру `bar(c_i)c_j`; произвольный отрицательный вектор H_psi на product-span не обязан иметь эту структуру. Поэтому (23) убивает универсальный primitive-аргумент, **но не** микроскопическую энергию (4) и **не** TARGET (6). `[ABSTRACT][PAPER]`

## 9. Где использована полная theta и что происходит с отрицательным контролем

Источник использован не только словами «положительная плотность»:

1. Полное convolution-tail тождество (9) выведено из всех rates `pi*n^2`, с конечным бюджетом `3/(2pi)`.
2. Экспоненциальный наклон оставляет **каждую** независимую компоненту и даёт точные rates (12). Именно квадратичная решётка даёт концентрацию на масштабе `R` и числовой бюджет (14)–(16).
3. Обе полные theta-серии (19), включая их малый аргумент, оплачивают продолжение к исходному интервалу.
4. В физическом весе остаются `r(T)` и `T>=1`; их цена явно входит в (16).

Для принятого контроля `g_epsilon(x)=exp(epsilon x^2)f(x)`, `epsilon<0`, его естественный lift имеет
\[
G_{x,\epsilon}=e^{\epsilon x^2}T^{\epsilon x}G_x.
\]
При `x!=0` множитель `T^(epsilon x)` неразделим по u,v: равенство cross-products на прямоугольнике требовало бы
`[(u_1+v_1)(u_2+v_2)]^k=[(u_1+v_2)(u_2+v_1)]^k`, `k=epsilon x!=0`, тогда как основания различаются на `(u_1-u_2)(v_2-v_1)`. Это точное различие уже доказано в D §5, здесь оно не считается новым supplier.

Поэтому факторизация, приводящая к (11)–(13), не является той же формулой для деформированного lift. Его дополнительный total-energy вес не превращается в независимые изменённые exponential rates. Но **мы не получили положительную TARGET-оценку даже для undeformed source**: сохранившаяся факторизация не спасает проверяемую Hodge-гипотезу. Называть её достаточным различающим условием знака было бы ошибкой.

Результат Z об отрицательных V-строках деформированных источников остаётся принятой внешней к этому доказательству проверкой. Нового исходного V-свидетеля при `epsilon=0` нет. Простой комплексный нуль диагонали из старого THETARF, старые fixed ports и fixed scale-difference карты здесь не используются. `[ABSTRACT][PAPER]`

## 10. Первый неоплаченный переход и две репрезентации без смены объекта

После отказа (H) не остаётся оплаченного source-sign продвижения TARGET. Точное ещё требуемое утверждение — (6) на **всём** классе finite x_i in I, c_i in C. В условных координатах это нижняя оценка
\[
\boxed{
\int_0^\infty f(X)^2\sum_{i,j}\overline{c_i}c_j
(2X+x_i+x_j)m_i(e^{2X})m_j(e^{2X})\,dX\ge0.} \tag{24}
\]
(24) — только locator остатка, не новая доказанная лемма и не прогресс за переименование. E_micro и оба слагаемых E_loss сохранены в (4)–(6).

Две допустимые репрезентации того же остатка для решения владельца, не авторизация второго опыта:

| Представление | Что проверяет | Оценка силы / стоимости |
|---|---|---|
| Условные fibres `T=t`: полная матрица `Sigma_ij(t)` вместе с `2X+x_i+x_j` и матрицей средних `m_i m_j` | Может сохранить нужную компенсацию, не требуя одноположительности Q_psi | сила 10/10; стоимость исходной оценки 9/10 |
| Исходный shift-flux `2 Re <P_c,Q_c>` с точными two-energy likelihoods как средством вычисления, но без primitive projection | Проверяет именно all-complex source-sign; не требует старой RF или простоты xi | сила 10/10; стоимость 9/10 |

Это качественные оценки, не измерения и не сроки. Ни одна репрезентация не поставляет здесь положительного бюджета.

**DISCRIMINATOR для нуль-совместимого результата:** для выбранного допустимого конечного ряда нужны нижняя/верхняя огибающие **полного** `E_micro-E_loss`, с совместным учётом mixed covariance, интегрального хвоста и точных зависимостей коэффициентов. Малость отдельно E_micro, E_loss или eigenvalues Sigma не определяет знак их разности. Для нынешнего scoped KILL нуль-неопределённости нет: (1) имеет строгую отрицательную верхнюю границу. `[ABSTRACT][CONDITIONAL]`

## 11. Сильнейшие возражения и проверка границ

**«Ты получил отрицательную V?»** Нет. (1), (21), (23) относятся к H_psi. Никакого тождества `V=H_psi` нет. Разность (6) не оценивается отрицательно.

**«Это чужой artificial kernel?»** Нет для Q_psi: он получается буквально из `w dmu` в (2), а свидетели построены из фактических ell_a. K_* — только явно контролируемый предел с бюджетом (16), не замена источника.

**«Снова неподходящие узлы вне интервала?»** Прямой свидетель действительно вне I. Поэтому §7 отдельно доказывает голоморфность и применяет all-rank A1; §8 отдельно возвращает обе множительные likelihood-координаты в требуемый интервал. Без этих разделов локальный KILL не был бы обоснован.

**«Поэлементная ошибка снова выдана за operator bound?»** Нет. Коэффициенты e,z фиксированы до проверки, их l1-цена полностью умножена на 15/sqrt(R). Только на этой фиксированной двухмерной плоскости применяется (18). Никакой размер-независимой оценки отсюда не следует.

**«Могла ли отрицательная primitive-форма компенсироваться?»** Да в полном TARGET. Поэтому удалён только универсальный Hodge-промежуточный знак. Специальный cone аргумент, иная correction или сама ковариационная компенсация не исключены.

**«Не пропал малый T, нарушающий cutoff?»** Нет: единица в §5.2 оплачивает весь `T<1`, а `Bcal`-разность оплачивает весь `T>=1`. Центральные и смешанные участки не выкинуты.

**«Не спрятан ли новый оператор с неоплаченным domain?»** Нет. Q_psi непрерывна на явно заданном L2-пространстве, а G_c и B_c определены конечными списками. Генераторы и замыкания не предполагаются.

**«Доказана невозможность всякой Brownian-энергии?»** Нет. Убит только перенос одноположительной copy-reflection формы на данный физический вес с последующим удалением одного направления. `[ABSTRACT][PAPER]`

## 12. K8A, регистрация и closeout

| Поле | Значение |
|---|---|
| DOWNSTREAM_CONSUMER | W Theorem T, после all-node V positivity; published Weil criterion |
| ACTUAL_CONSUMER_REQUIREMENT | V[c]>=0 для всех конечных реальных узлов и всех комплексных коэффициентов |
| ORIGINAL_REQUESTED_OBJECT | TARGET на I через полные simultaneous-dilation likelihoods |
| ORIGINAL_OBJECT_IS | PROVED_NECESSARY; обратная достаточность следует из принятого A1–A2; **не** заменяется Hodge-промежуточной гипотезой |
| TESTED_MECHANISM_PREMISE | H_psi>=0 на span исходных likelihoods/products |
| INTERMEDIATE_IS_NECESSARY_FOR_CONSUMER | UNKNOWN; необходимость не доказана и в consumer не включается |
| FAILURE_TYPE | COUNTEREXAMPLE для intermediate; NO_DERIVATION для TARGET |
| EPISTEMIC_STATUS | точная intermediate theorem-shape опровергнута кандидатом; TARGET — RESEARCH_DEBT |
| KILL_SCOPE | THEOREM_SHAPE |
| KILL_EVIDENCE | (1), с явными (12)–(18); затем (19)–(23) для исходного интервала |
| KNOWN_WEAKER_INTERFACE | непосредственно (24), сохраняя обе части условной ковариации; достаточно по D/A/W |
| NOVELTY_AXIS | физически взвешенный Brownian reflection имеет второе положительное направление на actual likelihood-span; общей библиографической новизны не заявлено |
| REOPEN_TRIGGER_TARGET | независимая оценка полного mixed conditional remainder, не предполагающая (H) |
| REOPEN_TRIGGER_HODGE | только изменение точной intermediate-формы/класса с новым source identity; нынешнюю (H) не переименовывать |

Математическое чтение и первичная paper-идея предшествовали Appendix-B регистрации. Регистрация предшествовала новому algebraic calibration. Она не выдаётся за независимую timestamp-квитанцию или за запись до первого размышления. Ставки не изменены после результата.

| Prediction | Fate |
|---|---|
| P1: две положительные размерности взвешенной формы на actual likelihood-span | CONFIRMED_BY_DERIVATION_AND_FIXED_EXACT_CALIBRATION; независимый приём ожидается |
| P2: полный наклон `L(pi/a)` и предел `((s+t)/2)^(5/2)` | CONFIRMED; усилено явным 15/sqrt(R) бюджетом |
| P3: фиксированные s=(1,17/16,9/8) и зарегистрированный finite-difference vector дают положительную плоскость | CONFIRMED_BY_EXACT_RATIONAL_BRACKETS; новых узлов после проверки не выбиралось |
| P4: полный TARGET | UNRESOLVED; ни одна истинностная ставка задним числом не объявляется подтверждённой |

Что стало меньше: исключён точный перенос прежнего одноположительного Hodge-закона на физическую условную задачу, даже после ограничения actual likelihood products. Что не стало меньше: область требуемого знака V и полный TARGET. Что не повторять: переносить primitive positivity через положительный, но зависящий от суммы вес без проверки индекса; забывать специальную матрицу covariance или объявлять условное среднее изометрией.

Исторический source-sign no-delta предлагается **10 -> 11** после независимого приёма; после последнего указания владельца completed attempts **1 -> 2**. Новый исходный знаковой supplier не создан, поэтому сброса нет. Состояние репозитория и счётчики автор не меняет. Cognitive operator: **COUNTEREXAMPLE_HUNT**. Route score: 4 для scoped falsification, не оценка близости RH.

Memory entry: физический weight превращает fractional sum kernel в `1_(T>=1) T^(3/2) r(T)`; точный экспоненциальный наклон всей Brownian-решётки выявляет индекс не меньше двух. Отрицательная primitive-энергия не равна отрицательной полной условной форме.

## 13. Одна директива независимой проверки и публикация

**CODEX DIRECTIVE:** независимо проверить только этот завершённый weighted-Hodge механизм: (2), все факторы (13), полные moment/cutoff бюджеты (14)–(16), ограниченную двухмерную цену entry errors, отрицательный primitive-вектор (1), идентификацию h и аналитичность (19)–(20), применение A1 и product-limit (22). Выполнить Appendix A без изменения исходника. Успех приёма: `ACCEPT_WEIGHTED_BROWNIAN_HODGE_INDEX_OBSTRUCTION_ONLY`; при отказе назвать первое неверное равенство/границу, не подменяя его отсутствием полного RH-доказательства. Не запускать новую covariance-кампанию, не повышать TARGET/V/IC/ODD2/RH и не менять registry/runtime из этого отчёта.

Сначала этот самостоятельный Markdown сохранён локально. Единственная разрешённая remote-запись — новый файл из YAML на `codex_mac/math-proshka-20260912`, commit subject с `[Proshka]`. Точный resulting commit SHA не включается в собственное содержимое коммита: после Contents API он возвращается в чат и проверяется чтением blob. Никаких Lean-файлов нет; Lean build и axiom profile **NOT_RUN / NOT_APPLICABLE**, не стандартная тройка по умолчанию. Независимый gate меняет лишь PAPER-кандидат на принятый scoped PAPER-результат, а не на Lean theorem или RH admission.

Ни поиск инструментов, ни техническая публикация не служат математическим аргументом. Старый SOURCEENERGY-отчёт и другие файлы не публикуются и не изменяются в этой транзакции.


## Appendix A. Исполненная рациональная проверка

Команда в рабочем окружении: `python /mnt/data/brownianjoint/check_limit.py`.
Для независимого запуска сохрани следующий блок как `check_limit.py` и выполни
`python check_limit.py`. `DIGITS=50` задаёт длину рациональных sqrt-скобок,
не число theta-мод. `R=10**24` — один заранее выбранный доказательный параметр;
`s`, `e`, `z` — буквальные узлы и векторы §6. Менять их для воспроизведения
не требуется. Для другого рабочего каталога замени только путь к скрипту:
`python {рабочая_папка}/check_limit.py`, например
`python /tmp/brownianjoint/check_limit.py`.

Python integer arithmetic и проверяемые квадраты рациональных концов — весь
арифметический механизм. Decimal, floating point, interval quadrature,
root-finding, исходные узлы theta и матрицы V не используются. Код проверяет
фиксированные константы; аналитические (12)–(16) нужно проверить отдельно.

```python
"""Exact rational brackets for one fixed limiting 3-node test. No theta sampling."""
from fractions import Fraction as Q
from math import isqrt

DIGITS = 50
SCALE = 10 ** DIGITS

def sqrt_bounds(x: Q):
    assert x > 0
    n = isqrt((x.numerator * SCALE * SCALE) // x.denominator)
    lo, hi = Q(n, SCALE), Q(n + 1, SCALE)
    assert lo*lo <= x <= hi*hi
    return lo, hi

def add(a,b): return a[0]+b[0],a[1]+b[1]
def mul(a,b):
    z=[x*y for x in a for y in b]
    return min(z), max(z)
def scale(a,c): return mul(a,(c,c))
def neg(a): return -a[1],-a[0]
def sub(a,b): return add(a,neg(b))
def quotient(a,b):
    assert b[0] > 0
    return mul(a,(1/b[1],1/b[0]))

s=[Q(1),Q(17,16),Q(9,8)]
M=[]
for u in s:
    row=[]
    for v in s:
        t=(u+v)/2
        row.append(scale(sqrt_bounds(t),t*t))
    M.append(row)
e=[Q(1),Q(0),Q(0)]
z=[Q(4495,16),Q(-536),Q(256)]
def form(u,v):
    out=(Q(0),Q(0))
    for i in range(3):
        for j in range(3): out=add(out,scale(M[i][j],u[i]*v[j]))
    return out
A,B,D=form(e,e),form(e,z),form(z,z)
Schur=sub(D,quotient(mul(B,B),A))
assert A[0] == 1
assert D[0] > Q(1,4)
assert Schur[0] > Q(1,4)
assert abs(B[0]) < Q(1,8) and abs(B[1]) < Q(1,8)
assert D[1] < 1

# Rigorous coarse endpoints, not floating-point values.
print('LIMIT_NODES=1,17/16,9/8; h=1/16')
print('LIMIT_TEST_VECTOR=4495/16,-536,256')
print('LIMIT_Q00=1')
print('LIMIT_ABS_Q01<1/8: PASS')
print('LIMIT_Q11>1/4: PASS')
print('LIMIT_SCHUR>1/4: PASS')
print('LIMIT_Q11<1: PASS')
# Positive index calibration in exact derivative coordinates.
J=[[Q(1),Q(5,4),Q(15,16)],[Q(5,4),Q(15,16),Q(15,64)],
   [Q(15,16),Q(15,64),-Q(15,256)]]
def det3(K):
    return sum((1 if p%2==0 else -1)*K[0][i]*K[1][j]*K[2][k]
               for p,(i,j,k) in enumerate([(0,1,2),(0,2,1),(1,2,0),(1,0,2),(2,0,1),(2,1,0)]))
assert det3(J)==-Q(75,256)
print('LIMIT_JET_DETERMINANT=-75/256')
# Planted false Hodge sign: beta=5/2 has two positive directions.
v=[Q(15,16),-Q(3,2),Q(1)]
vv=sum(v[i]*J[i][j]*v[j] for i in range(3) for j in range(3))
ev=sum(J[0][j]*v[j] for j in range(3))
assert vv==Q(15,32) and ev==0
print('PLANTED_ONE_POSITIVE_DIRECTION_FALSE: DETECTED; primitive_Q=15/32')
# Full-source asymptotic loss for the one registered three-node family.
R=10**24
error=Q(15,10**12)
L=sum(abs(t) for t in z)
assert L < 1073
# Perturbation of the 2x2 plane in coefficient Euclidean norm is bounded
# by entrywise error times 1 + ||z||_1^2, via the outer-product majorant.
plane_error=error*(1+L*L)
assert plane_error < Q(1,1000)
# Matrix [[1,B],[B,D]] is >= 1/8 I since |B|<1/8 and D>1/4.
assert Q(1,8)-plane_error > Q(1,9)
print('R=1000000000000000000000000')
print('ENTRY_ERROR<=15/10^12; PLANE_ERROR<1/1000: PASS')
print('FULL_SOURCE_POSITIVE_PLANE_FLOOR>1/9: PASS')
print('THETA_EVALUATIONS=0; QUADRATURES=0; SOURCE_RANK_SWEEPS=0; LEAN_RUNS=0')
```

Буквальный stdout успешного запуска (stderr пуст, exit 0):

```text
LIMIT_NODES=1,17/16,9/8; h=1/16
LIMIT_TEST_VECTOR=4495/16,-536,256
LIMIT_Q00=1
LIMIT_ABS_Q01<1/8: PASS
LIMIT_Q11>1/4: PASS
LIMIT_SCHUR>1/4: PASS
LIMIT_Q11<1: PASS
LIMIT_JET_DETERMINANT=-75/256
PLANTED_ONE_POSITIVE_DIRECTION_FALSE: DETECTED; primitive_Q=15/32
R=1000000000000000000000000
ENTRY_ERROR<=15/10^12; PLANE_ERROR<1/1000: PASS
FULL_SOURCE_POSITIVE_PLANE_FLOOR>1/9: PASS
THETA_EVALUATIONS=0; QUADRATURES=0; SOURCE_RANK_SWEEPS=0; LEAN_RUNS=0
```

## Appendix B. Буквальная регистрация перед вычислительной проверкой

```text
REQ-2026-09-13-BROWNIANJOINT
Scope: one weighted-copy-reflection Hodge mechanism on the actual dilation likelihoods.
This registration precedes the new algebraic calibration and any source computation.
It records the proposed test after initial paper inspection, not before all reasoning.
P1 (0.95): the physically weighted reflection kernel has at least two positive
    directions on the span of exact one-energy likelihoods. A rank-one primitive
    projection therefore cannot remain positive on the whole likelihood span.
P2 (0.95): the exact exponential tilt L(pi/a) at a=(R*s)^(-2) makes (U/a)/R
    converge in moments to s/2, using the full product with rates pi*n^2.
    The weighted reflection limit after positive congruence is ((s+t)/2)^(5/2).
P3 (0.90): the limit kernel on s=(1,17/16,9/8), with evaluation and the
    fixed finite-difference functional (15/16)*ev_1-(3/2)*D_h+D_h^2,
    h=1/16, has a positive two-dimensional restriction.
P4 (UNRESOLVED): a weighted primitive-form failure does not decide the full
    E_micro-E_loss. No negative V row is predicted or claimed.
No theta evaluations, source matrix sweep, polynomial/Hankel campaign,
new comparison carrier, spin model, or assumed zero location is authorized.
```

## Appendix C. Манифест воспроизведения

Все следующие hashes относятся к сохранённым локальным UTF-8 bytes с конечным LF.
Это не хеши внешних источников и не независимая acceptance-квитанция.

| Файл | Bytes | LF | SHA-256 |
|---|---:|---:|---|
| `check_limit.py` | 2831 | 85 | `f583cfdc918f3b6548f7b6e538eda8cf508fbe596fb9d932a68c41019fed2de8` |
| `check_limit.stdout` | 448 | 13 | `dc177ecb7c63b4110470b5ded6fb90638e2f9c66964d604a3e1ecfe2b9faa7f8` |
| `preregistration.txt` | 1240 | 17 | `626d28d5e059b42434612c440489bff03ed0fc5fa6fb2e551fb3c9df418f1958` |

Новый полный ответ заканчивается здесь. `KILL_NAMED_CONDITIONAL_MECHANISM`
относится только к физически взвешенному rank-one Hodge-промежуточному знаку.
Полная оценка условной ковариации, сам V и RH остаются открытыми.
