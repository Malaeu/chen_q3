# STATUS: RUN_NAMED_VARIANCE_NULL_CORRECTION
```yaml
OPERATIVE_CLASS: RUN_NAMED_VARIANCE_NULL_CORRECTION
REQUEST_ID: REQ-2026-09-13-NULLVAR
BOUNDARY_ID: GOAL058_FULL_THETA_VARIANCE_NULL_CORRECTION
REQUEST_COMMIT: 46c1b471e4ddf7d5b2f27270a986cd8401e79711
REQUEST_BLOB: 2a12a68e0ea6ad4d74a3889cd3d6e80d10ad31ed
SOURCE_BASE: e6065e50b0e8201cb9b5afd042e67123d643b3d9
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
HONESTY_STATE: CHALLENGER_NOT_RH
RESULT: FULL_N1_N2_WITH_ABSOLUTE_DOMAINS_AND_EXACT_CORRECTION_ACCOUNTING
N1: PAPER_DERIVED_PENDING_INDEPENDENT_ACCEPTANCE
N2: PAPER_DERIVED_PENDING_INDEPENDENT_ACCEPTANCE
BOUNDARY_AT_ZERO: RETAINED
BOUNDARY_AT_INFINITY: PROVED_ZERO
ALL_FINITE_COMPLEX_FAMILIES_IN_REQUESTED_INTERVAL: COVERED
NEW_TARGET_SIGN_SUPPLIER: false
TARGET_PROVED: false
TARGET_REFUTED: false
ACTUAL_V_NEGATIVE_WITNESS: false
KILL_SCOPE: NONE
AUTOPSY_DROPPED: COUPLING
FAILURE_TYPE_TARGET: NO_DERIVATION
EPISTEMIC_STATUS_TARGET: RESEARCH_DEBT
PROGRESS_CLASS: PROOF_PROGRESS_AT_NULL_IDENTITY_SCOPE_ONLY
COGNITIVE_OPERATOR: MINIMAL_LEMMA
SCOPE: ABSTRACT
VERIFIER: PAPER
LEAN_VERIFIED: false
INDEPENDENT_REVIEW_PERFORMED_BY_PRODUCER: false
THETA_EVALUATIONS: 0
QUADRATURES: 0
SOURCE_MATRIX_SWEEPS: 0
GLOBAL_IC: OPEN_UNCHANGED
GLOBAL_ODD2: OPEN_UNCHANGED
ALL_ORDER_SOURCE_SIGN: OPEN_UNCHANGED
FIXED_TWOCHANNEL_RF: PREVIOUSLY_REFUTED_NOT_REOPENED
PX_RH_CLAIM: NOT_MADE
CANONICAL_ADMISSION: false
SOURCE_SIGN_NO_DELTA:
  inherited: 11
  proposed: 11
  reason: bounded_null_identity_task_not_a_new_full_sign_attempt
  state_changed: false
PUBLICATION_BRANCH: codex_mac/math-proshka-20260912
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_NULLVAR_2026-09-13.md
```

AUTOPSY: dropped=COUPLING; note=No term is dropped in the proved identities. The still-unpaid sign step is a lower comparison of the complete corrected microscopic account with the complete corrected covariance account. A total derivative changes both accounts equally after its boundary is included; an unprojected transport insertion additionally changes the target by an explicit mean-boundary and score-commutator term.

## 1. Итог и источники

**N1 и N2 верны буквально с коэффициентами запроса.** Ни граничный член при `X=0`, ни производная физического веса, ни смешанная ковариация не исчезают. Ниже доказаны абсолютная интегрируемость отдельных слагаемых и нулевой след на бесконечности для каждой допустимой конечной комплексной семьи. Это **PAPER-кандидат**, ожидающий независимой проверки, не Lean-теорема.

**Знак полной V не получен.** Нулевые тождества предоставляют закон перераспределения уже существующих членов, а не положительную энергию. В частности, они выполняются и для предусмотренных отрицательных Gaussian-деформаций. `[ABSTRACT][PAPER]`

Используются ровно следующие закреплённые материалы. Запрос и H/D прочитаны целиком; B прочитан с продолжениями вплоть до конца Appendix C. Рекурсивные архивы, старые численные сертификаты и старый SOURCEENERGY не перечитывались и не запускались.

| ID | Путь от корня Malaeu/chen_q3 | Ref | Git blob, подтверждённый чтением |
|---|---|---|---|
| REQ | `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_NULLVAR_2026-09-13.txt` | request commit выше | `2a12a68e0ea6ad4d74a3889cd3d6e80d10ad31ed` |
| H | `docs/Codex/REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md` | request commit | `4efa5a319d89a7c215f6d8c8a746e197d173185b` |
| D | `docs/Codex/REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md` | SOURCE_BASE | `46d295269a62e4e951f6ab0f0b0ba2d22b537166` |
| B | `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_BROWNIANJOINT_2026-09-13.md` | SOURCE_BASE | `13712f57dd748118c9dad33d874eba4cdd0c85ee` |

SHA256 из управляющего запроса: H — `7aaf8e43faa5bfd37954d6076db3acb1801325777bd9d989b25d75c9a9466c14`; D — `8ea7ed0b70f57d271b09cb44f53156cd50b71aa6511bd1fd4077111ba5bef5ef`; B — `a80f2a563788e72cd694cf61ad8fc3fe1e53f5517c54c7217a70f33ab5a91d36`. Это закреплённые контрольные суммы, **не заявление о новом локальном пересчёте SHA256 этих трёх remote-файлов**. Их ref/path и возвращённые blobs проверены непосредственно. Внутренние ссылки вида `[H:R8]` далее относятся к этой таблице, не к плавающей ветке.

Bootstrap прочитан через GitHub из `rh_clean`: `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. Текущий pinned TXT, непосредственно заданный владельцем, определяет задачу.

Из внешнего первоисточника сверены только Saumard–Wellner, arXiv:1711.00668v3, Lemma 2.1, (2.4)–(2.5), HTML section 2: `https://arxiv.org/html/1711.00668v3`. Это словарь для уже принятого Green-представления ковариации, не новый поставщик знака. PDF не использовался; полного чтения статьи и хеша её HTML здесь не заявляется. Новые N1/N2 выводятся ниже непосредственно.

## 2. Неизменные определения

Сохраняем полный источник
\[
\Phi(x)=\sum_{n\ge1}(4\pi^2n^4e^{9x/2}-6\pi n^2e^{5x/2})e^{-\pi n^2e^{2x}},
\quad A=\|\Phi\|_2,
\quad f=\Phi/A.
\tag{1}
\]
`Z=int Phi` и `A` различны. Из D/B наследуем полный закон
\[
U=\sum_{n\ge1}E_n/(\pi n^2),\quad \nu(du)=h(u)du,\quad r=h*h,
\quad \Phi(X)=t^{5/4}r(t),\quad t=e^{2X},
\]
\[
C=\mathbb E(U+U')^{1/4}=2Z,\quad
 d\mu=C^{-1}(u+v)^{1/4}h(u)h(v)du\,dv.
\tag{2}
\]
Условие `T=u+v=t`, координата `s=u/t`, даёт
\[
p_t(s)=\frac{t h(ts)h(t(1-s))}{r(t)},\qquad 0<s<1.
\tag{3}
\]
Все ожидания `E_t` ниже используют именно эту вероятность. Для комплексных функций
\[
\operatorname{Cov}_t(v,z)=\mathbb E_t\overline{(v-\mathbb E_tv)}(z-\mathbb E_tz).
\]
Первый аргумент сопрягается.

Фиксируем произвольные `n>=1`, `x_i in I=(-(log 2)/2,0)`, `c_i in C`, и положим
\[
a_i=e^{2x_i}\in(1/2,1),\qquad
 g_i(t,s)=a_i^{9/4}\frac{h(a_its)h(a_it(1-s))}{h(ts)h(t(1-s))},
\]
\[
g=\sum_i c_i g_i,\quad b=\sum_i c_i x_i g_i,\quad
m=\mathbb E_tg,\quad z=g-m,\quad F=\mathbb E_t|z|^2.
\tag{4}
\]
Точка над функцией означает `partial_X` при **фиксированном s**. Обозначим
\[
q(X)=f'(X)/f(X),\quad \rho=\partial_X\log p_t,
\quad \omega_g=\mathbb E_t(\rho g).
\tag{5}
\]
Реальная положительность f делает q определённой на всей вещественной оси; на m или F нигде не делим. Из H:R6–R7
\[
\mathbb E_t\rho=0,\qquad m'=\mathbb E_t\dot g+\omega_g.
\tag{6}
\]

Физический вес после условного интегрирования — **ровно** `f(X)^2 dX`, `X>=0` [D:§§3–4]. Сократим обозначения двух полных счетов:
\[
\mathsf M=2\int_0^\infty f^2\{X\mathbb E_t|g|^2+\Re\mathbb E_t(\bar g b)\}\,dX,
\]
\[
\mathsf L=2\int_0^\infty f^2\{XF+\Re\operatorname{Cov}_t(g,b)\}\,dX,
\qquad V[c]=\mathsf M-\mathsf L.
\tag{7}
\]
Эти равенства — принятый точный source fit, не новое доказательство знака. `[ABSTRACT][PAPER]`

## 3. Полный источник оплачивает производную likelihood на всей полуоси

Это новая проверка домена, необходимая сверх локального по t дифференцирования H:R7.

Из B:(9),(19) и H:R2–R8 сохраняем
\[
h(u)=2\pi e^{-\pi u}\chi(u),\quad 0<\chi(u)\le1,\quad \chi'\ge0,
\quad J(t)=\int_0^t\chi(u)\chi(t-u)du,
\]
\[
r(t)=4\pi^2e^{-\pi t}J(t),\quad t-c_0\le J(t)\le t\ (t\ge1),
\quad c_0=3/(2\pi)<1.
\tag{8}
\]
В частности, `chi(0)=0`. Нужные оценки на концах следуют из **двух полных** рядов B:(19):
\[
h(u)=2\pi\sum_{n\ge1}(-1)^{n+1}n^2e^{-\pi n^2u}
=\sum_{k\ge0}\left(\frac{\pi(2k+1)^2}{2u^{5/2}}-\frac1{u^{3/2}}\right)
e^{-\pi(2k+1)^2/(4u)}.
\tag{9}
\]
В частности, при `u->0+`
\[
h(u)=\frac\pi2u^{-5/2}e^{-\pi/(4u)}[1-2u/\pi+O(e^{-2\pi/u})],
\quad b_0(u):=u\chi'(u)/\chi(u)=\pi/(4u)-5/2+O(u).
\tag{10}
\]
При `u->infinity` имеем `chi(u)=1+O(e^{-3pi u})`, `b_0(u)=O(u e^{-3pi u})`. Здесь употребляются доказанные в H оценки дифференцированных остатков: после выделения первого малого-аргументного показателя остальные имеют `exp(-pi k(k+1)/u)`; их фиксированные производные ограничиваются суммой полиномов, умноженных на тот же экспоненциальный хвост. Поэтому (10) **не дифференцирование неизвестного O-члена**.

Для каждого фиксированного `a in (1/2,1)` определим
\[
R_a(u)=\chi(au)/\chi(u),\quad
D_a=\sup_{u>0}R_a(u)|b_0(au)-b_0(u)|.
\tag{11}
\]
**D_a конечна.** Действительно, `0<R_a<=1`. При нуле
\[
R_a(u)=a^{-5/2}\exp[-\kappa_a/u](1+O(u)),
\quad \kappa_a=\frac\pi4(1/a-1)>0,
\]
так что произведение в (11) стремится к нулю даже после множителя `O(1/u)`. На бесконечности разность b_0 стремится к нулю. На каждом промежуточном компакте она непрерывна. Это доказывает конечность супремума из полного источника; численное значение не требуется и не заявляется.

При `u=ts`, `v=t(1-s)` получаем точную производную
\[
\dot g_i=2g_i\{\pi(1-a_i)t+b_0(a_i u)-b_0(u)+b_0(a_i v)-b_0(v)\}.
\tag{12}
\]
Определим конечные, не зависящие от X и s, константы
\[
a_* =\min_i a_i>1/2,\quad \lambda=\pi(1-a_*),\quad \beta=2\pi-2\lambda=2\pi a_*>\pi,
\]
\[
K_0=\sum_i|c_i|a_i^{9/4},\quad K_b=\sum_i|c_ix_i|a_i^{9/4},
\quad K_1=\sum_i2|c_i|a_i^{9/4}[\pi(1-a_i)+2D_{a_i}].
\tag{13}
\]
Тогда для **всех** `t>=1`, `0<s<1`
\[
|g|\le K_0e^{\lambda t},\quad |b|\le K_be^{\lambda t},\quad
|\dot g|\le K_1(1+t)e^{\lambda t}.
\tag{14}
\]
Для последней оценки перемножаем (12) с точными R_a(u)R_a(v); каждый член разности b_0 ограничивается D_a, а другой R_a не больше единицы. Таким образом, особенности score при `u=0` не выбрасываются.

Те же малые-аргументные оценки показывают: при t в любом положительном компакте g_i и нужные производные гладко и плоско продолжаются нулём к `s=0,1`. Все производные p_t имеют интегрируемые экспоненциальные мажоранты на концах. Это оплачивает локальное дифференцирование под E_t, в том числе в окрестности `t=1`. `[ABSTRACT][PAPER]`

## 4. Абсолютный интегральный домен и явная форма полного хвостового бюджета

Из (8), с учётом `dX=dt/(2t)`,
\[
f(X)^2\le C_f t^{9/2}e^{-2\pi t},\qquad C_f=16\pi^4/A^2.
\tag{15}
\]
Кроме того,
\[
J'(t)=\int_0^t\chi(u)\chi'(t-u)du\in[0,1],
\]
поскольку `chi(0)=0`, `chi<=1` и `int_0^t chi'=chi(t)<=1`. Следовательно
\[
q=5/2-2\pi t+2tJ'/J,\qquad
|q|\le C_q t,\quad C_q=5/2+2\pi+2/(1-c_0),\quad t\ge1.
\tag{16}
\]
Это оценка производной **полной** Phi. Никакая первая мода не подставлена в q.

Положим, как в H:R8,
\[
M_\chi=\int_0^\infty\frac{u^2\chi'(u)^2}{\chi(u)}du<\infty,
\quad I(t)=\mathbb E_t\rho^2\le\frac{16M_\chi}{t-c_0},
\quad I_* =16M_\chi/(1-c_0).
\tag{17}
\]
Конечность M_chi и оценка I — принятые полные исходные леммы. Их численная оценка не предполагается.

Из (14), Jensen и Cauchy–Schwarz следуют
\[
F\le K_0^2e^{2\lambda t},\quad
|\operatorname{Cov}_t(g,\dot g)|\le K_0K_1(1+t)e^{2\lambda t},
\]
\[
\mathbb E_t[|\rho|\,|z|^2]
\le\sqrt{I(t)}(\mathbb E_t|z|^4)^{1/2}
\le4K_0^2\sqrt{I(t)}e^{2\lambda t},
\]
\[
|\operatorname{Cov}_t(g,b)|\le K_0K_be^{2\lambda t},\qquad
|\omega_g|\le\sqrt{I(t)F}.
\tag{18}
\]
Здесь `|z|<=2K_0 exp(lambda t)`; поэтому оценка score-члена контролирует его **абсолютное условное ожидание**, не только его знаковую сумму.

Каждое сохраняемое слагаемое N1 абсолютно интегрируемо. Например, сумма модулей его трёх подынтегральных членов не больше
\[
C_f K_\Sigma\, t^{9/2}(1+t)e^{-\beta t},\quad
K_\Sigma=2K_0K_1+4K_0^2\sqrt{I_*}+2C_qK_0^2.
\tag{19}
\]
То же, с другой явной комбинацией K_0,K_b,K_1,C_q,I_*, верно для (7), `f^2|m m'|`, `f^2|m\omega_g|` и полных производных вторых моментов. В частности,
\[
f^2F\in L^1(0,\infty),\quad
\lim_{X\to\infty}f(X)^2F(X)=0.
\tag{20}
\]
Более точно, при `t_L=e^{2L}`, `L>=0`, из (19)
\[
\int_L^\infty |\text{каждый член N1}|\,dX
\le C_f K_\Sigma\, e^{-\beta t_L}
\sum_{j=0}^5\frac{5!}{j!}\frac{t_L^j}{\beta^{6-j}}.
\tag{21}
\]
Действительно, после замены переменной `(t^{7/2}+t^{9/2})/2<=t^5` при `t>=1`; затем пять интегрирований по частям вычисляют полный экспоненциальный хвост. Все константы конечны и определены источником и заданной конечной строкой. Они не являются численными сертификатами или общим по rank полом.

Отдельно для следа используется
\[
0\le f(X)^2F(X)\le C_fK_0^2t^{9/2}e^{-\beta t}\longrightarrow0.
\tag{22}
\]
При X=0, то есть t=1, (14) и гладкость дают конечный правый след. Индикатор `X>=0` не дифференцируется как гладкая функция: его вклад сохраняется именно как этот след. `[ABSTRACT][PAPER]`

## 5. N1: сначала точная производная, затем полный интеграл

Пусть `A_2(X)=E_t|g|^2`. Законность дифференцирования уже оплачена §3. Тогда
\[
A_2'=2\Re\mathbb E_t(\bar g\dot g)+\mathbb E_t(\rho|g|^2),
\quad m'=\mathbb E_t\dot g+\omega_g.
\]
Вычитаем производную `|m|^2`. Используя `E_t rho=0`, получаем
\[
\boxed{F'=2\Re\operatorname{Cov}_t(g,\dot g)+\mathbb E_t(\rho|g-m|^2).}
\tag{23}
\]
Член с производной m не потерян: именно он превращает `E rho|g|^2` в `E rho|g-m|^2`.

Положим
\[
B_\partial=f(0)^2F(0),\quad
J_{\rm tr}=2\int_0^\infty f^2\Re\operatorname{Cov}_t(g,\dot g)dX,
\]
\[
J_{\rm sc}=\int_0^\infty f^2\mathbb E_t(\rho|z|^2)dX,\quad
J_{\rm wt}=2\int_0^\infty f^2qF\,dX.
\tag{24}
\]
По §4 все четыре величины конечны, причём каждый интеграл абсолютно сходится. На конечном отрезке
\[
f(L)^2F(L)-f(0)^2F(0)=\int_0^L f^2[2\Re\operatorname{Cov}_t(g,\dot g)+\mathbb E_t(\rho|z|^2)+2qF]dX.
\]
Переход `L->infinity` по (19)–(22) даёт
\[
\boxed{B_\partial+J_{\rm tr}+J_{\rm sc}+J_{\rm wt}=0.}
\tag{N1}
\]
Итак, `f^2F` имеет интегрируемую производную и принадлежит `W^{1,1}` на полуоси; (N1) — формула следов, не условно сходящаяся перестановка интегралов. `[ABSTRACT][PAPER]`

### Граница действительно может быть ненулевой у нашей theta

Возьми один любой `x in I`, коэффициент 1. Функция `g_x(1,s)` положительна при `0<s<1` и непрерывно стремится к нулю на обоих концах. Она не константа; p_1 положительна внутри. Поэтому
\[
F_x(0)=\tfrac12\iint p_1(s)p_1(z)|g_x(1,s)-g_x(1,z)|^2ds\,dz>0.
\tag{25}
\]
Для строгого вывода достаточно двух малых интервалов: около `s=1/2`, где значение отделено от нуля, и достаточно близко к нулю, где оно меньше половины первого значения. Оба имеют положительную p_1-меру. Значит, если удалить границу из N1, оставшийся интеграл равен **строго отрицательному** `-B_partial`. Это проверка ложного сокращения на полном источнике, не отрицательная V-строка.

## 6. Деформированный полный домен

Для фиксированного `epsilon<0` положим
\[
A_\epsilon=\|e^{\epsilon X^2}\Phi\|_2\in(0,\infty),\quad
f_\epsilon=(A/A_\epsilon)e^{\epsilon X^2}f,
\quad q_\epsilon=q+2\epsilon X,
\]
\[
k_i=e^{\epsilon x_i^2}t^{\epsilon x_i},\quad
 g_\epsilon=\sum_i c_i k_i g_i,\quad b_\epsilon=\sum_i c_i x_i k_i g_i,
\quad \nabla_X^\epsilon g_\epsilon=\sum_i c_i k_i\dot g_i.
\tag{26}
\]
Именно `A_epsilon`, не Z, нормирует физическую форму контроля. p_t и rho остаются исходными.

Пусть `kappa=max_i epsilon*x_i>=0`. Введи K_{0,epsilon},K_{b,epsilon},K_{1,epsilon}, заменив в (13) каждый `|c_i|` на `|c_i|e^{epsilon*x_i^2}`. Тогда
\[
|g_\epsilon|\le K_{0,\epsilon}t^\kappa e^{\lambda t},\quad
|b_\epsilon|\le K_{b,\epsilon}t^\kappa e^{\lambda t},
\quad |\nabla_X^\epsilon g_\epsilon|\le K_{1,\epsilon}t^\kappa(1+t)e^{\lambda t},
\]
\[
\dot g_\epsilon=\nabla_X^\epsilon g_\epsilon+2\epsilon b_\epsilon,
\quad f_\epsilon^2\le(16\pi^4/A_\epsilon^2)t^{9/2}e^{-2\pi t}.
\tag{27}
\]
Поэтому все доказательства §§3–5 применяются к деформированной семье. Дополнительные множители — лишь фиксированные степени t и log t; показатель `exp(-beta t)` сохраняется.

В частности, абсолютно сходятся отдельно интегралы
\[
f_\epsilon^2\operatorname{Cov}_t(g_\epsilon,\nabla_X^\epsilon g_\epsilon),\quad
f_\epsilon^2\mathbb E_t[|\rho||g_\epsilon-m_\epsilon|^2],\quad
f_\epsilon^2 qF_\epsilon,
\]
\[
f_\epsilon^2XF_\epsilon,\quad f_\epsilon^2\operatorname{Cov}_t(g_\epsilon,b_\epsilon),
\quad f_\epsilon^2 q_\epsilon F_\epsilon.
\tag{28}
\]
Их модули имеют общую мажоранту `K t^{9/2+2kappa}(1+t)exp(-beta t)` для некоторого явно составленного конечного K. Формула полного хвоста (21) сохраняется с `5` заменённой на целое `N>=9/2+2kappa` и своим K. След `f_epsilon^2 F_epsilon` на бесконечности нулевой, при X=0 конечный. Это глобальная оценка, не только локальная равномерность по параметрам. `[ABSTRACT][PAPER]`

## 7. N2: оба слагаемых потери возникают с точными коэффициентами

Применяем уже доказанную N1 к `f_epsilon,g_epsilon`. В ней
\[
2\Re\operatorname{Cov}_t(g_\epsilon,\dot g_\epsilon)
=2\Re\operatorname{Cov}_t(g_\epsilon,\nabla_X^\epsilon g_\epsilon)
+4\epsilon\Re\operatorname{Cov}_t(g_\epsilon,b_\epsilon),
\]
\[
2q_\epsilon F_\epsilon=2qF_\epsilon+4\epsilon XF_\epsilon.
\tag{29}
\]
Складывая, получаем ровно
\[
\boxed{\begin{aligned}
0={}&f_\epsilon(0)^2F_\epsilon(0)\\
&+\int_0^\infty f_\epsilon^2[2\Re\operatorname{Cov}_t(g_\epsilon,\nabla_X^\epsilon g_\epsilon)
+\mathbb E_t(\rho|g_\epsilon-m_\epsilon|^2)+2qF_\epsilon]dX\\
&+2\epsilon\,\mathsf L_\epsilon,
\end{aligned}}
\tag{N2}
\]
\[
\mathsf L_\epsilon=2\int_0^\infty f_\epsilon^2[XF_\epsilon+
\Re\operatorname{Cov}_t(g_\epsilon,b_\epsilon)]dX.
\tag{30}
\]
Здесь нет неоплаченного обмена пределов: каждая часть (29) абсолютно интегрируема по (28). Производная likelihood даёт именно ковариационную часть; производная веса даёт именно X F. Потеря любого из них нарушает N2.

При `epsilon=0` остаётся N1; множитель перед loss равен нулю. Из этого нельзя извлекать значение или знак `L_0` делением на epsilon. Знак `2epsilon` при отрицательном epsilon также не определяет знак L_epsilon: прочие члены N2 знакопостоянными не доказаны. `[ABSTRACT][PAPER]`

## 8. Все смешанные комплексные тождества сохранены

Для двух допустимых конечных строк g,h обозначим
\[
F_{g,h}=\operatorname{Cov}_t(g,h),\quad z_g=g-\mathbb E_tg,
\quad z_h=h-\mathbb E_th.
\]
Тот же расчёт, либо комплексная поляризация (23), даёт
\[
F_{g,h}'=\operatorname{Cov}_t(\dot g,h)+\operatorname{Cov}_t(g,\dot h)
+\mathbb E_t(\rho\bar z_g z_h).
\tag{31}
\]
Полный интеграл `f(0)^2F_{g,h}(0)+int f^2(F_{g,h}'+2qF_{g,h})=0`. Абсолютный домен следует из (14),(17) и Cauchy–Schwarz для двух фиксированных строк, а не из предположения вещественных c.

В деформированном случае введи поляризованную потерю
\[
\mathsf L_\epsilon(g,h)=\int_0^\infty f_\epsilon^2[
2X F_{g,h}+\operatorname{Cov}_t(b_g,h)+\operatorname{Cov}_t(g,b_h)]dX.
\tag{32}
\]
После замены точечных производных на nabla в (31) добавляется **2epsilon L_epsilon(g,h)**. На диагонали (32) есть ровно (30). Таким образом, утверждения охватывают не только отдельные вещественные диагональные значения, но всю sesquilinear-поляризацию. `[ABSTRACT][PAPER]`

## 9. Точная таблица нулевых поправок к обоим счетам

Пусть eta — любая фиксированная вещественная константа. Используем обозначения (24) и
`Z_var=B_partial+J_tr+J_sc+J_wt=0`. Один буквальный способ прибавить `eta Z_var` к `M-L`:
\[
\mathsf M_\eta=\mathsf M+\eta B_\partial,\qquad
\mathsf L_\eta=\mathsf L-\eta(J_{\rm tr}+J_{\rm sc}+J_{\rm wt}).
\tag{33}
\]

| Сохраняемый член | Поправка к M | Поправка к L | Поправка к M-L |
|---|---:|---:|---:|
| След X=0 | `+eta B_partial` | `0` | `+eta B_partial` |
| Перенос профиля | `0` | `-eta J_tr` | `+eta J_tr` |
| Изменение условного закона | `0` | `-eta J_sc` | `+eta J_sc` |
| Производная физического веса | `0` | `-eta J_wt` | `+eta J_wt` |
| После полного интегрирования | `+eta B_partial` | `+eta B_partial` | `0` |

В частности,
\[
\mathsf L_\eta=\int_0^\infty f^2\{2(X-\eta q)F+
2\Re\operatorname{Cov}_t(g,b-\eta\dot g)-\eta\mathbb E_t(\rho|z|^2)\}dX
=\mathsf L+\eta B_\partial.
\tag{34}
\]
Каждый член этой таблицы допустим по §4. Прибавление положительного следа к M при eta>0 **одновременно** увеличивает L на ту же величину. Поэтому улучшения полного знакового запаса из (33) не следует. `[ABSTRACT][PAPER]`

## 10. Когда нулевой интеграл вставляют как поправку к самому сигналу

Это важное различие с формальным стиранием covariance. На заданной конечной семье определим выражение
\[
\mathfrak T_g=\dot g+qg+\tfrac12\rho(g-m).
\tag{35}
\]
Не предполагается оператор `g->b` на факторпространстве. (35) задано конкретными гладкими представителями; никакого замкнутого генератора или спектрального утверждения не вводим.

Домен (35) тоже оплачен: помимо §§3–4,
\[
\mathbb E_t|\rho z|^2\le4K_0^2e^{2\lambda t}I(t),
\]
поэтому `T_g in L2(f^2 dX p_t ds)`. Условное проектирование определено в этом же физическом пространстве. Прямой расчёт даёт
\[
2\Re\operatorname{Cov}_t(g,\mathfrak T_g)=F'+2qF,
\quad \mathcal C\mathfrak T_g=m'+qm-\tfrac12\omega_g.
\tag{36}
\]
Первое равенство верно потому, что `Cov(g,rho z)=E rho|z|^2`; второе сохраняет коммутатор `m'-E dot g=omega_g`.

Обозначим
\[
B_m=f(0)^2|m(0)|^2,\quad B_{\rm mic}=f(0)^2\mathbb E_1|g(1,S)|^2=B_\partial+B_m,
\quad J_c=\int_0^\infty f^2\Re(\bar m\omega_g)dX.
\tag{37}
\]
J_c абсолютно сходится по (18). Следы полных вторых моментов и `f^2|m|^2` на бесконечности нулевые, а их производные интегрируемы. Следовательно
\[
2\Re\int_0^\infty f^2\bar m(m'+qm)dX=-B_m.
\tag{38}
\]

Теперь сравним две операции над `D_c=Xg+b`.

| Операция | Delta M | Delta L | Delta V |
|---|---:|---:|---:|
| `D_c -> D_c+eta T_g` | `-eta(B_mic+J_c)` | `-eta B_partial` | `-eta(B_m+J_c)` |
| `D_c -> D_c+eta(1-C)T_g` | `-eta B_partial` | `-eta B_partial` | `0` |

Доказательство первой строки: loss меняется на интеграл первого равенства (36), то есть `-eta B_partial`; проекция меняет V на `2eta Re int f^2 bar(m) C T_g`, равный `-eta(B_m+J_c)` по второму равенству (36),(38). Сложение восстанавливает Delta M. Во второй строке `C(1-C)T_g=0`, а спаривание с `g-m` неизменно; это полностью определённый случай R9, теперь с вычисленным интегральным изменением `-eta B_partial`.

**Непроецированная вставка T_g не является допустимым нулём для V.** Для неё дополнительно требуется вернуть `eta(B_m+J_c)`. Игнорировать J_c значит потерять именно перенос среднего между изменяющимися условными слоями. Проецированная вставка допустима, но изменяет оба счета одинаково; никакого знака V это не даёт.

В деформированном случае та же структура видна без деления на epsilon:
\[
\mathfrak T_{\epsilon}^{\rm full}
:=\dot g_\epsilon+(q+2\epsilon X)g_\epsilon+\tfrac12\rho(g_\epsilon-m_\epsilon)
=\mathfrak T_{\epsilon}^{0}+2\epsilon(Xg_\epsilon+b_\epsilon),
\]
\[
\mathfrak T_{\epsilon}^{0}:=\nabla_X^\epsilon g_\epsilon+qg_\epsilon+
\tfrac12\rho(g_\epsilon-m_\epsilon).
\tag{39}
\]
Вычисление `2 Re Cov(g_epsilon, .)` в (39) воспроизводит **всю** (N2), включая обе части потери. Это точный контакт с прежним смешанным остатком, не утверждение его положительности. `[ABSTRACT][PAPER]`

## 11. Что действительно стало новым и что осталось открытым

Нуль не определён как «минус неизвестная потеря». Он построен независимо: это производная конкретной неотрицательной дисперсии с физическим весом и доказанными следами. Новые результаты — полный `W^{1,1}`-домен, точные N1/N2, их комплексная поляризация и таблицы (33)–(39). Они исправляют потенциально незаконный перенос производной и показывают точную цену сохранения исходной формы.

Однако этот нуль **не является source-sign supplier**. Он не превращает неизвестное сравнение в известное: после интегрирования разность счетов остаётся прежней.

Первый и единственный неоплаченный знаковой вход в этой записи:
\[
\boxed{\begin{aligned}
\mathsf M+\eta B_\partial\ \ge\ &\int_0^\infty f^2\{2(X-\eta q)F+
2\Re\operatorname{Cov}_t(g,b-\eta\dot g)-\eta\mathbb E_t(\rho|z|^2)\}dX\\
&\text{для всех конечных }x_i\in I,\ c_i\in\mathbb C.
\end{aligned}}
\tag{40}
\]
При любом фиксированном eta это **в точности** `M>=L`, а не новая доказанная лемма. Объявлять (40) продвижением самого знака — `NO_PROGRESS_TAUTOLOGY`. Требуется независимая нижняя оценка **целой разности**, сохраняя транспортный и score-члены, а не абсолютные оценки их размеров. В этом ответе её нет.

### Связь с Green-ядром

Если `K_t(s,z)=F_t(min(s,z))-F_t(s)F_t(z)` — принятое ядро H:R4, то при фиксированном X
\[
F=[g_s,g_s]_{K_t},\qquad \operatorname{Cov}_t(g,b)=[g_s,b_s]_{K_t},
\quad \operatorname{Cov}_t(g,\dot g)=[g_s,(\dot g)_s]_{K_t}.
\tag{41}
\]
Эти тождества допустимы по плоским концам §3. Здесь сначала выполняются два конечных fibre-интеграла, затем X-интеграл ковариации. Абсолютная сходимость последнего доказана выше; **абсолютная перестановка всех трёх производных интегралов не заявляется и не требуется**. Положительность K_t доказывает F>=0, но не знак спаривания с `b-eta dot g` или score-вклада.

### Обязательный отрицательный контроль

Для каждого фиксированного epsilon<0 исходные p_t,rho,I(t),K_t не меняются [REQ; H:§7; D:§5]. Его натуральный likelihood получает именно `k_i` из (26); все выполненные здесь доменные оценки и N2 продолжают действовать. Предусмотренные запросом отрицательные строки `V_(f_epsilon)` поэтому не противоречат нашим теоремам.

Двухфакторность недеформированного G_x и фиксированные rates `pi n^2` использованы для (8)–(14), то есть для доказательства **допустимости** поправки. Не доказано, что они обеспечивают (40). Ни свойство условной меры, ни Fisher-оценка, ни сами нулевые тождества не являются гипотезой, которая исключает отрицательный контроль по знаку. Придумывать такое исключение было бы ложным повышением результата. `[ABSTRACT][PAPER]`

## 12. Судейская граница, варианты представления и проверка

| Поле K8A | Значение |
|---|---|
| DOWNSTREAM_CONSUMER | all-complex V positivity, затем принятые analytic propagation и Weil transfer из D |
| ACTUAL_CONSUMER_REQUIREMENT | V[c]>=0 для всех конечных действительных узлов и комплексных c |
| ORIGINAL_REQUESTED_OBJECT | полные N1/N2 и точное сохранение исходной формы при поправке |
| ORIGINAL_OBJECT_IS | NOT_NECESSARY как выбранный способ доказательства знака; тождества теперь доказаны в своём домене |
| KNOWN_WEAKER_INTERFACE | непосредственно знак V на I при всех рангах; его достаточность — принятый условный перенос, не новый знак |
| FAILURE_TYPE | NO_DERIVATION только для полного знакового сравнения (40) |
| EPISTEMIC_STATUS | N1/N2: PAPER-кандидат; (40): RESEARCH_DEBT |
| KILL_SCOPE | NONE; нет отрицательной V и нет опровержения N1/N2 |
| REOPEN_TRIGGER | источник-специфическое нециркулярное сравнение всех членов (40), а не новое имя для него |
| NOVELTY_AXIS | оплаченный глобальный variance-transport домен и точная деформационная/граничная бухгалтерия; общей новизны не заявляется |

Две координатные формы **того же** остатка, без запуска второго механизма:

| Представление | Решающий вопрос | Качественная сила / стоимость |
|---|---|---|
| Полный Green-bilinear transport (34),(41) вместе со score-членом | Появится ли независимое сравнение смешанного спаривания, не уничтожающее компенсацию? | 9/10; 8/10 |
| Проекция на средние и явный коммутатор (36)–(38) | Можно ли оплатить весь mean-flux, а не принять T_g за невидимый для V нуль? | 10/10; 9/10 |

Это оценки исследовательской полезности, не сроки и не измеренные вероятности. Они не авторизуют новую сетку, профиль или sign-кампанию.

**DISCRIMINATOR:** равенство N1/N2 удостоверяет аналитическая формула следов с абсолютными бюджетами, не приближённый нуль. Для предполагаемого знака (40) нужен нижний предел полного `M_eta-L_eta`, а для отрицательного свидетеля — строгая отрицательная верхняя огибающая той же полной величины на допустимой строке. Малость каждого счета по отдельности и нулевая поправка этого не различают.

Сильнейшее возражение — «это только переименование TARGET» — верно для (40), но неверно для доменной теоремы §§3–7: до неё N1/N2 были лишь формальными кандидатами, а их интегральный смысл и следы не были оплачены. Различие не используется для ложного source-sign прогресса.

Регистрация была сохранена после чтения источников и первоначального просмотра формул, до законченного доказательства и математического кода. Это не независимая timestamp-квитанция. P1/P2 подтверждены доказательством домена и точными коэффициентами; P3 подтверждено (25),(33)–(39); P4 подтверждено (19)–(22),(27)–(28). Все подтверждения имеют статус PAPER до независимого приёма.

Первый запуск алгебраического checker остановился на сравнении разных синтаксических форм SymPy. После замены структурного равенства на `expand(left-right)==0` тот же тождественный тест прошёл; формулы, коэффициенты, предсказания и источники не менялись. Запись отказа сохранена в приложении.

Memory entry: integrated variance transport is a genuine source-admissible zero only WITH its X=0 trace and physical-weight derivative; raw transport changes projected V by a mean-boundary plus commutator; projected transport changes both accounts equally. Minimal missing sign: (40). Не повторять стирание границы, score или одной из двух epsilon-производных.

Исторический source-sign no-delta **11 сохраняется**, без сброса. Этот ограниченный запрос доказывает нулевое тождество, а не запускает очередную полную знаковую попытку. Реестры и машинные счётчики не изменяются. Все глобальные знаки и RH остаются открытыми.

**CODEX DIRECTIVE:** независимо проверить N1/N2 и только их полный домен: (11)–(22), (27)–(30), комплексную поляризацию и обе строки таблицы §10; воспроизвести Appendix A. Приём: `ACCEPT_FULL_N1_N2_AND_CORRECTION_ACCOUNTING_ONLY`. При отказе назвать первое неверное равенство или неоплаченное слагаемое, не подменять его отсутствием доказательства RH. Нового sign-run, изменения runtime и canonical admission не делать.

## 13. Доставка и проверяемость

Полный отчёт сначала сохранён локально. Разрешённая публикация — только новый Markdown из YAML в `codex_mac/math-proshka-20260912`, commit subject с `[Proshka]`. Resulting commit SHA возвращается после записи и чтения нового blob; его нельзя заранее вставить в собственное содержимое.

Lean-source не создаётся; `lake`, kernel gate и axiom profile: **NOT_RUN / NOT_APPLICABLE**. Публикация не является независимым математическим приёмом. Независимая проверка может повысить только указанный PAPER-результат N1/N2, не V/RH. Старые закрытые ответы, очередь и чужие файлы не меняются.

## Appendix A. Исполненная точная проверка алгебры

Команда: `python /mnt/data/nullvar/check_nullvar.py`. Для другого окружения сохрани блок как `check_nullvar.py` и выполни `python {workdir}/check_nullvar.py`, например `python /tmp/nullvar/check_nullvar.py`. `workdir` — только каталог скрипта. Все символы в программе формальные; T в тесте N2 обозначает вещественную ковариацию, а не исходный total-energy t. Никакая тестовая вероятность, новая модель или theta-ячейка не вводится. SymPy проверяет полиномиальные тождества; аналитические мажоранты нужно проверять по доказательству выше.

```python
"""Exact formal algebra only: no theta values, quadratures, or source matrices."""
from sympy import symbols, expand

mr, mi, ar, ai, zr, zi, T, R = symbols('mr mi ar ai zr zi T R', real=True)
ma = mr*ar + mi*ai
mz = mr*zr + mi*zi
raw = 2*T + R - 2*(mr*(ar+zr) + mi*(ai+zi))
centered = 2*(T-ma) + R - 2*mz
assert expand(raw-centered) == 0
print('N1_COMPLEX_CENTERING=EXACT')

F, q, X, eps, B, S = symbols('F q X eps B S', real=True)
base = 2*B + S + 2*q*F
full = 2*(B+2*eps*T) + S + 2*(q+2*eps*X)*F
loss = 2*(X*F+T)
assert expand(full-base-2*eps*loss) == 0
assert expand(full-base-4*eps*(X*F+T)) == 0
print('N2_EXTRA_TERM=2*eps*LOSS_DENSITY')
assert expand((2*B+S+2*(q+2*eps*X)*F)-base-2*eps*loss) == -4*eps*T
assert expand((2*(B+2*eps*T)+S+2*q*F)-base-2*eps*loss) == -4*eps*X*F
print('PLANT_DROP_LIKELIHOOD_DERIVATIVE=DETECTED')
print('PLANT_DROP_PHYSICAL_WEIGHT_DERIVATIVE=DETECTED')

M, L, B0, J1, J2, J3, eta = symbols('M L B0 J1 J2 J3 eta', real=True)
Z = B0+J1+J2+J3
newM, newL = M+eta*B0, L-eta*(J1+J2+J3)
assert expand(newM-newL-(M-L)-eta*Z) == 0
assert expand(newL.subs(J3, -B0-J1-J2)-(L+eta*B0)) == 0
assert expand((J1+J2+J3).subs(J3, -B0-J1-J2)) == -B0
print('SCALAR_NULL_CORRECTION_LEDGER=EXACT')
print('PLANT_DROP_X0_BOUNDARY=DETECTED')

Bv, Bm, Jc = symbols('Bv Bm Jc', real=True)
# R_g = partial_X g + q*g + rho*(g-Eg)/2.
deltaM = -eta*(Bv+Bm+Jc)
deltaL = -eta*Bv
assert expand(deltaM-deltaL+eta*(Bm+Jc)) == 0
# Subtracting C R_g restores the original projected form exactly.
deltaM_perp = deltaM + eta*(Bm+Jc)
assert expand(deltaM_perp-deltaL) == 0
print('UNPROJECTED_TRANSPORT_DEFECT=-eta*(B_mean+J_comm)')
print('PROJECTED_TRANSPORT_CORRECTION=EQUAL_ACCOUNT_SHIFTS')

j, bf, bh, Xc = symbols('j bf bh Xc', real=True)
assert expand(2*eps*(bf+bh)+4*eps*Xc*j-2*eps*(2*Xc*j+bf+bh)) == 0
print('N2_SESQUILINEAR_POLARIZATION=EXACT')
print('THETA_EVALUATIONS=0; QUADRATURES=0; SOURCE_MATRICES=0; LEAN_RUNS=0')
```

Буквальный stdout финального запуска, exit 0, stderr пуст:

```text
N1_COMPLEX_CENTERING=EXACT
N2_EXTRA_TERM=2*eps*LOSS_DENSITY
PLANT_DROP_LIKELIHOOD_DERIVATIVE=DETECTED
PLANT_DROP_PHYSICAL_WEIGHT_DERIVATIVE=DETECTED
SCALAR_NULL_CORRECTION_LEDGER=EXACT
PLANT_DROP_X0_BOUNDARY=DETECTED
UNPROJECTED_TRANSPORT_DEFECT=-eta*(B_mean+J_comm)
PROJECTED_TRANSPORT_CORRECTION=EQUAL_ACCOUNT_SHIFTS
N2_SESQUILINEAR_POLARIZATION=EXACT
THETA_EVALUATIONS=0; QUADRATURES=0; SOURCE_MATRICES=0; LEAN_RUNS=0
```

## Appendix B. Сохранённый отказ инструмента и регистрация

Первый вариант отличался от Appendix A только одной строкой:

```python
assert expand(full-base) == 4*eps*(X*F+T).expand()
```

Умножение справа оставалось нераскрытым, поэтому структурное `==` дало False для математически равных полиномов. Исходный вариант сохранён как `check_nullvar_shape_error.py`; его повтор для фиксации stderr завершился exit 1. Буквальные stdout и stderr этого повторного отказа:

```text
N1_COMPLEX_CENTERING=EXACT
```

```text
Traceback (most recent call last):
  File "/mnt/data/nullvar/check_nullvar_shape_error.py", line 17, in <module>
    assert expand(full-base) == 4*eps*(X*F+T).expand()
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
AssertionError
```

Заменена только проверка нормальной формы, не математическое утверждение. Первичный неуспешный запуск также вывел только строку N1_COMPLEX_CENTERING=EXACT.

Полная регистрация:

```text
REQUEST_ID: REQ-2026-09-13-NULLVAR
CANDIDATE: INTEGRATED_PHYSICAL_WEIGHTED_CONDITIONAL_VARIANCE_DERIVATIVE
REGISTRATION_STAGE: after controlling-request/source intake; before completed proof or any mathematical code test
P1 p=0.97: N1 is exact with its positive X=0 boundary term; full-source likelihood flatness pays endpoint-score products.
P2 p=0.99: N2 has coefficient 2*epsilon*E_loss,epsilon, requiring BOTH the likelihood derivative and the physical-weight derivative.
P3 p=0.98: adding the full integrated zero does not by itself supply a sign for V; removing its boundary or mixed score term is invalid.
P4 p=0.90: fixed-family bounds can be given with an explicit positive large-T exponential rate while retaining every theta mode; no uniform bound in rank/coefficients is needed for integrability.
TESTS_PLANNED: exact symbolic/rational identities and planted omitted-term failures only; no theta evaluation, quadrature, source rank sweep, Hankel grid, new profile or root computation.
NO_ASSUMPTIONS: RH, V>=0, E_micro>=0, E_loss<=0, vanished mixed covariance, target Gram representation.
```

## Appendix C. Локальный манифест

| Файл | Bytes | LF | SHA256 |
|---|---:|---:|---|
| `check_nullvar.py` | 1921 | 47 | `650a31fd65f26a616502d73d0c22e37f5d981408deb96ce770111f27a59ca1fa` |
| `check_nullvar.stdout` | 421 | 10 | `3535cf299d1c8ab9fa5856530aa718d4cc1ffaced14983e832a651fb2d0ee677` |
| `check_nullvar.stderr` | 0 | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check_nullvar_shape_error.py` | 1928 | 47 | `df3ba4498f2af1526222b74bf5092af98f58e59755a7f15ef70143d00f42f872` |
| `shape_error.stdout` | 27 | 1 | `e61ab131d5c733986972b97d427e66c08eb17d439606f50065021d4191903a39` |
| `shape_error.stderr` | 238 | 5 | `89a797e30bb38585b7f0ffeaf66d035e7caa0c383f79cf88ca6e17cd86b9b236` |
| `preregistration.txt` | 1101 | 9 | `e041844a5904d06909087826fc7356fca697081e7784e58713fcdbcc6cdef2da` |

Конец полного отчёта. N1/N2 доказаны на PAPER-уровне с полными интегралами; их принятие ещё требует независимой проверки. Никакого знака TARGET или RH из нулевых тождеств не заявляется.
