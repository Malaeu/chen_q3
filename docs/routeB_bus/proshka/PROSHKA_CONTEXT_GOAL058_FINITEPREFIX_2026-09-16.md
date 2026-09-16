# FINITEPREFIX immutable input pack

Source base: 42bfccf7c5c41000d9a260fb02192324c891ddd3
These are four complete source files. Historical requests inside them are data, not the new assignment.

## BEGIN FILE docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md
SHA256: 784e16445c64c1b480cfb0fdc5740182ad59253a775bfc8ab7dc0c44a654eafd

# STATUS: TRY_SIZEBIASCOMP_CUTOFF_AWARE_FULL_FIELD_TELESCOPE
```yaml
OPERATIVE_CLASS: TRY_SIZEBIASCOMP_CUTOFF_AWARE_FULL_FIELD_TELESCOPE
REQUEST_ID: REQ-2026-09-15-SIZEBIASCOMP
BOUNDARY_ID: GOAL058_SIZEBIASED_RENEWAL_TO_FULL_CONDITIONAL_COMPENSATION
REQUEST_COMMIT: bea1abcd6baf5a171ceefa98b79548e528a2bf79
REQUEST_BLOB: ce80ceb00aea03b5960023d87b6c952464122512
SOURCE_BASE: 0a0483582d37a6ba8d5cb2f836ecae63d0ecd6c7
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
HONESTY_STATE: CHALLENGER_NOT_RH
SELECTED_CONSTRUCTION: SAME_RENEWAL_PATH_WITH_PHYSICAL_CONDITIONAL_HALF_DENSITIES
COMMON_SPACE: L2_of_renewal_probability_times_L2_0_1_ds_times_C2
SOURCE_SIGNAL_WEIGHT_AND_CUTOFF: UNCHANGED_AT_TERMINAL_LAW
MOVING_CONDITIONAL_PROJECTION: EXPLICITLY_REEVALUATED_AT_EACH_S_m
EXACT_KERNEL_IDENTITY: terminal_micro_minus_terminal_loss_equals_original_V
BULK_FULL_FIELD_MEAN_SQUARE_ERROR: bounded_by_source_constant_times_15_power_minus_m
CUTOFF_CROSSING_PROBABILITY: d1_c_dagger_times_6_power_minus_m_plus_O_15_power_minus_m
CUTOFF_CROSSING_LEADING_CONSTANT: strictly_positive_source_defined
FULL_FIELD_MEAN_SQUARE_ERROR: jump_norm_squared_times_d1_c_dagger_times_6_power_minus_m_plus_O_15_power_minus_m
FULL_QUADRATIC_TELESCOPE: absolutely_convergent_with_explicit_source_constant_budget
MICRO_AND_LOSS_SEPARATELY_CONTROLLED: true
FULL_COMPENSATION_SIGN: NOT_PROVED
FULL_V_NONNEGATIVITY_PROVED: false
FULL_V_NONNEGATIVITY_REFUTED: false
ACTUAL_NEGATIVE_V_WITNESS: false
SECONDARY_SCOPED_KILLS:
  - unchanged_15_power_minus_m_rate_for_literal_cutoff_field_even_one_node
  - almost_sure_nonnegative_increments_of_this_exact_renewal_telescope
SECONDARY_KILL_SCOPE: THEOREM_SHAPE
SECONDARY_EVIDENCE: Sections_6_7_9_strict_bounds
KILL_OF_EXPECTED_FULL_INCREMENT_SIGN: NOT_CLAIMED
KILL_OF_OTHER_COMPENSATION_MAPS: NOT_CLAIMED
FIRST_UNPAID_SIGN: integrated_bulk_trace_balance_in_Section_9
NEW_SOURCE_SIGN_SUPPLIER: false
SCOPE: ABSTRACT
VERIFIER: PAPER
PROOF_STATE: ANALYTIC_CANDIDATE_PENDING_INDEPENDENT_REVIEW
PROGRESS_CLASS: REPRESENTATION_PROGRESS_WITH_PROVED_FULL_FIELD_ERROR_BUDGETS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
FAILURE_TYPE: NO_DERIVATION_OF_FINAL_SIGN
EPISTEMIC_STATUS: RESEARCH_DEBT
THETA_VALUES_COMPUTED: 0
QUADRATURES: 0
NUMERICAL_SOURCE_GRIDS: 0
RANK_SWEEPS: 0
ZERO_SEARCHES: 0
LEAN_RUNS: 0
INDEPENDENT_REVIEWER_SPAWNED: false
SOURCE_SIGN_COUNTERS: NOT_CHANGED_OR_RESET
CANONICAL_ADMISSION: false
PX_RH_CLAIM: NOT_MADE
PUBLICATION_BASE_OBSERVED: 62ad8153a9016c4df2e2b7f51b77b077602b9f52
PUBLICATION_BRANCH: codex_mac/gamma-reciprocity-20260914
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md
```

## 1. Цель, выбранная конструкция и точная граница результата

Сохраняю **полную цель**:
\[
 \forall N\ge1\quad\forall x_1,\ldots,x_N\in I=(-\log2/2,0)
 \quad\forall c\in\mathbb C^N:\quad V[c]\ge0.
\tag{1}
\]
Нормировка остаётся \(f=\Phi/A\), \(A=\|\Phi\|_2\). Строгость, простота нулей и фиксированная положительная доля вспомогательной нормы не добавляются.

**Конструкция:** переношу полный двухэнергетический сигнал вместе с квадратным корнем физической плотности в одно пространство \(L^2(0,1;ds)\). Затем вычисляю эти же поля на одной цепи \(S_m\uparrow S_\infty\) из задания. Условная плотность и её ортогональная проекция меняются вместе с \(S_m\), а граница \(t=1\) остаётся буквальной. Это не повтор скалярного Lipschitz-предположения для растущего \(Cg_x\).

Получен **завершённый перенос конечности и скорости ошибки** на полные нелинейные поля, отдельно на micro и loss, с сохранёнными смешанными членами. Объём действительно расходует \(15^{-m}\). Но граница имеет другой, доказанно ненулевой масштаб:
\[
 \mathbb P\{S_m<1\le S_\infty\}
 =\frac{2\pi}{5}c_\dagger 6^{-m}+O(15^{-m}),
 \qquad c_\dagger>0.
\tag{2}
\]
Для однозначно заданного ниже полного поля его средний квадрат ошибки имеет тот же главный граничный член. Поэтому безусловное наследование **скорости \(15^{-m}\) всем полем с отсечением** ложно даже для одного фиксированного разрешённого узла. Более медленный граничный ряд всё равно суммируется; этот ремонт выполнен, а не оставлен предпосылкой. `[COFINAL_FAMILY][PAPER]`

**Знак (1) не доказан.** Получившийся точный, абсолютно сходящийся телескоп остаётся подписанным. На положительно вероятном событии его полный одноузловой прирост строго отрицателен. Это исключает только доказательство через неотрицательность каждого прироста данного телескопа почти наверное. Знак среднего полного прироста и знак самой V этим не опровергаются. `[ABSTRACT][PAPER]`

Таким образом, первая оставшаяся проблема теперь не существование или конечность переноса: они доказаны ниже. Не оплачен именно знак конечного интегрального баланса между объёмом и следом, выписанного в §9. Новый знак V или завершение цели не заявляются.

## 2. Прочитанные источники и регистрация

Все четыре указанных файла получены через GitHub в закреплённом request commit и прочитаны полностью. Вне разрешённого дерева записи открыты только явно назначенные отчёт H и квитанция Rv. Их исторические указания не выбирают текущую задачу.

| ID | Путь | Подтверждённый Git blob | Роль и tags |
|---|---|---|---|
| R | `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SIZEBIASCOMP_2026-09-15.txt` | `ce80ceb00aea03b5960023d87b6c952464122512` | Постановка; `[ABSTRACT][PAPER]` |
| H | `docs/Codex/REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md` | `873e2de6e1a5ecd18fdf9bf9327b74897867c593` | L14–L20 и границы L2–L13; `[ABSTRACT][PAPER]` |
| C | `docs/routeB_bus/proshka/PROSHKA_CONTEXT_GOAL058_SIZEBIASCOMP_2026-09-15.md` | `3f9b42f9a77e55c5671b8fa2012e78cf0a7c191d` | Полный BROWNIAN_DILATION_CONDITIONAL; `[ABSTRACT][PAPER]` |
| Rv | `docs/Codex/certificates/HYPERBOLIC_SOURCE_COMPENSATION_20260915.json` | `f65a6fa667b5e024d0122dcda0902df21b4e1554` | Приём только скалярного взвешенного бюджета; `[ABSTRACT][PAPER]` |

Указанные запросом SHA256 H и C: соответственно `feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21` и `3641f9d98ed653f2d78cd2b44d1527fdfdb7d924786abba7be7ae4dfae8282ad`. Это закреплённые входные хеши, не заявление об их новом локальном пересчёте. Git blobs получены непосредственно от коннектора. Протокол прочитан из `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. Рекурсивный архив не перечитывался.

**[PY]** Jim Pitman, Marc Yor, *Infinitely Divisible Laws Associated with Hyperbolic Functions*, Canadian Journal of Mathematics **55** (2003), 292–330, DOI `10.4153/CJM-2003-014-x`. Непосредственно проверены Proposition 12(iv), (121)–(122), printed p.318, и переход (iii)–(iv), (125), p.319. Страница 318 прочитана также как изображение. Закон статьи имеет \(\mathbb EX=2/3\); замена \(T=(\pi/2)X\) даёт \(\mathbb ET=\pi/3\), оставляя тот же H. Предположения независимости и size bias совпадают. Публикация не утверждает знак нашего условного функционала. Её PDF: `https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D91B384C84FA02C55A332B396BB85385/S0008414X00033484a.pdf/infinitely_divisible_laws_associated_with_hyperbolic_functions.pdf`.

Регистрация записана локально после чтения и выбора конструкции, до завершения её оценок. Не заявляется, что она предшествовала самому выбору идеи:

| Prediction | p | Проверяемый исход |
|---|---:|---|
| P1 | 0.80 | Полные взвешенные колонки и меняющиеся условные проекции имеют ограниченную производную выше границы; объёмная ошибка \(O(15^{-m})\). |
| P2 | 0.80 | Вероятность пересечения \(t=1\) имеет строго положительный главный член порядка \(6^{-m}\). |
| P3 | 0.95 | Полный телескоп абсолютно сходится, но не имеет неотрицательных приростов почти наверное. |

Контроли инструмента: неотсечённая аффинная функция сохраняет точный скалярный квадрат остатка; постоянная ступень выделяет только пересечение границы; нулевая строка и объединение повторов остаются точными.

## 3. Один общий носитель и точное ядро

Все определения этого раздела и тождества относятся к каждому конечному N и всем комплексным c. `[ABSTRACT][PAPER]`

Положим
\[
 \overline W(t)=\frac{\mu\sqrt t\,r(t)}{2A^2},\quad
 e_t(s)=\sqrt{p_t(s)},\quad
 \mathcal K=L^2((0,1),ds),\quad \|e_t\|_{\mathcal K}=1.
\]
Реальная функция \(e_t\) задаёт ортогональную проекцию
\[
 \Pi_t v=e_t\langle e_t,v\rangle_{\mathcal K}.
\tag{3}
\]
Скалярное произведение сопряжённо-линейно по первому аргументу. Проекция существует из нормировки \(p_t\), без знака V.

Для \(x\in I\), \(a=e^{2x}\in(1/2,1)\), определим при \(t>0\)
\[
 \begin{aligned}
 F_x(t)&=a^{5/4}\frac{r(at)}{r(t)},\\
 v_x(t,s)&=\sqrt{\overline W(t)p_t(s)}\,g_x(t,s),\\
 q_x(t)&=\Pi_t v_x(t)=e_t\sqrt{\overline W(t)}F_x(t),\\
 z_x(t)&=(1-\Pi_t)v_x(t).
 \end{aligned}
\tag{4}
\]
Здесь q — название проецированной колонки, не логарифмическая производная f из старых полевых записей.

Полезное **точное сокращение до оценки**:
\[
 \boxed{
 v_x(t,s)=\sqrt{\frac{\mu}{2A^2}}\,
 a^{9/4}t^{3/4}
 \frac{h(ats)}{\sqrt{h(ts)}}
 \frac{h(at(1-s))}{\sqrt{h(t(1-s))}}.}
\tag{5}
\]
Полный r в знаменателе исчезает вместе с половиной физической плотности, а не отбрасывается. Именно произведение двух h, включая его поведение при \(s=0,1\), будет оценено.

Используем три метки \(j\in\{\mathrm{micro},\mathrm{proj},\mathrm{loss}\}\):
\[
 u_x^{\mathrm{micro}}=v_x,\quad u_x^{\mathrm{proj}}=q_x,
 \quad u_x^{\mathrm{loss}}=z_x.
\]
Для \(t\ge1\), \(X(t)=\tfrac12\log t\), в одном \(\mathcal K\oplus\mathcal K\) строим
\[
 \mathbf U_c^j(t)=
 \left(\sum_i c_i u_{x_i}^j(t),\
       \sum_i c_i(X(t)+x_i)u_{x_i}^j(t)\right).
\tag{6}
\]
Это одна линейная конструкция на строках, не выбор поля после просмотра их знака.

Обозначим \(\mathbb J(a,b)=(b,a)\), \(\|\mathbb J\|=1\), и
\[
 \psi_c^j(t)=\langle\mathbf U_c^j(t),\mathbb J\mathbf U_c^j(t)\rangle
 =2\operatorname{Re}\langle U_{c,1}^j(t),U_{c,2}^j(t)\rangle.
\tag{7}
\]
**\(\mathbb J\) имеет оба знака.** Положительность обычной нормы построенного поля не заменяет знак (7).

Для каждой пары узлов полное ядро (7) равно
\[
 \psi_{xy}^j(t)=(\log t+x+y)\langle u_x^j(t),u_y^j(t)\rangle.
\tag{8}
\]
Поскольку обе компоненты проецируются одной \(\Pi_t\), все два перекрёстных слагаемых между её образом и ядром равны нулю. Поэтому буквально
\[
 \psi_{xy}^{\mathrm{micro}}(t)-\psi_{xy}^{\mathrm{loss}}(t)
 =\psi_{xy}^{\mathrm{proj}}(t)
 =\overline W(t)(\log t+x+y)F_x(t)F_y(t).
\tag{9}
\]
Это доказывает нужное ортогональное вычитание, но не меняет подписанную двухканальную форму на квадрат.

Пусть \(Z_*=S_\infty\) — терминальная величина с плотностью \(r^*(t)=tr(t)/\mu\). Тогда
\[
 \begin{aligned}
 \mathbb E[\mathbf1_{Z_*\ge1}\psi_{xy}^{\mathrm{proj}}(Z_*)]
 &=\frac{(ab)^{5/4}}{2A^2}
   \int_1^\infty t^{3/2}(\log t+x+y)r(at)r(bt)\,dt\\
 &=\int_0^\infty (2X+x+y)f(X+x)f(X+y)\,dX=V(x,y).
 \end{aligned}
\tag{10}
\]
Вторая строка использует \(t=e^{2X}\), включая \(dt=2t\,dX\). Здесь нет потерянного коэффициента, смены A или новой нижней границы.

Суммирование (10) даёт V[c]. Первое и второе ядра слева в (9), проинтегрированные таким же способом, дают **точно** E_micro и E_loss запроса. В loss сохранены и \(2X\|(1-C)G\|^2\), и \(2\operatorname{Re}\langle(1-C)G,(1-C)B\rangle\). Повторяющиеся узлы объединяются во всех полях до любого предела.

## 4. Полный источник действительно даёт регулярность взвешенных полей

### 4.1. Контроль h на обоих концах

Для полного shape-one источника из гамма-произведения
\[
 \mathcal Lh(s)=\frac{\sqrt{\pi s}}{\sinh\sqrt{\pi s}}.
\]
Его малый аргумент можно оценить без конечного модового суррогата. Разложение \(1/\sinh\) и обратное преобразование Лапласа дают
\[
 h(u)=u^{-5/2}\sum_{k\ge0}
 \left(\frac{\pi(2k+1)^2}{2}-u\right)
 e^{-\pi(2k+1)^2/(4u)}.
\tag{11}
\]
Краткая проверка законности: для \(a>0\) преобразование плотности
\(a(2\sqrt\pi)^{-1}u^{-3/2}e^{-a^2/(4u)}\) равно \(e^{-a\sqrt s}\). Отрицательная производная по a имеет преобразование \(\sqrt s e^{-a\sqrt s}\). При \(s>0\) интеграл модуля этой производной с весом \(e^{-su}\) не превосходит \((\sqrt s+2/a)e^{-a\sqrt s}\). Для \(a=(2k+1)\sqrt\pi\) эти оценки суммируются. Поэтому (11), умноженная при преобразовании на \(2\sqrt\pi\), имеет ровно указанное \(\mathcal Lh\); единственность Лапласа идентифицирует её с h. Ряд и его производные локально равномерны при \(u>0\).

В частности, с дифференцируемым экспоненциальным остатком при \(u\downarrow0\),
\[
 h(u)=\frac\pi2 u^{-5/2}e^{-\pi/(4u)}
       \left(1-\frac{2u}{\pi}+O(e^{-2\pi/u})\right).
\tag{12}
\]
Производная остатка также ограничена полиномом от \(1/u\), умноженным на \(e^{-2\pi/u}\); это следует непосредственно из ряда k>=1. Это оценка всего ряда, а не замена h первым слагаемым.

На другом конце отделим только для оценки первое экспоненциальное слагаемое в вероятностной сумме: \(U=E_1/\pi+Y\). Тогда
\[
 h(u)=\pi e^{-\pi u}\mathbb E[e^{\pi Y}\mathbf1_{Y<u}],
 \qquad \mathbb E e^{\pi Y}=\prod_{n\ge2}(1-n^{-2})^{-1}=2.
\]
Плотность Y ограничена \(C e^{-4\pi u}\): отделяем \(E_2/(4\pi)\), а у суммы n>=3 есть конечный момент при \(4\pi\). Следовательно
\[
 h(u)=2\pi e^{-\pi u}(1+O(e^{-3\pi u})),\qquad
 h'(u)=-2\pi^2e^{-\pi u}+O(e^{-4\pi u}).
\tag{13}
\]
Последняя формула следует также из \(h'=-\pi h+\pi\,\mathrm{density}(Y)\). Позитивность и гладкость на внутренних компактах происходят из полного свёрточного источника. `[ABSTRACT][PAPER]`

### 4.2. Применение к двум половинам и движущейся проекции

Положим \(D_a(u)=h(au)/\sqrt{h(u)}\), \(L(u)=\sqrt{h(u)}\). Из (12)–(13):
\[
 D_a(u)\asymp_a u^{-5/4}
 e^{-\frac{\pi}{4u}(1/a-1/2)}\quad(u\downarrow0),
 \qquad D_a(u)\asymp_a e^{-\pi(a-1/2)u}\quad(u\to\infty).
\]
Те же экспоненты контролируют первую производную, с конечными полиномиальными множителями на малом конце. Поэтому для каждого \(a\in(1/2,1)\) существуют конечные, определяемые самим источником \(C_a\), \(c_a>0\), такие что
\[
 |D_a(u)|+|D_a'(u)|\le C_a e^{-c_a u},\qquad u>0.
\tag{14}
\]
Можно взять \(c_a=\pi(a-1/2)/2\). Аналогично
\[
 |L(u)|+|L'(u)|\le C_L e^{-\pi u/2}.
\tag{15}
\]
Остатки доказаны выше, а на промежуточном компакте используются максимумы явно заданных непрерывных функций. Все константы конечны независимо от знака V. Они могут быть выбраны едиными для a в любом фиксированном компакте внутри (1/2,1).

Формула (5), (14) и её первая t-производная дают, равномерно по s,
\[
 |v_x(t,s)|+|\partial_t v_x(t,s)|
 \le C_x(t^{3/4}+t^{-1/4})e^{-c_a t},\qquad t\ge1.
\tag{16}
\]
Это одновременно оплачивает оба условных конца \(s=0,1\).

Полный theta-ряд для r на \(t\ge1\) даёт
\[
 r(t)\ge(4\pi^2-6\pi)t e^{-\pi t},\quad
 |r(t)|+|r'(t)|\le C(1+t)e^{-\pi t}.
\tag{17}
\]
Все слагаемые r положительны на этой полуоси; для верхней оценки суммируются модули всех производных. В частности \(r'/r\) ограничена. Из
\[
 e_t(s)=\sqrt{t/r(t)}\,L(ts)L(t(1-s))
\]
и (15)–(17) следует \(\sup_{t\ge1}\|e_t'\|_{\mathcal K}<\infty\). Не используется ложное постоянство \(p_t\).

Далее
\[
 y_x(t):=\sqrt{\overline W(t)}F_x(t)
 =\sqrt{\frac\mu{2A^2}}\,a^{5/4}t^{1/4}\frac{r(at)}{\sqrt{r(t)}},
 \quad q_x=e_t y_x.
\]
Функции y_x и y_x' ограничены полиномом от t, умноженным на \(e^{-\pi(a-1/2)t}\). Поэтому q_x, q_x', z_x, z_x' ограничены и экспоненциально убывают. Множитель \(X+x\) и его производная \(1/(2t)\) этого не меняют.

Итак, для всех трёх каналов и любой конечной строки **доказана**, а не постулирована, конечность
\[
 K_{c,0}^j:=\sup_{t\ge1}\|\mathbf U_c^j(t)\|<\infty,
 \qquad K_{c,1}^j:=\sup_{t\ge1}\|\partial_t\mathbf U_c^j(t)\|<\infty.
\tag{18}
\]
Это source-defined константы; их численные значения здесь не вычисляются. Например \(K_{c,l}^j\le\sum_i|c_i|K_{x_i,l}^j\). Нет утверждения о единой константе в невзвешенной коэффициентной норме при всех N или при a, стремящемся к 1/2. `[ABSTRACT][PAPER]`

## 5. Условный score и вес не исчезают при дифференцировании

Для \(\rho_t=\partial_t\log p_t\), где производная берётся при фиксированном s,
\[
 \partial_t(C_tg_x)=C_t(\partial_tg_x)+C_t(\rho_tg_x).
\tag{19}
\]
Законность следует из (11)–(17) на компактных t-интервалах: возникающие обратные степени s и 1-s поглощаются полными экспоненциальными концами. В частности \(C_t\rho_t=0\), но \(C_t(\rho_tg_x)\) не зануляется этим равенством.

В полуплотности это же изменение записано как
\[
 \Pi_t'=e_t'\langle e_t,\cdot\rangle+e_t\langle e_t',\cdot\rangle,
 \qquad q_x'=\Pi_t v_x'+\Pi_t'v_x.
\tag{20}
\]
Слагаемое \(\Pi_t'v_x\) сохранено. Обе половины производной \(e_t\) восстанавливают весь score в (19). Например точная производная скалярной амплитуды равна
\[
 \frac{y_x'}{y_x}
 =\frac1{4t}+a\frac{r'(at)}{r(at)}-\frac12\frac{r'(t)}{r(t)}.
\tag{21}
\]
Здесь уже учтены и \(\overline W'\), и изменение условного закона, и производная исходного отношения. Поле никогда не оценивается через недоказанный глобальный Lipschitz-модуль растущего \(F_x\). `[ABSTRACT][PAPER]`

## 6. Новый исходный расчёт: резкая скорость пересечения физической границы

Работаем на одной вероятностной цепи из H, L14–L17. Введём
\[
 d_1=\mathbb ET^*=2\pi/5,\quad d_2=\mathbb E(T^*)^2=4\pi^2/21,
 \quad \beta=\pi/e,\quad L_r=\pi^2.
\]
Имеем \(\mathbb ER_m=d_1 6^{-m}\), \(\mathbb ER_m^2=d_2 15^{-m}\). Значение d_1 следует из \(\mathbb ET^2=2\pi^2/15\) и \(\mu=\pi/3\).

Продолженная нулём плотность r имеет \(\|r\|_\infty\le\beta\) и глобальный Lipschitz-модуль не больше L_r. Действительно, r есть свёртка \(\pi^2te^{-\pi t}\mathbf1_{t\ge0}\) с вероятностным законом остатка; исходная плотность имеет максимум \(\pi/e\) и Lipschitz-модуль \(\pi^2\). Это не новое предположение о гладкости.

Для \(m\ge1\) положим
\[
 A_m=S_m-T_1,\quad \chi_m=\mathbf1_{S_m<1\le Z_*},\quad p_m=\mathbb E\chi_m.
\]
Пара \((A_m,R_m)\) независима от T_1. Условно по этой паре,
\[
 p_m=\mathbb E\int_{1-A_m-R_m}^{1-A_m}r(u)\,du,
\]
и, следовательно,
\[
 p_m\le\beta d_1 6^{-m},\qquad
 \mathbb E[R_m\chi_m]\le\beta d_2 15^{-m},
\tag{22}
\]
\[
 \left|p_m-\mathbb E[R_m r(1-A_m)]\right|
 \le\frac{L_r}{2}d_2 15^{-m}.
\tag{23}
\]
Нулевое продолжение r делает эти формулы законными и при отрицательных концах интервала.

Чтобы вычислить главный член, наклоним **первые m множителей**, а не терминальный источник:
\[
 \nu_H^\dagger(dh)=6h\nu_H(dh)=6(h^{1/2}-h)\,dh,
 \qquad\mathbb E H^\dagger=2/5.
\tag{24}
\]
Поскольку \(R_m=W_m Z_{\mathrm{tail},m}\), где хвост независим и имеет среднее d_1,
\[
 \mathbb E[R_m r(1-A_m)]
 =d_1 6^{-m}\mathbb E^\dagger r(1-A_m^\dagger).
\tag{25}
\]
При одном бесконечном наборе H^dagger зададим
\[
 A_\infty^\dagger=\sum_{j=2}^\infty
  \left(\prod_{l=1}^{j-1}H_l^\dagger\right)T_j,
 \qquad c_\dagger=\mathbb E^\dagger r(1-A_\infty^\dagger).
\tag{26}
\]
Этот ряд конечен почти наверное и в L1, так как
\[
 \mathbb E A_\infty^\dagger=2\pi/9,\quad
 \mathbb E(A_\infty^\dagger-A_m^\dagger)
 =\frac{5\pi}{9}(2/5)^m.
\tag{27}
\]
Отсюда (23)–(27) дают полностью числовой остаточный бюджет
\[
 \boxed{
 |p_m-d_1c_\dagger6^{-m}|
 \le\frac{20\pi^4}{63}\,15^{-m},\qquad m\ge1.}
\tag{28}
\]

**Главная константа строго положительна независимо от V.** По неравенству Маркова и \(\pi<4\),
\[
 \mathbb P(A_\infty^\dagger\le9/10)
 \ge1-20\pi/81>1/81.
\]
Позитивность непрерывной плотности r на (0,infinity) поэтому даёт
\[
 \boxed{c_\dagger\ge\frac1{81}\min_{1/10\le u\le1}r(u)>0.}
\tag{29}
\]
Это минимум **положительной исходной плотности на положительном вещественном компакте**, не неизвестный минимум Fourier-преобразования и не предположение RH. Тем самым (2) доказано. `[COFINAL_FAMILY][PAPER]`

## 7. Полный среднеквадратичный перенос: объём плюс ненулевая граница

Для любой из колонок/строк (6) определим в одном пространстве
\(L^2(\Omega_{\rm renewal};\mathcal K\oplus\mathcal K)\)
\[
 \mathbf F_{c,m}^j=\mathbf1_{S_m\ge1}\mathbf U_c^j(S_m),\qquad
 \mathbf F_{c,\infty}^j=\mathbf1_{Z_*\ge1}\mathbf U_c^j(Z_*).
\tag{30}
\]
При \(S_m<1\) значение равно нулю; никакие исходные сигналы вне физической области не нужны. В оценках продолжаем \(\mathbf U(t)\) константой \(\mathbf U(1)\) ниже 1, то есть используем \(\mathbf U(t\vee1)\). Это техническое продолжение всегда сопровождается исходным индикатором.

Пусть \(J_c^j=\mathbf U_c^j(1)\). Точное тождество остатка:
\[
 \mathbf F_{c,\infty}^j-\mathbf F_{c,m}^j
 =\mathbf1_{Z_*\ge1}\left[\mathbf U_c^j(Z_*)-
                              \mathbf U_c^j(S_m\vee1)\right]
   +J_c^j\chi_m.
\tag{31}
\]
Первый член имеет норму не больше \(K_{c,1}^j R_m\). Квадрат первого члена оплачивается \(d_2 15^{-m}\). **Смешанный член с границей также сохранён**; (22) даёт
\[
 \boxed{
 \left|\mathbb E\|\mathbf F_{c,\infty}^j-\mathbf F_{c,m}^j\|^2
                 -\|J_c^j\|^2p_m\right|
 \le d_2\left[(K_{c,1}^j)^2+2\beta\|J_c^j\|K_{c,1}^j\right]15^{-m}.}
\tag{32}
\]
Никакой независимости границы, веса или сигнала от R_m здесь нет.

В частности весь ряд ошибок полных полей конечен:
\[
 \boxed{
 \sum_{m\ge1}\mathbb E\|\mathbf F_{c,\infty}^j-\mathbf F_{c,m}^j\|^2
 \le \frac{\beta d_1}{5}\|J_c^j\|^2
 +\frac{d_2}{14}\left[(K_{c,1}^j)^2+2\beta\|J_c^j\|K_{c,1}^j\right].}
\tag{33}
\]
Для m=0 добавляется не больше \((K_{c,0}^j)^2\). Оценки действуют отдельно для micro, proj и loss, а значит включают нелинейность g, обе условные половины, изменение p_t, смешанный сигнал B и физический вес. `[COFINAL_FAMILY][PAPER]`

Из (28), (32) получаем ещё более точную формулу:
\[
 \mathbb E\|\mathbf F_{c,\infty}^j-\mathbf F_{c,m}^j\|^2
 =\|J_c^j\|^2d_1c_\dagger6^{-m}+\varepsilon_{c,m}^j,
\tag{34}
\]
\[
 |\varepsilon_{c,m}^j|\le
 \left\{\|J_c^j\|^2\frac{20\pi^4}{63}
 +d_2[(K_{c,1}^j)^2+2\beta\|J_c^j\|K_{c,1}^j]\right\}15^{-m}.
\]

Для одного узла x в проецированном канале
\[
 \|J_x^{\mathrm{proj}}\|^2
 =\overline W(1)F_x(1)^2(1+x^2)>0.
\tag{35}
\]
Следовательно средний квадрат полного остатка **не является \(O(15^{-m})\)** для этой фиксированной колонки. Для всех достаточно больших m он не меньше половины положительного главного члена в (34). Если предлагалась оценка с любой конечной константой K, то
\[
 K15^{-m}-\mathbb E\|\mathbf F_{x,\infty}^{\mathrm{proj}}-
                           \mathbf F_{x,m}^{\mathrm{proj}}\|^2
 \le K15^{-m}-\tfrac12\|J_x^{\mathrm{proj}}\|^2d_1c_\dagger6^{-m}<0
\]
при достаточно большом m. Это строгая отрицательная верхняя огибающая **дефекта предложенного rate-bound**, не V. `[COFINAL_FAMILY][PAPER]`

Нулевые направления сохранены. В proj-канале \(J_c=0\) равносильно одновременным
\[
 \sum_i c_iF_{x_i}(1)=0,\qquad\sum_i c_ix_iF_{x_i}(1)=0.
\tag{36}
\]
Для них (32) действительно даёт чистый объёмный \(15^{-m}\). Нулевой скалярный граничный поток сам по себе не равносилен двум условиям (36).

## 8. Абсолютно сходящийся телескоп именно полной формы

Продолжим \(\psi_c^j\) нулём ниже 1, сохраняя её скачок:
\[
 b_c^j=\psi_c^j(1),\qquad
 \phi_c^j(t)=\mathbf1_{t\ge1}\psi_c^j(t),\qquad \phi_c^j(0)=0.
\]
По (18), \(|(\psi_c^j)'|\le2K_{c,0}^jK_{c,1}^j\). Для s<=t точно
\[
 \phi_c^j(t)-\phi_c^j(s)
 =b_c^j\mathbf1_{s<1\le t}
  +\int_s^t\mathbf1_{u>1}(\psi_c^j)'(u)\,du.
\tag{37}
\]
Это и есть граничный член, который нельзя назвать нулевым.

Положим
\[
 E_m^j[c]=\mathbb E\phi_c^j(S_m),\quad E_0^j[c]=0,\quad
 D_c^j=2K_{c,0}^jK_{c,1}^j+\beta|b_c^j|.
\]
Для каждого \(m\ge1\) тем же условным расчётом по T_1, теперь с приращением \(W_mT_{m+1}\),
\[
 \mathbb E|\phi_c^j(S_{m+1})-\phi_c^j(S_m)|
 \le\mu D_c^j6^{-m}.
\tag{38}
\]
Первое приращение не превосходит \((K_{c,0}^j)^2\) по модулю. Поэтому
\[
 \sum_{m\ge0}\mathbb E|\phi_c^j(S_{m+1})-\phi_c^j(S_m)|
 \le (K_{c,0}^j)^2+\frac\mu5D_c^j<\infty.
\tag{39}
\]
Обмен суммы и ожидания теперь оплачен независимо от целевого знака. Кроме того
\[
 \left|\mathbb E\phi_c^j(Z_*)-E_m^j[c]\right|
 \le d_1D_c^j6^{-m},\qquad m\ge1.
\tag{40}
\]

Для **каждой пары узлов**, а затем каждой комплексной строки, из (9)–(10) следует
\[
 \boxed{
 V[c]=E_\infty^{\mathrm{micro}}[c]-E_\infty^{\mathrm{loss}}[c]
     =E_\infty^{\mathrm{proj}}[c]
     =\sum_{m\ge0}(E_{m+1}^{\mathrm{proj}}[c]-E_m^{\mathrm{proj}}[c]).}
\tag{41}
\]
Все три телескопа абсолютно сходятся. При каждом m точное micro-loss равенство сохраняется, поскольку \(\Pi_{S_m}\) используется в обоих каналах. **Закон S_m не объявляется r*, и \(p_{S_m}\) не заменяется \(p_{Z_*}\).** Это вспомогательные аппроксимации физического поля; лишь их доказанный терминальный закон возвращает исходную V.

Положительные множители, \(W\), сигнал \(B\) и конечные границы не удалены ни из одного равенства. На \(t=\infty\) поля и их гладкие энергетические плотности стремятся к нулю по §4. При \(s=0,1\) все использованные пределы оплачены (12)–(16); интегрирования по частям с необъявленными условными краями нет. `[COFINAL_FAMILY][PAPER]`

## 9. Первый неоплаченный знак и результат испытания положительных приростов

Для краткости здесь \(j=\mathrm{proj}\). Обозначим через
\(\overline R_*(t)=\mathbb P(Z_*\ge t)=\mu^{-1}\int_t^\infty u r(u)du\)
**известную положительную функцию выживания**, не новую плотность или предпосылку о V.

Из (37)–(41) получается полностью конечный баланс
\[
 \boxed{
 V[c]=b_c\overline R_*(1)
       +\int_1^\infty\overline R_*(t)\psi_c'(t)\,dt.}
\tag{42}
\]
Его первая ещё не доказанная знаковая стрелка была бы
\[
 \int_1^\infty\overline R_*(t)\psi_c'(t)\,dt
 \ \ge\ -b_c\overline R_*(1)\quad\text{для всех исходных строк}.
\tag{43}
\]
(43) здесь **не вводится как новый оплаченный Y или независимое достижение**: после (42) это тот же оставшийся целевой знак. Отличие результата данной попытки — независимые полные бюджеты (28), (33), (39), (40) и точная обнаруженная потеря на границе, а не новое название (43).

Объект в (43) можно вычислять непосредственно из источника. Для пары x,y, a=e^(2x), b=e^(2y), положим
\[
 A_{xy}(t)=\frac\mu{2A^2}(ab)^{5/4}\sqrt t\,
                      \frac{r(at)r(bt)}{r(t)}>0.
\]
Тогда
\[
 \begin{aligned}
 \psi_{xy}(t)&=A_{xy}(t)(\log t+x+y),\\
 \psi_{xy}'(t)&=A_{xy}(t)\left\{\frac1t+(\log t+x+y)
 \left[\frac1{2t}+a\frac{r'(at)}{r(at)}
 +b\frac{r'(bt)}{r(bt)}-\frac{r'(t)}{r(t)}\right]\right\}.
 \end{aligned}
\tag{44}
\]
Это сохраняет все моды и весь меняющийся условный score через (19)–(21). Положительность отдельных A_xy или функции выживания не доказывает знак их произвольной комплексной смеси.

### 9.1. Реальная граница имеет строго отрицательный вклад

Для одного фиксированного x<0,
\[
 b_x=2x\overline W(1)F_x(1)^2<0,\quad
 b_x\overline R_*(1)<0.
\tag{45}
\]
Хвост ещё не появившейся граничной массы равен \(b_xp_m\). По (28) для всех достаточно больших m,
\[
 b_xp_m\le-\frac{|b_x|d_1c_\dagger}{2}\,6^{-m}<0.
\tag{46}
\]
Это отрицательная верхняя огибающая **одного полностью идентифицированного граничного члена**. Положительный объём может его компенсировать — (46) не является отрицательной V.

### 9.2. Неотрицательные приросты почти наверное действительно исключены

Зафиксируем x в I и
\[
 \delta_x=(e^{-2x}-1)/2>0,\quad
 J_x=[1+\delta_x/2,1+\delta_x]\subset(1,e^{-2x}).
\]
Определим из положительного источника
\[
 \eta_x=-[\log(1+\delta_x)+2x]
          \min_{t\in J_x}\overline W(t)F_x(t)^2>0.
\]
На событии
\(\mathcal A_{m,x}=\{S_m<1,\ S_{m+1}\in J_x\}\)
имеем точный полный прирост
\[
 \phi_x(S_{m+1})-\phi_x(S_m)\le-\eta_x<0.
\tag{47}
\]
У \(\mathcal A_{m,x}\) положительная вероятность для каждого конечного m>=0. Для m>=1 событие S_m<1 имеет положительную вероятность, W_m>0 почти наверное, а условно по первым m инновациям T_(m+1) имеет положительную плотность на всей положительной полуоси. Для m=0 достаточно T_1 in J_x. Следовательно
\[
 \mathbb E[\mathbf1_{\mathcal A_{m,x}}
      (\phi_x(S_{m+1})-\phi_x(S_m))]
 \le-\eta_x\mathbb P(\mathcal A_{m,x})<0.
\]
Это убивает ровно **поточечный положительный telescoping-transfer** выбранной конструкции. Не доказана отрицательность всего среднего приращения: дополнение события не отбрасывается.

**Ремонт выполнен в той же конструкции:** граница выделена, её масштаб вычислен, более медленный ряд суммирован, полная условная плотность оставлена движущейся. После ремонта не остаётся неоплаченной бесконечной нормы; остаётся (43), то есть подлинная интегральная компенсация со знаком. Предполагать её из одной конечности (39) было бы ошибкой. `[ABSTRACT][PAPER]`

## 10. Контроли, кванторы и точная область исключений

**Плант аффинного сигнала.** Для неотсечённой скалярной U(t)=t ошибка равна R_m, поэтому её средний квадрат буквально d_2 15^(-m). Это проверяет, что исходный коэффициент не был потерян.

**Плант ступени.** Для постоянного U(t)=1 выше границы и нуля ниже неё ошибка равна chi_m; (31)–(34) дают точно p_m. При ошибочном удалении границы этот тест дал бы ноль, хотя (28)–(29) доказывают ненулевой главный член. Это различает настоящий нуль от малого остатка без вычислений theta.

**Комплексный плант ортогональности.** Для проекции на первую координату в C² оба смешанных члена между её образом и ядром исчезают, но оставшийся межканальный функционал 2 Re<g,d> имеет оба знака. Проекция не превращает swap-матрицу J в положительную матрицу. Простая рациональная калибровка включена в приложение.

**Отрицательные соседние источники.** Не постулируется закон L14 для деформированной theta или для f0. [PY] при фиксированном среднем характеризует конкретный исходный закон. Их старые отрицательные строки не используются как контрпример ему. Более сильный контроль здесь внутренний: (45)–(47) относятся к самой theta, но только к указанным компонентам и промежуточным приращениям.

**Кванторы:** m относится к глубине renewal, N — к произвольному числу физических узлов. Ни один не заменяет другой. Все утверждения о полях действуют для каждого конечного N и произвольных комплексных c. Константы зависят от самой строки по доказанным source-suprema (18), не от её предполагаемого знака; на компактном интервале узлов есть единые колонковые bounds. Упрощение до фиксированного ранга, смена нормы f или предельного consumer не производится.

**Не исключены:** неотрицательность полной V, интегральная компенсация между разными renewal-уровнями, другие сцепления или более богатая конструкция поля. Не возобновлялись raw-k monotonicity, scalar Sturm, NULLFIELD-coercivity, global gamma preserver, C6 или припаркованные Barvinok-попытки.

## 11. Ledger, два точных представления остатка и один следующий шаг

| Утверждение | Итог | Scope / verifier |
|---|---|---|
| Закон T*, исходные моменты R_m | Принятый вход H/[PY], не новая находка | ABSTRACT / PAPER |
| Общая half-density карта и kernel-level (10) | Выведены здесь | ABSTRACT / PAPER |
| Полный moving-projection domain и (18) | Выведены здесь, включая оба s-конца | ABSTRACT / PAPER |
| Граничная асимптотика (28) с положительным c_dagger | Выведена здесь с остатком 20pi^4/63 | COFINAL_FAMILY / PAPER |
| Полный нелинейный MSE бюджет (32)–(34) | Выведен здесь для всех трёх каналов | COFINAL_FAMILY / PAPER |
| Полная сходимость micro/loss и подписанного телескопа | Выведена здесь, без предпосылки о конечности | COFINAL_FAMILY / PAPER |
| Наследование 15^(-m) буквальным отсечённым полем | Опровергнуто на каждом одноузловом proj-поле | THEOREM_SHAPE; COFINAL_FAMILY / PAPER |
| Неотрицательность каждого полного прироста почти наверное | Опровергнута (47) | THEOREM_SHAPE; ABSTRACT / PAPER |
| Знак среднего полного прироста; (43); V>=0 | Не доказаны и не опровергнуты | ABSTRACT / CONDITIONAL |

Два представления для открытого остатка фиксируются до любой следующей вычислительной эскалации. Они не запускаются как два новых опыта.

**R1 — survival-weighted bulk/trace balance**, буквально (42)–(44). Стоимость проверки объекта 1/5; ожидаемая решающая сила исходной знаковой оценки 5/5; стоимость её доказательства пока неизвестна. Преимущество — один конечный интеграл, явный отрицательный след, никакой неизвестной суммы хвостов. Риск — считать entrywise-позитивность матричным знаком. Без доказательства (43) это только представление.

**R2 — ортогональные мартингальные приращения двух каналов.** Для терминального bounded поля (30) взять M_m=E[F_infinity^proj | F_m], где F_m содержит первые m H,T. Тогда M_m сходится в L², и ортогональность приращений даёт
\[
 \mathbb E\langle F_\infty,\mathbb JF_\infty\rangle
 =\langle M_0,\mathbb JM_0\rangle+
   \sum_{m\ge1}\mathbb E\langle M_m-M_{m-1},
                              \mathbb J(M_m-M_{m-1})\rangle.
\]
Ряд абсолютно сходится, поскольку норма J равна 1 и квадраты норм мартингальных приращений суммируются. Межуровневые смешанные члены исчезают; **внутриуровневый межканальный знак не исчезает**. Стоимость проверки объекта 2/5; решающая сила 4/5, если найдено новое совместное правило для двух каналов. Риск — выдать обычную мартингальную ортогональность за положительность J. Это не уже доказанный положительный ответ и не другая начатая модель.

**Единственный следующий Codex joint:** независимо проверить точные байты этого отчёта, прежде всего conditional-first-innovation шаг (23)–(28), moving-projection bounds и знак (47). Успех — приём только full-field transport budget and cutoff-rate obstruction. Проверка не должна переключать задачу на поиск новой сетки или объявлять (43) погашенной. Это проверка нового аналитического результата, не обещание новой RH-леммы.

**DISCRIMINATOR:** для нулевого граничного коэффициента проверить обе амплитуды (36), а не округлённый поток. Для спорного rate-transfer использовать \(6^m\mathbb E\|F_\infty-F_m\|^2\), предел которого в (34) доказан, а не измерен. Для знака V нужен полный (42); ни (46), ни отрицательное событие (47) его не заменяют.

## 12. Dependency epistemics и closeout

```yaml
DOWNSTREAM_CONSUMER: all_complex_finite_original_V_nonnegativity_then_accepted_Weil_transfer
ACTUAL_CONSUMER_REQUIREMENT: V[c]>=0_for_every_finite_row_on_I
ORIGINAL_REQUESTED_OBJECT: sizebiased_source_budget_transfer_to_full_compensation
ORIGINAL_OBJECT_IS: NOT_NECESSARY_as_a_specific_proof_method
KNOWN_WEAKER_INTERFACES:
  - any_independently_proved_full_integrated_identity_with_nonnegative_total
  - cross_level_compensation_without_nonnegative_individual_increments
  - summable_error_rates_other_than_15_power_minus_m
FAILURE_TYPE: NO_DERIVATION_of_the_integrated_sign
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: conditional_half_density_transport_plus_sharp_cutoff_crossing_rate
REOPEN_TRIGGER: new_source_identity_controlling_the_complete_bulk_trace_balance
SECONDARY_KILL_1:
  scope: THEOREM_SHAPE
  object: unchanged_15_power_minus_m_bound_for_the_literal_cutoff_coupling
  evidence_kind: strict_asymptotic_lower_bound_with_explicit_error
  evidence_ref: Sections_6_7_equations_28_29_34_35
  epistemic_status: MATHEMATICALLY_DEAD_AT_THIS_SCOPE_PENDING_REVIEW
SECONDARY_KILL_2:
  scope: THEOREM_SHAPE
  object: almost_sure_nonnegative_full_renewal_increments_for_this_coupling
  evidence_kind: strict_negative_upper_bound_on_positive_probability_event
  evidence_ref: Section_9_equation_47
  epistemic_status: MATHEMATICALLY_DEAD_AT_THIS_SCOPE_PENDING_REVIEW
ROUTE_FAMILY_KILL: NONE
```

Что стало меньше: неоплаченный перенос скалярного остатка через нелинейные likelihoods, физический вес, меняющуюся условную проекцию и границу заменён доказанными bounds (32)–(40). Конечность полного подписанного телескопа больше не новая гипотеза.

Что не стало меньше: универсальный исходный знак. После этих bounds он по-прежнему требует (43), а не следует из геометрической суммы. Это не новый source-sign supplier.

Что не повторять: W_max вместе с сырым глобальным Lipschitz-модулем Cg; отсутствие cutoff-jump; перенос 1/15 без trace-проверки; объявление подписанных мартингальных/renewal-приращений квадратами.

P1 **confirmed**: §4 и (32). P2 **confirmed**: (28)–(29). P3 **confirmed**: (39) и (47). Предсказания не переименованы после результата. Исторические counters не реконструированы, не сброшены, репозиторное состояние не меняется.

Memory: target=full conditional compensation; status=OPEN; failed_strategy=positive-pathwise-renewal-telescope; operator=MINIMAL_LEMMA; invariant=literal physical cutoff produces a nonzero trace; next_decisive_test=independent audit of the sharp crossing and full-channel estimates. Route score **3/5**: полезный, но не решающий транспортный результат.

## 13. Verification handoff и публикация

Единственный новый репозиторный путь указан в YAML. Ветка — `codex_mac/gamma-reciprocity-20260914`; перед записью прочитана её актуальная вершина. Запись — обычное создание одного UTF-8 файла через GitHub Contents API, без force и без правок чужих файлов. Точный commit SHA возвращается в чат после подтверждённой записи; он не может быть самоссылочно вписан в собственное содержимое. Проверка diff должна показать ровно один добавленный назначенный файл.

Lean-файлы не написаны, Lean/lake не запускались, axiom profile не получен. Поэтому здесь нет команды фиктивного Lean gate и нет LEAN_PROVED. Новые теоремы имеют статус PAPER-кандидатов до независимого аналитического приёма. Никакой результат арифметического приложения этого приёма не заменяет.

Независимый проверяющий должен отдельно проверить (11)–(17), полное ядро (10), обе ортогональные смеси (9), закон смены H в (25), оба конца интервала в (23), все пределы (27)–(34), абсолютно суммируемое доминирование (38)–(40) и точную область (47). При успехе меняется только состояние приёма этих теорем; V/RH автоматически не повышаются.

## Приложение A. Исполненная рациональная калибровка

Это не theta-вычисление, не квадратура и не проверка вероятностного предела. Код проверяет арифметику констант и простой плант смешанного вычитания. Здесь `q` — целый порядок момента H; например `eh(2)` означает E[H²]. Подставлять узлы, моменты xi или численные значения источника в этот код не требуется.

```python
from fractions import Fraction as F

def eh(q: int) -> F:
    return F(1, (2*q+1)*(q+1))

checks = {
    'H_density_mass': eh(0) == 1,
    'H_first': eh(1) == F(1,6),
    'H_second': eh(2) == F(1,15),
    'tilted_H_first': eh(2)/eh(1) == F(2,5),
    'T_second_over_pi2': F(1,9)+F(1,45) == F(2,15),
    'T_third_over_pi3': F(1,27)+3*F(1,3)*F(1,45)+F(4,945) == F(4,63),
    'Tstar_first_over_pi': F(2,15)/F(1,3) == F(2,5),
    'Tstar_second_over_pi2': F(4,63)/F(1,3) == F(4,21),
    'Atilt_mean_over_pi': F(1,3)*F(2,5)/(1-F(2,5)) == F(2,9),
    'Atilt_tail_prefactor_over_pi': F(1,3)/(1-F(2,5)) == F(5,9),
    'crossing_error_over_pi4': F(4,21)/2+F(2,5)*F(5,9) == F(20,63),
    'all_scalar_R2_budget_over_pi2': F(4,21)/(1-F(1,15)) == F(10,49),
    'bulk_m_ge1_budget_over_pi2': F(4,21)*F(1,14) == F(2,147),
    'boundary_m_ge1_factor': F(2,5)*F(1,5) == F(2,25),
    'crossing_positive_probability_from_pi_lt4': 1-F(2*4,9)/F(9,10) == F(1,81),
    'mixed_projection_plant': (2*(1*3+2*(-4))-2*(2*(-4))) == 2*1*3,
}
for key, passed in checks.items():
    print(f'{key}: {"PASS" if passed else "FAIL"}')
if not all(checks.values()):
    raise SystemExit(1)
print(f'CHECKS={len(checks)}; ALL_PASS; NO_SOURCE_EVALUATIONS')
```

Буквальный stdout:

```text
H_density_mass: PASS
H_first: PASS
H_second: PASS
tilted_H_first: PASS
T_second_over_pi2: PASS
T_third_over_pi3: PASS
Tstar_first_over_pi: PASS
Tstar_second_over_pi2: PASS
Atilt_mean_over_pi: PASS
Atilt_tail_prefactor_over_pi: PASS
crossing_error_over_pi4: PASS
all_scalar_R2_budget_over_pi2: PASS
bulk_m_ge1_budget_over_pi2: PASS
boundary_m_ge1_factor: PASS
crossing_positive_probability_from_pi_lt4: PASS
mixed_projection_plant: PASS
CHECKS=16; ALL_PASS; NO_SOURCE_EVALUATIONS
```

Все 16 сравнений прошли. Это арифметическая калибровка, не независимая проверка доказательства.

## END FILE docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md

## BEGIN FILE docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md
SHA256: fb83c216aef4687425074732904f9d2f52aac77527a926e7556fb0067335e2bd

# Any open interval already carries the full all-rank sign question

STATUS: ACCEPTED_CONDITIONAL_CONSUMER_BRIDGE_PAPER.
GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. ALL_ORDER_SOURCE_SIGN: OPEN.
RH: OPEN. PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

This is a conditional consumer bridge for the pending TWOCHANNEL request,
not a new source-sign attempt. The sent request and its input report remain
unchanged at de2271bebae87c24ca0dfd3d02ae885de8db1b11.

## A1. Analytic propagation lemma, with the all-rank hypothesis exposed

Let J be a nonempty open real interval, Omega a complex open set containing
J, and K holomorphic on Omega x Omega. Suppose K(x,y)=conjugate(K(y,x))
for real x,y in J. If the restriction of K to I x I is positive semidefinite
for EVERY finite family of nodes and complex coefficients on one nonempty
open subinterval I of J, then K is positive semidefinite on all of J.

Here holomorphic refers to both unbarred complex variables. Equivalently
K(conjugate(z),w) is a sesquiholomorphic kernel on conjugation-stable pieces;
the proof below only forms Gram matrices at real nodes.

Proof. Assume K is PSD on an open interval B contained in J. Fix a in B
and eta>0 such that the complex disk |z-a|<eta is contained in Omega.
For each integer n>=0, forward differences at a give functionals

    ell_(n,h)(g)=sum_(k=0)^n (-1)^(n-k) binom(n,k) g(a+kh)/(n! h^n)
                  -> g^(n)(a)/n! as h->0 through real positive h. (A1)

For any fixed maximum order M and any fixed collection of old nodes in B,
all nodes a+kh lie in B for sufficiently small h. Applying these functionals
and the old evaluations to BOTH variables of the PSD kernel, then taking
h->0, gives a PSD block matrix of old evaluations and derivative evaluations.
In particular its derivative block is

    B_mn=partial_x^m partial_y^n K(a,a)/(m! n!), 0<=m,n<=M.     (A2)

This uses only finite congruences and a finite-dimensional matrix limit.
The coefficients of ell are real; arbitrary complex vectors remain allowed.

For finitely many new real nodes y_j with |y_j-a|<eta and y_j in J,
replace each new evaluation by the finite Taylor functional

    L_(M,y_j)(g)=sum_(n=0)^M (y_j-a)^n g^(n)(a)/n!.

Together with any old evaluations this again gives a PSD matrix. Its
new/new entries are the double Taylor partial sums using (A2). They tend
to K(y_i,y_j) by absolute convergence on the polydisk at (a,a).
Its old/new entries tend to K(x_i,y_j) by the one-variable Taylor series
in the SECOND variable, with old x_i fixed in B. The radius eta is valid
for every such old x_i because the domain is the product Omega x Omega.
Taking M->infinity thus proves positivity on

    B union ((a-eta,a+eta) intersection J).                    (A3)

This includes all mixed old/new matrices, not just positivity separately
on two overlapping intervals. The order of limits is fixed: first h->0
for each finite M, then M->infinity. No bounded inverse, uniform bound on
Taylor coefficients in M, or exchange of those limits is assumed.

Finally fix any desired finite node family in J. The real segment joining
it to an interior point of I is compact in J and in Omega. A sufficiently
small uniform disk radius therefore works at every point on that segment.
Repeated applications of (A3) with overlapping intervals, in finitely many
steps, include the entire family. This proves the lemma.

## A2. The actual full theta kernel has the required analytic extension

The exact source and consumer are those of
REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, sections1--2 and10,
at 667c22a589336a584ee31a84ab42a9ad9d1bcbf3, 15303bytes/335LF,
SHA2561e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.
That independently accepted report fixes f=Phi/A, A=||Phi||_2, and

    Phi(z)=sum_(n>=1) [4pi^2 n^4 exp(9z/2)-6pi n^2 exp(5z/2)]
                       exp(-pi n^2 exp(2z)),
    V(z,w)=integral_0^infinity (z+w+2t) f(z+t)f(w+t)dt.         (A4)

Let S={z:|Im z|<pi/4}. On each compact subset of S, Re(exp(2z)) has
a strictly positive lower bound. The full series in (A4) converges normally
there and defines a holomorphic Phi; it is not a finite theta approximation.

More explicitly, for z in a fixed compact subset of S and t>=0, let
m<=Re z<=M and |Im z|<=theta<pi/4. With c=pi exp(2m)cos(2theta)>0,
the absolute sum for Phi(z+t) is bounded by

    C exp(9t/2) sum_(n>=1)(n^4+n^2) exp(-c n^2 exp(2t))
      <= C' exp(9t/2) exp(-(c/2) exp(2t)).                    (A5)

Indeed split the exponent in half and use exp(2t)>=1 in the summable
n-dependent half. For any compact pair (z,w), the product of two bounds
(A5), times a constant multiple of 1+t, is integrable in t. The integrals
over finite t-intervals are holomorphic in both variables; their tails
converge uniformly on compact subsets of S x S. Thus V is jointly
holomorphic on S x S. On real nodes V is real symmetric.

Applying A1 to Omega=S, J=R proves, for EVERY nonempty open interval I,

    [all finite V matrices on I are PSD]
       iff [all finite V matrices on R are PSD].              (A6)

By the already accepted full-sign transfer and its named classical Weil
criterion dependency, either side of (A6) is equivalent to RH. This is an
equivalence only: neither side's positive sign is supplied here.

In particular an all-rank theorem on x>R, on |x|>R, or on any fixed open
window suffices for the full consumer. Conversely, if there is a negative
V witness somewhere, every nonempty open interval contains some finite
complex negative witness. A1 gives no useful bound on its rank, coefficient
size or conditioning. This does not contradict positive fixed-rank regions.

## A3. Application to the exact pending relative comparison

The independently accepted global W is T12--T14 in
REPORT_2026-09-13_TWOCHANNEL_LAPLACE_BRIDGE.md at de2271bebae87c24ca0dfd3d02ae885de8db1b11,
11996bytes/245LF, SHA256
e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908.
It is PSD on all real nodes. Consequently, if some delta>0 satisfies
V>=delta W as forms for ALL finite complex families on an exterior interval,
V is PSD there and A2 already supplies the full consumer bridge.

The same delta in fact propagates, provided this particular W is retained.
To verify the extra analytic hypothesis, fix a compact real interval [-L,L].
The analytic D(z)=V(z,z) is strictly positive for real z: by evenness
D(x)=D(|x|)=integral_(|x|)^infinity 2u f(u)^2 du>0.
Hence D has a holomorphic square root on a sufficiently thin rectangle
around [-L-1,L+1]; shrink the rectangle until Re D>0 there.

Every real square-root argument in T12--T13 is strictly positive there:
r_x=sqrt(x^2+4)>=2, cosh x>=1, 1-1/r_x>=1/2, and N_x^2>=1.
By compactness and continuity, shrink the same rectangle so all their
chosen positive branches extend holomorphically. Also choose it so
|Im(r_z-r_w)|<pi/2 for every z,w in it. Then C=sech and
T(d)=d/sinh(d) (with the removable value at zero) are holomorphic at every
required difference. Formula T13 therefore extends W holomorphically on
the product of that rectangle with itself.

For fixed delta, K=V-delta W now satisfies A1 on that rectangle. Starting
from any smaller source interval where the presumed inequality holds,
choose L large enough to include it and any desired finite target family.
Propagation proves V>=delta W for that family, with the SAME delta.
The rectangle may depend on L; delta does not. This pays the exterior-to-
global relative-bound bridge without assuming the relative bound itself.

## Evidence and boundaries

Registered shelf query `analytic kernel positivity continuation` returned
INCOMPLETE due semantic-index freshness, receipt SHA256
1943b29a213ff8c9b8475fcdf971ae1d6c898f351251a4e292b40b022c912be2.
The existing ALL_ODD_TO_RH report's section4 proves a local Loewner/Hankel
continuation for a different kernel; it was not silently applied to V.

A neighbouring primary source was checked to avoid reversing a theorem's
premise: Buescu--Paixao--Oliveira, arXiv:1802.07092v1,
https://arxiv.org/pdf/1802.07092, 261826bytes, SHA256
d1ab51b841e276613fc48205d38547aaf7e81c3b16c39f6480efe59049e08282.
Read scope: introduction pp1--2, Theorems3.20--3.22 and Remark3.23,
printed/PDF pp18--20. Theorem3.20 already requires a positive definite
kernel on its whole domain and propagates regularity. It is not a source
for our converse-direction A1. A1--A3 above are direct root proofs with no
novelty claim; no unverified literature theorem supplies the missing sign.

No numerical evaluation, finite-matrix scan, or Lean run was needed.
No full-source sign, relative bound, or original negative witness is proved.
The source-sign counter stays5; TWOCHANNEL is still the one pending third
construction since owner resumption. No new Pro request is sent.

## Independent acceptance receipt

The complete draft SHA256
cc0faac5bdcdaf301574ddd3f7297eac7ff3d7a5ce402094c965130ac2ff48e8
was independently CLEAN as ACCEPTED_CONDITIONAL_CONSUMER_BRIDGE.
Review SHA256
e1277e4153f97bf703f076e4fdca927b4578920858a057d90c1e939551b26da7.
The sole checker verified the mixed old/new blocks, ordered limits and
finite continuation chain; full theta holomorphy; and the thin-rectangle
square-root branches for propagation of the same assumed delta.
Only the acceptance status and this receipt were added afterward.

## END FILE docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md

## BEGIN FILE docs/Codex/REPORT_2026-09-16_RENEWAL_TWO_STEP_OBSTRUCTION.md
SHA256: 7a3e0972ca8e2306de49f048a7b31c4eb10c4f0217c35837105eb3a9d8c55a90

# Two-step renewal block \(K_2\): analytic all-row obstruction

STATUS: INDEPENDENTLY_REVIEWED_PAPER; FINITE-BLOCK POSITIVITY REJECTED AT ALL-ROW
SCOPE, WITH NO CLAIM ABOUT THE TERMINAL \(V\).

The pinned plan selects the first two renewal increments as its first bounded
test (PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES.md, item 1, equations in lines
34--50; local SHA256
f614fa57901954d7fc1716965fe81250e6d8a02f6ad800face52823be8721cc2).
The source response defines the complete field and its cutoff-aware telescope
in equations (4), (8)--(10), (37), and (41)--(44) of
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md
(local SHA256
784e16445c64c1b480cfb0fdc5740182ad59253a775bfc8ab7dc0c44a654eafd).
The source law is fixed by REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md,
L14--L17 (local SHA256
feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21), together
with the SIZEBIASCOMP response §6, equations (22)--(29).  Thus
\(T=\sum_{n\geq1}\operatorname{Gamma}(2,1)/(\pi n^2)\) has density \(r\),
and the multiplier \(H\), distinct from the shape-one density \(h\), has
density
\[
k_H(\lambda)=\lambda^{-1/2}-1,\qquad 0<\lambda<1.
\]
Thus
\[
S_2=T_1+H T_2
\]
with independent \(T_1,T_2,H\).

For \(a=e^{2x}\), \(b=e^{2y}\), the exact projected pair field from the source
equation (44) is
\[
\psi_{xy}(t)=A_{xy}(t)(\log t+x+y),\qquad
A_{xy}(t)=\frac{\mu}{2A^2}(ab)^{5/4}\sqrt t\,
                 \frac{r(at)r(bt)}{r(t)}>0.
\]
The proposed two-step block, including the physical cutoff, is therefore
\[
K_2(x,y)=\mathbb E\!\left[
  \mathbf 1_{\{S_2\geq1\}}\psi_{xy}(S_2)\right].
\tag{1}
\]
This is exactly the first two expected increments of the source telescope;
it does not replace the terminal law by a new source.

Let \(q_2\) be the density of \(S_2\).  The density \(v\) of \(HT_2\) is
\[
v(t)=\int_t^\infty
       \left((tu)^{-1/2}-u^{-1}\right)r(u)\,du,
\qquad q_2=r*v.
\tag{2}
\]
The full source tail estimate already paid in the source report is
\[
r(t)\leq4\pi^2t e^{-\pi t},\qquad
r(t)\sim C t e^{-\pi t},\qquad C=4\pi^2.
\tag{3}
\]
For \(t\geq1\), (2) and \(\sqrt{1+z}-1\leq z/2\) give the global bound
\[
0\leq e^{\pi t}v(t)
 \leq4\pi^2\int_0^\infty
       \left(\sqrt{1+w/t}-1\right)e^{-\pi w}\,dw
 \leq \frac{2}{t}.
\tag{4}
\]
The same change of variables, dominated by \(w e^{-\pi w}/(2t)\), and (3)
give the exact tail limit
\[
t\,e^{\pi t}v(t)\longrightarrow
\frac{C}{2\pi^2}=2.
\tag{5}
\]
Near zero, (2) gives
\[
v(t)\leq t^{-1/2}\mathbb E[T^{-1/2}],
\tag{6}
\]
so the convolution below has no hidden endpoint divergence.

Writing \(\widehat r(t)=e^{\pi t}r(t)\) and
\(\widehat v(t)=e^{\pi t}v(t)\), one has
\[
e^{\pi t}q_2(t)=\int_0^t\widehat r(t-u)\widehat v(u)\,du.
\]
Split this integral into \(u< M\), \(M\leq u\leq t/2\), and
\(t/2<u<t\).  Equations (3)--(6) make the first and last pieces
\(O(t)\), uniformly after \(M\) is fixed.  On the middle piece,
\(\widehat r(t-u)/(t-u)\to C\) and \(u\widehat v(u)\to2\), uniformly after
first taking \(M\) large.  Hence
\[
\frac{q_2(t)}{r(t)}\sim2\log t,\qquad t\to\infty,
\tag{7}
\]
and the same split supplies the usable global bound
\[
0\leq\frac{q_2(t)}{r(t)}\leq C_0(1+\log t),\qquad t\geq1.
\tag{8}
\]
The coefficient \(2\) is source-specific: the \(H\)-density vanishes
linearly at \(\lambda=1\), while the \(T\)-density has the double
\(e^{\pi t}\)-moment pole inherited from its first Gamma(2) factor.

Now take the diagonal \(y=x\), so \(b=a\).  Substituting (1) and then
\(u=at\) gives the exact cutoff-preserving formula
\[
K_2(x,x)
 =\frac{\mu}{2A^2}\,a
   \int_a^\infty \sqrt u\,r(u)^2
     \frac{q_2(u/a)}{r(u/a)}\log u\,du.
\tag{9}
\]
Let \(L=\log(1/a)\).  From (7)--(8), for every fixed \(u>0\),
\[
\frac{1}{L}\frac{q_2(u/a)}{r(u/a)}\longrightarrow2
\qquad(a\downarrow0).
\]
For \(u\geq a\), (8) bounds this ratio divided by \(L\) by a constant
multiple of \(2+|\log u|\).  Therefore dominated convergence applies to
(9), because
\[
\sqrt u\,r(u)^2|\log u|\,(2+|\log u|)
\]
is integrable on \((0,\infty)\): at infinity this follows from (3), and at
zero from the reciprocal full-source identity
\(r(1/u)=u^{5/2}r(u)\) together with (3).  Consequently
\[
\lim_{a\downarrow0}\frac{K_2(x,x)}{a\log(1/a)}
 =\frac{\mu}{A^2}J,
\qquad
J=\int_0^\infty \sqrt u\,r(u)^2\log u\,du.
\tag{10}
\]
The sign of \(J\) is exact, with no numerical evaluation.  Splitting at one
and substituting \(u=1/v\) in \((0,1)\), reciprocity gives
\[
J=\int_1^\infty
      \bigl(u^{1/2}-u^{5/2}\bigr)r(u)^2\log u\,du<0.
\tag{11}
\]
Thus
\[
K_2(x,x)<0
\]
for all sufficiently negative real \(x\) (equivalently, sufficiently small
\(a\)).  This is a genuine diagonal obstruction for the analytically
continued block, and it retains \(S_2\)'s law and the cutoff \(S_2\geq1\).

It remains to bring the obstruction back to the original interval
\(I=(-\log2/2,0)\), where \(a\in(1/2,1)\).  No pointwise claim that the
diagonal is negative inside \(I\) is needed.  Using \(q_2/r\) in (1), write
\[
K_2(z,w)=\frac{\mu}{2A^2}e^{\frac52(z+w)}
 \int_1^\infty \sqrt t\,\frac{q_2(t)}{r(t)}
       r(e^{2z}t)r(e^{2w}t)(\log t+z+w)\,dt.
\tag{12}
\]
On
\[
\Omega=\{z\in\mathbb C:\operatorname{Re}z<0,\ |\operatorname{Im}z|<\pi/8\},
\]
\(\operatorname{Re}(e^{2z})>0\).  The full-source series used in
REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, equations (15)--(23) and
(54)--(58) (local SHA256
1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282), gives
the exact normally convergent expansion
\[
r(\zeta)=\sum_{n\geq1}
 \bigl(4\pi^2n^4\zeta-6\pi n^2\bigr)e^{-\pi n^2\zeta},
\qquad \operatorname{Re}\zeta>0.
\tag{12a}
\]
For every compact \(Q\Subset\Omega\), put
\(\delta_Q=\min_{z\in Q}\operatorname{Re}(e^{2z})>0\).  The expansion gives
\[
\left|r(e^{2z}t)\right|
\leq C_Q(1+t)e^{-\pi\delta_Qt},
\qquad z\in Q,\quad t\geq1.
\tag{12b}
\]
Together with (3) and (8), (12b) gives a compact-uniform integrable
majorant for (12), so \(K_2\) is jointly holomorphic on
\(\Omega\times\Omega\).  On real \(x,y<0\), it is real symmetric and finite.
The denominator \(r(t)\) in (12) stays on the positive real axis; no complex
zero is divided out.

The accepted analytic propagation lemma
docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md,
SHA256
fb83c216aef4687425074732904f9d2f52aac77527a926e7556fb0067335e2bd,
applies to (12) on \(J=(-\infty,0)\).  If every finite complex matrix
\([K_2(x_i,x_j)]\) were positive semidefinite for all \(x_i\in I\), the lemma
would propagate that property to every finite family in \(J\).  Equation
(10)--(11) contradicts it on a one-node family at sufficiently negative
\(x\).  Therefore there exists a finite complex row
\[
x_1,\ldots,x_N\in I,\qquad c\in\mathbb C^N,
\qquad c^* [K_2(x_i,x_j)]_{ij}c<0.
\tag{13}
\]
This is the requested all-row sign obstruction on the original interval.
The argument does not supply a rank bound or a two-node witness inside \(I\);
it only proves that the proposed universal positive-block rule cannot hold
there.

Finally, (13) concerns the first two signed telescope increments only.
It is not a negative witness for the terminal \(V\): later increments may
compensate it, exactly as the source response warns after equations
(41)--(43).  Conversely, a positive diagonal or determinant check for a
particular pair would not establish the all-row rule.  No numerical sweep,
convergence-to-sign argument, or new unproved compensation condition is used.

## END FILE docs/Codex/REPORT_2026-09-16_RENEWAL_TWO_STEP_OBSTRUCTION.md

## BEGIN FILE docs/Codex/REPORT_2026-09-16_POINCARECOMP_INTAKE.md
SHA256: 7204afc827b61abfc5683f507724cfa08e5fbd7accdc265474d34f6a7f2dc977

# Poincare comparison closed; complete signed form still open

STATUS: INDEPENDENTLY_REVIEWED_PAPER_SCOPED_RESULT.
No canonical admission, Lean proof, negative original-V witness or RH claim.

## Exact received artifact

Request REQ-2026-09-16-POINCARECOMP was sent once and has now been answered.
Response commit: `2dbd8191cfa515121c3c24c44ca61c2e5bc46acc`.
Path: `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_POINCARECOMP_2026-09-16.md`.
Git blob: `2f2b28ac8f73033e7671d6c5467fcff09bb98fc6`.
SHA256: `1920733be233ad33403c1c482b3db6c0d253db091ca646415fe84fd5b3a0bc6d`.
49478 bytes, 518 LF, no CR, final LF. Parent read all 518 lines.
The independent checker read the same immutable artifact in full; its report
and exact digest are preserved in the accompanying certificate.

## Accepted theorem and its exact limit

For every kappa>0 and every nonempty open interval J contained in (-infinity,0),
there is a finite complex row with nodes in J for which

    M[c] - kappa D_X[c] < 0.

In particular the sufficient lower envelope L_pi=M-(D_X+sqrt(D_G D_B))/(2pi^2)
has a negative finite row on the original interval I. Thus improving the
fixed positive constant in this absolute derivative comparison cannot prove
the required all-row sign. The valid conditional Poincare inequality and
L<=B_pi are unaffected. A negative lower bound is not a negative value of V.

This agrees with the independently published parent obstruction at
345dfea4365498cfdff460e78620f4d717e49147. The two parallel derivations concern
one proposed comparison, not two failed full-sign attempts.

## Parent reproduction of the proof

1. On Omega={Re z<0, |Im z|<pi/6}, a=e^(2z) satisfies Re a>0 and
   Re(1/a)>1/2. The full small-u modular series gives exponential decay for
   h(au)/sqrt(h(u)) and [a h'(au)-(h'/h)(u)h(au)]/sqrt(h(u)). The latter
   expression never divides by complex h(au). The large-u growth allowed
   when Re a<1/2 is canceled by the retained sqrt(r(t)) physical factor.
   The resulting half-density bounds are t^(7/4)e^(-pi delta t) and
   t^(11/4)e^(-pi delta t), locally uniformly in the two complex arguments.
   This establishes one joint holomorphic domain for the actual quadratic
   kernels M and D_X, not for the nonquadratic L_pi.
2. U=ats, W=at(1-s), T=U+W gives dt ds=dU dW/(aT). In M the signed
   coefficient log(t)+2x becomes exactly log(T). The complete transformed
   measure has the integrable majorant (15), so the M diagonal stays bounded
   and converges. On a fixed positive-mass rectangle with T>1, the limiting
   s-score is nonzero and X>=-x; hence D_X>=c_D(-x), c_D>0. No negative
   contribution was discarded from this nonnegative derivative energy.
3. The already accepted all-finite analytic positivity propagation lemma
   applies to K_kappa=M-kappa D_X. Were it PSD on every row in J, it would
   remain PSD along the connected negative real axis, contradicting the
   distant negative diagonal. This gives an actual finite-row existence
   result in J; it supplies neither a numerical rank nor a negative V row.

## Exact reciprocal transport also accepted

Writing w(t)=t^(3/2)r(t)^2/(2A^2), reciprocity gives

    j_t=p_(1/t)/p_t=g_(-log t),  E_t j_t=1,
    j_t g_x(1/t)=g_(x-log t)(t),
    F_x(1/t)=F_(-x)(t),  w(1/t)/t^2=w(t).

These identities have the correct -9/2 likelihood exponent and all Jacobians.
The conditional projection changes: j_t is nonconstant for t!=1, and the
rank-one projection discrepancy (27) is strictly positive. The primitive
potential changes by 2 alpha beta+beta^2-beta'; this is retained, not dropped.

Parent directly substituted t=1/tau into the truncated full expression:

    V_H(x,y)=integral_(1/H)^1 w(tau)(x+y-log tau)
                         F_(-x)(tau)F_(-y)(tau) d tau.

The finite cutoff becomes [1/H,1]. With the transformed conditional measure,
the covariance identity has factor 2 and cancels exactly the same covariance
part of M. Conditional endpoint products vanish by the exponential source
bounds; the physical t=1 trace remains w(1)(x+y)F_x(1)F_y(1). No integration
by parts in t occurred, so that trace is not an omitted additive term.
The H->infinity limit follows from the separately established absolute
integrability of the original signed pieces.

After this change of space the remaining expression is exactly

    V[c]=-2 Re integral_0^1 w(tau) conjugate(m^r)
                           [X m^r+b^r] d tau,
    m^r=sum c_i F_(-x_i), b^r=sum c_i(-x_i)F_(-x_i).

It is the original unknown sign in new coordinates. For two distinct nodes
the pointwise mean-channel determinant equals
-(x_1-x_2)^2 F_(x_1)^2 F_(x_2)^2. Thus neither positivity of a conditional
potential nor positivity at each integration point is the missing mechanism.
This determinant is not a negative integrated V witness.

## What is now excluded and what remains useful

Do not reopen a fixed positive absolute derivative budget, an unchanged
conditional projection under inversion, or positivity from an isometry alone.
The full source product was used to control the complex domain and score;
no property special to primes was used in this new proof.

The earlier reciprocal likelihood covariance diagnostic at
98d00ddda0777c4d19d4de9b83910e8477011ba5 is compatible with this response:
reciprocal means agree while their conditional fluctuations do not admit the
specified forward contraction. That diagnostic and a generic reverse Markov
contraction do not supply the mixed signed comparison.

Next action is a bounded semantic return on the mixed pair, before another
proof request. A useful candidate must supply a source-checkable sufficient
condition, distinguish the known negative control, and account for the whole
integrated mean channel. Merely restating its positivity fails this test.
The source-specific renewal block test already recorded in
PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES remains untried, not a proved supplier.

The current request is complete. The native goal of the complete V sign remains
active. This is one scoped exclusion and one exact reformulation; the sign of
the original V has not been proved or disproved.

## END FILE docs/Codex/REPORT_2026-09-16_POINCARECOMP_INTAKE.md
