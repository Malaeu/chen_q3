# STATUS: TRY_CCM_EXACT_FERRERS_MELLIN_GENERATOR
```yaml
OPERATIVE_CLASS: TRY_CCM_EXACT_FERRERS_MELLIN_GENERATOR
ARTIFACT_TYPE: PAPER_IDENTITY_AND_SOURCE_PROVENANCE_VERDICT
AUTHOR: Proshka
DATE: 2026-09-20
REPO: Malaeu/chen_q3
BRANCH: rh_clean
BASE_HEAD: 431a3d39c1e09693c25e3e2a36aac38896c13d22
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
BOUNDARY: OWNER_REQUESTED_EXACT_GENERATOR_HUNT_FOR_SAME_SOURCE
PRODUCTION_REQUEST_BINDING: MISSING_REGISTERED_TXT
PRODUCTION_THEOREM_TRANSACTION: HOLD
PAPER_RESULT: EXACT_ALL_M_N_FERRERS_TO_NORMALIZED_SOURCE_COEFFICIENT_IDENTITY
SCOPE: ABSTRACT
VERIFIER: PAPER
CACHE_EQUALS_ANALYTIC_SOURCE: REFUTED_FOR_PINNED_CACHE_AND_REAL_SOURCE_UP_TO_COMMON_SCALAR
REFUTED_SCHEMA_SCOPE: THEOREM_SHAPE
REFUTATION_EVIDENCE: cache_three_modes.json; exact_checks.stdout; section_6
REFUTATION_UPPER_ENVELOPE: -2e-112
CACHE_ACCURACY_REFUTED: false
NEW_ANALYTIC_SOURCE_COERCIVITY: NOT_PROVED
NEW_COFINAL_POSITIVITY: NOT_PROVED
NEW_LEAN_PATHS: []
LEAN_CHECKED: false
ARB_REPLAY: false
CATALOG_CHECK: TARGETED_PINNED_SOURCE_LOOKUP_ONLY_NOT_FULL_ASK_SH
CLOSES: []
OPENS: []
CATALOG_SUPPLIER_ADDED: false
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: ABSTRACT_PAPER_IDENTITY_NOT_ROUTE_PROMOTION
PROJECT_SUPPLIER_CLOSURE_COUNT: 0
ROUTE_PROMOTION: false
RH_CLAIM: false
BUS_010_POLICY: VOID
```

## 1. Результат

[ABSTRACT | PAPER] Найден точный генератор коэффициентов аналитического источника для каждого целого m>=2, N>=0 и всей пары абсолютно суммируемых рядов Феррерса, при ненулевой конечной проекции. Он исключает численную квадратуру из определения коэффициентов и устраняет индивидуальные L2-нормировки двух мод. Это тождество того же источника, не оценка разности двух пробников.

[FINITE_CELL | PAPER] Сохранённые десятичные коэффициенты не равны коэффициентам выбранного вещественного источника, даже с общей ненулевой комплексной фазой/масштабом: три коэффициента нарушают точное сопряжение Фурье. Опровергнуто равенство, не точность приближения и не прежний сертификат для рационального кэша.

[COFINAL_FAMILY | CONDITIONAL] Положительность аналитической семьи остаётся открытой. Старый сертификат кэша не становится сертификатом точного источника от одного общего генератора. Production-запрос и запуск Lean здесь не выполнялись; очереди и посторонние OPEN-маркеры не использовались для выбора задачи.

## 2. SOURCE LOCK

Все пути имеют pin BASE_HEAD. RB = q3.lean.aristotle/Q3/Proofs/RouteB/; LADDER = q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/.

| Источник | Git blob | Содержание |
|---|---|---|
| LADDER/portable_k_channel_v1.py | 29c1b8cacc2e91558920c0f4accf8212d1f0b157 | build_coeff_cache; 110 dps; квадратура 192; mp.nstr(...,90) |
| LADDER/true_precision_packet_gate_v1.py | f6b6ed5dd7e87750c877e48da3bad9b8f06dcbd3 | MAX_DEGREE=180; build_prolate_model; integrate_coefficients |
| LADDER/out/portable_k_coeffs_lambda_sq_13_N_120.json | 67dfbce6c8adff67858a83fc7755a93d175276fd | точные десятичные строки n=-1,0,1 |
| RB/D0KTrialStage1.lean | daeaa6a3e1e12e0960ba7de67ee3a0b9ef133ec2 | lambda, du/u, фаза V_n и проекция |
| RB/D0Mode4FerrersCoefficientAbsoluteSummability.lean | f8e406db556181c024f587cf7bd33598989839e5 | (-1)^j a_j P_(2j); абсолютная/равномерная сходимость |
| RB/D0Mode4FerrersNormalizedActualModeLocalFields.lean | 8d6950d56248a0ad0f1d97fb8f6e5ddcab7089b3 | реальность и внутреннее собственное уравнение |
| RB/G6N1SelectedFerrersPreAnchorDataInhabitant.lean | 8d420f8a6e2926f9c10d65480dca41e13ffe97ce | selectedFerrersPreAnchorSolution0/4 и pair_spec |

[ABSTRACT | CONDITIONAL — чтение источников, не новый kernel gate] build_coeff_cache получает конечный Galerkin-спектр на степенях 0,2,...,180 (матрица 91x91), берёт первую и третью колонки чётного блока для g04, вычисляет квадратуры порядков 96/192, нормирует конечную Fourier-строку и сериализует 90 значащих цифр. Эти этапы не являются точным равенством сохранённых десятичных рациональных чисел аналитическим коэффициентам.

Точный источник уже определён: selectedFerrersPreAnchorSolution0/4 k и selectedFerrersPreAnchorPair_spec k. Последний фиксирует h0/h4 как нормированные физические моды, I0,I4>0 и спектральное происхождение. Их ряды бесконечны; K=5*(k+2) не означает нулевой хвост. Дифференциальные собственные значения не отождествляются с Fourier-скалярами ProlatePair.chi0/chi2. Выбранное pre-anchor-расписание N=m=k+2 не меняется на N=120 автоматически.

[ABSTRACT | PAPER] Перевод ортонормированного Legendre-базиса численного генератора в обычный Ferrers-базис: a_j=(-1)^j v_j sqrt((4j+1)/(2 lambda)) для физически нормированного представления. Это множитель scaled_coeffs. Он применим и в бесконечной модели, но не делает конечные eigsy-коэффициенты точными бесконечными спектральными данными.

## 3. Точное сокращение нормировок

[ABSTRACT | PAPER] Пусть lambda=sqrt(m), L=log(m), a^(0),a^(4) — вещественные абсолютно суммируемые ряды и

\[
F_r(t)=\sum_{j\ge0}(-1)^j a_j^{(r)}P_{2j}(t),\qquad r\in\{0,4\}.
\]

P_l — обычный Legendre-полином, P_l(1)=1. Ряд равномерно сходится на [-1,1], поскольку |P_l|<=1; соответствующий исходниковый интерфейс — mode4FerrersSeries_hasSumUniformlyOn.

Пусть h_r(x)=F_r(x/lambda)/N_r на носителе [-lambda,lambda], N_r>0, и h_r=0 вне его. Почленное интегрирование и ортогональность Лежандра дают

\[
I_r=\int h_r=\frac{2\lambda a_0^{(r)}}{N_r}.
\]

Вводим

\[
d_j=a_0^{(4)}a_j^{(0)}-a_0^{(0)}a_j^{(4)},\qquad
H(t)=\sum_{j\ge0}(-1)^j d_jP_{2j}(t).
\tag{G1}
\]

Тогда точно

\[
\boxed{d_0=0,\qquad\int_{-1}^{1}H(t)\,dt=0.}
\tag{G2}
\]

Для источниковой комбинации

\[
h_{trial}=\frac{I_4h_0-I_0h_4}{\sqrt{I_0^2+I_4^2}}
\]

имеем

\[
h_{trial}(\lambda t)=C H(t),\qquad
C=\frac{2\lambda}{N_0N_4\sqrt{I_0^2+I_4^2}}>0.
\tag{G3}
\]

Знаменатель ненулевой в выбранной паре, где I0,I4>0. Линейные E_star и проекция сохраняют C, а заключительная единичная нормировка его точно уничтожает. Индивидуальные N0,N4 и отдельное вычисление I0,I4 поэтому не нужны для конечной нормированной Fourier-строки.

Исчезает Legendre-компонента d0, а не Fourier-коэффициент n=0 и не вейлевская невязка (K-aI)q.

## 4. Точный Mellin-генератор без квадратуры

[ABSTRACT | PAPER] Для h(x)=H(x/lambda), продолженной нулём вне носителя, обозначим

\[
\alpha_{m,n}(H)=\langle V_{n,m},E_*h\rangle_{L^2(du/u)},\quad
V_{n,m}(u)=L^{-1/2}e^{2\pi i n\log(\lambda u)/L}.
\]

Здесь E_*h(u)=sqrt(u) sum_(k>=1) h(ku). На u in [1/lambda,lambda] нужны только k<=m; точки u=lambda/k меняют конечный носитель суммы. Значения на самих концах не меняют интегралы.

Положим

\[
s_n=\frac12-\frac{2\pi i n}{L},\quad
\mathfrak D_m(s)=\sum_{k=1}^{m}k^{-s},\quad
\mathfrak P_{m,d}=\sum_{k=1}^{m}k^d.
\]

Для каждого целого d>=0:

\[
\boxed{
\mathcal M_{m,n,d}=\alpha_{m,n}(t^d)
=\frac{m^{-1/4}}{\sqrt L}
\frac{\sqrt m\,\mathfrak D_m(s_n)-m^{-d}\mathfrak P_{m,d}}{d+s_n}.
}
\tag{G4}
\]

### Доказательство

При x=log(lambda*u), du/u=dx, фиксированное слагаемое k живёт на 0<=x<=log(m/k). Поэтому

\[
\begin{aligned}
\alpha_{m,n}(t^d)
&=\frac{m^{-1/4}}{\sqrt L}\sum_{k=1}^{m}(k/m)^d
\int_0^{\log(m/k)}e^{(d+s_n)x}\,dx\\
&=\frac{m^{-1/4}}{\sqrt L}\sum_{k=1}^{m}
\frac{(m/k)^{s_n}-(k/m)^d}{d+s_n}.
\end{aligned}
\]

Целочисленность n даёт m^(s_n)=sqrt(m), откуда G4. Re(d+s_n)=d+1/2>0. Все основания положительны, log вещественный. В общей переменной s кажущаяся особенность s=-d устранима, со значением (k/m)^d log(m/k) у k-го слагаемого.

Пусть P_(2j)(t)=sum_(d=0)^(2j) p_(2j,d)t^d — конечное разложение с рациональными коэффициентами. Определим

\[
\mathcal T_{m,n,j}=(-1)^j\sum_{d=0}^{2j}p_{2j,d}\mathcal M_{m,n,d},\qquad
\Gamma_{m,n}=\sum_{j\ge0}d_j\mathcal T_{m,n,j}.
\tag{G5}
\]

Тогда

\[
\boxed{\alpha_{m,n}(H)=\Gamma_{m,n}.}
\tag{G6}
\]

Обоснование: абсолютная суммируемость d_j и равномерная сходимость Ferrers-ряда позволяют почленно интегрировать. Также |T_(m,n,j)| ограничено одной конечной константой независимо от j, через исходный интеграл и |P_(2j)|<=1. Внешний ряд по j сохраняется сгруппированным: нельзя без доказательства переставлять его в бесконечный мономиальный ряд.

### Нормированная строка того же источника

При

\[
Z_{m,N}=\left(\sum_{n=-N}^{N}|\Gamma_{m,n}|^2\right)^{1/2}>0
\]

получаем

\[
\boxed{q^{source}_{m,N}(n)=\Gamma_{m,n}/Z_{m,N},\quad |n|\le N.}
\tag{G7}
\]

Сохранённый Fourier-коэффициент ортогональной проекции равен коэффициенту полной функции, а норма проекции — именно Z_(m,N). Положительный множитель C из G3 сокращается. Полную норму E_*h или h вместо Z использовать нельзя. При Z=0 требуется тот же TrialNonzero; деление не создаёт единичного вектора.

G1,G4,G5,G7 дают одну точную source-defined карту для всех m,N. В ней нет десятичных коэффициентов и численной квадратуры.

## 5. Спектральный генератор и запрет нулевой обрезки

[ABSTRACT | PAPER] Точная угловая модель имеет оператор

\[
\mathcal L_c f=-((1-t^2)f')'+c^2t^2f,\qquad c=2\pi m.
\]

Для выбранного дифференциального уровня theta локальное even-решение f(0)=1 определяется рекурсией

\[
A_{j+1}=\frac{(2j(2j+1)-\theta)A_j+c^2A_{j-1}}{(2j+2)(2j+1)},
\quad A_{-1}=0,\ A_0=1.
\tag{G8}
\]

Регулярность на концах и выбор mode 0/4 определяют правильный спектральный корень; локальная рекурсия сама его не выбирает. Для source-mapped реализации предпочтительны существующие selectedFerrersPreAnchorSolution0/4, а G8 — независимое представление.

Если f — ненулевой многочлен степени D, ведущий коэффициент a_D, то коэффициент t^(D+2) в (L_c-theta)f равен c^2*a_D. При c!=0 он ненулевой. Значит, конечная полиномиальная Galerkin-обрезка не является точной собственной модой полного оператора. Это не запрет приближений.

Новая формула убирает квадратуру, но не восстанавливает потерянную точность округления и не делает MAX_DEGREE=180 точным бесконечным спектром. Для устойчивой реализации высокой степени может быть выгоднее сохранить Legendre-рекурсию, а не раскрывать огромные мономиальные коэффициенты при прежней точности.

## 6. Точный свидетель против cache = source, включая общую фазу

[ABSTRACT | PAPER] Для вещественного H выполнены alpha_-n=conj(alpha_n), alpha_0 real. Положительная конечная нормировка сохраняет эти свойства. Если z_n=rho*q_n с общей ненулевой комплексной rho, то

\[
\boxed{\operatorname{Im}(z_1z_{-1}\overline{z_0}^{\,2})=0,}
\tag{G9}
\]

поскольку произведение равно |rho|^4 |q_1|^2 q_0^2, вещественному неотрицательному числу.

[FINITE_CELL | PAPER] Для закреплённых десятичных рациональных строк кэша:

\[
-3\cdot10^{-112}<\operatorname{Im}(z_1z_{-1}\overline{z_0}^{\,2})<-2\cdot10^{-112}<0.
\tag{G10}
\]

Обе границы проверены точными дробями. Отображение: -2.304002437911253809203196853177718804650e-112. Три исходные строки сохранены в cache_three_modes.json с pin/blob исходного файла; это явно выдержка, не его полный локальный клон. Скрипт записывает полный числитель/знаменатель в result.json при воспроизведении.

Исходниковая реальность обеспечивается normalizedPhysicalMode_im_eq_zero и selectedFerrersPreAnchorPair_spec, не названием общего типа. G10 исключает точное равенство этого кэша любому общему комплексному кратному коэффициентов вещественного источника. Он не исключает численную близость, не даёт отрицательной энергии Weil-формы и не отменяет сертификат для точных десятичных рациональных входов.

## 7. Структура, маршруты, dependency epistemics

[ABSTRACT | PAPER] Сохранены m,lambda,L,du/u, носитель, Fourier-фаза log(lambda*u), порядок -N,...,N, (-1)^j Ferrers-конвенция, выбор мод 0/4, конечная нормировка, кванторы по всем m,N. Концы отбрасываются только как множества меры ноль в интегралах. Убраны ненужные промежуточные N0,N4,I0,I4 и квадратура. Не убраны спектральная ветвь, бесконечный хвост, TrialNonzero, выбранное расписание и положительность.

[ABSTRACT | PAPER] R1 — Mellin-преобразование конечной суммы дилатаций, BRIDGE_KIND=FORM_IDENTITY. Выбран. Закрывает все коэффициенты одной формулой; бумажная стоимость мала, диагностическая сила по фазе/носителю высока. Арифметическая устойчивость большой степени отдельно не обещана.

[ABSTRACT | CONDITIONAL] R2 — точная бесконечная Jacobi-рекурсия с регулярной/минимальной хвостовой ветвью, вместо нулевого конечного обрезания. Стоимость выше; диагностическая сила высокая против неверной спектральной ветви. Использовать существующие selectedFerrersPreAnchorSolution0/4 прежде нового конструктора. Это не само по себе сертификат Weil-положительности.

K9(b): VANISHING IDENTITY d0=0 и отмена общего C, не желаемое зануление Weil residual. K9(c): COLLAPSE OBJECT — одна точная карта T от пары спектральных рядов к любой конечной Fourier-строке. Минимальные фальсификаторы: неправильная фаза, потерянный support cutoff, (-1)^j и конечная нормировка. Для закрытия положительности всей семьи нужен сертификат на точном образе этой карты.

```yaml
DOWNSTREAM_CONSUMER: sourceCCMComplexTrialComplementFloor_then_same_family_transform_consumer
ACTUAL_CONSUMER_REQUIREMENT: exact_source_row_with_positive_complement_floor_and_transform_budget
ORIGINAL_REQUESTED_OBJECT: exact_identity_between_decimal_cache_and_analytic_prolate_source
ORIGINAL_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - G1_G7_define_unchanged_analytic_source_coefficients_without_cache_equality
  - certified_rounding_can_validate_numeric_view_but_is_not_source_equality
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: RESEARCH_DEBT
SCOPED_MATHEMATICALLY_DEAD_CLAIM: literal_cache_equality_up_to_common_scalar_to_real_source_coefficients
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: EXACT_PHASE_INVARIANT_NEGATIVE_RATIONAL_WITNESS
KILL_EVIDENCE_REFERENCE: pinned_cache_blob_67dfbce6; G9_G10; exact_checks.stdout
ROUTE_FAMILY_DEATH: false
NOVELTY_AXIS: exact_Ferrers_Mellin_transfer_and_normalization_elimination
MATHEMATICAL_PRIORITY_CLAIM: false
REOPEN_TRIGGER:
  - kernel_check_G1_G7_on_existing_exact_Ferrers_source
  - source_family_form_certificate_using_T_not_relabelled_cache_certificate
```

[ABSTRACT | PAPER] DISCRIMINATOR: G9. Если он равен нулю, это лишь необходимый контроль, не доказательство совпадения с пролатной модой; затем нужны точное собственное уравнение с правильной ветвью и G7. Для положительности прежний L>=0/U<0 gate остаётся отдельным; нулесодержащий интервал знак не определяет.

## 8. Исполнение и closeout

Предсказания зарегистрированы в registration.json после чтения генератора и до вычислений. Старые предсказания не менялись. Выполнена 21 точная алгебраическая проверка, включая рациональный witness, контроль общей фазы, намеренную порчу сопряжения, рекурсию, полюса, сокращение нормировок и точную проверку публичного генератора через интеграл в исходной u-координате. Отдельно 15 численных сравнений с кусочными интегралами и отрицательные контроли фазы/носителя: это диагностика, не интервальное доказательство.

P_GEN подтверждено бумажным выводом и контролями; P_PHASE — точной дробью; P_TRUNC — ведущим коэффициентом собственного уравнения; P_NORMALIZATION — формулой проекции и отменой C. Project positivity и аналитическая точность старого кэша не проверялись.

Уменьшилось: квадратура и четыре лишних нормировочных величины исчезли из точного определения строки всей семьи. Опровергнуто: буквальное равенство рационального кэша вещественному источнику, даже с общей фазой. Запрещённые повторы: source := cache; конечный полином как точная мода; mp.nstr как equality certificate; перенос cache-PASS на source-PASS по имени.

```yaml
iteration:
  target: exact_generator_instead_of_decimal_difference_bound
  status: PROGRESS
  progress_class: PROOF_PROGRESS
  progress_scope: ABSTRACT_PAPER_FAMILY_FORM_IDENTITY
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: source_is_exact_spectral_series_plus_transfer_not_decimal_payload
  forbidden_future_move: redefine_analytic_source_as_cache
  next_decisive_test: kernel_check_G7_for_existing_Ferrers_pair
  route_score: 4
```

Из корня репозитория:

```bash
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python docs/routeB_bus/proshka/ccm_exact_source_generator_2026-09-20/exact_generator.py
```

Заполнителей в команде нет. Скрипт создаёт result.json локально; повторные результаты публиковать новым артефактом, не менять закрытую регистрацию/вывод. Lean и Arb не запускались. Записывается один append-only docs-коммит с [Proshka]; SHA сообщается после публикации.

Внешние первичные справочники: NIST DLMF 30.3,30.8 (https://dlmf.nist.gov/30.3, https://dlmf.nist.gov/30.8) и документация mpmath nstr (https://mpmath.org/doc/current/general.html). Они подтверждают стандартную спектральную терминологию и сериализацию. G1-G10 выведены здесь из закреплённых конвенций, а не выданы за готовую внешнюю source-to-cache теорему.

## 9. CODEX DIRECTIVE — один следующий математический узел

TRY_CCM_EXACT_FERRERS_MELLIN_SOURCE_IDENTITY. Использовать selectedFerrersPreAnchorSolution0/4 и pair_spec; не восстанавливать моды из JSON. Реализовать G4-G7 как source-defined формулу и формализовать равенство её нормированной строки существующему c_n того же prolateCombination, с TrialNonzero. Сначала спросить ./ask.sh по mode4FerrersSeries, c_n, E_star, sourcePositiveIndexFinset; не плодить дубликаты. Gate: du/u, integer phase, одна конечная нормировка, endpoint-границы, grouped Ferrers series с доступным Summable. Запрет: q_source := q_cache, потеря бесконечного хвоста, предположение желаемого знака K. Успех — source equality для всех допустимых m,N; неуспех — первое конкретное недоказанное равенство/условие с существующим именем. Production-источник и kernel run требуют регистрации транзакции; документ не является уже зарегистрированным запросом или Lean-результатом.
