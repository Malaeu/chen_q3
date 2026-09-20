# STATUS: KILL_CCM_TYPE_ONLY_UNIVERSAL_FLOOR
```yaml
OPERATIVE_CLASS: KILL_CCM_TYPE_ONLY_UNIVERSAL_FLOOR
ARTIFACT_TYPE: PAPER_FALSIFICATION_VERDICT
AUTHOR: Proshka
DATE: 2026-09-20
REPO: Malaeu/chen_q3
BRANCH: rh_clean
BASE_HEAD: e658f14dada334ff1b7df3dfded8dff9afaf3727
PROTOCOL_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
BOUNDARY: SAME_TARGET_SOURCE_CONTRACT_SUFFICIENCY_FALSIFIER_ONLY
TRANSPORT_FINDING: SOURCE_LOCKED_PRODUCTION_REQUEST_BINDING_MISSING
PRODUCTION_THEOREM_TRANSACTION: HOLD
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: EXPLICIT_LITERAL_MATRIX_NEGATIVE_WITNESS_WITH_SOURCE_TYPE_REALIZATION
KILL_EVIDENCE_REFERENCE: BASE_HEAD; CCMFiniteWeilSourceMatrixN1.lean blob 960f1de9d00e9ca4b309a99fe98be48db40cdb31; sections 3-5 below
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
EPISTEMIC_STATUS_APPLIES_ONLY_TO: TYPE_ONLY_UNIVERSAL_FLOOR_SCHEMA
SCOPE: FINITE_CELL
VERIFIER: PAPER
CELL: [2, 1]
NEGATIVE_UPPER_ENVELOPE: -32/6939
TRIAL_ROW_MODE_ORDER: [-1, 0, 1]
TRIAL_ROW: [1/2, 1/sqrt(2), 1/2]
WITNESS_ROW: [-1/2, 1/sqrt(2), -1/2]
TRIAL_REAL_AND_EVEN: true
WITNESS_REAL_AND_EVEN: true
SOURCE_TYPE_REALIZATION: PAPER_CONSTRUCTION_FOR_ALL_PairIndex_INCLUDING_N_ZERO
CANONICAL_PARENT: m_k=k+2; N_k=k+1; extract_k=k
BAD_SELECTED_INDEX: 0
EVENTUAL_COFINAL_FAILURE_PROVED: false
INTENDED_SPECTRAL_SOURCE_COUNTEREXAMPLE: false
CONCRETE_SELECTED_SPECTRAL_C: OPEN_RESEARCH_DEBT
EXISTING_LEAN_THEOREM_REFUTED: false
LEAN_PATHS: []
LEAN_CHECKED: false
EXPECTED_AXIOM_PROFILES: {}
CLOSES: []
OPENS: []
CATALOG_SUPPLIER_ADDED: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
PROJECT_POSITIVITY_PROOF_PROGRESS: false
NEXT_CATALOG_GAP: FINITE_EVEN_HEAD_SCHUR_MARGIN
ROUTE_PROMOTION: false
RH_CLAIM: false
BUS_010_POLICY: VOID
STATE_FILES_CHANGED: false
```

## 1. Что установлено — и что именно не установлено

[FINITE_CELL | PAPER] Для буквальной конечной CCM-матрицы при `(m,N)=(2,1)` построены вещественные чётные единичные строки `q,y`, причём `y` ортогональна `q`, а при настоящем сдвиге Рэлея `a=q* K q` выполнено

\[
\boxed{y^*(K-aI)y<-\frac{32}{6939}<0.}\tag{1}
\]

Это верхняя отрицательная оболочка, а не отрицательная нижняя оценка. Следовательно, для этой строки не существует положительного complement floor. Строка не произвольно подставлена вместо исходной: ниже построены все поля `ProlateKTrialSourceData` и `ProlateCanonicalSourceData`, которые порождают её через буквальную цепочку `prolateCombination -> E_star -> projection -> normalization -> c_n`.

[ABSTRACT | PAPER] **Опровергнута только излишне широкая формулировка**

```text
forall S : ProlateCanonicalSourceData, forall i : PairIndex,
  exists beta > 0, sourceCCMComplexTrialComplementFloor S i beta.
```

Опровергнут и вариант `forall S, forall k` на `selectedPairIndex S k`: в построенной ниже семье плоха ячейка `k=0`. Это НЕ утверждение о конкретном источнике настоящих спектральных мод, который владелец намерен использовать. Ни существование хорошей семьи, ни утверждение «eventually» на кофинальной последовательности этим примером не опровергнуты.

[ABSTRACT | CONDITIONAL] Для запрошенного доказательства выбранной спектральной C сохраняется `RESEARCH_DEBT`. Байт-точный зарегистрированный production-запрос не поступал. Этот документ — фальсификатор достаточности уже обсуждавшегося общего контракта, не подмена выбранной задачи другой production-задачей. Ни очередь, ни посторонние OPEN-задачи не выбирались. Новых Lean-источников нет.

## 2. Source lock и обнаруженная граница контракта

Все пути ниже относительно `q3.lean.aristotle/Q3/Proofs/RouteB/`, все чтения привязаны к `BASE_HEAD`. Ранее прочитанные residual/floor-файлы дополнительно перечислены в `SOURCE_BINDING_AUDIT_2026-09-20.md` (blob `6d676dc8c6dd6b772cd7984850ee57d8fac64e25`).

| Файл | Git blob | Использовано |
|---|---|---|
| `ProlateLayer.lean` | `71f523672481aa6449c93fd84a5e3ad7db4196f6` | Все поля `ProlatePair`, формула комбинации и дифференциальное выражение |
| `D0ProlateKTrialSource.lean` | `27ec0d46e68549db6ea00e4711e369695873e5a5` | Поля двух source-структур, same-m и коэффициентная привязка |
| `D0CanonicalApproximation.lean` | `64d2cfb709c3b9b339ec727660260c6c6946c700` | `PairIndex`, включая N=0; `CanonicalData`, центральная нормировка |
| `D0KTrialStage1.lean` | `daeaa6a3e1e12e0960ba7de67ee3a0b9ef133ec2` | `du/u`, окно, точная фаза `V_n_m`, ортогональная проекция |
| `D0KTrialStage2.lean` | `ffa6cf243670087f6735a2d8896a1dcd74829f8d` | `E_star f(u)=sqrt(u) sum f(nu)` |
| `D0KTrialStage3.lean` | `a139d3f91659d9baf4936008d8a429d6a2e96705` | Ненулевая проекция, положительная нормировка, `c_n` |
| `CCMFiniteWeilSourceMatrixN1.lean` | `960f1de9d00e9ca4b309a99fe98be48db40cdb31` | Буквальные Q, W02, WR, Prime и их знаки |
| `Proposition59EntireTransform.lean` | `6d38df2ff26cc7dc7eadc4757c15605649cbb6d4` | Значения removable kernel при z=0 |
| `D0PstarCCMFiniteSourceResidual.lean` | `0cb7db0b23f9b0ef67e6e27e0d43f0a090184964` | Буквальные K, q, Rayleigh и невязка |
| `CCMProposition59ComplexTrialComplementFloor.lean` | `74d5c67f5d95b5e853218f76b27b22fa3226d8d4` | Точный предикат, который отвергает свидетель |

[ABSTRACT | PAPER — чтение определений] `ProlatePair` требует чётности функций, компактного носителя, интегрируемости, единичных L2-норм, равенств интегралов и двух центральных равенств `I=chi*h(0)`. Он НЕ требует собственного дифференциального или интегрального уравнения, нумерации собственных мод либо порядка собственных значений. `ProlateOperatorData.action_eq` фиксирует выражение оператора, но не связывает его с `h0,h4` собственным уравнением. Docstring прямо предупреждает о типовом, а не спектральном содержании.

Это не дефект доказанной Lean-теоремы. Дефектом было бы принять такую упаковку за достаточный выбор настоящих спектральных мод. Наличие более сильного отдельного конструктора в репозитории здесь НЕ отрицается.

## 3. Отрицательный свидетель для настоящей матрицы

[FINITE_CELL | PAPER] Положим `L=log 2`, `K=ccmWeilMatFinite 2 1`, порядок мод `(-1,0,1)`. Из буквальных формул следуют симметрия и отражение:

\[
K=\begin{pmatrix}A&b&C\\ b&D&b\\ C&b&A\end{pmatrix}.
\]

Здесь `b` — элемент между модами 0 и 1, а не гипотетический параметр другого оператора. Возьмём

\[
q=\begin{pmatrix}1/2\\1/\sqrt2\\1/2\end{pmatrix},\qquad
 y=\begin{pmatrix}-1/2\\1/\sqrt2\\-1/2\end{pmatrix}.
\]

Прямое вычисление даёт `q*q=y*y=1`, `q*y=0`; обе строки вещественны и чётны. При `a=q*Kq`:

\[
a=\frac{A+C+D}{2}+\sqrt2 b,\qquad
 y^*Ky=\frac{A+C+D}{2}-\sqrt2 b,
\]

поэтому

\[
\boxed{y^*(K-aI)y=-2\sqrt2\,b.}\tag{2}
\]

Поскольку `Q=I-qq*` фиксирует `y`, та же энергия получается из буквальной компрессии `Q(K-aI)Q`. Это также точно тот тестовый вектор, который можно подставить в исходный предикат `complexTrialComplementFloor`; метрика не меняется.

### 3.1 Строгий знак одного источникового элемента

[FINITE_CELL | PAPER] При n=0, m=1 источник задаёт

\[
Q_{01}(x)=-\frac{\sin(2\pi x/L)}{\pi}.
\]

Следовательно, `Q01(0)=Q01(L)=0`. В Prime при `mProject=2` имеется только k=2, и его вклад равен нулю. Постоянная часть WR тоже равна нулю. Введём

\[
c_L=\frac{32L\sinh^2(L/4)}{L^2+16\pi^2},\qquad
w(x)=\frac{e^{x/2}}{e^x-e^{-x}}.
\]

Буквальное правило `W02-WR-Prime` даёт

\[
 b=c_L+\frac1\pi\int_0^L w(x)\sin(2\pi x/L)\,dx.\tag{3}
\]

Для `x>0`

\[
w'(x)=-\frac{e^{x/2}(e^x+3e^{-x})}{2(e^x-e^{-x})^2}<0.
\]

После отражения второй половины интеграла его знак виден без квадратуры:

\[
\int_0^L w(x)\sin(2\pi x/L)dx
=\int_0^{L/2}[w(x)-w(L-x)]\sin(2\pi x/L)dx>0.\tag{4}
\]

На открытом интервале `(0,L/2)` оба множителя строго положительны. У нуля произведение имеет конечный предел `pi/L`; у L проблем нет. Таким образом, интегралы корректны, исключённые/включённые концы `Ioc` не меняют их значений. Получено `b>c_L>0`.

### 3.2 Рациональная отрицательная верхняя оболочка

[FINITE_CELL | PAPER] Достаточно грубых, но строгих границ

\[
\frac23<\log2<1,\qquad 0<\pi<4,\qquad \sinh t\ge t\quad(t\ge0).
\]

Первая нижняя граница следует из `log2=2 integral_0^(1/3) (1-t^2)^(-1) dt > 2/3`; верхняя — из `log2=integral_1^2 dx/x<1`. Для pi используем `pi/4=integral_0^1 dx/(1+x^2)<1`; для sinh интегрируем `cosh t>=1`.

Тогда

\[
c_L\ge\frac{2L^3}{L^2+16\pi^2}>\frac{16}{6939}.
\]

Из (2)-(4), с `sqrt2>1`, следует (1). Это независимая отрицательная верхняя оболочка `U=-32/6939`, не измерение с плавающей точкой.

**Следствие:** для данного q не существует beta>0 с `Q(K-aI)Q >= beta Q`. Поскольку свидетель лежит внутри двухмерной чётной головы, добавление сертифицированного хвоста не устранит его для той же полной формы и того же q,a.

## 4. Почему это не произвольная подмена исходной строки

[ABSTRACT | PAPER] Построим допустимые source-данные для ВСЕХ `PairIndex`, включая N=0. Это бумажная реализация полей записанных типов, не новый Lean-конструктор.

Для каждого целого m>=2 положим

\[
\lambda=\sqrt m,\quad \ell=\lambda^{-1},\quad L=\log m,
\]

и используем точные представители из `V_n_m`:

\[
V_{n,m}(u)=L^{-1/2}\exp\!\left(2\pi i n\frac{\log(\lambda u)}L\right).
\]

На `[ell,lambda]` зададим вещественный пакет

\[
g_m(u)=\frac{V_{0,m}(u)}{\sqrt2}
      +\frac{V_{1,m}(u)+V_{-1,m}(u)}2.\tag{5}
\]

Подстановка `t=log(lambda*u)/L` переводит `du/u` в `L dt`, t от 0 до 1. Обычная интеграция экспонент даёт ортонормированность мод и `||g_m||_(du/u)=1`. Функция g_m вещественна.

### 4.1 Обратим E_star на этом окне

[ABSTRACT | PAPER] Пусть

\[
\Phi_m(u)=\begin{cases}u^{-1/2}g_m(u),&\ell\le u\le\lambda,\\0,&\text{иначе},\end{cases}
\]

и на положительном внешнем окне определим

\[
F_m(u)=\sum_{n=1}^{m}\mu_{\rm Mob}(n)\Phi_m(nu).
\]

Здесь `mu_Mob` — арифметическая функция Мёбиуса, НЕ сдвиг Рэлея: она равна 0 при квадратном простом делителе и `(-1)^r` для произведения r различных простых. Поэтому

\[
\sum_{n\mid j}\mu_{\rm Mob}(n)=\begin{cases}1,&j=1,\\0,&j>1,\end{cases}
\]

что следует раскрытием произведения `product_(p|j)(1-1)` при j>1.

Продолжим F_m константой

\[
c_m=-\ell^{-1}\int_\ell^\lambda F_m(u)\,du
\]

на `[0,ell)`, чётно на отрицательную полуось и нулём за `[-lambda,lambda]`. Тогда F_m вещественна, чётна, ограничена, имеет компактный носитель и нулевой интеграл на R. В частности, F_m и её квадрат интегрируемы. Значения в конечном числе точек разрыва можно выбрать средними; ниже нужны равенства почти всюду.

Для `ell<u<lambda` все аргументы `ku` в сумме E_star не попадают в добавленный внутренний интервал. Все ненулевые члены имеют `nk<=lambda/u<=m`, так что перестановка сумм конечна. По тождеству делителей

\[
\begin{split}
\sum_{k\ge1}F_m(ku)
 &=\sum_{j\le\lambda/u}\Phi_m(ju)\sum_{n\mid j}\mu_{\rm Mob}(n)\\
 &=\Phi_m(u).
\end{split}
\]

Таким образом,

\[
\boxed{E_*F_m=g_m\quad\text{почти всюду на }[\ell,\lambda].}\tag{6}
\]

Это точное равенство, не асимптотика. F_m ненулевая в L2: иначе каждая из конечного числа растянутых функций была бы нулевой почти всюду на окне, что противоречит `||g_m||=1` в (6).

### 4.2 Заполним все поля ProlatePair

[ABSTRACT | PAPER] Пусть `d_m=||F_m||_(L2(R,dx))>0`. Положим

\[
h_0=F_m/d_m,\quad
h_4=(2\lambda)^{-1/2}\mathbf1_{[-\lambda,\lambda]},
\]

\[
I_0=0,\quad I_4=\sqrt{2\lambda},\quad
\chi_0=0,\quad \chi_2=2\lambda.
\]

Возьмём `pw.lambda=lambda`, `pw.action=prolateWaveExpression lambda`. Обе функции вещественны, чётны, имеют требуемый носитель, интегрируемы и нормированы в L2. Их интегралы равны I0,I4. Центральные равенства выполнены:

```text
I0 = chi0*h0(0) = 0;
I4 = chi2*h4(0) = sqrt(2*lambda).
```

Знаменатель комбинации равен `I4>0`, поэтому `prolateCombination=h0`. Более того, h0 и h4 ортогональны по нулевому интегралу h0, хотя записанный тип этого не требует.

Этот h4 не является собственной функцией формального пролатного дифференциального выражения: на открытом интервале его отношение `PW_lambda(h4)/h4` равно `(2*pi*lambda*x)^2`, которое не постоянно. Следовательно, пример не выдаётся за настоящую нулевую/четвёртую спектральную моду. Именно отсутствие такого ограничения в общей упаковке и используется.

### 4.3 Ненулевые проекции для всех N, без дыры при N=0

[ABSTRACT | PAPER] Из (6) следует `E_*h0=g_m/d_m` в исходном H_m. Это даёт `eStar_memLp`. При N>=1 проекция сохраняет g_m, а положительная нормировка даёт `kTrial_m_N=g_m`. При N=0 проекция равна `V0/(sqrt2*d_m)`, поэтому она тоже ненулевая, а нормированный результат равен V0.

Следовательно, коэффициенты источника ровно следующие:

```text
N=0:  coefficient(0)=1.
N>=1: coefficient(0)=1/sqrt(2), coefficient(-1)=coefficient(1)=1/2;
      all other coefficients vanish.
```

Для m=2,N=1 это буквально q из §3, не приближённая строка. Все пары зависят только от m, поэтому поле `prolateCombination_eq_of_same_m` также выполнено. Этим построены все поля `ProlateKTrialSourceData`.

### 4.4 Каноническая упаковка и кофинальный parent

[ABSTRACT | PAPER] При z=0 в исходном P59-ядре центральная мода даёт L, остальные моды дают 0. Поэтому `rawFplus(0)=sqrt(L)*coefficient(0)`, что ненулево для каждого i. Фазовый множитель `bareTransform` при нуле равен 1.

Выберем `canonical.kTrial=source.coefficientFamily`,

```text
parent(k): m=k+2, N=k+1, with the central-nonzero proof above;
extract(k)=k.
```

Обе координаты parent стремятся к бесконечности, extract строго возрастает; `kTrial_eq` выполнено по определению. Все поля `ProlateCanonicalSourceData` теперь реализованы. На `selectedPairIndex S 0=(2,1)` действует отрицательный свидетель (1).

**Кофинальность parent не превращает один отрицательный первый член в отрицательность его хвоста.** Утверждение `eventually` не опровергнуто.

## 5. Сильнейшая атака на собственный результат

[ABSTRACT | PAPER] Возражение: «Ты выбрал не наши настоящие пролатные моды». Верно. Поэтому убита только попытка получить универсальную C из одного широкого source-типа, даже с вещественностью и чётностью. Этот пример НЕ контрпример к C для отдельно указанного настоящего спектрального конструктора. Названия полей не заменяют его дополнительные свойства.

[ABSTRACT | PAPER] Возражение: «Плохая маленькая ячейка может быть отброшена». Верно. Утверждение для всех выбранных k ложно, но существование хорошего кофинального хвоста или другой семьи не опровергнуто. Ни `ROUTE_FAMILY` kill, ни RH-вывод не разрешены.

[ABSTRACT | PAPER] Возражение: «Символьный скрипт не проверяет функциональный конструктор». Верно. Его полная бумажная проверка дана в §4; 20 групп скрипта проверяют алгебру, знаки формул и конечные controls. Это не Lean-формализация. Никакая существующая проверенная теорема с явной предпосылкой floor здесь не опровергается.

## 6. Два ремонта и минимальная действительная цель

| Представление | Что должно дойти до неизменённого потребителя | Решающая сила / стоимость |
|---|---|---|
| Источниковый выбор S_* вместо forall S | Закрепить существующий конструктор настоящих мод, его область, индексы и ту же выбранную строку; затем доказать literal floor | Высокая сила против ложного обобщения, дёшево проверить тип/исключение данного свидетеля; стоимость нужной аналитики пока неизвестна |
| Прямой сертификат того же K,q,a | Построить `Q(K-aI)Q-beta Q=R*R`, beta>0, либо прямую нижнюю оболочку, без обязательного eigenmode-экспорта | Высокая сила для точного объекта; стоимость зависит от источниковой оценки; даёт тот же floor без навязывания лишнего спектрального интерфейса |

[ABSTRACT | CONDITIONAL] Собственное уравнение мод — возможный поставщик дополнительной структуры, НЕ объявленная необходимая предпосылка любого доказательства C. Само его добавление ещё не доказывает C. Ремонт «просто исключить этот q» также не даёт положительности на всём оставшемся классе.

[COFINAL_FAMILY | CONDITIONAL] Минимальная открытая цель для выбранного источника остаётся прежней: на точно указанной выбранной последовательности дать положительную нижнюю оболочку истинной формы на ортогональном дополнении и потребительский взвешенный бюджет направленной невязки. `FINITE_EVEN_HEAD_SCHUR_MARGIN` не закрыт.

[FINITE_CELL | PAPER] **DISCRIMINATOR:** для нашего q вопрос уже решён верхней оболочкой (1). Для другого, правильного q_* нужно вычислять другую форму с его собственным сдвигом. Допускается только доказанная нижняя оболочка L>=0 для заявленного запаса либо отрицательный свидетель с U<0. Интервал через ноль остаётся неразрешённым; отдельный точный анализ ядра различает нулевой запас и отрицательность.

## 7. Предсказания, проверки и meta closeout

Аналитическая конструкция и знаковой довод были найдены **до** локальной регистрации. Регистрация относится к последующим исполняемым exact checks, а не приписывает задним числом предсказание самому открытию. Это явно записано в `registration.json`.

| ID | Зарегистрировано | Судьба |
|---|---|---|
| P_F1, 0.99 | Unit/even/orthogonal и энергия `-2 sqrt2 b` | CONFIRMED, точная алгебра |
| P_F2, 0.90 | Положительность источникового offdiag и U=-32/6939 | CONFIRMED бумажным доводом §3; производная, отражение, endpoint и рациональная арифметика проверены скриптом |
| P_F3, 0.99 | Möbius inversion и отбраковка неверных знаков | CONFIRMED controls; общий вывод доказан формулой делителей, не конечным перебором |
| P_F4, 0.99 | Перестановка trial/witness меняет знак; неортогональная подмена отвергается | CONFIRMED |
| P_F5, 0.99 | N=0 и центральная нормировка не создают дырку | CONFIRMED на бумаге §4 и алгебраических controls |

Скрипт завершился exit code 0, **20 групп**. Нет floating-point eigensolver, численной квадратуры или экстраполяции. Старые P1-P5 и P_BIND предсказания не менялись и в этом проходе не пересчитывались.

```yaml
iteration:
  target: sufficiency_of_unbound_ProlateCanonicalSourceData_for_literal_floor
  status: FATAL
  fatal_scope: TYPE_ONLY_UNIVERSAL_THEOREM_SHAPE
  progress_class: FALSIFICATION_PROGRESS
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  project_supplier_closure_count: 0
  failed_strategy: derive_selected_spectral_positivity_from_the_broad_source_record_alone
  invariant_learned: source_type_membership_is_not_spectral_mode_selection
  forbidden_future_move: claim_C_from_normalization_parity_provenance_or_type_names
  current_catalog_gap: FINITE_EVEN_HEAD_SCHUR_MARGIN
  next_decisive_test: bind_the_actual_spectral_constructor_and_check_that_its_proved_properties_exclude_this_source
  route_score: 4
```

Математический положительный запас для целевой семьи не улучшен. Получен отрицательный результат, который исключает доказательство ложного универсального утверждения. Запись результата не повышает статус маршрута.

## 8. Dependency epistemics

```yaml
DOWNSTREAM_CONSUMER: Q3.RouteB.sourceCCMComplexTrialComplementFloor
ACTUAL_CONSUMER_REQUIREMENT: positive_literal_complement_floor_for_the_intended_source_and_schedule
ORIGINAL_REQUESTED_OBJECT: positive_concrete_Schur_or_Gram_certificate
ORIGINAL_OBJECT_IS: UNKNOWN
REFUTED_OVERGENERALIZATION: all_ProlateCanonicalSourceData_supply_the_floor_at_all_cells
KNOWN_WEAKER_INTERFACES:
  - source_specific_direct_lower_bound_implies_literal_floor
  - source_specific_exact_Gram_factor_with_positive_beta_implies_literal_floor
  - certified_eventual_family_may_discard_finitely_many_bad_cells_if_the_unchanged_consumer_allows_reindexing
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS:
  type_only_universal_schema: MATHEMATICALLY_DEAD
  intended_spectral_source_floor: RESEARCH_DEBT
NOVELTY_AXIS: explicit_source_contract_realization_of_a_literal_CCM_negative_witness
MATHEMATICAL_METHOD_NOVELTY_CLAIM: false
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: PAPER_EXACT_NEGATIVE_UPPER_ENVELOPE
KILL_EVIDENCE_PIN: BASE_HEAD_and_sections_3_4
ROUTE_FAMILY_DEATH: false
REOPEN_TRIGGER_FOR_INTENDED_C:
  - registered_request_binds_the_actual_source_constructor_not_only_its_type
  - source_specific_positive_certificate_or_a_strictly_weaker_interface_reaching_the_same_consumer
```

## 9. Доставка и воспроизведение

В одном новом коммите с `[Proshka]` публикуются только четыре файла в
`docs/routeB_bus/proshka/ccm_source_contract_counterexample_2026-09-20/`:
`VERDICT.md`, `exact_checks.py`, `exact_checks.stdout`, `registration.json`.
Ни Lean, ни route-state, ни протокол, ни чужой закрытый артефакт не меняются.
Коммит указывается владельцу после подтверждённой записи, не помещается в
собственное содержимое до создания.

```yaml
VERIFICATION_HANDOFF:
  WORKDIR: REPOSITORY_ROOT
  COMMAND: uv run --no-project --with sympy==1.14.0 python docs/routeB_bus/proshka/ccm_source_contract_counterexample_2026-09-20/exact_checks.py
  EXPECTED_GROUP_COUNT: 20
  EXPECTED_EXIT_CODE: 0
  STATUS_CHANGE_ON_SUCCESS: algebraic_controls_reproduced_only
  LEAN_GATE: NOT_RUN_NO_LEAN_SOURCE
  EXPECTED_AXIOM_PROFILES: {}
```

В команде нет переменных или заполнителей. Контейнерный запуск выполнен обычным Python с установленным SymPy 1.14.0; uv-команда предназначена для воспроизведения на стороне владельца. Сам Linux/Lean gate не запускался.

| Файл | Git blob | SHA-256 |
|---|---|---|
| `exact_checks.py` | `c40742a195da927e281c249c46d76f999552c156` | `8fd7ee62114551931a786f334c2342f4ccffc77587995e5e92c54475371f4d66` |
| `exact_checks.stdout` | `625b5a3fe5905e36677bf03a65c214b9b4192eda` | `30f0242ca3e74c29184356990172a3f39d0789e67009c8477266175b9a22448a` |
| `registration.json` | `5edac679da9dcb8ad9166959f667b267ab25c0a8` | `efdb9e31a6498f6812266a030a95f1662d159896ba9efdf035840aa722b25553` |

## 10. CODEX DIRECTIVE

Один следующий read-only target: на текущем pin найти **существующий конкретный конструктор** intended `ProlateCanonicalSourceData`, а не повторно показать определение типа. Через `./ask.sh ProlateCanonicalSourceData` и его настоящие зависимости установить точные h0/h4, их оператор, область и индексы; показать, каким уже доказанным источниковым свойством исключается конструкция §4. Зафиксировать тот же q, Rayleigh и selected schedule в одном зарегистрированном byte-exact `.txt`-запросе для C. Успех — именованный источниковый выбор с доказанным отличием от широкого типа; неуспех — точный отсутствующий selector/equality, без объявления смерти маршрута. Не добавлять предпосылку C как поле ради получения C, не строить новый условный Schur-wrapper, не менять route-state. Эта директива записана, но не отправлена отдельному исполнителю.
