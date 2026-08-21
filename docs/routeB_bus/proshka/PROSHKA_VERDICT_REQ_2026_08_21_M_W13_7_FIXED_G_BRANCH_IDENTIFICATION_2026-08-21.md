# STATUS: CONDITIONAL — W13.7 IS A BOUNDED SOURCE CROSSWALK; FIXED-`G` ORDERING IS THE CANONICAL ANCHOR
```yaml
PRIMARY: SELECT_FIXED_G_ORDERED_EVEN_SPECTRUM_CROSSWALK
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-21-M

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 8a65751a7b3af7f29383a41a3b111d9a3e28499f
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_BLOB: a9fd7f45d8a176f2cb0bb886784e69c8e9491a5b
  CENTER_NONVANISHING_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1EvenSolutionCenterNonvanishing.lean
  CENTER_NONVANISHING_BLOB: f353622e8198284c3954ce2f1b799c5f26e9515a
  FINITE_CARRIER_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4ClassicalCarrierFromFiniteLimit.lean
  FINITE_CARRIER_BLOB: 9ed4ed59330f92073f8b1c323d0c7021ea694caa
  FULL_FINITE_DLMF_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMFFullFiniteSpectrumCrosswalk.lean
  FULL_FINITE_DLMF_BLOB: cee34b4dbd40800937e839e62f12c4d496732e67
  CHARACTERISTIC_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenCharacteristicSource.lean
  CHARACTERISTIC_BLOB: fb7f7ad7b9286ee0faaf03056376245306599728
  CARRIER_TO_L2_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4ClassicalCarrierToDLMF3035EvenL2.lean
  CARRIER_TO_L2_BLOB: fc1322f45e9eded5b92ed98895e9bc93b5d28b46
  STRICT_ORDER_CLOSEOUT_PATH: q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DLMF_STRICT_ORDER_DEGREE_FOUR_SELECTION_CLOSEOUT_2026-08-15.md
  STRICT_ORDER_CLOSEOUT_BLOB: c9edc187b5f5e9e83cc869449761d07d44fd736f
  SOURCE_INTERFACE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1Satz9SourcePackageInterface.lean
  SOURCE_INTERFACE_BLOB: be80f839c969397f7d8307bf517a525d99be24d1
  MS_USAGE_CARD_PATH: docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md
  MS_USAGE_CARD_BLOB: a8b82969b13c447ac90343ba661ec177af078409

DIRECT_ANSWER:
  existing_project_DLMF_layer_sufficient_alone: false
  existing_layer_plus_exact_DLMF_30_3_5_solution_set: sufficient
  new_asymptotic_or_ODE_analysis_required: false
  new_source_crosswalk_required: true
  zero_parameter_source_anchor_valid: true
  zero_parameter_anchor_required: false
  project_carrier_extension_to_G_zero_required: false
  fixed_G_ordering_selected: true
  source_derivative_monotonicity_role: CUTOFF_ADMISSION_ONLY
  source_noncrossing_role_in_selected_route: NOT_REQUIRED
  physical_lift_W13_8_9: UNCHANGED_MECHANICAL_DOWNSTREAM

INDEX_FIREWALL:
  project_even_ordinal: j
  source_full_degree: n = 2*j
  DLMF_30_3_5_split_degree: s = 2*(K-1)
  forbidden_identification: split_degree_s_is_not_source_degree_n
  selected_project_ordinals: [0, 2]
  selected_source_degrees: [0, 4]

W13_7_FLOORS:
  W13_7A_PARAMETER_AND_CHARACTERISTIC_LOCK:
    status: CLOSED
    scope: ABSTRACT
    verifier: LEAN
  W13_7B_SOURCE_EVEN_SOLUTION_SET_AND_CUTOFF:
    status: PAPER_PROVED_PORT_OPEN
    scope: ABSTRACT
    verifier: PAPER
  W13_7C_PROJECT_EVEN_SOLUTION_SET_BELOW_TWENTY:
    status: CLOSED_BY_EXISTING_COMPOSITION
    scope: ABSTRACT
    verifier: LEAN
  W13_7D_FIXED_G_ORDERED_ENUMERATION_LOCK:
    status: OPEN_LEAN_READY
    scope: ABSTRACT
    verifier: CONDITIONAL
  W13_7E_SELECTED_THETA_EQUALITY_AND_PACKAGE_TRANSPORT:
    status: OPEN_MECHANICAL_AFTER_W13_7D
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL

EXACT_MINIMAL_MISSING_IDENTITY:
  name: W13_7_FIXED_G_EVEN_BRANCH_EQ_FINITE_LIMIT_CARRIER
  statement: >-
    For every precommitted k and j in {0,2}, with G_k = gamma_k^2 > 0,
    the independently named source eigenvalue lambda_(2*j)^0(G_k) equals
    mode4ClassicalEvenEigenvalue G_k j. Consequently the source and project
    physical separation values remain equal after adding the common shift G_k.

PRIMARY_REPRESENTATION:
  name: FIXED_G_STRICT_ORDER_ISOMORPHISM
  kill_power: 10/10
  cost: 2/10_after_source_card

RUNNER_UP:
  name: ZERO_PARAMETER_ANALYTIC_BRANCH_CONTINUATION
  kill_power: 9/10
  cost: 5/10
  status: NOT_SELECTED

CLOSES:
  - REQ_M_BRANCH_IDENTIFICATION_ADJUDICATION
  - W13_7_ZERO_PARAMETER_ANCHOR_DECISION
  - W13_7_CANONICAL_REPRESENTATION_SELECTION
OPENS: []

NEXT_LOAD_BEARING_GAP: W13_7B_DLMF3035_EVEN_SOLUTION_SET_SOURCE_INTERFACE
NEXT_CHEAPEST_DECISIVE_TEST: VERIFY_EXHAUSTIVE_EVEN_SOLUTION_SET_WORDING_FOR_DLMF_30_3_5

FAILURE_CODES:
  - W13_7_SAME_PARAMETER_NOT_SAME_EIGENVALUE
  - W13_7_ONE_WAY_MEMBERSHIP_CAN_SKIP_INDICES
  - W13_7_SPLIT_DEGREE_CONFUSED_WITH_MODE_DEGREE
  - W13_7_SOURCE_SOLUTION_SET_NOT_EXHAUSTIVE
  - W13_7_ORDERED_ENUMERATION_INTERFACE_GAP
  - W13_7_SOURCE_PROJECT_THETA_CROSSWALK_GAP

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: false
ARISTOTLE_AUTHORIZED: false
QUEUE_STATUS_MUTATED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
```

## ROUTE MAP

### 1. Прямой ответ на три вопроса

1. **Существующий DLMF-слой сам по себе недостаточен.** Он доказывает точную
   конечную DLMF-матрицу, предел её фиксированного собственного уровня,
   характеристическое уравнение 30.3.5, эквивалентность с квадрат-суммируемой
   рекуррентной строкой и строгий порядок carrier-уровней ниже `20`. Он не
   содержит source-объекта `lambda_n^0(G)` и не доказывает, что книжная ветвь с
   этим именем является данным carrier-уровнем. `[ABSTRACT][LEAN]`

2. **Метка при `G=0` математически годится**, хотя production schedule всегда
   имеет `G>0`. Ноль нужен только source-ветви: аналитичность и отсутствие
   пересечений сохраняют её имя от `0` до нужного положительного `G`. Проектный
   carrier к нулю продолжать не требуется. Но этот маршрут не устраняет главный
   crosswalk: всё равно надо доказать, что source-ветвь и project carrier
   перечисляют один спектр. `[ABSTRACT][PAPER]`

3. **Выбран другой якорь: порядок при фиксированном `G`.** NIST DLMF 30.3.5
   прямо утверждает, что при чётном split уравнение имеет решения
   `lambda_(m+2r)^m(G)`; при `m=0` это ровно чётные ветви
   `lambda_(2r)^0(G)`. DLMF 30.3.1 строго упорядочивает их при каждом вещественном
   `G`. Это короче, чем переносить метки вдоль параметра. `[ABSTRACT][PAPER]`

Итог:

```text
это одна и та же ветвь не потому, что индексы похожи,
а потому, что обе стороны являются одним и тем же по номеру элементом
одного и того же строго упорядоченного fixed-G solution set.
```

Пока последняя строка не материализована как theorem, W13.7 остаётся OPEN.

---

### 2. Что уже доказал проект

#### Конечный carrier

`mode4ClassicalEvenEigenvalue G j` определён как инфимум фиксированного
`j`-го собственного значения литеральных конечных DLMF-матриц. Проект уже
доказал монотонность по глубине и сходимость этой последовательности к carrier.
`[ABSTRACT][LEAN]`

#### Точный source characteristic object

`mode4DLMF3035EvenCharacteristicEquation` написан независимо, литеральными
коэффициентами DLMF 30.3.7, в единицах

```text
G = gamma^2
Lambda = DLMF lambda.
```

На production split `s=2*(K-1)` он эквивалентен project root-function zero.
`[ABSTRACT][LEAN]`

#### Полный spectral set ниже `20`

Проект уже доказал обе стороны:

```text
normalized square-summable DLMF even row
  <-> exists j, mode4ClassicalEvenEigenvalue G j = Lambda
```

на production-domain и при `Lambda < 20`. Там же доказан строгий carrier-order
и уникальный degree-four ordinal `j=2`. `[ABSTRACT][LEAN]`

Следовательно, новая работа не является ещё одним limit theorem. Нужен source
adapter, который говорит, что книжные `lambda_(2r)^0(G)` являются **ровно**
решениями того же characteristic equation, а затем маленький ordinal theorem.

---

### 3. Почему fixed-`G` ordering дешевле нулевого якоря

Обозначим:

```text
a_j(G) = mode4ClassicalEvenEigenvalue G j
b_r(G) = lambda_(2*r)^0(G).
```

Нужны две строки:

```text
{a_j(G) | a_j(G) < 20}
  =
{b_r(G) | b_r(G) < 20};

both sequences are strictly increasing on the relevant initial segment.
```

Тогда две строго возрастающие нумерации одного множества совпадают по индексам:

```text
a_0(G)=b_0(G),
a_1(G)=b_1(G),
a_2(G)=b_2(G).
```

Production потребляет только `j=0` и `j=2`, но промежуточный `j=1` нужен
порядку: его нельзя выбросить из ordinal argument. `[ABSTRACT][PAPER]`

#### Роль derivative monotonicity

Оценка

```text
-1 < d lambda_n^0(G) / dG < 0
```

не нужна для сохранения имени ветви в выбранном fixed-`G` доказательстве.
Однако она удобно допускает первые три чётных source-уровня под project cutoff:

```text
lambda_0^0(G) < 0,
lambda_2^0(G) < 6,
lambda_4^0(G) < 20
```

для `G>0`, потому что при нуле значения равны `n(n+1)`. Так degree four
попадает именно в строгий домен существующего carrier theorem. `[ABSTRACT][PAPER]`

#### Роль noncrossing

Непересечение кривых подтверждает source-branch interpretation, но для
выбранного route избыточно: DLMF уже даёт strict fixed-parameter order.

---

## W13.7 FLOORS

### W13.7A — `PARAMETER_AND_CHARACTERISTIC_LOCK` — CLOSED

Требуется:

```text
order m = 0;
project G = source gamma^2;
project Lambda = source lambda;
continued-fraction split s = 2*(K-1) is even;
literal coefficients are DLMF 30.3.7.
```

Это уже зафиксировано source module и parameter dictionary.
`[ABSTRACT][LEAN]`

**Критический index firewall:** split degree `s`, source full degree `n` и
project ordinal `j` — три разных индекса. Для выбранных мод

```text
j = 0,2;
n = 2*j = 0,4;
s = 2*(K-1), independent of j.
```

Смешение `s=n` — немедленный kill. **[C04]**

### W13.7B — `SOURCE_EVEN_SOLUTION_SET_AND_CUTOFF` — PAPER PROVED / PORT OPEN

Нужен точный source theorem-interface:

```text
for every real G and every even split s,
Solutions(DLMF_30_3_5(m=0,G,s))
  = { lambda_(2*r)^0(G) | r : Nat };

r -> lambda_(2*r)^0(G) is strictly increasing;
for G>0 and r<=2, lambda_(2*r)^0(G) < 20.
```

Первичные источники: NIST DLMF 30.3.1, 30.3.3, 30.3.4, 30.3.5 and 30.3.7;
Meixner–Schäfke §3.22 Satz 1 supplies the analytic/simple branch language.
`[ABSTRACT][PAPER]`

Это следующий load-bearing gap. Нужен exact source card/interface, не новая
оценка и не реализация special function.

### W13.7C — `PROJECT_EVEN_SOLUTION_SET_BELOW_TWENTY` — CLOSED

Композиция уже имеющихся theorem даёт:

```text
DLMF characteristic equation
  <-> normalized square-summable left row
  <-> exists project carrier index j.
```

Carrier strictly ordered below `20`; indices `0,1,2` лежат под cutoff.
`[ABSTRACT][LEAN]`

Новый wrapper theorem допустим для удобства, но не является новой математикой.

### W13.7D — `FIXED_G_ORDERED_ENUMERATION_LOCK` — OPEN / LEAN READY

Абстрактный theorem должен потреблять:

```text
strictly increasing a,b : Nat -> Real;
same range below cutoff;
a 0, a 1, a 2 < cutoff;
b 0, b 1, b 2 < cutoff;
```

и выдавать:

```text
a 0 = b 0;
a 1 = b 1;
a 2 = b 2.
```

Или generic pointwise equality на всём общем initial segment. Proof — induction
on the ordinal; никакой ODE, asymptotic или continuity machinery здесь нет.
`[ABSTRACT][LEAN_READY]`

### W13.7E — `SELECTED_THETA_EQUALITY_AND_PACKAGE_TRANSPORT` — MECHANICAL

После W13.7D:

```text
lambda_0^0(G_k) = mode4ClassicalEvenEigenvalue G_k 0;
lambda_4^0(G_k) = mode4ClassicalEvenEigenvalue G_k 2.
```

Добавление общего shift `G_k` даёт equality физических separation values.
После `subst`/rewrite source package feeds the existing center-normalized
receiver. W13.8/9 по-прежнему выполняют dimensionless-to-physical coordinate
lift; W13.7 их не поглощает. `[COFINAL_FAMILY][LEAN_READY]`

---

## FINAL PROPOSAL

### Chosen route

Использовать **fixed-`G` strict-order isomorphism**.

Не строить project analytic branch from `G=0`. Не формализовать derivative
of project carrier. Не использовать curve continuation, если exact fixed-`G`
solution-set theorem уже лежит в DLMF.

### Registered prediction

```text
P_M_NEXT_1:
  exact DLMF 30.3.5 source interface will confirm an exhaustive even solution
  set, not merely one-way membership;
  probability = 0.86.

P_M_NEXT_2:
  after that interface, W13.7D closes as ordinal bookkeeping with no new
  analytic hypothesis;
  probability = 0.82.

Most likely first failure:
  source theorem is recorded only as one-way "these are solutions" and the
  project still lacks an explicit exhaustive source-set contract.
```

### Cheapest decisive test

Produce one read-only source card/interface with the literal quantifiers of
DLMF 30.3.5:

```text
Does "has the solutions lambda_(m+2r)^m" mean the exhaustive solution set
of the even characteristic equation in the exact 30.3.7 normalization?
```

PASS: authorize only the abstract ordered-enumeration theorem.

FAIL/AMBIGUOUS: use the runner-up source characterization from DLMF 30.3(i),
30.4.1–30.4.5 and completeness/regular endpoint theory to prove the reverse
membership. Do not switch to project branch continuation by inertia.

---

## STRONGEST ATTACK

### Attack 1 — same equation is not same eigenvalue

At fixed `G`, the prolate equation has infinitely many simple even modes.
Therefore

```text
source mode solves the same ODE
project mode solves the same ODE
```

does not imply equal separation values. Equality requires the ordinal lock.
`[ABSTRACT][PAPER]` **[C04] [C10]**

### Attack 2 — one-way membership can skip indices

Even if every source branch maps to some project carrier, a strictly increasing
map can skip project levels. Example: `r -> 2*r`. Strict order alone does not
repair missing completeness.

Therefore W13.7B must be exhaustive in both directions, or W13.7C must supply
an exact root-count argument. One-way source membership is insufficient.
`[ABSTRACT][PAPER]` **[C09]**

### Attack 3 — the zero anchor does not cross categories

`lambda_n^0(0)=n(n+1)` labels the source branch. It does not say anything about
`mode4ClassicalEvenEigenvalue` until same-spectrum has been proved. Using the
zero label as the project/source equality would be a same-coordinates-two-laws
error. **[C04]**

The repaired statement is the fixed-`G` ordered-set theorem above.

---

## CODEX DIRECTIVE

```text
NO LEAN EXECUTION IS AUTHORIZED BY THIS VERDICT.

First produce or extend one source card:
  DLMF_30_3_5_EVEN_SOLUTION_SET_USAGE_CARD

Required exact fields:
  m = 0;
  real G = gamma^2;
  even split degree s;
  literal 30.3.7 coefficient convention;
  exhaustive solution set lambda_(2*r)^0(G);
  strict order at fixed G;
  first three even levels lie below 20 for G>0.

Do not:
  define source lambda from mode4ClassicalEvenEigenvalue;
  identify split degree with source degree;
  use same G as proof of same theta;
  formalize project continuation to G=0;
  add a project axiom;
  claim W13.7 LEAN_PROVED.

After the card passes, the sole next Lean target is:
  W13_7_FIXED_G_ORDERED_ENUMERATION_LOCK.
```

---

## META CLOSEOUT

**What became smaller?**

W13.7 is no longer “prove that two spectral constructions are the same branch.”
It is reduced to:

```text
one exact source solution-set interface
+ one abstract ordered-enumeration lemma
+ one scalar-shift rewrite.
```

**What was killed?**

- shared parameter `G` as a proof of shared eigenvalue;
- mandatory project continuation to `G=0`;
- monotonicity/noncrossing as the primary branch-crosswalk engine;
- same-ODE uniqueness across different eigenvalues;
- one-way membership as enough to identify indices.

**What must not be tried again?**

Do not define the book branch by the project carrier. Do not use matching index
notation as numerical equality. Do not omit the intermediate even level
`j=1` when pinning selected degree four.

**Current smallest named gap:**

```text
W13_7B_DLMF3035_EVEN_SOLUTION_SET_SOURCE_INTERFACE
```

**Next cheapest decisive test:**

Verify and card the exhaustive solution-set meaning of DLMF 30.3.5 in the
literal 30.3.7 normalization.

**Fate of prior registered predictions:**

```text
P_K_IMPL_1:
  CONFIRMED.
  The generic receiver and endpoint extension remain kernel-green.

P_K_IMPL_2:
  CONFIRMED_AND_COMPRESSED.
  The load-bearing source/project issue is exactly W13.7; the source existence
  theorem is now carded and centre nonvanishing is proved without citation.
```

**Memory entry:**

```text
iteration: REQ-2026-08-21-M
  target: W13.7 source/project separation eigenvalue crosswalk
  status: PROGRESS
  failed_strategy: infer same eigenvalue from shared G or same ODE
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: W13_7B_DLMF3035_EVEN_SOLUTION_SET_SOURCE_INTERFACE
  invariant_learned: branch identity is ordinal identity inside one exhaustive fixed-G solution set
  forbidden_future_move: zero-anchor or same-parameter substitution before same-spectrum
  next_decisive_test: exact exhaustive DLMF 30.3.5 source card
```
