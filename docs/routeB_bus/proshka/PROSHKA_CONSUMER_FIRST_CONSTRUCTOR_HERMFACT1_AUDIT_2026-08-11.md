# STATUS: OPEN — `hermfact1` PROVENANCE RESOLVED; CONSUMER-FIRST CONSTRUCTOR SELECTED
```yaml
PRIMARY: BUILD_CONSUMER_FIRST_PROOF_CONSTRUCTOR
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  TIP: d719193125b23601b1b7a4f4cc11e4816e003f05
  TIP_VERIFIED: true

HERMFACT1:
  LEAN_DECLARATION_EXISTS: false
  CURRENT_TREE_HITS:
    - docs/routeB_bus/maps/ROUTEB_FORK_2026-08-07_THE_GAP.md
    - docs/routeB_bus/maps/ROUTEB_CHAIN_LOGIC_2026-08-06.html
    - docs/routeB_bus/PROSHKA_REQUEST_UNIFIED_CHAIN_AND_PROBE_2026-08-06.md
  CLASS: DOC_ALIAS
  INTENDED_SOURCE: CCM_LEMMA_7_3_TRIAL_TRANSFORM_TO_XI
  FIRST_VISIBLE_ALIAS_COMMIT: 2cbb718e88ec5e3e06ef3f617aecfe5c5ecd36e0
  REQUEST_COPY_COMMIT: dea558d9bb0c37c256a49397dec31a3f1568ff6e
  CORRECTED_PROVENANCE_COMMIT: d9a44a0940820bae7bc2471bc18136311f6ee97f
  LEAN_PORT: OPEN

ACTUAL_HERMITIAN_FACTS:
  SOURCE_TRANSPOSE:
    theorem: Q3.RouteB.ccmWeilMatFinite_transpose_eq
    commit: 4c7de4b678ffcef1775309213f509b60c0fec476
  SHIFTED_TRANSPOSE:
    theorem: Q3.RouteB.ccmShiftedWeilMatFinite_transpose_eq
    commit: 2efe7f7ad851d1f8afa17004bdff4f24cc833225
  TRANSPOSE_TO_HERMITIAN:
    theorem: Q3.RouteB.ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh
    commit: b7685eb080131a54607a639629ffb08c77556b9f
    standalone_named_hermitian_theorem: false

CONSUMER:
  theorem: Q3.RouteB.ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
  output: CONCRETE_SOURCE_LAGRANGE_POLYNOMIAL_REAL_ZEROS
  exact_contract_source: LEAN_ELABORATED_TYPE

BINDER_LEDGER:
  mProject_N_epsilon_xi: DATA
  hm_hN: AUTO_SIDE_CONDITIONS
  heig: WITNESS_EQUATION
  hnormalized: NORMALIZATION_GUARD
  hbottom: OPEN_FIXED_EPSILON_FORM_INEQUALITY
  hsimple: OPEN_ONE_DIMENSIONAL_EIGENSPACE
  hxiEven: DERIVED_BY_EXISTING_PARITY_THEOREM
  IsHermitian: DERIVED_INTERNALLY_FROM_TRANSPOSE
  quotient_basis: AUTO_WITNESS_PENDING_COMPILE
  concrete_to_abstract_family: OPEN_MISMATCH

CURRENT_REAL_GAPS:
  finite_simple_bottom_package: OPEN
  concrete_polynomial_to_selectedFamily: OPEN
  c_N_normalizer: ABSENT
  lagrangeToXi_bridge: ABSENT

CONSTRUCTOR_ORDER:
  - CONSUMER_DISCOVERY
  - ELABORATED_CONTRACT_EXTRACTION
  - BINDER_ROLE_CLASSIFICATION
  - BACKWARD_SUPPLIER_DESCENT
  - RESIDUAL_ONLY_RETRIEVAL
  - EXPLICIT_APPLICATION_COMPILE
  - EXACT_CLAIM_AND_AXIOM_COMPARATOR
  - WORKER_DISPATCH

ROUTES:
  R1_CONSUMER_CONTRACT_GRAPH:
    selected: true
    kill_power: 5
    cost: 1
  R2_BUNDLE_SUPPLIER_SEARCH:
    selected_as_secondary: true
    kill_power: 5
    cost: 2

NEXT_TARGET: CARTOGRAPHER_CONSUMER_CONTRACT_V0_CCM_REALZERO

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

EXECUTION:
  READ_ONLY_BACKTEST_AUTHORIZED: true
  REPO_WRITE_AUTHORIZED: false
  LEAN_SOURCE_EDIT_AUTHORIZED: false
  ROUTE_PROMOTION: false

ROUTE_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
```

## Исправленная формулировка

> Про `hermfact1`: где это у нас лежит и в каком коммите? Opus не может найти. Но часть предложенного реально работает. Продолжаем моделировать конструктор.

## Короткий ответ про `hermfact1`

**Opus не может найти `hermfact1` как Lean-теорему, потому что такой Lean-декларации в репозитории нет.**

Живой поиск по `rh_clean` находит строку `hermfact1` только в трёх документах. Ни одного `.lean`-файла среди результатов нет. fileciteturn96file0L1-L5 fileciteturn96file1L6-L10 fileciteturn96file2L11-L15

Это **doc-alias** — документальный псевдоним. Он обозначал бумажную лемму из CCM §7:

\[
\widehat{k_\lambda}\longrightarrow\Xi
\]

локально равномерно на замкнутых подполосах.

В старом request эта строка записана буквально как:

```text
CCM §7 Lemma "hermfact1":
  k̂_λ → Ξ uniformly on closed substrips
```

fileciteturn111file0L1-L2

### Точные коммиты

| Роль | Commit |
|---|---|
| Первое видимое появление alias в карте | `2cbb718e88ec5e3e06ef3f617aecfe5c5ecd36e0` |
| Поздняя request-копия | `dea558d9bb0c37c256a49397dec31a3f1568ff6e` |
| Исправленная provenance-запись: это **CCM Lemma 7.3** | `d9a44a0940820bae7bc2471bc18136311f6ee97f` |

История файла `ROUTEB_CHAIN_LOGIC_2026-08-06.html` указывает на commit `2cbb718e…`. fileciteturn104file0L1-L7 Сам commit добавил карту условной цепи и связанный fork. fileciteturn103file0L2-L7

Request-копия позже вошла через commit `dea558d9…`. fileciteturn112file0L1-L7

Корректная классификация уже материализована в commit `d9a44a09…`:

```text
CCM_LEMMA_7_3:
  trial transform → Xi on closed substrips:
  PAPER_PROVED.

project Lean port:
  OPEN.
```

fileciteturn106file0L1-L2 fileciteturn119file0L1-L7

### Итоговая запись для конструктора

```yaml
name: hermfact1
kind: DOC_ALIAS
resolves_to:
  source: CCM
  theorem: Lemma 7.3
  claim: trial-transform locally uniformly tends to Xi
verifier: PAPER
scope: COFINAL_FAMILY
lean_declaration: null
lean_port: OPEN
```

Нельзя больше отправлять агенту задачу:

```text
Find theorem hermfact1 in Lean.
```

Правильная задача:

```text
Find or construct the Lean import of CCM Lemma 7.3
after the exact project object and normalization crosswalk.
```

Это **[C04] SAME-COORDINATES-TWO-LAWS**: одинаковая подпись в карте и в коде не означает одинаковый тип объекта.

---

# Что было перепутано с Hermitian-фактом

`hermfact1` **не имеет отношения к эрмитовости CCM-матрицы**.

Реальные факты лежат здесь.

## 1. Симметрия исходной матрицы

```lean
Q3.RouteB.ccmWeilMatFinite_transpose_eq
```

Файл:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean
```

Commit:

```text
4c7de4b678ffcef1775309213f509b60c0fec476
```

История фиксирует этот commit как `Materialize general finite CCM source matrix`. fileciteturn114file0L1-L7

## 2. Симметрия сдвинутой матрицы

```lean
Q3.RouteB.ccmShiftedWeilMatFinite_transpose_eq
```

Файл:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilShiftedRankOne.lean
```

Commit:

```text
2efe7f7ad851d1f8afa17004bdff4f24cc833225
```

Теорема уже доказывает transpose equality для

\[
K-\varepsilon I.
\]

fileciteturn118file0L2-L6 fileciteturn116file0L1-L7

## 3. Переход `transpose = self` → `IsHermitian`

Отдельной публичной теоремы с названием вроде `hermfact1` нет.

Переход уже встроен в:

```lean
ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh
```

Там Lean раскрывает `Matrix.IsHermitian`, заменяет conjugate transpose на transpose для \(\mathbb R\), затем применяет:

```lean
ccmShiftedWeilMatFinite_transpose_eq
```

fileciteturn113file0L2-L6

Commit:

```text
b7685eb080131a54607a639629ffb08c77556b9f
```

fileciteturn115file0L1-L7

**Вывод:** карта была права по математике и неточна по адресу. Эрмитовость не отсутствует. Она является внутренним derivation, а не отдельным supplier.

---

# Главная находка: правило «перевод брать из потребителя» правильное

Твоя новая формулировка сильнее старого яруса 3:

\[
\boxed{
\text{Не сочинять перевод. Извлекать exact obligations из типа consumer theorem.}
}
\]

Это уже поддерживается живой инфраструктурой: зарегистрированный workflow `property-descent` начинает с точного target и terminal consumer, затем спускает каждую premise до статуса `READY`, `GAP`, `MISMATCH`, `OWNER_DATA` или `NUMERIC`. fileciteturn142file0L1-L2

Старый словарь сделал полезную разведку. Но его первая запись действительно слишком свободно перевела `hbottom` в язык внутренних произведений. Живой consumer уже задаёт точное утверждение:

```lean
hbottom :
  ∀ x : CCMModeFinite N → ℝ,
    epsilon * (x ⬝ᵥ x) ≤
      x ⬝ᵥ Matrix.mulVec
        (ccmWeilMatFinite mProject N) x
```

Это не prose и не семантическая догадка. Это exact contract. fileciteturn113file0L2-L6

## Новое правило

```text
Consumer exists:
  consumer type is authoritative.

Consumer does not exist:
  first create a trusted Challenge theorem statement.

Never:
  translate from narrative directly into search terms
  and then treat the result as the target.
```

---

# Что из предложенного реально работает

## 1. Конкретный finite real-zero consumer уже собран

Есть точная цепочка:

```text
shifted source matrix
→ nonnegative form
→ one-dimensional radical
→ quotient real-zero consumer
→ concrete source Lagrange polynomial has only real zeros.
```

Основной weld:

```lean
ccmSourceLagrangePolynomial_complex_zerosRealOn_of_shifted_nonneg_finrank_one
```

уже связывает точный CCM source-object с generic quotient consumer. fileciteturn126file0L2-L6

Commit:

```text
70789ab39b3c6796c8fc69669f340ae932f7bfba
```

fileciteturn137file0L1-L7

## 2. Чётность уже не независимый input

Wrapper:

```lean
ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
```

сам выводит `hxiEven` через:

```lean
ccmEigenvector_even_of_simple_eigenspace_and_normalized
```

fileciteturn121file0L2-L6

Commit:

```text
68217ce339d517a80c6e3f4a607309038119f00f
```

fileciteturn122file0L1-L7

Значит constructor не должен выдавать worker-задачу:

```text
Prove hxiEven.
```

для этой цепи. Он должен отметить:

```yaml
hxiEven:
  role: DERIVED
  supplier:
    ccmEigenvector_even_of_simple_eigenspace_and_normalized
```

## 3. Нормировка тоже имеет готовый downstream-механизм

После independent simple-even eigenvector проект доказывает ненулевость eta-паринга и строит eta-нормированный representative:

```lean
exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector
```

fileciteturn135file0L2-L6

Commit:

```text
d95078004c71f6a68b1704a3eb1856bab0499ae1
```

fileciteturn136file0L1-L7

Но здесь есть важная граница:

```text
simple + normalized → even
```

и

```text
simple + even → eta normalization exists
```

нельзя склеивать в круг.

Для честного автоматического route нужен источник evenness независимо от normalization. **Penalty theorem** является таким возможным bundle supplier, потому что он выдаёт simple + even ground package. Но concrete CCM crosswalk и uniform family theorem ещё открыты. fileciteturn132file0L1-L2

## 4. `exact?` действительно полезен как retrieval probe

Точечный import дал ответ за восемь секунд. Производительность не является текущей стеной. fileciteturn110file0L2-L7

Но найденный green-control был:

```lean
(hA.eigenvalues i : ℝ) = hA.eigenvalues i
```

и Lean предложил `rfl`. Это tautological control, а не supplier H2a. fileciteturn109file0L2-L6

Следовательно:

```text
exact? works as typed retrieval and compile assistant.
exact? is not an exact-claim comparator.
```

Иначе срабатывает **[C10] FUNCTIONAL-NOT-SURROGATE**.

---

# Что из предложенного не работает

## 1. Rayleigh theorem не закрывает exact `hbottom`

Mathlib theorem:

```lean
LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
```

говорит, что infimum частного Рэлея является собственным значением.

Consumer требует другое:

```text
заранее выбранное epsilon является глобальной нижней границей формы.
```

Чтобы применить Rayleigh theorem, надо:

1. определить `epsilon` как точный `iInf`;
2. построить eigenvector для этого `epsilon`;
3. доказать order inequality для этого определения;
4. перенести всё с `toEuclideanLin` обратно на exact CCM `mulVec`.

Без этого Rayleigh theorem остаётся механизмом, не supplier.

Принимать его напрямую было бы **[C10] surrogate acceptance**.

## 2. Foreign `posIndex` не закрывает `hsimple`

Теоремы:

```text
finrank_range_hermPosPart = posIndex
finrank_le_posIndex_of_posDefOn
```

описывают positive index и positive subspaces.

Они не доказывают:

```lean
Module.finrank ℝ
  ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1
```

Нужен отдельный rank/nullity, gap или penalty theorem.

## 3. `heig` — не имя потерянной леммы

`heig` — зависимые данные:

```lean
epsilon
xi
A *ᵥ xi = epsilon • xi
```

Constructor должен искать не theorem с названием `heig`, а **witness producer**, который одновременно возвращает:

```text
epsilon;
xi;
xi ≠ 0;
eigen equation;
bottomness;
possibly simplicity/evenness.
```

То есть здесь нужен **bundle search**, а не поиск одной premise.

## 4. Concrete output не равен abstract roof family

Consumer доказывает real zeros для:

```lean
sourceLagrangePolynomial
  (fun i => ccmModeFinite N i)
  xi
```

Roof требует real-zero property для:

```lean
C.Pstar.family i
```

Это разные objects, пока не доказан crosswalk.

Именно поэтому SIMPLE_EVEN:1 остаётся `MISMATCH`.

Это **[C04]**: оба объекта являются entire functions, но equality после забывания construction provenance не доказана.

---

# Exact binder ledger для consumer

Используем более сильный wrapper:

```lean
ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
```

| Binder | Роль конструктора | Статус |
|---|---|---|
| `mProject`, `N` | **DATA** — параметры source family | известны |
| `epsilon`, `xi` | **WITNESS DATA** | надо построить |
| `hm`, `hN` | **AUTO SIDE CONDITION** | дешёвая арифметика |
| `heig` | **WITNESS EQUATION** | часть ground-state package |
| `hnormalized` | **NORMALIZATION GUARD** | downstream supplier существует |
| `hbottom` | **OPEN THEOREM** — exact fixed-\(\epsilon\) form inequality | load-bearing |
| `hsimple` | **OPEN THEOREM** — eigenspace dimension one | load-bearing |
| quotient basis `b` | **BOOKKEEPING WITNESS** | вероятно автоматизируется; compile не проверен |
| `hxiEven` | **DERIVED** | уже устранён wrapper |
| matrix `IsHermitian` | **DERIVED INTERNAL** | уже устранён |
| concrete output → `C.Pstar.family` | **OUTPUT CROSSWALK** | OPEN MISMATCH |

Ключевой результат:

\[
\boxed{
\text{Не шесть равных дыр. Две содержательные spectral premises + witness package + один output crosswalk.}
}
\]

---

# Исправленная архитектура конструктора

Старое:

```text
gap
→ свободный перевод
→ атомы
→ поиск
→ сборка
```

Новое:

```text
assembly gap
→ nearest concrete terminal consumer
→ exact elaborated consumer type
→ binder roles
→ backward supplier descent
→ residual theorem obligations only
→ typed retrieval
→ explicit application
→ exact output comparison
→ axiom audit
```

## Layer −1 — Consumer Discovery

Найти theorem, который уже выдаёт ближайший полезный output.

Для SIMPLE_EVEN:6 это:

```lean
ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
```

Не начинать с `hbottom`.

## Layer 0 — Elaborated Contract

Взять `ConstantInfo.type` из Lean environment.

Не regex.

Не docstring.

Не ручной пересказ.

## Layer 1 — Binder Role Classifier

Классы:

```text
DATA
AUTO_SIDE_CONDITION
WITNESS
NORMALIZATION
OPEN_THEOREM
DERIVED
BOOKKEEPING
SOURCE_CROSSWALK
```

## Layer 2 — Backward Supplier Descent

Для каждой premise сначала проверить:

```text
already derived by another wrapper?
part of a larger bundle theorem?
definitional?
existing exact project theorem?
```

Только после этого искать по Mathlib и чужому дереву.

## Layer 3 — Residual Retrieval

Поиск запускается только на тех premises, которые действительно остались.

**Atom overlap** остаётся последним recall-channel.

## Layer 4 — Explicit Application Compile

`exact?` и `apply?` могут предложить route.

Статус повышается только после замены suggestion явным proof term и компиляции.

## Layer 5 — Exact-Claim Comparator

Проверить:

```text
same output;
same source object;
same normalization;
same quantifiers;
same scope;
permitted axioms.
```

Именно здесь должен падать concrete-to-abstract family mismatch.

## Layer 6 — Worker Dispatch

Worker получает не тему:

```text
prove H2a.
```

А один exact residual:

```text
prove fixed-epsilon bottom inequality for ccmWeilMatFinite
under exact penalty certificate X.
```

---

# Обязательная provenance-система

Каждое найденное имя получает один тип:

```yaml
LEAN_DECL:
  exact compiled declaration

PAPER_THEOREM:
  source theorem, Lean port absent

DOC_ALIAS:
  narrative label such as hermfact1

LOCAL_HYPOTHESIS:
  binder name such as heig

DATA_CONSTRUCTION:
  epsilon, xi, matrix, basis, normalization

NUMERIC_CERT:
  finite external certificate

PLACEHOLDER:
  architecture slot without source theorem
```

Это остановит повтор истории `hermfact1`.

---

# Два candidate representations

## R1 — Consumer Contract Graph

```yaml
object:
  theorem consumer
nodes:
  exact binders
hyperedge:
  all binders -> conclusion
kill_power: 5/5
cost: 1/5
```

Преимущество: не теряет AND-структуру и dependent witnesses.

Выбран.

## R2 — Bundle Supplier Graph

Вместо независимых `heig`, `hbottom`, `hsimple`, `even` искать theorem package:

```text
penalty certificate
→ lowest eigenpair
→ bottomness
→ simplicity
→ evenness.
```

```yaml
kill_power: 5/5
cost: 2/5
main_risk:
  bundle theorem lives over a neighboring complex generalized pencil
  and still needs an exact CCM crosswalk
```

Это правильный secondary route.

---

# Registered predictions

```text
P1:
  hermfact1 is classified DOC_ALIAS,
  not LEAN_DECL.
  confidence 1.00.

P2:
  exact consumer descent removes hxiEven and standalone Hermitian
  from the open ledger.
  confidence 0.99.

P3:
  exact consumer descent leaves hbottom, hsimple,
  witness construction and concrete-to-abstract family crosswalk.
  confidence 0.95.

P4:
  quotient basis can be generated automatically
  after finite-dimensional/free instances are exposed.
  confidence 0.70.
  UNTESTED.

P5:
  bundle-first search is more useful than independent search
  for heig/hbottom/hsimple.
  confidence 0.90.
```

---

# STRONGEST ATTACK

Consumer-first descent can still certify the wrong route.

Why?

Because the consumer conclusion may be only the nearest local result:

```text
concrete source Lagrange polynomial has real zeros.
```

The assembly target is:

```text
the selected canonical approximation family has real zeros.
```

A perfect proof of the consumer does not close the route until the output crosswalk is exact.

Therefore the final semantic guard is:

\[
\boxed{
\text{consumer conclusion = assembly target object}
}
\]

not merely:

```text
consumer compiled.
```

This is the exact place where current node 1 remains `MISMATCH` and node 15 remains `GAP`.

---

# FINAL PROPOSAL

Freeze these conclusions:

```text
hermfact1:
  stale documentary alias for CCM Lemma 7.3.
  No Lean declaration.

Hermitian CCM fact:
  already internal through transpose equality.

Consumer signature:
  authoritative source of exact obligations.

Current substantive finite gap:
  construct one simple bottom eigenpair package.

Current route gap after finite consumer:
  concrete Lagrange polynomial
  → selected canonical family
  → c_N normalization
  → Xi limit.
```

Do not update the dictionary by replacing one prose translation with another prose translation.

Update its schema:

```text
consumer theorem
→ exact binders
→ role of every binder
→ exact suppliers
→ remaining residuals
→ exact output crosswalk.
```

---

# CODEX DIRECTIVE

```text
TARGET:
  CARTOGRAPHER_CONSUMER_CONTRACT_V0_CCM_REALZERO

PIN:
  repo = /Users/emalam/GitHub/rh_lean_01_2026
  branch = rh_clean
  HEAD = d719193125b23601b1b7a4f4cc11e4816e003f05

MODE:
  read-only backtest
  no repo writes
  no Lean source edits
  no commit

CONSUMER:
  Q3.RouteB.
    ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized

PACKAGE:
  q3.lean.aristotle
  Lean 4.26.0
  Mathlib 4.26.0

TASK 1 — ELABORATED CONTRACT:
  Read the theorem from the Lean environment.
  Export exact:
    declaration name;
    universe parameters;
    full elaborated type;
    forall binders;
    conclusion;
    constants used in the type;
    source position.

  Do not use regex source parsing as truth.

TASK 2 — BINDER ROLES:
  Classify every binder as:
    DATA
    AUTO_SIDE_CONDITION
    WITNESS
    NORMALIZATION
    OPEN_THEOREM
    DERIVED
    BOOKKEEPING
    SOURCE_CROSSWALK

TASK 3 — BACKWARD SUPPLIERS:
  Resolve exact existing suppliers for:
    shifted transpose/Hermitian derivation;
    parity/evenness;
    eta nonvanishing and normalization;
    shifted kernel/eigenspace identity;
    real-zero quotient weld.

  Mark hbottom and hsimple OPEN unless an exact theorem
  consumes the same CCM object and exact epsilon.

TASK 4 — OUTPUT COMPARISON:
  Compare the exact consumer conclusion with:
    SIMPLE_EVEN_GROUND_TO_REAL_ZEROS node 1 target
    and the current canonical selectedFamily target.

  Required outcome:
    preserve CONCRETE_TO_ABSTRACT_FAMILY_MISMATCH.

TASK 5 — PLANTS:
  P1:
    resolve `hermfact1`.
    Required classification: DOC_ALIAS.
    It must not resolve to a Lean declaration.

  P2:
    present
      LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
    as candidate for fixed-epsilon hbottom.
    Required: reject without an epsilon=iInf bridge.

  P3:
    present foreign posIndex/finrank theorem as hsimple.
    Required: reject as wrong conclusion.

  P4:
    present standalone IsHermitian as an open gap.
    Required: reject because the active consumer path already derives it
    from transpose equality.

OUTPUTS:
  /tmp/cartographer_ccm_consumer_contract.json
  /tmp/cartographer_ccm_consumer_contract_report.md

REPORT:
  exact HEAD;
  exact toolchain;
  exact consumer type;
  binder table;
  supplier graph;
  residual obligations;
  output mismatch;
  plant results;
  prediction scores P1-P5.

SUCCESS:
  CCM_CONSUMER_CONTRACT_BACKTEST_PASS

FAILURE:
  DOC_ALIAS_MISCLASSIFIED_AS_LEAN_DECL
  FIXED_EPSILON_HBOTTOM_SURROGATE_ACCEPTED
  POSINDEX_SURROGATE_ACCEPTED_AS_HSIMPLE
  INTERNAL_HERMITIAN_FACT_REOPENED
  CONCRETE_TO_ABSTRACT_FAMILY_MISMATCH_DROPPED
  ELABORATED_CONTRACT_EXTRACTION_FAIL

FORBIDDEN:
  no exact? = comparator claim;
  no atom overlap as applicability proof;
  no foreign code port;
  no theorem weakening;
  no new axiom;
  no route promotion;
  no RH claim.
```

---

# META CLOSEOUT

## Что стало меньше?

Неопределённый «перевод H2aAt» сжат до exact consumer contract:

```text
two spectral obligations
+ dependent witness package
+ one output crosswalk.
```

## Что убито?

- `hermfact1` как якобы Lean theorem;
- standalone Hermitian gap;
- independent `hxiEven` gap;
- Rayleigh iInf theorem as direct fixed-epsilon hbottom supplier;
- foreign positive-index theorem as direct simplicity supplier;
- `exact rfl` control as evidence of H2a progress.

## Что нельзя повторять?

Нельзя переводить binder из головы, если его exact consumer type уже существует.

Нельзя считать local consumer conclusion равным roof target без output crosswalk.

## Current smallest named gap

Для конструктора:

\[
\boxed{\texttt{ConsumerContractExtractionAndRoleClassification}}
\]

Для математики:

\[
\boxed{\texttt{CCMSimpleBottomEigenpairPackage}}
\]

После finite consumer:

\[
\boxed{\texttt{CCMLagrangePolynomialToCanonicalSelectedFamilyCrosswalk}}
\]

## Next cheapest decisive test

Read-only backtest на одном уже существующем CCM consumer.

```yaml
iteration:
  target: consumer_first_proof_constructor
  status: OPEN
  failed_strategy: prose_translation_then_atom_search
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: ConsumerContractExtractionAndRoleClassification
  invariant_learned: exact consumer type precedes search and decomposition
  forbidden_future_move: resolve documentary aliases as Lean declarations
  next_decisive_test: CCM_CONSUMER_CONTRACT_BACKTEST
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
