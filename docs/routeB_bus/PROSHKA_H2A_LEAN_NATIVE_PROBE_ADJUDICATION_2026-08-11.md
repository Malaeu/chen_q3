# STATUS: OPEN — REPAIRED LEAN-NATIVE PROBE AUTHORIZED; ORIGINAL THREE-PROBE PLAN REJECTED
```yaml
PRIMARY: RUN_H2A_RAYLEIGH_TYPED_BRIDGE_PROBE
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  TIP: 087e3bbc14bcec2d86f81c2f9e18d027e224f32c
  TIP_VERIFIED: true
  PROSHKA_PROTOCOL_BLOB: 334b33106a818e76c2f4553339dd90f13fb10ee5
  ARSENAL_KERNEL_BLOB: c258a18c18ea40e2496bd3e133ddee75ebc4f458
  ARSENAL_DECK_BLOB: 94e87434980395e99b0600ecffba929f1f03ad2b

ARSENAL_MANDATE:
  ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

PACKAGE_LOCK:
  SELECTED_PACKAGE: q3.lean.aristotle
  LEAN: v4.26.0
  MATHLIB: v4.26.0
  OTHER_PACKAGE_NOT_USED:
    path: docs/routeB_bus
    lean_mathlib: v4.28.0
    reason: TARGET_OBJECT_LIVES_IN_Q3_PACKAGE

ORIGINAL_PROPOSAL_AUDIT:
  M2_LEAN_NATIVE_SEARCH: REPAIRED_ALIVE
  M3_ENVIRONMENT_DUMP: ALIVE_DEFERRED
  DOC_GEN4_RECON: ALIVE_OPTIONAL
  EXACT_APPLY_AS_COMPARATOR: KILLED
  THREE_UNTYPED_H2A_EXAMPLES: KILLED
  FOREIGN_HSIMPLE_AS_DIRECT_SUPPLIER: KILLED
  RUN_IN_WHICHEVER_PACKAGE_SUCCEEDS: KILLED

SELECTED_PROBE:
  id: H2A_RAYLEIGH_TYPED_BRIDGE_PROBE
  mode: TEMPORARY_READ_ONLY_REPO
  target:
    - CCM_MATRIX_TO_EUCLIDEAN_SYMMETRIC_BRIDGE
    - BOTTOM_RAYLEIGH_IINF_IS_EIGENVALUE
  positive_source_matrix: Q3.RouteB.ccmWeilMatFinite
  negative_plant: ARBITRARY_NONSYMMETRIC_MATRIX
  search_tools:
    - exact?
    - apply?
  final_verifier:
    - EXPLICIT_TERM_COMPILATION
    - PRINT_AXIOMS
    - NEGATIVE_PLANT_REJECTION

EXECUTION:
  AUTHORIZED_BY_OWNER_MESSAGE: true
  REPO_WRITE_AUTHORIZED: false
  COMMIT_AUTHORIZED: false
  DICTIONARY_MUTATION_BEFORE_RESULT: false
  FOREIGN_CODE_PORT: false
  DOC_GEN_RUN: false
  ENV_DUMP_BUILD: false

SUCCESS:
  code: H2A_RAYLEIGH_TYPED_BRIDGE_COMPILED
  meaning: TYPED_RETRIEVAL_PIPELINE_VALIDATED_NOT_H2A_CLOSED

FAILURES:
  - H2A_RAYLEIGH_TARGET_NOT_TYPED
  - H2A_MATRIX_TO_EUCLIDEAN_BRIDGE_GAP
  - H2A_LIBRARY_SEARCH_TIMEOUT
  - H2A_EXPLICIT_BRIDGE_COMPILE_FAIL
  - H2A_PLANT_NOT_REJECTED
  - H2A_AXIOM_PROFILE_DIRTY

LOAD_BEARING_H2A_STATUS:
  generic_penalty_engine: ALREADY_PROVED
  concrete_family_instantiation: OPEN
  concrete_penalty_certificate: OPEN
  H2A_CLOSED_BY_THIS_PROBE: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Исправленный вердикт

Связка **Lean-native search + environment index** правильна.

Исходный план надо разрезать.

Правильный порядок:

```text
exact typed challenge
→ exact?/apply? как retrieval
→ explicit proof term
→ negative plant
→ axiom audit
→ environment dump
→ exact comparator
→ dispatch
```

Неправильный порядок:

```text
три псевдо-example
+ environment dumper
+ doc-gen4
+ exact?/apply? как comparator
```

Причина простая: пока нет точного elaborated target, поиск проверяет не тот контракт или вообще не имеет контракта.

---

## Что в предложении правильно

### 1. Lean должен судить применимость

**Unification** — сопоставление elaborated типов с учётом definitional equality.

Он действительно сильнее `rg`.

Поэтому финальная применимость candidate theorem должна проверяться временным Lean-файлом.

`[ABSTRACT][LEAN]`

### 2. Environment dump нужен

Lean environment хранит полный `ConstantInfo.type`.

`forallTelescope` может разложить тип на binders и conclusion.

`Expr.getUsedConstants` существует в Lean 4.26.

Значит typed JSON index реализуем без парсинга `.lean`.

`[ABSTRACT][PAPER]`

### 3. Пины пакетов надо разделять

```text
q3.lean.aristotle:
  Lean 4.26.0
  Mathlib 4.26.0

docs/routeB_bus:
  Lean 4.28.0
  Mathlib 4.28.0
```

Candidate считается применимым только после проверки в пакете consumer.

`[ABSTRACT][PAPER]`

### 4. Поиск по смыслу полезнее общего атомного overlap

Первый dictionary pass уже показал это.

Но semantic phrase search остаётся recall-layer.

Lean typecheck остаётся judge.

`[ABSTRACT][PAPER]`

---

## Что в предложении неверно

### 1. `exact?` и `apply?` не являются comparator

Lean 4.26 реализует оба через library search и `solveByElim`.

Максимальная глубина поиска равна шести.

`exact?` требует закрыть цель.

`apply?` разрешает частичную suggestion с остаточными подцелями.

Следовательно:

```text
exact?:
  typed retrieval + possible local proof search.

apply?:
  typed retrieval + residual-goal exposure.

comparator:
  exact trusted statement equality
  + permitted axiom policy
  + source/consumer identity.
```

Это три разных роли.

Приравнивание `exact?` к comparator является **[C10] surrogate kill**.

Одинаковый локальный goal не гарантирует, что весь заявленный route theorem не ослаблен.

Это также **[C04] same-interface warning**.

`[ABSTRACT][PAPER]`

### 2. `exact?` не одношаговый

Он может цеплять несколько declarations через `solveByElim`.

Поэтому результат нельзя классифицировать как «найдена одна готовая лемма» без dependency inspection.

`[ABSTRACT][PAPER]`

### 3. Три строки dictionary не являются Lean-targets

Сейчас записано:

```text
hbottom
heig
hsimple
```

Но отсутствуют полные binders, carrier, scalar field, self-adjointness, normalization и точный consumer.

До их фиксации писать три `example` рано.

`[ABSTRACT][PAPER]`

### 4. `hbottom` неверно сопоставлен с Rayleigh theorem

Mathlib доказывает:

```text
iInf Rayleigh quotient is an eigenvalue
```

для symmetric finite-dimensional operator.

Это даёт existence нижнего eigenpair.

Это не доказывает произвольную заранее указанную inequality:

```text
epsilon * ||x||² ≤ <Ax,x>.
```

Если `epsilon` определён как `iInf`, lower-bound является order fact.

Если `epsilon` пришёл из certificate, Mathlib Rayleigh не создаёт certificate.

Правильный dictionary split:

```text
bottom eigenpair existence:
  Mathlib Rayleigh.

certified lower bound at chosen epsilon:
  project penalty/coercivity certificate.
```

`[ABSTRACT][LEAN]`

### 5. Foreign `hsimple` не является прямым supplier

`Zeta23/LinAlg/Inertia.lean` даёт positive-index и pullback machinery.

Он не выдаёт напрямую:

```text
finrank (eigenspace A μ) = 1.
```

Для этого всё ещё нужен rank/nullity-one или penalty/gap theorem.

Кроме того, foreign theorem отсутствует в импортированном Q3 environment.

`exact?` его не увидит.

Его статус:

```text
MECHANISM_CANDIDATE
PORT_REQUIRED
NOT_DIRECT_SUPPLIER
```

`[ABSTRACT][PAPER]`

### 6. `doc-gen4` не заменяет environment dump

`doc-gen4` уже записан как dependency.

Но его JSON хранит rendered `header`, имя, kind, docstring и source position.

Он не хранит raw Lean `Expr`.

Он также не заменяет proof dependency extraction.

Выходные declaration files имеют формат compressed JSON `.bmp`.

Это полезный documentation index.

Это не canonical typed IR.

`[ABSTRACT][PAPER]`

### 7. Нельзя выбирать пакет по тому, где proof случайно проходит

Target object `ccmWeilMatFinite` живёт в `q3.lean.aristotle`.

Значит probe запускается там.

Проверка в `docs/routeB_bus` с Mathlib 4.28 проверяла бы другой environment.

Это **[C04] category mismatch**.

`[ABSTRACT][PAPER]`

---

## Важный repo-факт: большая часть общей H2a-машины уже есть

Проект уже содержит:

```lean
H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity
```

Этот theorem даёт:

```text
lowest generalized eigenvalue;
global minimum;
gap;
simplicity;
J-evenness;
```

из точного penalty certificate.

Кроме того, проект уже имеет:

```text
ccmWeilMatFinite_transpose_eq;
ccmEigenvector_even_of_simple_eigenspace_and_normalized;
exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector;
```

Следовательно, текущий load-bearing H2a gap не равен:

```text
Mathlib lacks Rayleigh theory.
```

Текущий gap:

```text
concrete CCM family
→ exact penalty data
→ verified certificate
→ SIEG family instantiation.
```

Проба ниже проверяет конструктор.

Она не закрывает H2a.

`[ABSTRACT][LEAN]`

---

# ROUTE MAP

| Маршрут | Kill-power | Стоимость | Вердикт |
|---|---:|---:|---|
| Typed `exact?`/`apply?` probe на exact Q3 target | 5/5 | 1/5 | **SELECTED** |
| Environment meta-dump сразу | 4/5 | 2/5 | После probe |
| `doc-gen4` docs build | 2/5 | 3/5 | Optional recon |
| Port foreign Inertia layer сейчас | 2/5 | 4/5 | Не запускать |
| Три псевдо-example параллельно | 1/5 | 3/5 | Убито |
| Treat `exact?` as comparator | 0/5 | — | **FATAL CONCEPT ERROR** |

---

# SELECTED PROBE

## Имя

```text
H2A_RAYLEIGH_TYPED_BRIDGE_PROBE
```

## Цель

Проверить одну exact chain:

```text
ccmWeilMatFinite_transpose_eq
→ matrix Hermitian
→ toEuclideanLin symmetric
→ Rayleigh iInf is an eigenvalue.
```

Mathlib уже имеет точный bridge:

```lean
Matrix.isHermitian_iff_isSymmetric
```

Проект уже имеет:

```lean
Q3.RouteB.ccmWeilMatFinite_transpose_eq
```

Mathlib уже имеет:

```lean
LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
```

`[ABSTRACT][LEAN]`

## Почему этот probe правильный

Он проверяет сразу:

1. перевод dictionary;
2. matrix/operator carrier;
3. typeclass compatibility;
4. library search;
5. explicit proof;
6. negative plant;
7. axiom profile.

Он не притворяется H2a closure.

---

# REGISTERED PREDICTIONS

```yaml
P1:
  prediction: explicit matrix-to-Rayleigh bridge compiles in Q3 Lean 4.26
  confidence: 0.85

P2:
  prediction: exact? may close; otherwise apply? names the Rayleigh theorem and leaves a symmetry bridge
  confidence_exact_close: 0.55
  confidence_apply_useful: 0.80

P3:
  prediction: arbitrary nonsymmetric-matrix plant is not closed
  confidence: 0.99

P4:
  prediction: foreign hsimple candidate is invisible in current Q3 environment
  confidence: 0.99

P5:
  prediction: doc-gen4 is unnecessary for this decision and does not provide raw typed dependency IR
  confidence: 0.95
```

Predictions must be scored without rewriting after the run.

---

# OUTCOME MAP

## Outcome A

```text
exact? closes;
explicit suggested term compiles;
plant fails.
```

Verdict:

```text
LEAN_NATIVE_TYPED_RETRIEVAL_GREEN.
```

Next:

```text
build restricted environment dump.
```

## Outcome B

```text
exact? fails;
apply? returns useful candidate and residual;
explicit two-step proof compiles;
plant fails.
```

Verdict:

```text
LEAN_NATIVE_PARTIAL_RETRIEVAL_GREEN.
```

Next:

```text
use apply? as residual generator;
build environment dump for ranking.
```

## Outcome C

```text
exact?/apply? find nothing;
explicit proof compiles;
plant fails.
```

Verdict:

```text
LIBRARY_SEARCH_RECALL_INSUFFICIENT.
```

Next:

```text
environment dump + typed retrieval;
exact Lean compilation remains final applicability judge.
```

## Outcome D

```text
explicit proof does not compile.
```

Verdict:

```text
TRANSLATION_OR_MATRIX_OPERATOR_BRIDGE_WRONG.
```

Next:

```text
repair typed dictionary before building tools.
```

A timeout is not a type mismatch.

It receives its own code:

```text
H2A_LIBRARY_SEARCH_TIMEOUT.
```

---

# STRONGEST ATTACK

Даже полный PASS может не уменьшить RH-gap.

Причина:

```text
the generic Rayleigh bridge may merely duplicate machinery
already subsumed by H2aPenaltyCoercivity.
```

Therefore success must be classified as:

```text
constructor validation;
typed representation progress.
```

It becomes proof progress only if it removes an explicit premise from a live consumer.

This is the main anti-decoration guard.

---

# TWO RE-REPRESENTATIONS IF THE PROBE IS INCONCLUSIVE

## R1 — Direct matrix spectral API

Use:

```text
Matrix.IsHermitian.eigenvalues;
spectral theorem;
eigenvalues₀ ordering.
```

Do not convert to `ContinuousLinearMap`.

```yaml
kill_power: 4/5
cost: 2/5
main_risk: eigenvalue ordering and target normalization
```

## R2 — Penalty contract as the computing object

Translate H2a directly into the eight inputs of:

```lean
H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity
```

Search for suppliers of those fields instead of searching for `hbottom/heig/hsimple` independently.

```yaml
kill_power: 5/5
cost: 3/5
main_risk: concrete certificate and family crosswalk remain open
```

R2 is the stronger load-bearing representation.

---

# CODEX DIRECTIVE

```text
TARGET:
  H2A_RAYLEIGH_TYPED_BRIDGE_PROBE

PIN:
  repo = /Users/emalam/GitHub/rh_lean_01_2026
  branch = rh_clean
  HEAD = 087e3bbc14bcec2d86f81c2f9e18d027e224f32c

ABORT:
  if HEAD differs.

PACKAGE:
  /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle

MODE:
  temporary probe;
  read-only repository;
  no commit;
  no dictionary edit.

DO NOT USE:
  docs/routeB_bus package;
  import Mathlib;
  foreign zeta-23 imports;
  doc-gen4;
  custom environment dumper.

CREATE:
  /tmp/H2aRayleighProbe.lean
  /tmp/H2aRayleighPlant.lean
  /tmp/H2aRayleighProbe.report.md

TARGETED IMPORTS:
  Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
  Mathlib.Analysis.InnerProductSpace.Rayleigh
  Mathlib.Analysis.Matrix.Hermitian

PHASE 0 — EXACT API:
  In the positive probe, print:

    #check Matrix.isHermitian_iff_isSymmetric
    #check LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
    #check Q3.RouteB.ccmWeilMatFinite_transpose_eq

  Materialize the exact target type from #check output.
  Do not manually guess implicit binders.

PHASE 1 — POSITIVE SEARCH:
  Build theorem:

    ccmWeilMatFinite_toEuclideanLin_isSymmetric

  Inputs:

    mProject N : ℕ
    hm : 2 ≤ mProject
    hN : 1 ≤ N

  Conclusion:

    the Euclidean linear map of
    ccmWeilMatFinite mProject N
    is symmetric.

  First body:

    by exact?

  Record:
    full suggestion;
    wall-clock;
    heartbeat failure if any.

  If exact? fails:
    use by apply? only to expose candidate and residual goals.
    Do not count an apply? diagnostic as a proof.

PHASE 2 — EXPLICIT TERM:
  Replace search tactic with explicit proof using:

    ccmWeilMatFinite_transpose_eq
    Matrix.isHermitian_iff_isSymmetric

  Then define:

    ccmWeilMatFinite_hasEigenvalue_iInf_rayleigh

  Its conclusion must be copied from the exact type of:

    LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional

  Instantiate it with the proved symmetric Euclidean linear map.

  Do not weaken the conclusion to mere existence of some eigenvalue.

PHASE 3 — AXIOMS:
  Add:

    #print axioms
      ccmWeilMatFinite_toEuclideanLin_isSymmetric

    #print axioms
      ccmWeilMatFinite_hasEigenvalue_iInf_rayleigh

  Expected:
    no sorryAx;
    no project axiom;
    only standard Lean axioms if any.

PHASE 4 — NEGATIVE PLANT:
  In H2aRayleighPlant.lean define an arbitrary nonsymmetric
  2×2 real matrix M.

  Attempt the same symmetric-map conclusion using exact?.

  Required:
    exact? does not close the goal.

  Also run apply? and record whether it leaves a Hermitian/symmetry residual.

  The plant file is expected to fail.
  Treat a zero exit as:
    H2A_PLANT_NOT_REJECTED.

COMMANDS:
  cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle

  /usr/bin/time -p \
    lake env lean /tmp/H2aRayleighProbe.lean \
    2>&1 | tee /tmp/H2aRayleighProbe.log

  if lake env lean /tmp/H2aRayleighPlant.lean \
      > /tmp/H2aRayleighPlant.log 2>&1; then
    echo H2A_PLANT_NOT_REJECTED
    exit 1
  else
    echo H2A_PLANT_REJECTED
  fi

REPORT:
  Write /tmp/H2aRayleighProbe.report.md with:

  - exact HEAD;
  - exact toolchain;
  - exact #check outputs;
  - exact? result;
  - apply? result;
  - explicit theorem statements;
  - commands and wall-clock;
  - axiom outputs;
  - plant output;
  - prediction scores P1–P5;
  - one final code.

SUCCESS CODE:
  H2A_RAYLEIGH_TYPED_BRIDGE_COMPILED

SUCCESS MEANING:
  Typed constructor retrieval pipeline validated.
  Do not claim H2a closed.

FAILURE CODES:
  H2A_RAYLEIGH_TARGET_NOT_TYPED
  H2A_MATRIX_TO_EUCLIDEAN_BRIDGE_GAP
  H2A_LIBRARY_SEARCH_TIMEOUT
  H2A_EXPLICIT_BRIDGE_COMPILE_FAIL
  H2A_PLANT_NOT_REJECTED
  H2A_AXIOM_PROFILE_DIRTY

FORBIDDEN:
  no repo writes;
  no commit;
  no Q3.Main;
  no theorem weakening;
  no `sorry`;
  no `admit`;
  no new axiom;
  no foreign port;
  no claim that exact?/apply? is comparator;
  no claim that this closes H2a.
```

---

# META CLOSEOUT

## Что стало меньше?

Исходный batch:

```text
three H2a probes
+ meta-dump
+ doc-gen4
+ comparator claim
```

сжат до одного exact typed bridge:

```text
CCM matrix
→ symmetric Euclidean operator
→ bottom Rayleigh eigenvalue.
```

## Что убито?

- `exact?` как comparator;
- `exact?` как одношаговый поиск;
- untyped triple probe;
- foreign `hsimple` как direct supplier;
- package selection by convenience;
- doc-gen4 as canonical typed IR.

## Что нельзя повторять?

Нельзя считать search suggestion доказательством.

Нельзя считать compile success semantic equality с другим source object.

Нельзя менять package/toolchain после результата.

## Current smallest named gap

Для конструктора:

```text
CCMMatrixToRayleighBottomEigenpairTypedBridge
```

Для настоящего H2a:

```text
ConcretePenaltyCertificateAndSIEGFamilyInstantiation
```

## Next cheapest decisive test

Запустить только указанный positive probe и negative plant.

## Fate of prior predictions

```text
Dictionary-first:
  CONFIRMED.

Atom overlap as supplier search:
  REFUTED.

Comparator before dictionary:
  REFUTED.

Lean-native typed applicability:
  REGISTERED, UNTESTED.

doc-gen4 as immediate canonical extractor:
  DEMOTED, UNTESTED.
```

```yaml
iteration:
  target: lean_native_constructor_probe
  status: OPEN
  failed_strategy: treat_library_search_as_exact_claim_comparator
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: CCMMatrixToRayleighBottomEigenpairTypedBridge
  invariant_learned: target package, exact elaborated type, source object and axiom policy are separate locks
  forbidden_future_move: run multiple extractor/search systems before one typed negative-controlled probe
  next_decisive_test: H2A_RAYLEIGH_TYPED_BRIDGE_PROBE
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
