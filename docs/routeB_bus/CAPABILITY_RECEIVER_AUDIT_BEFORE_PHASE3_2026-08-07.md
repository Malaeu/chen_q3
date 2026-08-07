# Goal 057 · capability receiver audit before Phase 3

```yaml
STATUS: COMPLETE
SOURCE: q3.lean.aristotle/aristotle_db/knowledge.db
SOURCE_TABLE: capability
SOURCE_ROW_COUNT: 507
LEAN_FILES_CHANGED: 0
PHASE_2_PRECOMMIT_CHANGED: false
PHASE_3_NUMERICS_RUN_AFTER_THIS_AUDIT: false
```

## 1. `SectorIsolationRadius` — использовать, но не путать labels

Файл:
`q3.lean.aristotle/Q3/Proofs/RouteB/SectorIsolationRadius.lean`, SHA-256
`67342984d35a0d0ef223186f76a44584e546e3e5c3c5f383fd7128746c1d8c82`.
Bus-copy байтово совпадает. `lake env lean` проходит; все пять declarations имеют
стандартный axiom profile `[propext, Classical.choice, Quot.sound]`.

Теорема действительно пакует минимум двух конкурентов. Но буквальная eigen-labeling из
комментария файла не совпадает с текущими Phase-2 объектами:

| receiver label | Phase-2 instantiation | важная граница |
|---|---|---|
| `epsilonPlus1` | `a = q* K q` | trial Rayleigh upper level, не доказанное равенство ground eigenvalue |
| `epsilonPlus2` | `lambda_min(K_even restricted to q-perp)` | compression floor, не доказанное равенство next-even eigenvalue |
| `epsilonMinus1` | `lambda_min(K_odd)` | настоящий finite odd-sector floor |

С этой relabeling hypotheses `a < epsilonPlus2` и `a < epsilonMinus1` интервально
разряжены на всех четырёх `N`. Поэтому `sectorIsolationRadius_certificate` выдаёт
правильный консервативный двухконкурентный пакет вокруг trial level. Поскольку odd floor
контролирует `beta*_N` на всём ladder, binding clause —
`sectorIsolationRadius_le_odd_gap`.

| N | `(beta*_N - a)/2` |
|---:|---:|
| 120 | `1.52772069975860736298092901222e-55` |
| 160 | `1.36119594702619438307777122467e-55` |
| 200 | `1.31126699939628331810875315727e-55` |
| 240 | `1.23870743075492352705372550004e-55` |

Это пока numerical-to-receiver matching, не Lean instantiation: JSON/Arb endpoints должны
быть импортированы как Lean inequalities. Для буквальной eigen-labeling
`epsilonPlus1=ground`, `epsilonPlus2=next even` Phase 3 должна отдельно изолировать два
нижних even eigenvalues.

```yaml
DECISION: USE_RECEIVER_WITH_EXPLICIT_PHASE2_RELABEL
BINDING_CLAUSE: sectorIsolationRadius_le_odd_gap
DIRECT_TRUE_EIGEN_LABEL_MATCH: false
MISSING_FOR_LEAN_INSTANTIATION: endpoint_hbox_or_exact_inequality_import
```

## 2. `PerturbativeTrueGapLower` — receiver готов, premises ещё не получены

Файл:
`q3.lean.aristotle/Q3/Proofs/RouteB/PerturbativeTrueGapLower.lean`, SHA-256
`bc16c18363618728b323d03fc7ebda0132aa93ba04cce22a6bc1464e9148fd19`.
Bus-copy байтово совпадает. `lake env lean` проходит; все declarations имеют стандартный
axiom profile `[propext, Classical.choice, Quot.sound]`.

Комментарий самого theorem точен: это scalar bookkeeping; endpoint estimates он не
доказывает. Arb balls могут служить `errLow/errHigh` для перехода

```text
numerical model endpoint -> exact eigenvalue of the same finite CCM matrix
```

после того, как membership exact endpoint in Arb ball материализован в Lean. Они **не**
являются автоматически оценками

```text
finite sectional endpoint -> continuum operator endpoint.
```

Filter-level theorem также не превращает четыре точки `[120,160,200,240]` в asymptotic
statement. Для содержательного `l = Filter.atTop` нужны `eventually` endpoint estimates и
budget для всех достаточно больших `N`. Выбор конечного index type дал бы формально иной,
не asymptotic смысл.

Два контрпримера в строках 69 и 80 проверены и остаются load-bearing guards:

- положительный model gap без endpoint control не заставляет true gap быть положительным;
- endpoint errors могут съесть весь model gap.

```yaml
DECISION: RECEIVER_READY_PREMISES_OPEN
FINITE_ENDPOINT_IMPORT_USE: valid_after_Lean_endpoint_bounds
FINITE_TO_CONTINUUM_USE: not_justified
AT_TOP_EVENTUAL_USE: requires_new_eventual_estimates
COUNTEREXAMPLE_GUARDS: KEEP_BOTH
```

## 3. `quotientByRadicalForm_definite` — доступен, сейчас не несущий

Файл:
`q3.lean.aristotle/Q3/Proofs/RouteB/QuotientByRadicalSelfAdjoint.lean:58`.
`lake env lean` проходит; theorem имеет стандартный axiom profile. Он доказывает
невырожденность положительной формы на quotient by radical.

Текущий CCM crosswalk фиксирует `G=I`, следовательно radical нулевой и quotient не нужен
для finite Phase-2/3 matrices. Receiver полезен для будущего abstract semidefinite skeleton,
если basis quotient будет поставляться как existence.

```yaml
DECISION: AVAILABLE_NOT_LOAD_BEARING_WHILE_G_EQUALS_IDENTITY
```

## 4. Wiring verdict

Поиск по `q3.lean.aristotle/Q3/**/*.lean` не нашёл ни одного import/call этих двух gap
receivers вне их собственных файлов. Они доказаны, но не подключены к Goal 057.

Следующий numerical run обязан:

1. отдельно выдавать true finite even ground, next-even и odd endpoints;
2. отдельно сохранять Phase-2 trial/compression labels;
3. не называть Arb radius finite-to-continuum perturbation error;
4. не заявлять `Eventually atTop` по конечной сетке;
5. подготовить endpoint payload так, чтобы последующая Lean materialization могла вызвать
   `sectorIsolationRadius_certificate` и finite-point форму
   `true_gap_lower_of_abs_endpoint_perturbations` без изменения их theorem statements.

```yaml
OVERALL: RECEIVERS_FOUND_AND_CLASSIFIED
PHASE_3_GATE: OPEN_WITH_LABEL_AND_ENDPOINT_DISCIPLINE
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PX_RH_CLAIM: NOT_MADE
```
