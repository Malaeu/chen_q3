# GOAL 058 — REALZERO_GROUND_DIAGONAL_TO_XI: одна семья с двумя свойствами

```yaml
GOAL: 058
NODE: REALZERO_GROUND_DIAGONAL_TO_XI
STATUS: OPEN
OPERATIVE_CLASS: RUN_REALZERO_GROUND_DIAGONAL_TO_XI
TRANSACTION: REALZERO_FINITE_GROUND_DIAGONAL_TO_XI
STOP: TWO_DIFFERENT_FAMILIES_USED
SUCCESS: ONE_NORMALIZED_GROUND_FAMILY_REAL_ZEROS_AND_LOCALLY_UNIFORM_LIMIT

SOURCE: docs/routeB_bus/proshka/PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md
SOURCE_PIN: f82b09f8c24f0b74a62c5c48e5e4e9a3b2b36cc7
ASSEMBLY_CHAIN: REALZERO_GROUND_DIAGONAL_TO_XI
MIGRATOR: orchestrator/kb_migrate_route058.py

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
N480: HOLD
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

---

## Зачем этот гол существует

Предыдущие голы 001–057 закрывали **узлы**. Этот закрывает **связность**: он объявляет, какая
именно последовательность несёт оба нужных свойства и в каком порядке они на неё попадают.

До него в проекте одновременно жили две семьи, и это выглядело почти цепочкой:

```
trial-семья сходится к Ξ            (CCM Lemma 7.3, доказано в статье)
ground-семья имеет вещественные нули (Theorem 5.10, доказано у нас условно)
следовательно RH                     ← ЛОЖНЫЙ ВЫВОД
```

Вывод ложен: использованы **две разные последовательности**. Одинаковый интерфейс целых
функций не стирает происхождение коэффициентов — это `[C04]` плюс `[C10]`.

---

## Несущий инвариант — нарушение останавливает гол

```
G_j   transform конечного CCM ground-вектора       несёт ВЕЩЕСТВЕННОСТЬ НУЛЕЙ
T_j   transform пролатного пробника (kTrial)       несёт СХОДИМОСТЬ к Ξ
```

**Мост переносит сходимость на `G_j`.** Обратное направление — перенос вещественности на
`T_j` — невозможно в принципе, а не трудно: вещественность нулей неустойчива к возмущению.
У `z² + ε` при `ε < 0` два вещественных нуля, при `ε > 0` — сопряжённая пара; сколь угодно
точное приближение переводит одно в другое.

Гурвиц читает нули **предела**, а не переносит их вдоль последовательности. Поэтому нужна
одна последовательность с обоими свойствами, а не две с одним каждая.

`STOP: TWO_DIFFERENT_FAMILIES_USED` — если в цепочке окажутся две семьи, гол останавливается
независимо от того, сколько шагов закрыто.

---

## Восемь ворот

| шаг | ворота | что требуется | статус |
|---|---|---|---|
| 0 | `G0` | точный объект, координата, нормировка | `GAP` частично |
| 1 | `G1` | кофинальный конечный simple-even ground-пакет | `GAP` главный спектральный фронт |
| 2 | `G2` | вещественность нулей лагранжева многочлена строки | **`READY`** условно на G1 |
| 3 | `G2b` | перенос **множества** нулей на преобразование Prop-5.9 | **`PROVED`** 2026-08-12 |
| 4 | `G3` | та же `F_j` отслеживает projected trial | `GAP` **ГЛАВНАЯ СТЕНА** |
| 5 | `G3c` | projected trial отслеживает continuum trial | `GAP` |
| 6 | `G4` | CCM Lemma 7.3: continuum trial → Ξ | `GAP` доказано в статье, порт открыт |
| 7 | `G5` | zero-escape → `Q3.RH` | **`READY`** логическое ядро доказано |

Живое состояние — не здесь, а в базе:

```bash
python3 docs/cartographer/brief.py     # что закрыто по цепочкам
python3 docs/cartographer/cheap.py     # что дешевле закрыть следующим
python3 orchestrator/kb_migrate_route058.py --check   # разошлась ли база с маршрутом
```

Таблица выше — снимок на 2026-08-12 и **протухнет**. База — источник истины.

---

## Что уже стоит в дереве под этот гол

**Ворота 2 — потребитель существует и доказан.**
`ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized`
(`CCMFiniteWeilParity.lean:161`) — внешняя обёртка: `hxiEven` выводит внутри, базис фактора
устраняется автоматикой (`probes/Probe_QuotientBasis_Auto.lean`). Ему нужен только пакет G1.

**Ворота 7 — логическое ядро доказано.** `rh_of_canonical_strip_slots`
(`CanonicalRHRouteSkeleton.lean:145`) выводит `Q3.RH` из одной фиксированной семьи;
`sameCofinalGuard` не даёт подставить независимую диагональ.

**Ворота 3 — доказаны.** `Proposition59GroundLagrangeZeroSetBridge`
(`Proposition59GroundLagrangeZeroSetBridge.lean:341`) переносит вещественность нулей
лагранжева многочлена той же строки на точное P59-преобразование. Доказательство
разбирает removable pole, exterior sine-lattice zero и off-lattice Cauchy/Lagrange
case, сохраняет координату `-L*z/(2*pi)` и завершает вызов буквального
`..._simple_normalized`. Direct Lean, target build и full build прошли; аксиомы только
`propext`, `Classical.choice`, `Quot.sound`.

**Ворота 1 — шесть поставщиков-кандидатов**, ни один не доведён: penalty-сертификат ·
блочное расщепление чётности · GLOWER/Yoshida · Schur/Feshbach · ранг-инерция · внешняя
теорема.

---

## Scoped exclusions и conditional supplier ban

Эти записи относятся к разным epistemic классам и не создают общий запрет на
поиск более слабого consumer-sufficient интерфейса.

```yaml
dependencies:
  - original_requested_object: PSTAR_EQUALS_SCALAR_TIMES_SOURCE_LAGRANGE_POLYNOMIAL
    downstream_consumer: PROPOSITION59_SAME_ROW_ZERO_SET_TRANSFER
    actual_consumer_requirement: EXACT_ZERO_SET_DECOMPOSITION_WITH_REAL_LATTICE_FACTOR
    original_object_is: NOT_NECESSARY
    known_weaker_interfaces: [ZERO_SET_UNION_WITH_REAL_LATTICE_FACTOR]
    consumer_implication: ZERO_SET_UNION_WITH_REAL_LATTICE_FACTOR => PROPOSITION59_SAME_ROW_ZERO_SET_TRANSFER
    failure_type: COUNTEREXAMPLE
    failure_scope: NONZERO_FINITE_POLYNOMIAL_VERSUS_INFINITE_SINE_LATTICE_ZERO_SET
    epistemic_status: MATHEMATICALLY_DEAD
    death_evidence:
      - kind: COUNTEREXAMPLE
        path: docs/routeB_bus/ROUTE058_GATE_CONTRACTS.md
        commit: fef398aa75d5ae37012e8a672f80ca5f7d0e5359
        git_blob: f30481486ad219a5c3c6454ee56a82fd214cf305
        scope: SCALAR_ONLY_FULL_TRANSFORM_EQUALITY_FOR_NONZERO_FINITE_SOURCE_POLYNOMIAL
        claim: FULL_TRANSFORM_HAS_INFINITELY_MANY_EXTERIOR_SINE_LATTICE_ZEROS_WHILE_NONZERO_FINITE_POLYNOMIAL_HAS_FINITELY_MANY
  - original_requested_object: EXACT_GROUND_EQUALS_TRIAL
    downstream_consumer: SAME_GROUND_FAMILY_TRACKS_PROJECTED_TRIAL
    actual_consumer_requirement: CONVERGENCE_OR_TRACKING_ON_THE_SAME_GROUND_FAMILY
    original_object_is: NOT_NECESSARY
    known_weaker_interfaces: [SAME_FAMILY_TRACKING_ESTIMATE]
    consumer_implication: SAME_FAMILY_TRACKING_ESTIMATE => GOAL058_G3
    failure_type: NO_DERIVATION
    failure_scope: EXACT_IDENTITY_ATTEMPT_OF_SECTION_8_7_UNSUPPORTED_BY_CURRENT_SOURCE_CONTRACT
    epistemic_status: RESEARCH_DEBT
    death_evidence: []
    reopen_triggers: [NEW_THEOREM, NEW_DERIVATION, COUNTEREXAMPLE]
  - original_requested_object: GLOWER_ARTIFACTS_AS_DIRECT_ODD_BLOCK_SUPPLIER
    downstream_consumer: LITERAL_SELECTED_ODD_COMPRESSION
    actual_consumer_requirement: FINITE_COMPRESSION_BRIDGE_IN_EXACT_COORDINATES
    original_object_is: UNKNOWN
    known_weaker_interfaces: [EXPLICIT_FINITE_COMPRESSION_BRIDGE]
    consumer_implication: EXPLICIT_FINITE_COMPRESSION_BRIDGE => LITERAL_SELECTED_ODD_COMPRESSION
    failure_type: NO_DERIVATION
    failure_scope: DIRECT_SUPPLIER_USE_WITHOUT_COMPRESSION_BRIDGE
    epistemic_status: RESEARCH_DEBT
```

**`Pstar = c_N · лагранжев многочлен`** — запись `PSTAR_C_N_UMNOZHIT_NA_LAGRANZHEV_MNOGOCHLEN`.
У преобразования Proposition-5.9 бесконечно много внешних нулей на синус-решётке, у ненулевого
конечного многочлена — конечное число; один скаляр их не сравняет. Верная структура — не
равенство, а разложение множества нулей:

```
Z(F_{m,N}) = Z(P_{m,N}) ∪ Z(Λ_{m,N})       Λ — вещественный решёточный множитель
```

**`exact ground equals trial`** — operationally killed как неподтверждённая и
необязательная exact-identity попытка, но математически не опровергнута, §8.7.
Живой consumer требует более слабую same-family tracking estimate.

**Артефакты GLOWER как поставщик odd-блока** — запрещено до явной леммы-моста конечной
компрессии (`GLOWER_ARTEFAKTY_NE_POSTAVSHCHIKI_ODD_BLOKA_BEZ_MOSTA_KOMPRE`).

---

## Закрытый дешёвый шаг G2b

Ворота `G2b`, теорема `Proposition59GroundLagrangeZeroSetBridge`:

> если `sourceLagrangePolynomial` строки `ξ` имеет только вещественные нули, то точное
> преобразование Proposition-5.9 **с той же строкой** — тоже.

Схема из маршрута, семь шагов:

```
1. z — устранимый включённый полюс        ⟹ z вещественный
2. вне конечных полюсов раскрыть:
     rawFplus(z) = scale · sin(Lz/2) · Σ_k ξ_k/(z + 2πk/L)
3. синус-множитель нулевой                ⟹ z на вещественной решётке
4. иначе нулевая сумма Коши
5. умножить на конечный знаменатель
6. получить  P(−Lz/2π) = 0
7. вещественная корневость P              ⟹ Im z = 0
```

Исполнено 2026-08-12 с кодом `P59_GROUND_LAGRANGE_ZEROSET_BRIDGE_PROVED`.
Следующий математический фронт этим файлом не выбирается: `G1` остаётся главным
спектральным gap, `G3` — главной стеной same-family tracking.

---

## Границы гола

Гол **не заявляет** RH, не заявляет закрытым ни одно из ворот `G0`, `G1`, `G3`, `G3c`, `G4`,
не поднимает численный сертификат ячейки в Lean и не занимает квантор `∀N` конечными
сертификатами. `PX_RH_CLAIM: NOT_MADE` действует, пока все восемь ворот не закрыты и не
проверены.
