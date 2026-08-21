# Codex audit 2026-08-21 — ten Linux-authored Route B nodes

## Scope

- Audit source commit: `b30b67472f7ec8273471e74b33ce6286e99eaa02`.
- Audited working-tree commit: `5b6bce8b5ab25a1567c2d6d00f008d10f229a6b6`.
- All ten audited Lean blobs match the source commit.
- No audited Lean source was modified.
- Route B remains `CHALLENGER / NOT_RH`; no promotion or RH claim is made.

## Per-file verdicts

G6N1SelectedFerrersPreAnchorDataInhabitant.lean  MECH: PASS  SEMANT: PASS  находки: текущий blob, gate и assembly step 25 согласованы; фактический Ferrers witness и `pair_spec` сохранены; `OPENS: []` честно.
G6N1SelectedFerrersPaperParameterDictionary.lean  MECH: PASS  SEMANT: PASS  находки: законы `n=2j`, `gamma=2*pi*lambda^2`, `gamma^2=mode4JacobiG`, `gamma=mode4SlepianC` совпадают с кодом, gate и assembly row 12; суррогата нет.
G6N1FuchsProjectOperatorIntertwining.lean  MECH: PASS  SEMANT: PASS  находки: множитель `sqrt(2*pi)` и замена `s=sqrt(2*pi)*y` верны; доказан только operator intertwining, eigenvalue crosswalk не заявлен; `OPENS: []` честно.
G6N1ParabolicCylinderD0D4Exact.lean  MECH: PASS  SEMANT: PASS  находки: Mathlib `Polynomial.hermite` использован в вероятностной конвенции без лишнего `2^(-n/2)`; разложение `explicitCCMLimitH=(1/16)D_4-(3/16)D_0` является точным кольцевым тождеством.
G6N1CenterAnchorScalarLock.lean  MECH: PASS  SEMANT: PASS  находки: `centerAnchorScalarZero/Four` определены до любого rate-утверждения как `1/f0(0)` и `3/f4(0)`; подгонки по ошибке и бумажного суррогата нет.
G6N1EvenCenterDerivative.lean  MECH: PASS  SEMANT: FAIL  находки: Lean-утверждения соответствуют W13.11, но отдельный `LINUX_GATE_*`-артефакт отсутствует; заявленную в задании сверку с gate выполнить невозможно.
G6N1CenterNormalizedUniquenessReceiver.lean  MECH: PASS  SEMANT: FAIL  находки: endpoint theorem требует глобальные `Continuous (centerNormalized f/g)`, тогда как REQ-K требует только `ContinuousOn f/g (Icc ...)`; на полке для Ferrers-мод есть только `physicalComplex_continuousOn_closed`; это скрытый более сильный вход, поэтому `OPENS: []` и закрытие endpoint extension завышены; отдельного gate-артефакта нет.
G6N1Satz9SourcePackageInterface.lean  MECH: PASS  SEMANT: FAIL  находки: исправление C10 корректно — структура является payload, не provenance firewall; однако оба пакета требуют глобальную `normalized_continuous : Continuous`, повторяя скрытый вход receiver; `OPENS: []` поэтому нечестно; отдельного gate-артефакта нет; assembly и session protocol содержат старую blob-квитанцию.
G6N1EvenSolutionCenterNonvanishing.lean  MECH: PASS  SEMANT: FAIL  находки: сама теорема верна, но докстринг называет `center_ne` следствием «остальных полей», тогда как theorem явно требует дополнительный `hnontrivial : ∃ x ∈ Ioo ..., p x ≠ 0`, которого нет в `Satz9SourceData`; paper eigenfunction должен отдельно поставить этот typed witness; отдельного gate-артефакта нет.
G6N1OrderedEnumerationLock.lean  MECH: PASS  SEMANT: FAIL  находки: строгая индукция корректна, `le_of_agree_below` применён симметрично, `hrange.symm.subset` даёт обратное включение; но докстринг утверждает, что файл идентифицирует project branch с book branch, хотя theorem только абстрактен и требует ещё не поставленное равенство low ranges — W13.7B и W13.7E остаются открыты; отдельного gate-артефакта нет.

## Mechanical verification

Для каждого файла выполнены:

```text
env -u LD_LIBRARY_PATH lake env lean Q3/Proofs/RouteB/<file>.lean
env -u LD_LIBRARY_PATH lake build Q3.Proofs.RouteB.<Module>
env -u LD_LIBRARY_PATH scripts/q3_check.sh Q3/Proofs/RouteB/<file>.lean
```

Результат: все 30 команд завершились с `EXIT 0`; все десять `q3_check` вернули `q3_check ok`.

Все печатаемые теоремы имеют профиль:

```text
[propext, Classical.choice, Quot.sound]
```

`selectedFerrersPaperDegree` не зависит ни от каких аксиом, что является допустимым строгим подмножеством и уже честно записано в его gate-артефакте. `sorryAx`, `sorry` и `admit` не обнаружены.

## Detailed semantic findings

### 1. Endpoint continuity contract drift

REQ-K задаёт receiver с:

```lean
hf_cont : ContinuousOn f (Icc (-lambda) lambda)
hg_cont : ContinuousOn g (Icc (-lambda) lambda)
```

Реализованный receiver вместо этого требует:

```lean
hfc : Continuous (centerNormalized f)
hgc : Continuous (centerNormalized g)
```

`Satz9SourceData` и `ProjectModeData` повторяют это усиление полями:

```lean
normalized_continuous : Continuous (centerNormalized ...)
```

Для выбранных Ferrers-мод на полке имеется только:

```lean
Mode4FerrersRegularEvenProlateSolution.physicalComplex_continuousOn_closed
```

с выводом `ContinuousOn ... Icc`. Производственная `normalizedPhysicalMode` является `Icc.indicator`-нуль-продолжением; глобальная непрерывность из существующих теорем не следует и может ломаться на концах при ненулевом endpoint value.

Следствие: open-window uniqueness доказана корректно, но endpoint extension и source bind пока закрыты только при скрытом усиленном предположении.

Предлагаемый код разрыва:

```text
F72_0B2_GLOBAL_NORMALIZED_CONTINUITY_CONTRACT_GAP
```

### 2. Nontriviality is not one of the other source fields

`center_ne_zero_of_even_of_nontrivial` корректно доказывает ненулевой центр из parity, ODE и явного interior nontriviality witness.

Но `Satz9SourceData` не содержит nontriviality. Нулевая функция удовлетворяет `hasDeriv`, `flux`, `even` и глобальной непрерывности нормированного вида в текущем Lean-смысле деления на ноль. Поэтому `center_ne` не является следствием остальных полей структуры.

Бумажное слово eigenfunction семантически означает ненулевую функцию, но будущий source-only supplier должен перенести это в typed Lean witness либо сразу доказать `center_ne`.

Предлагаемый код разрыва:

```text
SATZ9_SOURCE_NONTRIVIALITY_TYPED_PORT_GAP
```

### 3. Ordered-enumeration theorem does not itself identify branches

Проверены оба подозрительных места:

- первый вызов `le_of_agree_below` даёт `b j <= a j`;
- вызов со сменой аргументов и `hrange.symm.subset` даёт `a j <= b j`.

Доказательство корректно.

Однако theorem предполагает точное равенство:

```lean
range a ∩ Iio C = range b ∩ Iio C
```

Именно поставка этого равенства остаётся в W13.7B/W13.7E. Поэтому файл закрывает только generic ordered-enumeration lock, но не идентификацию project/book branches. Докстринг строки 25 и соответствующие внешние формулировки должны быть ослаблены.

### 4. Missing Linux gate artifacts

Для следующих пяти файлов отсутствуют любые соответствующие `docs/routeB_bus/LINUX_GATE_*.md`:

```text
G6N1EvenCenterDerivative.lean
G6N1CenterNormalizedUniquenessReceiver.lean
G6N1Satz9SourcePackageInterface.lean
G6N1EvenSolutionCenterNonvanishing.lean
G6N1OrderedEnumerationLock.lean
```

Их механический статус независимо перепроверен этим аудитом и зелёный. Находка относится к traceability: прежние заявления о gate нельзя сверить с отдельным неизменяемым артефактом и его SHA-256.

## Receipt discrepancies

Текущее дерево и source commit задания полностью совпадают по всем десяти Lean-файлам.

Одна устаревшая квитанция остаётся в `SESSION_PROTOKOLL_2026-08-21.md` и в `assembly` row 12:

```text
file: G6N1Satz9SourcePackageInterface.lean
stale blob: a7407963
stale full blob: a7407963...
stale SHA-256: 73dac3214e3dbde5d0d769dd7515acfd541da197ebf369cc4332ea89ba5e1dc1

audited blob: be80f839
audited full blob: be80f839c969397f7d8307bf517a525d99be24d1
audited SHA-256: 436d72bcb4ec62557534361ae745de7948b45cc3526d08f68f9acc12efeb9e90
```

Diff `a7407963 -> be80f839` меняет только докстринг: удаляет ложное утверждение, что имена полей обеспечивают provenance firewall, и записывает опровержение REQ-L. Теоремы и структуры байтово не менялись вне документации.

## C09, C10, units and normalization verdict

- Фактического бумажного объекта, определённого через project target, в десяти файлах нет.
- `Satz9SourceData` допускает суррогатное заселение как тип, но текущий докстринг это честно признаёт; фактического inhabitant здесь нет.
- `centerAnchorScalarZero/Four` определены по центрам до любого rate и не fitted по ошибке.
- Fuchs/project crosswalk использует правильный множитель `sqrt(2*pi)`.
- Parabolic-cylinder bridge использует probabilists' Hermite без лишнего `2^(-n/2)`.
- `explicitCCMLimitH=(1/16)D_4-(3/16)D_0` подтверждено независимо по коэффициентам `x^4`, `x^2` и константе.

## Current gate

До начала W13.7B требуется сначала решить найденный интерфейсный drift:

```text
ContinuousOn on Icc
versus
global Continuous of center-normalized zero extensions
```

После этого прежний несущий gate остаётся W13.7B: порт книжной исчерпывающести в project characteristic range. W13.7E и последующие rate assemblies остаются глубже. Route B не повышен и остаётся `CHALLENGER / NOT_RH`.
