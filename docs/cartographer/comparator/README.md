# Comparator-lite: проверка «доказано ли ЗАЯВЛЕННОЕ»

## Зачем это существует

Весь день 12 августа ушёл на один класс ошибки: **имя разрешается, теорема доказывает
другое**. Убитый alias `hermfact1` — имя без адреса. Шесть строк карты CvS — адреса верны,
утверждения не те. Обе ошибки прошли бы любую проверку на существование.

Отличает такие случаи только проверка типов. Этот каталог её и ставит.

## Устройство — заимствованный шаблон, не свой

Взято у Anthropic (`zeta-23-lean/comparator`, Apache-2.0), которые упаковали свои теоремы
под `leanprover/comparator` от Lean FRO. Заимствован **шаблон** «доверенный вызов против
недоверенного решения», не код.

| файл | роль | доверять? |
|---|---|---|
| `Challenge.lean` | ЧТО заявлено. Формулировка, доказательство `sorry` | да — читать его |
| `Solution.lean` | положительная закладка: то же через настоящего поставщика | нет |
| `SolutionR6.lean` | отрицательная закладка: ОБЯЗАНА не собраться | нет |
| `PrintAxioms.lean` | быстрая проверка ядром | — |

`Challenge.lean` импортирует **только** `MuntzV3.Core`. Настоящего поставщика
`RplusExactClass` он не видит: иначе решение сослалось бы на него мимо проверки, и вызов
перестал бы быть вызовом.

## Пилот

Цель — уже закрытая теорема
`EStarMuntzZeroMassContinuation.rplus_analyticOnNhd_shiftedHalfPlane_v3Class`,
`q3.lean.aristotle/Q3/Proofs/RouteB/MuntzV3/RplusExactClass.lean:16`.

Отрицательная закладка — обёртка R6 из
`docs/routeB_bus/muntz_v3/RequestProject/MuntzV3R6HrpWrapper.lean:9`. У неё **то же имя,
тот же вывод**, и поиск по имени, по головным символам или по пересечению атомов выдал бы
её первым кандидатом. Она негодна, потому что требует более сильных посылок:

| цель v3 | обёртка R6 |
|---|---|
| носитель в `Icc 0 b` | носитель в `Icc a b` при `0 < a` |
| `LipschitzOnWith K h (Ico 0 b)` | глобальная `LipschitzWith K h` |
| `Measurable h` | липшицевость сильнее |

## Результат прогона 2026-08-12

Дерево: `rh_clean`, все 204 модуля RouteB собраны, олеанов 204/204.

```
1. Challenge  элаборируется, единственное сообщение — ожидаемый sorry     PASS
2. Solution   закрывает цель, аксиомы [propext, Classical.choice,
              Quot.sound], код возврата 0                                 PASS
3. SolutionR6 отказ, код возврата 1                                       PASS
```

Причина отказа R6, дословно из Lean:

```
Application type mismatch: The argument
  hlip
has type
  LipschitzOnWith K h (Ico 0 b)
but is expected to have type
  LipschitzWith K h
```

плюс недоказуемая цель `⊢ False` — попытка вывести `0 < a` при `a = 0`.

Классификация: `STRONGER_CLASS_REQUIRES_UNAVAILABLE_HYPOTHESES`.

**Условие смерти пробы не наступило.** Если бы обёртка R6 прошла как закрытие цели v3,
семантический слой конструктора был бы мёртв и расширять его было бы нельзя.

## Как прогнать заново

Модули лежат вне дерева Lean, поэтому прогоняются копиями в корне `q3.lean.aristotle`,
без правки `lakefile.toml`:

```bash
cd q3.lean.aristotle
cp ../docs/cartographer/comparator/Challenge.lean   CmpChallenge.lean
sed 's|^import Solution$||' ../docs/cartographer/comparator/Solution.lean > CmpSolution.lean
printf '\n#print axioms Q3Challenge.rplus_analyticOnNhd_shiftedHalfPlane_v3Class\n' >> CmpSolution.lean
cp ../docs/cartographer/comparator/SolutionR6.lean  CmpSolutionR6.lean

lake env lean CmpChallenge.lean     # ожидается: только warning про sorry
lake env lean CmpSolution.lean      # ожидается: строка axioms, код 0
lake env lean CmpSolutionR6.lean    # ожидается: ОШИБКА, код 1

rm -f CmpChallenge.lean CmpSolution.lean CmpSolutionR6.lean
```

## Чего здесь НЕТ

**Это не полный `leanprover/comparator`.** Нет формальной сверки констант двух модулей,
нет второго ядра `nanoda`, нет песочницы. Полный прогон требует `elan`, `landrun` и
`lean4export`, собранный под наш `leanprover/lean4:v4.26.0`; у Anthropic toolchain
`v4.33.0-rc2`, и их README предупреждает, что comparator берёт toolchain проекта.

**Нет шести проектных проверок**, которые вердикт судьи назвал обязательными сверх
comparator: тот же объект-источник, та же область действия, та же нормировка, то же
направление теоремы, отсутствие скрытой аксиомы, цель не ослаблена. Их нигде не существует,
и писать их придётся самим.

**Одна цель, не пятнадцать.** У Anthropic в `config.json` пятнадцать теорем. Здесь одна —
столько, сколько нужно, чтобы проверить сам механизм.
