# LINUX CORRECTION — GROUND-FAMILY PREFLIGHT: THE GAP WAS MISNAMED

```yaml
KIND: APPEND_ONLY_CORRECTION
CORRECTS: docs/routeB_bus/LINUX_SELECTED_FERRERS_GROUND_FAMILY_ROOF_PREFLIGHT_GOAL058_2026-08-26.md
CORRECTED_COMMIT: 7f748f1d
RETROACTIVE_EDIT_OF_ORIGINAL: false
ERROR_CLASS: FALSE_NEGATIVE_EXISTENCE_CLAIM
RULE_VIOLATED: ASK_THE_CATALOGUE_FIRST
WRONG_GAP_NAME: SELECTED_CCM_GROUND_LINE_ETA_NONVANISHING
CORRECTED_GAP_NAME: SELECTED_CCM_GROUND_ODD_SECTOR_STRICTLY_ABOVE
REALIFICATION_ARGUMENT_STATUS: UNCHANGED_AND_STILL_VALID
PROPOSED_HETA_HYPOTHESIS: WITHDRAWN
```

## Что было заявлено неверно

В §3 отчёта 7f748f1d я написал: «источника η-невырождения нет, нормировка
всюду является гипотезой, а не выводом». **Это ложь.** Я искал потребителей
`grep`-ом и не спросил каталог стыковок — прямое нарушение правила проекта
«Спроси полку первой». `./ask.sh` возвращает цепь сборки
`PSD_CERTIFICATE_FOR_CCM_CELL`, где шаг 12 «eta*xi != 0 (нормируемость)»
имеет статус READY и названного поставщика.

## Что есть на самом деле

Проверено чтением файла, не только каталогом
(`Q3/Proofs/RouteB/CCMFiniteWeilEtaNonzero.lean`):

| строка | теорема | вывод |
|---|---|---|
| 157 | `ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector` | из ненулевого ЧЁТНОГО простого вещественного собственного вектора ⟹ `ccmEtaFinite ⬝ᵥ ξ ≠ 0` |
| 188 | `exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector` | сразу даёт η-нормированного представителя |
| 42, 82 | вспомогательные (`modeDiag`, `shifted_kernel`) | — |

## Точная структура зависимости — это круг

- `ccmEigenvector_even_of_simple_eigenspace_and_normalized` требует
  `hnormalized : ccmEtaFinite ⬝ᵥ ξ = 1`, чтобы вывести ЧЁТНОСТЬ;
- `ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector` требует
  ЧЁТНОСТЬ, чтобы вывести `η ⬝ᵥ ξ ≠ 0`.

Ни одно направление не бесплатно. Коммутирование с инволюцией плюс простота
дают только дихотомию `J ξ = ±ξ` (доказана в
`SimpleEvenGroundSectorCriterion.lean` ~100), и зарегистрированный
контрпример `commute_simple_ground_does_not_force_even` охраняет ровно этот
шаг. Если грунтовая линия НЕЧЁТНАЯ, то `η ⬝ᵥ ξ = 0` тождественно (у
нечётного вектора нулевая сумма координат), и круг не замыкается нормировкой.

## Корректное имя щели

**`SELECTED_CCM_GROUND_ODD_SECTOR_STRICTLY_ABOVE`** — для литеральной
`ccmWeilMatFinite` на отобранном расписании каждый НЕЧЁТНЫЙ собственный
вектор имеет собственное значение СТРОГО больше дна чётного сектора.

Независимый потребитель этого входа уже существует:
`simpleEvenGround_of_sector_order` (SimpleEvenGroundSectorCriterion.lean:125)
выводит `IsSimpleEvenGround` из четырёх секторных входов, последний из
которых — `hoddStrict`.

## Что меняется в предложенном узле

Гипотеза-дизъюнкция `heta` из §6 отчёта 7f748f1d **отзывается**: форма
неверная. Честная гипотеза — строгость нечётного сектора (либо прямо
`IsSimpleEvenGround`), и при ней теорема реализации ЗАКРЫВАЕТ η-нормировку
внутри себя, а не принимает её.

Аргумент реализации из §2 отчёта (комплексный грунт → вещественный, через
вещественность `ccmWeilMatFinite` и простоту) остаётся в силе без изменений.

## Урок для всех пишущих тел

Отрицательное утверждение о существовании («поставщика нет») требует
`./ask.sh` с секцией СТЫКОВКИ, а не `grep` по потребителям. `grep` находит
использования, каталог находит поставщиков. Именно этот режим отказа правило
«Спроси полку первой» и предотвращает.
