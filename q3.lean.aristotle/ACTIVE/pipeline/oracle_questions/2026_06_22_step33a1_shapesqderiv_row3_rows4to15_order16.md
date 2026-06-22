---
status: "resolved_local_partial"
date: "2026-06-22"
main_address: "Step33A.1-A.ShapeSqDeriv.rows3to15_order16"
related_addresses: []
ancestor_addresses: ["Step33A.1-A.ShapeSqDeriv.rows2to15"]
child_or_next_addresses: ["Step33A.1-A.ShapeSqDeriv.rows4to15_order16"]
raw_address_notation: "Step33A.1-A / ShapeSqDeriv row 3 then rows 4..15 + order16"
normalized_addresses: ["Step33A.1-A / ShapeSqDeriv row 3 then rows 4..15 + order16", "Step33A.1-A.ShapeSqDeriv.rows3to15_order16", "Step33A.1-A.ShapeSqDeriv.rows2to15", "Step33A.1-A.ShapeSqDeriv.rows4to15_order16"]
address_status: "superseded_by_child"
blocker: "Sharp ShapeSqDeriv center row 3 and remaining rows 4..15 plus order16 source in singleAbs normalization"
collections: ["q3_docs"]
tags: ["step33", "shapesqderiv", "row3"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md"]
strong_terms: ["ShapeSqDeriv row3 coarseSmall", "CoarseTwoShapeProductSum_eq n=4", "shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ"]
empty_terms: []
false_friend_terms: ["global order17 constant"]
opens_new_branch_terms: []
neighbor_addresses: []
---

# Step33A.1-A.ShapeSqDeriv.rows3to15_order16 — Sharp ShapeSqDeriv center row 3 and remaining rows 4..15 plus order16 source in singleAbs normalization

## Статус

- q3_docs серия отработана;
- готового row-3 theorem-packet не найдено;
- row `3` закрыт локальным Lean-патчем;
- следующий адрес: `Step33A.1-A.ShapeSqDeriv.rows4to15_order16`.

## Точный блокер

Sharp ShapeSqDeriv center row 3 and remaining rows 4..15 plus order16 source in singleAbs normalization

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`Step33A.1-A.ShapeSqDeriv.rows3to15_order16`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- rows `0,1,2` уже были spendable через
  `PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012Payload.lean`;
- локально доступные поверхности:
  `primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`;
- row `3` закрыт тем же механизмом: exact product order `n = 4`, division by
  `3!`.

## Что именно мы хотим узнать поиском

- есть ли готовая row-3 формулировка в q3_docs;
- можно ли переиспользовать row2-механизм без нового receiver;
- какой точный child-address остаётся после row3.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `Step33A.1-A ShapeSqDeriv row3 rows 4..15 order16 singleAbs` | `Step33A.1-A.ShapeSqDeriv.rows3to15_order16` | найти готовую row3/source запись | адресная формулировка | noisy | готового theorem-packet нет |
| `primaryFiniteRow0Parent0Split100Sub0 shapeSqDeriv row3 coeffErrorAbs productSum n=4` | `Step33A.1-A.ShapeSqDeriv.rows3to15_order16` | найти точные локальные имена row3/product | имя + нормировка | weak local signal | подтвердил rows012-шаблон |
| `CoarseTwoShapeProductSum_eq n=4 shapeSq_derivative_abs_of_shape_derivative_abs row3` | `Step33A.1-A.ShapeSqDeriv.rows3to15_order16` | проверить product-order механизм | receiver-surface | local usable surface | row3 закрыт через existing Lean surfaces |

## Пустые / шумовые слова

- `row3` само по себе шумит;
- `ShapeSqDeriv rows 4..15` без `singleAbs` и `productSum` уводит в общие
  Step33 notes;
- `global order17 constant` остаётся false friend для этого шага.

## Новые возможные комбинации слов

- `ShapeSqDeriv row4 productSum n=5 factorial 4`
- `ShapeSqDeriv rows4to15 order16 singleAbs`
- `CoarseTwoShapeProductSum_eq 5 shapeSqDeriv centerJet4`

## Переход в INSIGHTS

- `ShapeSqDerivRows0123CheckedRows4To15Gap` в
  `q3.lean.aristotle/docs/INSIGHTS.md`.

## Следующий адресный шаг

- `Step33A.1-A.ShapeSqDeriv.rows4to15_order16`

## Локальный outcome

Added Lean file:

```lean
Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows0123Payload.lean
```

Checked:

```lean
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123Coeff_eq_generated
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet3_coarseSmall_abs
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123_valid
primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows0123TaylorSource
primaryFiniteRow0Parent0Split100Sub0_rows0123ShapeSqDerivRows4To15_width_fail
```

New failure code:

```text
STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_4_TO_15_ORDER16_SHARP_SOURCE_GAP
```
