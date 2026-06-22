---
status: "resolved_local_partial"
date: "2026-06-22"
main_address: "Step33A.1-A.ShapeSqDeriv.rows5to15_order16"
related_addresses: []
ancestor_addresses: ["Step33A.1-A.ShapeSqDeriv.rows4to15_order16"]
child_or_next_addresses: ["Step33A.1-A.ShapeSqDeriv.rows6to15_order16"]
raw_address_notation: "Step33A.1-A / ShapeSqDeriv row 5 then rows 6..15 + order16"
normalized_addresses: ["Step33A.1-A / ShapeSqDeriv row 5 then rows 6..15 + order16", "Step33A.1-A.ShapeSqDeriv.rows5to15_order16", "Step33A.1-A.ShapeSqDeriv.rows4to15_order16", "Step33A.1-A.ShapeSqDeriv.rows6to15_order16"]
address_status: "superseded_by_child"
blocker: "Sharp ShapeSqDeriv center row 5 and remaining rows 6..15 plus order16 source in singleAbs normalization"
collections: ["q3_docs"]
tags: ["step33", "shapesqderiv", "row5"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md"]
strong_terms: ["ShapeSqDeriv row5 coarseSmall", "CoarseTwoShapeProductSum_eq n=6", "shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ"]
empty_terms: []
false_friend_terms: ["global order17 constant"]
opens_new_branch_terms: []
neighbor_addresses: []
---

# Step33A.1-A.ShapeSqDeriv.rows5to15_order16 — Sharp ShapeSqDeriv center row 5 and remaining rows 6..15 plus order16 source in singleAbs normalization

## Статус

- q3_docs серия отработана;
- готового row-5 theorem-packet не найдено;
- row `5` закрыт локальным Lean-патчем;
- следующий адрес: `Step33A.1-A.ShapeSqDeriv.rows6to15_order16`.

## Точный блокер

Sharp ShapeSqDeriv center row 5 and remaining rows 6..15 plus order16 source in singleAbs normalization

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`Step33A.1-A.ShapeSqDeriv.rows5to15_order16`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- rows `0,1,2,3,4` уже были spendable через
  `PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows01234Payload.lean`;
- локально доступные поверхности:
  `primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`;
- generated coefficient stream is zero after row `0`, so row `5` reduces to a
  normalized derivative majorant;
- row `5` закрыт тем же механизмом: exact product order `n = 6`, division by
  `5!`.

## Что именно мы хотим узнать поиском

- есть ли готовая row-5 формулировка в q3_docs;
- можно ли переиспользовать row4-механизм без нового receiver;
- какой точный child-address остаётся после row5.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `Step33A.1-A ShapeSqDeriv row5 rows 6..15 order16 singleAbs` | `Step33A.1-A.ShapeSqDeriv.rows5to15_order16` | найти готовую row5/source запись | адресная формулировка | noisy | готового theorem-packet нет |
| `primaryFiniteRow0Parent0Split100Sub0 shapeSqDeriv row5 coeffErrorAbs productSum n=6` | `Step33A.1-A.ShapeSqDeriv.rows5to15_order16` | найти точные локальные имена row5/product | имя + нормировка | weak local signal | подтвердил rows01234-шаблон |
| `CoarseTwoShapeProductSum_eq n=6 shapeSq_derivative_abs_of_shape_derivative_abs row5` | `Step33A.1-A.ShapeSqDeriv.rows5to15_order16` | проверить product-order механизм | receiver-surface | local usable surface | row5 закрыт через existing Lean surfaces |

## Пустые / шумовые слова

- `row5` само по себе шумит;
- `ShapeSqDeriv rows 6..15` без `singleAbs` и `productSum` уводит в общие
  Step33/H1 notes;
- `global order17 constant` остаётся false friend для этого шага.

## Новые возможные комбинации слов

- `ShapeSqDeriv row6 productSum n=7 factorial 6`
- `ShapeSqDeriv rows6to15 order16 singleAbs`
- `CoarseTwoShapeProductSum_eq 7 shapeSqDeriv centerJet6`

## Переход в INSIGHTS

- `ShapeSqDerivRows012345CheckedRows6To15Gap` в
  `q3.lean.aristotle/docs/INSIGHTS.md`.

## Следующий адресный шаг

- `Step33A.1-A.ShapeSqDeriv.rows6to15_order16`

## Локальный outcome

Added Lean file:

```lean
Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012345Payload.lean
```

Checked:

```lean
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345Coeff_eq_generated
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet5_coarseSmall_abs
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345_valid
primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows012345TaylorSource
primaryFiniteRow0Parent0Split100Sub0_rows012345ShapeSqDerivRows6To15_width_fail
```

New failure code:

```text
STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_6_TO_15_ORDER16_SHARP_SOURCE_GAP
```
