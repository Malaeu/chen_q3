---
status: "resolved_local_partial"
date: "2026-06-22"
main_address: "Step33A.1-A.ShapeSqDeriv.rows9to15_order16"
related_addresses: []
ancestor_addresses: ["Step33A.1-A.ShapeSqDeriv.rows8to15_order16"]
child_or_next_addresses: ["Step33A.1-A.ShapeSqDeriv.rows10to15_order16"]
raw_address_notation: "Step33A.1-A / ShapeSqDeriv row 9 then rows 10..15 + order16"
normalized_addresses: ["Step33A.1-A / ShapeSqDeriv row 9 then rows 10..15 + order16", "Step33A.1-A.ShapeSqDeriv.rows9to15_order16", "Step33A.1-A.ShapeSqDeriv.rows8to15_order16", "Step33A.1-A.ShapeSqDeriv.rows10to15_order16"]
address_status: "superseded_by_child"
blocker: "Sharp ShapeSqDeriv center row 9 and remaining rows 10..15 plus order16 source in singleAbs normalization"
collections: ["q3_docs"]
tags: ["step33", "shapesqderiv", "row9"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md"]
strong_terms: ["ShapeSqDeriv row9 coarseSmall", "CoarseTwoShapeProductSum_eq n=10", "shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ"]
empty_terms: []
false_friend_terms: ["global order17 constant"]
opens_new_branch_terms: []
neighbor_addresses: []
---

# Step33A.1-A.ShapeSqDeriv.rows9to15_order16 — Sharp ShapeSqDeriv center row 9 and remaining rows 10..15 plus order16 source in singleAbs normalization

## Статус

- серия запросов отработана локально;
- готового row-9 theorem в `q3_docs` не найдено;
- row `9` закрыт новым Lean payload;
- активный дочерний адрес: `Step33A.1-A.ShapeSqDeriv.rows10to15_order16`.

## Точный блокер

Sharp ShapeSqDeriv center row 9 and remaining rows 10..15 plus order16 source in singleAbs normalization

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`Step33A.1-A.ShapeSqDeriv.rows9to15_order16`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- row `9` доказан в том же `ShapeSqDerivTaylorIntervalCert.singleAbs`
  соглашении, что и rows `0..8`;
- используемые локальные surfaces:
  `primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`;
- новый payload:
  `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows0123456789Payload.lean`.

## Что именно мы хотим узнать поиском

- результат: готового external/local-doc theorem для row `9` не найдено;
- local proof route был достаточен: product-order sharpening at `n = 10`,
  divided by `9!`;
- следующий живой адрес теперь row `10`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `Step33A.1-A ShapeSqDeriv row9 rows 10..15 order16 singleAbs` | `Step33A.1-A.ShapeSqDeriv.rows9to15_order16` | Find existing row-9 singleAbs closure | row index | noisy/no ready theorem | local Lean proof used |
| `primaryFiniteRow0Parent0Split100Sub0 shapeSqDeriv row9 coeffErrorAbs productSum n=10` | `Step33A.1-A.ShapeSqDeriv.rows9to15_order16` | Find exact product-order payload | product order | noisy/no ready theorem | existing product-sum surface reused |
| `CoarseTwoShapeProductSum_eq n=10 shapeSq_derivative_abs_of_shape_derivative_abs row9` | `Step33A.1-A.ShapeSqDeriv.rows9to15_order16` | Check theorem surface names | Lean surface | usable local names | row9 payload written |

## Пустые / шумовые слова

- `global order17 constant` remains a false friend: it is proof-grade but too
  coarse for this narrowing.

## Новые возможные комбинации слов

- `ShapeSqDeriv row10 coarseSmall`
- `CoarseTwoShapeProductSum_eq n=11`
- `shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`

## Переход в INSIGHTS

- `docs/INSIGHTS.md`: `ShapeSqDerivRows0123456789CheckedRows10To15Gap`.

## Следующий адресный шаг

- Continue at
  `ACTIVE/pipeline/oracle_questions/2026_06_22_step33a1_shapesqderiv_row10_rows11to15_order16.md`.

## Локально проверенные Lean theorem names

```lean
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123456789Coeff_eq_generated
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet9_coarseSmall_abs
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123456789_valid
primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows0123456789TaylorSource
primaryFiniteRow0Parent0Split100Sub0_rows0123456789ShapeSqDerivRows10To15_width_fail
```

## Решение

`Step33A.1-A.ShapeSqDeriv.rows9to15_order16` is resolved as a local partial
closure.  It does not close Step33A.1-A.  The new exact live failure is:

```text
STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_10_TO_15_ORDER16_SHARP_SOURCE_GAP
```
