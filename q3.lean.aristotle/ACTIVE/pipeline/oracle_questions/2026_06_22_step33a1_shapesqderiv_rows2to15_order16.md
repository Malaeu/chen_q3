---
status: "active"
date: "2026-06-22"
main_address: "Step33A.1-A.ShapeSqDeriv.rows2to15"
related_addresses: []
ancestor_addresses: ["Step33A.1-A"]
child_or_next_addresses: ["Step33A.1-A.ShapeSqDeriv.order16"]
raw_address_notation: "Step33A.1-A / ShapeSqDeriv rows 2..15 + order16"
normalized_addresses: ["Step33A.1-A / ShapeSqDeriv rows 2..15 + order16", "Step33A.1-A.ShapeSqDeriv.rows2to15", "Step33A.1-A", "Step33A.1-A.ShapeSqDeriv.order16"]
address_status: "active"
blocker: "Sharp ShapeSqDeriv center rows 2..15 and order16 source in singleAbs normalization"
collections: ["q3_docs"]
tags: ["step33", "shapesqderiv", "rows2to15"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md"]
strong_terms: ["ShapeSqDerivTaylorIntervalCert.singleAbs", "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff", "rows 2..15 order16"]
empty_terms: []
false_friend_terms: ["coarseTwo budget"]
opens_new_branch_terms: []
neighbor_addresses: []
---

# Step33A.1-A.ShapeSqDeriv.rows2to15 — Sharp ShapeSqDeriv center rows 2..15 and order16 source in singleAbs normalization

## Статус

- серия запросов отработана;
- локальный Lean patch закрыл row `2` через существующий coarse shape majorant
  at exact `n = 3`;
- адрес сужен: rows `0,1,2` больше не live-obstruction, текущий следующий
  адрес `Step33A.1-A.ShapeSqDeriv.rows3to15_order16`.

## Точный блокер

Sharp ShapeSqDeriv center rows 2..15 and order16 source in singleAbs normalization

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`Step33A.1-A.ShapeSqDeriv.rows2to15`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- rows `0,1` закрыты в
  `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpPayload.lean`;
- row `2` закрыт в
  `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012Payload.lean`;
- закрывающие theorem names:
  `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet2_coarseSmall_abs`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012_valid`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows012TaylorSource`;
- width-fail theorem:
  `primaryFiniteRow0Parent0Split100Sub0_rows012ShapeSqDerivRows3To15_width_fail`.

## Что именно мы хотим узнать поиском

- q3_docs не нашёл готового закрытого rows `2..15` theorem packet;
- рабочий локальный сигнал пришёл из `rg`, не из semantic hits:
  `primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq`,
  `primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs`,
  and
  `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `Step33A.1-A ShapeSqDeriv rows 2..15 order16 singleAbs centerJet` | `Step33A.1-A.ShapeSqDeriv.rows2to15` | найти готовый rows/order16 source | semantic exact blocker | noisy | no closure source |
| `primaryFiniteRow0Parent0Split100Sub0 shapeSqDeriv powerSeriesCoeff2 interval generated` | `Step33A.1-A.ShapeSqDeriv.rows2to15` | проверить готовую row2 interval lemma | exact generated name | noisy | no row2 theorem |
| `ShapeSqDeriv majorant receiver product Leibniz derivative bounds payload order16 row2` | `Step33A.1-A.ShapeSqDeriv.rows2to15` | найти reusable receiver | receiver vocabulary | noisy in q3_docs, useful via rg | use product-bound receiver |
| `shapeSqDeriv_centerJet_eq_powerSeriesCoeff coeff2 derivative formula iteratedDeriv 2` | `Step33A.1-A.ShapeSqDeriv.rows2to15` | найти centerJet/order-shift bridge | normalization | noisy in q3_docs, useful via rg | use public order-shift theorem |

## Пустые / шумовые слова

- `rows 2..15` as free text in q3_docs is too weak; it surfaces unrelated H/PO3
  notes unless paired with exact Lean theorem names.

## Новые возможные комбинации слов

- `CoarseTwoShapeProductSum_eq n=3`
- `shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`
- `ShapeSqDeriv row2 coarseSmall`

## Переход в INSIGHTS

- `docs/INSIGHTS.md`, section
  `ShapeSqDerivRows012CheckedRows3To15Gap`.

## Следующий адресный шаг

- `Step33A.1-A.ShapeSqDeriv.rows3to15_order16`: repeat the same pattern for
  row `3` using exact `n = 4`, unless a stronger shared generated payload for
  rows `3..15` appears.
