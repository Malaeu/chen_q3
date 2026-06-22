---
status: "resolved_constant_fail"
date: "2026-06-22"
main_address: "Step33A.1-A.rows01234567891011.product_budget_final_comparison"
related_addresses: ["Step33A.1-A.ShapeSqDeriv.rows01234567891011.product_bridge"]
ancestor_addresses: ["Step33A.1-A.ShapeSqDeriv.rows01234567891011.product_bridge"]
child_or_next_addresses: ["Step33A.1-A.product_source_sharpening_after_rows01234567891011_constant_fail"]
raw_address_notation: "Step33A.1-A / rows 0..11 product budget final comparison"
normalized_addresses: ["Step33A.1-A / rows 0..11 product budget final comparison", "Step33A.1-A.rows01234567891011.product_budget_final_comparison", "Step33A.1-A.ShapeSqDeriv.rows01234567891011.product_bridge"]
address_status: "resolved_constant_fail"
blocker: "Resolved: Lean proves the current row11 product assembly budget is too wide"
collections: ["q3_docs"]
tags: ["step33", "product-budget", "final-comparison", "row11"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md"]
strong_terms: ["Rows01234567891011ProductAssemblyErrorBudget", "product budget final comparison", "generated coefficient unfold", "integratedTaylorCoeff", "omegaPrimeGeneratedCoeff"]
empty_terms: []
false_friend_terms: ["row11 product bridge as finalBudgetPassed", "local width_pass as full product budget pass"]
opens_new_branch_terms: []
neighbor_addresses: []
---

# Step33A.1-A.rows01234567891011.product_budget_final_comparison — constant fail for row11 product budget

## Статус

- resolved constant-fail card;
- row11 source is checked;
- row11 product/P45 enclosure bridge is checked;
- final budget comparison is checked false for the current product source class.

## Точный блокер

Lean fail certificate now exists for:

```lean
((1866608532757 : Real) / 500000000000000000000000000000 -
    (-(94119513411 : Real) / 500000000000000000000000000000)) <
  2 * primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget
```

The checked theorem is
`primaryFiniteRow0Parent0Split100Sub0_rows01234567891011ProductAssemblyErrorBudget_width_fail`.

## Почему этот поиск нужен сейчас

The row11 product bridge is a proof object.  The exact constant comparison now
shows that the current product source class cannot feed the final residual
interval receiver.

## Что уже известно по этому адресу

- Checked enclosure:
  `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_rows01234567891011_enclosure`.
- Budget to compare:
  `primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget`.
- Arithmetic certificate:
  `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorRows01234567891011BudgetArithmetic.lean`.
- Checked witness:
  `NominalScaleAbsBound * OmegaTaylorRemainderAbs * ShapeSqDerivNominalAbsBudget`
  is already too wide.

## Что именно мы хотим узнать поиском

- next source class that reduces the witness term;
- whether the Omega Taylor remainder can be sharpened;
- whether the product-error decomposition can avoid multiplying the Omega
  remainder by the full ShapeSqDeriv nominal abs budget.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `Rows01234567891011ProductAssemblyErrorBudget final comparison` | `Step33A.1-A.rows01234567891011.product_budget_final_comparison` | find comparison truth value | budget theorem | constant fail | Lean width_fail checked |
| `omegaPrimeGeneratedCoeff integratedTaylorCoeff nominal abs budget norm_num` | `Step33A.1-A.rows01234567891011.product_budget_final_comparison` | unfold coefficient budgets | coeff unfold | superseded | Rat split avoided monolithic unfold |
| `ShapeSqDerivTaylorCenter_generated abs budget closed rational` | `Step33A.1-A.rows01234567891011.product_budget_final_comparison` | close shape derivative nominal abs term | generated coeff | resolved | witness theorem uses this nominal abs budget |

## Пустые / шумовые слова

- `width_pass finalBudgetPassed`.
- `product bridge closure final comparison`.

## Новые возможные комбинации слов

- `generated coeff closed rational abs budget`.
- `row11 product budget width fail`.
- `row11 product budget final receiver`.

## Переход в INSIGHTS

- `docs/INSIGHTS.md` entries:
  `Rows01234567891011ProductBridgeCheckedFinalComparisonGap`;
  `Rows01234567891011ProductBudgetConstantFail`.

## Следующий адресный шаг

- Do not retry the same final comparison under the current source class.
- Move to
  `STEP33_A1_SUB0_PRODUCT_SOURCE_SHARPENING_AFTER_ROWS01234567891011_CONSTANT_FAIL`.
- Target the witness term
  `OmegaTaylorRemainderAbs * ShapeSqDerivNominalAbsBudget`.
