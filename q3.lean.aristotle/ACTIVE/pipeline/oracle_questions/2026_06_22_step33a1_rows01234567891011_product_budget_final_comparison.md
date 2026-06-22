---
status: "active"
date: "2026-06-22"
main_address: "Step33A.1-A.rows01234567891011.product_budget_final_comparison"
related_addresses: ["Step33A.1-A.ShapeSqDeriv.rows01234567891011.product_bridge"]
ancestor_addresses: ["Step33A.1-A.ShapeSqDeriv.rows01234567891011.product_bridge"]
child_or_next_addresses: []
raw_address_notation: "Step33A.1-A / rows 0..11 product budget final comparison"
normalized_addresses: ["Step33A.1-A / rows 0..11 product budget final comparison", "Step33A.1-A.rows01234567891011.product_budget_final_comparison", "Step33A.1-A.ShapeSqDeriv.rows01234567891011.product_bridge"]
address_status: "active"
blocker: "Prove or fail the final target-width comparison for the row11 product assembly budget"
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

# Step33A.1-A.rows01234567891011.product_budget_final_comparison — final comparison for row11 product budget

## Статус

- active card;
- row11 source is checked;
- row11 product/P45 enclosure bridge is checked;
- final budget comparison is not checked.

## Точный блокер

Need a Lean proof or fail certificate for:

```lean
2 * primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget <=
  ((1866608532757 : Real) / 500000000000000000000000000000 -
    (-(94119513411 : Real) / 500000000000000000000000000000))
```

or the reverse strict inequality if the row11 product budget is still too wide.

## Почему этот поиск нужен сейчас

The row11 product bridge is now a proof object.  The remaining question is not
source compatibility; it is the exact constant comparison needed by the final
residual interval receiver.

## Что уже известно по этому адресу

- Checked enclosure:
  `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_rows01234567891011_enclosure`.
- Budget to compare:
  `primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget`.
- A direct `norm_num` attempt did not close because generated/integrated
  coefficient abs-budget surfaces remained partly opaque.

## Что именно мы хотим узнать поиском

- whether existing coeff unfold lemmas already expose closed rationals for the
  nominal abs budgets;
- whether a small generated rational certificate should replace direct
  unfolding;
- whether the comparison is true or should become a checked width-fail.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `Rows01234567891011ProductAssemblyErrorBudget final comparison` | `Step33A.1-A.rows01234567891011.product_budget_final_comparison` | find existing comparison surface | budget theorem | pending | TODO |
| `omegaPrimeGeneratedCoeff integratedTaylorCoeff nominal abs budget norm_num` | `Step33A.1-A.rows01234567891011.product_budget_final_comparison` | unfold coefficient budgets | coeff unfold | pending | TODO |
| `ShapeSqDerivTaylorCenter_generated abs budget closed rational` | `Step33A.1-A.rows01234567891011.product_budget_final_comparison` | close shape derivative nominal abs term | generated coeff | pending | TODO |

## Пустые / шумовые слова

- `width_pass finalBudgetPassed`.
- `product bridge closure final comparison`.

## Новые возможные комбинации слов

- `generated coeff closed rational abs budget`.
- `row11 product budget width fail`.
- `row11 product budget final receiver`.

## Переход в INSIGHTS

- `docs/INSIGHTS.md` entry:
  `Rows01234567891011ProductBridgeCheckedFinalComparisonGap`.

## Следующий адресный шаг

- Build the exact final comparison certificate for the row11 product budget.
- If direct unfold remains too opaque, create a small rational budget lemma for
  the nominal abs budgets, then retry the final comparison.
