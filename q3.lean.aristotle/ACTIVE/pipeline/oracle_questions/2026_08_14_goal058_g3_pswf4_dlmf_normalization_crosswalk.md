---
status: "resolved"
date: "2026-08-14"
main_address: "Goal058.G3.Mode4SourceCrosswalk"
related_addresses: ["Goal058.G3", "Goal058.G3.Mode4IndexSelection"]
ancestor_addresses: ["Goal058.G3.Mode4PhysicalScale"]
child_or_next_addresses: ["Goal058.G3.ClassicalPSWF4CoefficientSource"]
raw_address_notation: "Goal058.G3.Mode4SourceCrosswalk, Goal058.G3, Goal058.G3.Mode4IndexSelection"
normalized_addresses: ["Goal058.G3.Mode4SourceCrosswalk", "Goal058.G3", "Goal058.G3.Mode4IndexSelection", "Goal058.G3.Mode4PhysicalScale", "Goal058.G3.ClassicalPSWF4CoefficientSource"]
address_status: "resolved_local_normalization_only"
blocker: "DLMF degree-four coefficient normalization did not literally match the current unit-weighted tail receiver"
collections: ["q3_docs", "math_papers"]
tags: ["Goal058", "G3", "PSWF4", "DLMF"]
insight_links: []
request_nodes: ["docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"]
strong_terms: ["DLMF 30.8.5", "degree four rescale three", "one ninth normalization", "mode4DLMF3085_degreeFour_rescale_three"]
empty_terms: ["ready degree-four rescaling theorem", "ready classical psi4 coefficient supplier"]
false_friend_terms: ["m = n = 0 specialization"]
opens_new_branch_terms: []
neighbor_addresses: ["Goal058.G3.Mode4IndexSelection"]
---

# Goal058.G3.Mode4SourceCrosswalk — DLMF degree-four normalization crosswalk

## Точный блокер

The current canonical-tail receiver expects

```text
sum_q a_q^2 / (4q+1) = 1.
```

For the classical DLMF degree-four row, `n = 4`, `m = 0`, and the reindexing
`q = k + 2` turn DLMF 30.8.5 into

```text
sum_q a_q^2 / (4q+1) = 1/9.
```

The exact compatible project row is therefore `q -> 3 * a_q`.

## Почему этот поиск нужен сейчас

The prepared Mythos attack explicitly asked whether the existing
`mode4DLMF3084_3085_shiftedHermitianTail_eq_c_mul_canonical` normalization
matched the classical degree-four row.  This had to be answered before using
that theorem as the source crosswalk.

## Что уже известно по этому адресу

- DLMF 30.8.1 gives the Ferrers expansion.
- DLMF 30.8.3--30.8.4 gives the coefficient recurrence.
- DLMF 30.8.5 gives the source normalization.
- The current Lean core identifies a recurrence row with unit weighted sum
  with the canonical square-summable tail, up to nonzero scale.

## Что именно мы хотим узнать поиском

- whether a degree-four-specific normalization bridge already exists;
- whether the current receiver's right-hand side `1` is source-faithful;
- the exact rescaling needed before reusing the current canonical-tail core;
- whether any ready classical `psi_4` coefficient supplier exists locally.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `DLMF 30.8.5 degree four rescale three normalization` | `Goal058.G3.Mode4SourceCrosswalk` | найти exact normalization bridge | theorem capability | partial | найден unit receiver, degree-four rescale отсутствовал |
| `PSWF4 Legendre coefficient normalization one ninth` | `Goal058.G3.Mode4SourceCrosswalk` | проверить source RHS | source indexing | decisive | DLMF `n=4,m=0`, reindex `q=k+2`, RHS `1/9` |
| `mode4DLMF3085 source row rescaling recurrence` | `Goal058.G3.Mode4SourceCrosswalk` | найти готовую scaling assembly | local Lean | negative | найден только anonymous unit receiver |
| `classical psi4 coefficients current minimal Hermitian tail` | `Goal058.G3.Mode4SourceCrosswalk` | проверить полный source supplier | object provenance | negative | готового classical `psi_4` supplier нет |

## Пустые / шумовые слова

- готовый theorem для degree-four `1/9 -> 1` rescaling отсутствовал;
- готовый classical `psi_4` coefficient-row constructor отсутствовал;
- прежняя фраза `m = n = 0 specialization` фиксировала правильный вес после
  переиндексации, но неверно описывала источник degree-four normalization.

## Новые возможные комбинации слов

- `DLMF 30.8.5 n=4 m=0 q=k+2`;
- `one ninth rescale three weighted coefficient row`;
- `degree-four raw row canonical minimal tail`.

## Переход в INSIGHTS

The reusable fact is local and is recorded directly beside the Lean source:
degree-four raw DLMF coefficients must be multiplied by `3` before invoking
the current unit-normalized canonical-tail receiver.

## Следующий адресный шаг

`Goal058.G3.ClassicalPSWF4CoefficientSource`: construct or import the actual
indexed `psi_4` coefficient row and discharge the reindexed 30.8.4 recurrence
without assuming the desired current root or function identity.
