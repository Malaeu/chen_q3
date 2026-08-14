---
status: "resolved"
date: "2026-08-14"
main_address: "Goal058.G3.CompactZeroSelection"
related_addresses: ["Goal058.G3", "Goal058.G3.Mode4"]
ancestor_addresses: ["Goal058.G3.Mode4FerrersSturmComparison"]
child_or_next_addresses: ["Goal058.G3.Mode4IndexSelection"]
raw_address_notation: "Goal058.G3.CompactZeroSelection, Goal058.G3, Goal058.G3.Mode4"
normalized_addresses: ["Goal058.G3.CompactZeroSelection", "Goal058.G3", "Goal058.G3.Mode4", "Goal058.G3.Mode4FerrersSturmComparison", "Goal058.G3.Mode4IndexSelection"]
address_status: "resolved_local"
blocker: "Закрыто локально: конечность множества простых нулей на компактном внутреннем отрезке и выбор соседней nodal-пары"
collections: ["q3_docs"]
tags: ["Goal058", "G3"]
insight_links: []
request_nodes: ["docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"]
strong_terms: ["interior_zero_simple", "HasDerivAt.eventually_ne", "IsCompact.finite", "Finset.min'", "exists_mode4Ferrers_zero_between_of_lt_Lambda_between_lower_zeros"]
empty_terms: ["ready project compact zero supplier", "ready consecutive-zero selector"]
false_friend_terms: []
opens_new_branch_terms: ["consecutive nodal pair"]
neighbor_addresses: []
---

# Goal058.G3.CompactZeroSelection — Конечность множества простых нулей на компактном внутреннем отрезке и выбор соседней nodal-пары

## Статус

- карточка разрешена локально;
- четыре последовательных `q3_docs` запроса выполнены;
- exact supplier теперь kernel checked в
  `D0Mode4FerrersCompactZeroSelection.lean`.

## Точный блокер

Закрыто локально.  `interior_zero_simple` вместе с
`HasDerivAt.eventually_ne` изолирует каждый ноль, `IsCompact.finite` даёт
конечность compact zero set, а `Finset.min'` выбирает первую правую nodal
точку.

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`Goal058.G3.CompactZeroSelection`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- `Mode4FerrersRegularEvenProlateSolution.interior_zero_simple` доказывает
  ненулевую производную в любом interior zero;
- `exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval` даёт
  Sturm comparison при supplied zero-free interval;
- готового project theorem о finite compact zero set или consecutive pair до
  этой карточки не было.

## Что именно мы хотим узнать поиском

- найти готовый project supplier конечности простых нулей;
- найти Mathlib primitive, превращающий nonzero derivative в isolated zero;
- найти compact-discrete-to-finite bridge;
- выбрать точную finite-order конструкцию consecutive right zero.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `simple zeros compact interval finite zero set derivative nonzero` | `Goal058.G3.CompactZeroSelection` | найти готовый supplier | project capability | partial | найден `interior_zero_simple`, exact compact supplier отсутствовал |
| `HasDerivAt nonzero derivative isolated zero Mathlib` | `Goal058.G3.CompactZeroSelection` | локальная изоляция | calculus primitive | decisive | `HasDerivAt.eventually_ne` |
| `compact discrete subset finite real interval` | `Goal058.G3.CompactZeroSelection` | global finiteness on `Icc` | topology primitive | decisive | `IsCompact.finite` плюс closed restricted zero set |
| `consecutive zeros finite interval Sturm comparison` | `Goal058.G3.CompactZeroSelection` | снять `hNodal` binder | finite order selection | local assembly | `Finite.toFinset`, filter, `Finset.min'` |

## Пустые / шумовые слова

- готовый project `compact zero set finite` supplier — нет exact hit;
- готовый project `consecutive zero selector` — нет exact hit;
- общие слова `Sturm zeros compact` возвращали текущий comparison node и
  несвязанные документы, но не новый theorem.

## Новые возможные комбинации слов

- `HasDerivAt.eventually_ne IsCompact.finite`;
- `interior_zero_simple Finset.min' nodal interval`;
- `compact discrete restricted zero set`.

## Переход в INSIGHTS

- reusable branch decision recorded in `docs/Progress_Log.md` under
  `Goal 058: compact zero selection снимает nodal guard`.

## Следующий адресный шаг

- `Goal058.G3.Mode4IndexSelection`: source-faithful ordered oscillation and
  degree/index `4` identification.
