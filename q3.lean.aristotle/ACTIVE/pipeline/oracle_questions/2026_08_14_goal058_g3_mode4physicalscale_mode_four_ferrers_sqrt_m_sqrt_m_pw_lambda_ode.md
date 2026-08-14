---
status: "resolved"
date: "2026-08-14"
main_address: "Goal058.G3.Mode4PhysicalScale"
related_addresses: []
ancestor_addresses: ["Goal058.G3.Mode4"]
child_or_next_addresses: ["Goal058.G3.Mode4SourceCrosswalk"]
raw_address_notation: "Goal058.G3.Mode4PhysicalScale"
normalized_addresses: ["Goal058.G3.Mode4PhysicalScale", "Goal058.G3.Mode4", "Goal058.G3.Mode4SourceCrosswalk"]
address_status: "resolved_local"
blocker: "Закрыто локально: физическое масштабирование принятого mode-four Ferrers решения на окно (-sqrt(m), sqrt(m)) с точным PW_lambda ODE"
collections: ["q3_docs"]
tags: ["Goal058", "G3", "PSWF", "physical-scale"]
insight_links: []
request_nodes: []
strong_terms: ["mode4PhysicalFerrersSeries", "physicalProlateDifferentialEquation", "exists_mode4MatchedNormalizedPhysicalProlateRow_of_root", "c = 2*pi*mProject"]
empty_terms: ["existing Lean physical Ferrers scale supplier"]
false_friend_terms: []
opens_new_branch_terms: ["Goal058.G3.Mode4SourceCrosswalk"]
neighbor_addresses: []
---

# Goal058.G3.Mode4PhysicalScale — Физическое масштабирование принятого mode-four Ferrers решения на окно (-sqrt(m), sqrt(m)) с точным PW_lambda ODE

## Статус

- карточка разрешена локально;
- три последовательных `q3_docs` запроса выполнены;
- physical derivative interfaces and exact ODE kernel checked in
  `D0Mode4FerrersPhysicalProlateScaling.lean`.

## Точный блокер

Закрыто локально.  Транспорт `x = u / sqrt(mProject)` теперь сохраняет actual
first/second derivatives и даёт буквальную физическую формулу с potential
`(2*pi*sqrt(mProject)*u)^2`.

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`Goal058.G3.Mode4PhysicalScale`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- `Mode4FerrersRegularEvenProlateSolution` уже хранит dimensionless `C2`,
  actual derivative series and exact ODE;
- architecture memorandum source-locks `lambda = sqrt(mProject)` and
  `c = 2*pi*mProject`;
- exact Lean physical-scale supplier before this card was absent.

## Что именно мы хотим узнать поиском

- locate an existing physical scale theorem;
- find reusable `ContDiffOn` composition and derivative-chain interfaces;
- verify the project/source parameter crosswalk rather than infer it by name.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `mode4 Ferrers physical scaling sqrt m prolate ODE` | `Goal058.G3.Mode4PhysicalScale` | exact project supplier | object/scale | strong context | architecture memorandum plus accepted solution, no Lean supplier |
| `ContDiffOn comp linear scaling Ioo sqrt derivative chain rule` | `Goal058.G3.Mode4PhysicalScale` | implementation API | calculus | noisy/partial | local Mathlib API audit supplied `ContDiffOn.comp` and `HasDerivAt.comp` |
| `physicalProlateEigenmode PW lambda scale dimensionless Ferrers` | `Goal058.G3.Mode4PhysicalScale` | source normalization cross-check | physics convention | decisive context | pinned `c=2*pi*lambda^2`; no competing production theorem |

## Пустые / шумовые слова

- generic `ContDiffOn comp` vocabulary was noisy across unrelated files;
- no existing Lean physical Ferrers scaling declaration was found.

## Новые возможные комбинации слов

- `mode4JacobiG sqrt physical potential`;
- `actual derivative series linear scale`;
- `root-conditioned physical Ferrers row`.

## Переход в INSIGHTS

- branch decision recorded in `docs/Progress_Log.md` under
  `Goal 058: mode-four Ferrers physical scaling`.

## Следующий адресный шаг

- `Goal058.G3.Mode4SourceCrosswalk`: classical regular `psi4` Legendre row to
  the current minimal tail and root equation.
