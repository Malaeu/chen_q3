---
status: "active"
date: "2026-08-05"
main_address: "RouteB.G5.Mode4.RegularRow"
related_addresses: []
ancestor_addresses: ["RouteB.G5.Mode4.HermitianTailUniqueness", "G5"]
child_or_next_addresses: ["RouteB.G5.Mode4.InfiniteSchurInertia"]
raw_address_notation: "G5 / MODE4 / PSWF_REGULAR_COEFFICIENT_ROW_EQUALS_CANONICAL_SQUARE_SUMMABLE_TAIL_ROW"
normalized_addresses: ["G5 / MODE4 / PSWF_REGULAR_COEFFICIENT_ROW_EQUALS_CANONICAL_SQUARE_SUMMABLE_TAIL_ROW", "RouteB.G5.Mode4.RegularRow", "RouteB.G5.Mode4.HermitianTailUniqueness", "G5", "RouteB.G5.Mode4.InfiniteSchurInertia"]
address_status: "active"
blocker: "Источник регулярного чётного PSWF-ряда (regular even PSWF coefficient row): ненулевой начальный коэффициент, точная scaled recurrence и квадрат-суммируемость"
collections: ["q3_docs"]
tags: ["routeb", "g5", "pswf", "legendre"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: []
strong_terms: ["regular even PSWF Legendre expansion coefficients square summable recurrence", "DLMF 30.8.3 30.8.7 radial angular spheroidal coefficients"]
empty_terms: ["abstract recurrence row without source eigenfunction"]
false_friend_terms: ["finite tridiagonal approximation alone"]
opens_new_branch_terms: ["Sturm-Liouville compact resolvent eigenfunction Legendre basis"]
neighbor_addresses: []
---

# RouteB.G5.Mode4.RegularRow — Источник регулярного чётного PSWF-ряда (regular even PSWF coefficient row): ненулевой начальный коэффициент, точная scaled recurrence и квадрат-суммируемость

## Статус

- карточка создана;
- четыре локальных запроса завершены с пустым результатом;
- source-locked путь найден в DLMF §30.8;
- Proshka выбрал exact 30.8.5 weight-match receiver;
- receiver Lean-proved, genuine regular-PSWF source object остаётся открыт.

## Точный блокер

Источник регулярного чётного PSWF-ряда (regular even PSWF coefficient row): ненулевой начальный коэффициент, точная scaled recurrence и квадрат-суммируемость

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`RouteB.G5.Mode4.RegularRow`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- `D0Mode4JacobiHermitianTailUniqueness.lean` уже доказывает пропорциональность
  любых двух квадрат-суммируемых решений точной симметричной recurrence;
- DLMF 30.8.1--30.8.5 задаёт Ferrers-ряд, recurrence и ненулевую нормировку;
- DLMF 30.8.7 и 30.16(ii) дают recessive-асимптотику коэффициентов;
- Mathlib не содержит готового spheroidal/PSWF-конструктора или Legendre
  Hilbert basis на нужном интервале.

## Что именно мы хотим узнать поиском

- какие формулировки уже были бесполезны;
- какие слова могут открыть соседнюю живую ветку;
- какие локальные теоремы или reviewed notes реально усиливают `RouteB.G5.Mode4.RegularRow`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `regular even PSWF Legendre expansion coefficients square summable recurrence` | `RouteB.G5.Mode4.RegularRow` | прямой объект | source row | empty | нет кандидатов |
| `DLMF 30.8.5 30.8.7 recessive solution spheroidal coefficients normalization` | `RouteB.G5.Mode4.RegularRow` | нормировка плюс decay | source theorem | empty | нет кандидатов |
| `PSWF regular coefficient row canonical square summable tail row` | `RouteB.G5.Mode4.RegularRow` | точный project crosswalk | project vocabulary | empty | нет кандидатов |
| `spheroidal eigenfunction Ferrers series coefficients recurrence asymptotic ratio` | `RouteB.G5.Mode4.RegularRow` | общая source формулировка | external vocabulary | empty | нет кандидатов |

## Пустые / шумовые слова

- `abstract recurrence row` без source eigenfunction;
- `finite tridiagonal approximation` без cofinal/source identification.

## Новые возможные комбинации слов

- `DLMF 30.8.5 normalization` + `DLMF 30.8.7 recessive ratio` +
  `discrete Wronskian uniqueness`;
- `regular source row` + `positive canonical Hermitian row` +
  `nonzero proportionality constant`.

## Переход в INSIGHTS

- `q3.lean.aristotle/docs/INSIGHTS.md`, запись
  `G5 regular PSWF coefficient-row source gate`.

## Следующий адресный шаг

- использовать доказанный
  `mode4DLMF3085_nonzero_and_shiftedHermitian_sqSummable` в следующем
  conditional consumer-е
  `mode4DLMF3084_3085_shiftedHermitianTail_eq_c_mul_canonical`;
- отдельно сохранить открытым genuine source-object supplier для regular
  first-kind PSWF/Ferrers coefficients;
- не строить полный Sturm--Liouville operator без отдельного решения.
