---
status: "active"
date: "2026-04-15"
main_address: "PO2"
related_addresses: ["D2g33", "PO2.1", "PO2.2"]
ancestor_addresses: ["H-bridge.11"]
child_or_next_addresses: ["PO2-shell"]
raw_address_notation: "PO2, D2g33"
normalized_addresses: ["PO2", "D2g33", "PO2.1", "PO2.2", "H-bridge.11", "PO2-shell", "PO3"]
address_status: "active"
blocker: "Выделить одномерные фильтрованные профили Сузуки для M^{+-}, M^{++} и связать их с concrete Section 8 shell"
collections: ["q3_docs"]
tags: ["po2", "suzuki", "filtered_profile"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md"]
request_nodes: []
strong_terms: ["фильтрованный профиль Сузуки", "M^{+-} сумма по m+n", "M^{++} профиль по разности"]
empty_terms: ["общий Volterra ansatz", "boundary algebra"]
false_friend_terms: []
opens_new_branch_terms: ["adjacent Suzuki tails", "raw gamma blocks"]
neighbor_addresses: ["PO3"]
---

# PO2 — Выделить одномерные фильтрованные профили Сузуки для M^{+-}, M^{++} и связать их с concrete Section 8 shell

## Статус

- карточка создана;
- первая серия запросов проведена;
- локальный вывод уже зафиксирован в `INSIGHTS`;
- следующий шаг сузился до подстановки реальной формулы Сузуки в готовый
  shell сравнения профилей.

## Точный блокер

Выделить одномерные фильтрованные профили Сузуки для M^{+-}, M^{++} и связать их с concrete Section 8 shell

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO2`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- в `HBridge_PO3_Shell.lean` уже есть concrete Section 8 профили
  `po3_section8_filtered_pp_profile` и
  `po3_section8_filtered_pm_profile`;
- по `main_closure.tex` filtered `(+,-)` остаётся первым честным потребителем;
- raw-to-filtered Q-side shell уже заморожен, так что дальше нужен не новый
  двухиндексный расчёт, а только точная подстановка одномерного профиля.

## Что именно мы хотим узнать поиском

- можно ли посадить `M^{+-}` в честный одномерный профиль-кандидат;
- есть ли у `M^{++}` такая же редукция или это пока ложная надежда;
- какие локальные manuscript / insight узлы реально дают формулу, а не общий
  разговор.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `фильтрованный профиль Сузуки M^{+-} сумма по m+n four-term stencil` | `PO2` | проверить, есть ли уже явная свёртка mixed-блока в одну ось | `(+,-)` против общего filtered shell | слабый | вернул в `main_closure.tex`, но сам по себе дал мало структуры |
| `adjacent Suzuki tails raw gamma blocks filtered M^{+-} main_closure` | `PO2` | вытащить точную рукописную формулу и опорные узлы | raw gamma blocks / adjacent tails | сильный | привёл к `main_closure.tex` и подтвердил, что `M^{+-}` надо бить первым |
| `Section 8 filtered q profile Suzuki comparison plus minus plus plus` | `PO2` | связать новый concrete Section 8 shell с живой веткой bulk-comparison | Section 8 vs Suzuki | сильный | вернул к `eq:H1-filtered-bulk-plus-minus` и `h1_po2_cross_sign_bulk_exactness_2026_03_16.md` |
| `M^{++} filtered Suzuki denominator alpha_m alpha_{m+1} difference profile adjacent tails` | `PO2` | проверить, честно ли ожидать одномерную разностную форму для same-sign блока | `(++ )` профиль по разности | средний отрицательный | подтвердил, что для `(++ )` нельзя заранее обещать one-variable collapse |

## Пустые / шумовые слова

- `общий Volterra ansatz`
- `boundary algebra`
- слишком широкие запросы без `adjacent tails` и без `filtered`

## Новые возможные комбинации слов

- `adjacent Suzuki tails`
- `raw gamma blocks`
- `filtered bulk plus minus`
- `Section 8 filtered profile`

## Переход в INSIGHTS

- синтез зафиксирован в
  `q3.lean.aristotle/docs/INSIGHTS.md`
  под заголовком
  `In progress (2026-04-15): Suzuki filtered shell should reduce block equality to profile equality`.

## Следующий адресный шаг

- подать реальную формулу Сузуки для `(+,-)` в вид
  `po3_suzuki_filtered_pm_candidate u`;
- затем закрыть точечное равенство
  `u = po3_section8_filtered_pm_profile B t`;
- только после этого решать, есть ли честный аналогичный ход для `(++ )`.
