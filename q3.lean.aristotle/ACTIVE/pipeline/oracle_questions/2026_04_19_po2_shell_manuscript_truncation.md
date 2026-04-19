---
status: "active"
date: "2026-04-19"
main_address: "PO2-shell"
related_addresses: ["PO2", "D2g33"]
ancestor_addresses: ["H-bridge.11", "PO2"]
child_or_next_addresses: ["PO2-shell"]
raw_address_notation: "PO2-shell; PO2, D2g33; H-bridge.11"
normalized_addresses: ["PO2-shell", "PO2", "D2g33", "H-bridge.11", "PO2.2"]
address_status: "active"
blocker: "Точная manuscript finite truncation для M^{+-} и её посадка в anti-diagonal shell"
collections: ["q3_docs"]
tags: ["po2", "suzuki", "manuscript"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md"]
request_nodes: []
strong_terms: ["антидиагональный разрыв (anti-diagonal gap)", "рукописная gamma-сумма (manuscript gamma sum)", "конечная truncation (finite truncation)"]
empty_terms: ["общая формула Сузуки"]
false_friend_terms: ["чисто формальная Toeplitz-симметрия"]
opens_new_branch_terms: ["singleton manuscript truncation"]
neighbor_addresses: ["PO2.2"]
---

# PO2-shell — Точная manuscript finite truncation для M^{+-} и её посадка в anti-diagonal shell

## Статус

- карточка создана;
- первая серия запросов отработана;
- главный сигнал пришёл из локального note `h1_po2_cross_sign_bulk_exactness_2026_03_16.md`
  и из `full/sections/main_closure.tex`;
- внешний web-search полезного первичного источника не дал.

## Точный блокер

Точная manuscript finite truncation для M^{+-} и её посадка в anti-diagonal shell

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO2-shell`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- в `main_closure.tex` уже зафиксирована точная raw `\gamma`-сумма для
  `M_{mn}^{+-}(a)`:
  общий множитель `2\pi^2/a^3`, фактор `(-1)^{m+n}` и четыре same-sign pole;
- в `h1_po2_cross_sign_bulk_exactness_2026_03_16.md` уже выписано, что
  `(+,-)`-канал имеет естественную зависимость от `m+n` и именно поэтому
  его надо сажать в anti-diagonal shell раньше `(++)`;
- в `Q3/Proofs/HBridge_PO3_Shell.lean` уже были готовы manuscript shell-объекты
  `po3_suzuki_filtered_pm_partial_sum_manuscript` и
  `po3_suzuki_filtered_pm_singleton_manuscript`, плюс gap/kill-теоремы для них.

## Что именно мы хотим узнать поиском

- есть ли в проекте уже готовая прямая формула, которая выглядит именно как
  raw manuscript finite `\gamma`-sum для `M^{+-}`, а не как абстрактная
  упаковка через `weight`;
- есть ли уже готовый мост от tex-формулы к anti-diagonal gap shell;
- нужно ли строить новый объект, или достаточно переименования существующего.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `M^{+-} manuscript gamma sum anti-diagonal gap` | `PO2-shell` | Найти прямой мост от рукописной формулы к shell разрыва | `M^{+-}` / anti-diagonal | strong | `Q3/Proofs/HBridge_PO3_Shell.lean`, `docs/INSIGHTS.md`, `h1_po2_cross_sign_bulk_exactness_2026_03_16.md` |
| `raw gamma sum Suzuki blocks finite truncation manuscript` | `PO2-shell` | Проверить, есть ли уже формулировка про finite truncation | raw / finite truncation | strong | `full/sections/main_closure.tex`, существующий manuscript shell |
| `po3_suzuki_filtered_pm_singleton_manuscript raw gamma sum M^{+-}` | `PO2-shell` | Понять, нужен ли новый raw-объект поверх singleton shell | singleton / raw gamma sum | medium | подтвердило, что shell уже почти готов и нужен только прямой raw alias |
| `filtered q blocks raw gamma blocks manuscript M^{+-} alpha_m` | `PO2-shell` | Проверить, где лучше брать формулировку для combined-index geometry | Q-side / Suzuki-side | medium | `h1_po2_cross_sign_bulk_exactness_2026_03_16.md` и `h1_four_block_bulk_2026_03_08.md` |

## Пустые / шумовые слова

- `общая формула Сузуки`;
- слишком общие запросы по `filtered q blocks`;
- внешний web-search по `M_{mn}^{+-}` без локальных имён теорем.

## Новые возможные комбинации слов

- `raw manuscript gamma sum (сырая рукописная gamma-сумма)`;
- `direct finite truncation (прямая конечная truncation)`;
- `singleton manuscript truncation`;
- `anti-diagonal gap shell` вместе с `M^{+-}`.

## Переход в INSIGHTS

- синтез и кодовая посадка зафиксированы в `q3.lean.aristotle/docs/INSIGHTS.md`
  update от `2026-04-19`.

## Следующий адресный шаг

- из этого поиска вырос следующий узкий шаг:
  завести в Lean прямой raw manuscript объект для finite/singleton
  `\gamma`-truncation и свести его к уже существующему manuscript shell;
- следующий адрес после этого шага остаётся `PO2-shell`, но уже в режиме
  прямой подстановки реальной finite truncation из рукописи.
