---
status: "active"
date: "2026-04-19"
main_address: "PO3-shell.3"
related_addresses: ["PO3-shell", "PO3-shell.2", "PO3Cert"]
ancestor_addresses: ["PO3-shell.2"]
child_or_next_addresses: ["PO3-shell.4"]
raw_address_notation: "PO3-shell.3, PO3-shell.2, PO3-shell, PO3Cert"
normalized_addresses: ["PO3-shell.3", "PO3-shell.2", "PO3-shell", "PO3Cert", "PO3-shell.4"]
address_status: "active"
blocker: "Дать прямой shell-bridge от tagged raw packet к theorem-форме raw tag ≠ po3_suzuki_filtered_pm_candidate u для любого u"
collections: ["q3_docs"]
tags: ["po3", "shell", "witness_stack", "direct_bridge", "inequality"]
insight_links: []
request_nodes: []
strong_terms: ["direct inequality bridge", "raw tag ne filtered candidate", "tagged packet direct theorem"]
empty_terms: []
false_friend_terms: []
opens_new_branch_terms: ["shell direct bridge"]
neighbor_addresses: []
---

# PO3-shell.3 — Дать прямой shell-bridge от tagged raw packet к theorem-форме raw tag ≠ po3_suzuki_filtered_pm_candidate u для любого u

## Статус

- карточка создана;
- search-pass уже выполнен;
- кодовый шаг ещё не начат.

## Точный блокер

Дать прямой shell-bridge от tagged raw packet к theorem-форме raw tag ≠ po3_suzuki_filtered_pm_candidate u для любого u

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3-shell.3`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- в `Q3/Proofs/PO3Cert/FirstZetaWitnessStack_2026_04_19.lean` уже есть:
  `po3_first_zeta_initial_packet_tag`,
  `po3_first_zeta_initial_packet_raw`,
  `po3_first_zeta_initial_packet_profile_of_tag`,
  `po3_no_suzuki_filtered_pm_candidate_of_first_zeta_initial_packet`;
- текущая дыра не математическая, а интерфейсная:
  downstream shell-код пока должен вручную упаковывать равенство
  `po3_first_zeta_initial_packet_raw tag = po3_suzuki_filtered_pm_candidate u`
  в existential predicate `po3_first_zeta_initial_packet_profile_of_tag tag`;
- в `Q3/Proofs/HBridge_PO3_Shell.lean` уже есть общий shell-слой
  `po3_suzuki_filtered_pm_candidate` и generic anti-diagonal obstruction
  machinery, так что новый узел должен оставаться коротким local bridge.

## Что именно мы хотим узнать поиском

- какие формулировки уже были бесполезны;
- какие слова могут открыть соседнюю живую ветку;
- какие локальные теоремы или reviewed notes реально усиливают `PO3-shell.3`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3 shell tagged packet raw family direct inequality theorem` | `PO3-shell.3` | Проверить, нет ли уже прямой theorem-формы `raw ≠ candidate` | theorem shape | medium | Готового bridge не нашлось; ближайшие попадания указывают только на shell-generic machinery и `INSIGHTS` |
| `first zeta packet tag bridge not equal filtered candidate` | `PO3-shell.3` | Проверить, не сидит ли нужный bridge под first-zeta именованием | naming / witness layer | weak | Локальная база не дала готового локального bridge; значит слой действительно ещё не вынесен |
| `existential tag shell consumer theorem profile of tag raw packet` | `PO3-shell.3` | Сравнить existential-форму с прямой pointwise theorem-формой | consumer interface | medium | Подтверждено, что сейчас есть только existential wrapper, а pointwise bridge отсутствует |
| `Lean 4 inductive cases theorem by cases exists not eq function` | `PO3-shell.3` | Внешне проверить, что минимальный путь — обычный theorem by cases + elimination of `Exists` | Lean implementation shape | strong | Официальные Lean docs подтверждают, что здесь естественна минимальная реализация через `cases` и обычное устранение `∃` |

## Пустые / шумовые слова

- `consumer theorem` без `tag/raw` слишком общий и сливается с уже закрытым `PO3-shell.2`;
- `first zeta bridge` без `filtered candidate` уводит в witness arithmetic, а не в интерфейс.

## Новые возможные комбинации слов

- `direct inequality bridge`
- `raw tag ne filtered candidate`
- `tagged packet direct theorem`
- `shell direct bridge`

## Переход в INSIGHTS

- синтез записан в `q3.lean.aristotle/docs/INSIGHTS.md`.

## Следующий адресный шаг

- реализовать pointwise bridge theorem `(tag) (u)`;
- при необходимости добавить collapsed existential theorem `¬ ∃ tag u, ...`;
- после кода перевести узел в `done` и открыть `PO3-shell.4`.
