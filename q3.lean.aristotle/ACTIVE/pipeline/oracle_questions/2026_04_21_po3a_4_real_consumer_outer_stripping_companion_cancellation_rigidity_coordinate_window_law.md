---
status: "done"
date: "2026-04-21"
main_address: "PO3a.4-real"
related_addresses: ["PO3a.4", "PO3-rig.1", "PO3-rig.1b"]
ancestor_addresses: ["PO3a.4", "PO3a-A-real", "H-bridge.11"]
child_or_next_addresses: ["PO3-rig.1", "PO3-rig.1b"]
raw_address_notation: "PO3a.4-real"
normalized_addresses: ["PO3a.4-real", "PO3a.4", "PO3-rig.1", "PO3-rig.1b", "PO3a-A-real", "H-bridge.11"]
address_status: "done"
blocker: "Прямой consumer от outer-stripping в companion-cancellation rigidity и coordinate window law"
collections: ["q3_docs"]
tags: ["po3a", "outer-stripping", "companion-rigidity", "window-law"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: []
strong_terms: ["outer transport", "companion cancellation", "coordinate profile"]
empty_terms: ["new spectral theorem", "global analysis of U and V"]
false_friend_terms: ["rebuild PO3-rig.1 shell", "prove full physical Volterra normal form"]
opens_new_branch_terms: ["direct consumer from PO3a.4 to PO3-rig.1b"]
neighbor_addresses: ["PO3a.4", "PO3-rig.1", "PO3-rig.1b"]
---

# PO3a.4-real — Прямой consumer от outer-stripping в companion-cancellation rigidity и coordinate window law

## Статус

- проведён local oracle pass и внешний sanity-check;
- адрес narrowed to one direct shell consumer;
- после интеграции следующий живой шаг сдвигается на реальный Q3-side
  certificate, а не на новую линейную алгебру.
- Lean consumer интегрирован и компилируется;
- `PO3a.4-real` закрыт как shell-level feeder.

## Точный блокер

Нужно добавить один прямой theorem-packet:
из real outer-stripped companion cancellation получить
`v ∈ 𝕜∙h`, `β_v ∈ 𝕜∙β_h`, а затем сразу один coordinate window law.

## Почему этот поиск нужен сейчас

Потому что после закрытия `PO3a-A-real` следующий честный узел уже не
про antiderivative transport, а про один короткий bridge:
снять outer `f,g` и без новых идей вернуть пакет прямо в уже замороженный
`PO3-rig.1` shell.

## Что уже известно по этому адресу

- В Lean уже есть:
  `po3_rankOne_companion_rigidity`,
  `mem_span_singleton_map_iff_of_injective`,
  `mem_span_singleton_comp_iff_of_surjective`,
  `po3_coordinate_profile_of_mem_span_singleton`.
- В notes уже зафиксировано, что `PO3a.4` должен быть именно
  outer-factor stripping, а не новой аналитической веткой.
- Значит реальный blocker узкий:
  one-step consumer от outer-stripped cancellation к existing rigidity shell.

## Что именно мы хотим узнать поиском

- хватает ли уже существующих span-transfer lemmas для прямой сборки;
- нужен ли отдельный новый theorem о зависимости после outer transport;
- можно ли сразу прикрутить coordinate-profile corollary и тем самым
  закрыть shell side для `PO3-rig.1b`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a.4 real outer-factor stripping two by two receiver identity outer rigidity` | `PO3a.4-real` | проверить, нет ли уже готового direct consumer-а | outer-stripping package | strong | вернул прежние `PO3a.4` syntheses и подтвердил, что missing piece ровно один |
| `PO3a outer invariance injective U star surjective V pullback rank one companion rigidity` | `PO3a.4-real` | проверить достаточность уже формализованных transfer lemmas | injective/surjective bridge | strong | вернул `mem_span_singleton_*` и `po3_rankOne_companion_rigidity` как достаточный набор |
| `PO3a.4 local sign preserving injective endpoint spaces two endpoint physical Volterra` | `PO3a.4-real` | проверить, не требуется ли новая endpoint algebra | endpoint-space control | medium | подтвердил, что на shell-уровне нужен только consumer, а не новый endpoint theorem |
| `PO3-rig.1 feed from physical two by two receiver with outer factors` | `PO3a.4-real` | проверить прямую сцепку с оконным законом | rigidity handoff | strong | указал на уже закрытый `PO3-rig.1` shell и отсутствие только одного feeder theorem |
| внешний web-поиск по injective/surjective linear-algebra transfer и rank-one cancellation | `PO3a.4-real` | sanity-check на off-the-shelf theorem | local shell vs external literature | weak | готового theorem-packet не дал; лучший ход — собрать локальный consumer из уже существующих лемм |

## Пустые / шумовые слова

- новые “общие” разговоры про harmless outer operators без точной receiver-shape;
- попытка снова доказывать весь `PO3-rig.1` вместо одного feeder theorem.

## Новые возможные комбинации слов

- outer transport companion cancellation
- outer-stripped rigidity feeder
- coordinate window law from transported receiver

## Переход в INSIGHTS

- `q3.lean.aristotle/docs/INSIGHTS.md`: synthesis block от `2026-04-21`
  на адресе `PO3a.4-real`.

## Следующий адресный шаг

- добавить в `Q3/Proofs/HBridge_PO3_Shell.lean` theorem
  `PO3a.4-real`-типа, который переводит outer-stripped cancellation в
  `v ∈ 𝕜∙h` и `β_v ∈ 𝕜∙β_h`;
- сразу добавить coordinate-profile corollary, чтобы следующий live burden был
  уже не shell-level linear algebra, а реальный Q3-side certificate.

## Итог

- в `Q3/Proofs/HBridge_PO3_Shell.lean` добавлены
  `po3_rankOne_companion_rigidity_of_outer_transport`
  и
  `po3_coordinate_profile_of_outer_transport_companion_cancellation`;
- первый theorem exactly strips outer `f,g` and feeds the already frozen
  singleton-span rigidity shell;
- второй theorem immediately converts that span conclusion into one scalar
  coordinate window law;
- verification passed:
  `lake env lean Q3/Proofs/HBridge_PO3_Shell.lean`
  and
  `lake build Q3.Proofs.PO3Cert`;
- следующий живой узел теперь уже не про `PO3a.4`, а про real Q3-side
  certificate into `PO3-rig.1b`, then `PO3-tail.1`.
