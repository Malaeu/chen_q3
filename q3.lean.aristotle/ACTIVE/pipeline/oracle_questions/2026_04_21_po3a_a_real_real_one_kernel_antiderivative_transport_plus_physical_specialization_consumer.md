---
status: "done"
date: "2026-04-21"
main_address: "PO3a-A-real"
related_addresses: ["PO3a-A", "PO3a-A0", "PO3a-A1", "PO3a-A2", "PO3a.4", "PO3-rig.1"]
ancestor_addresses: ["PO3a-A", "PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a.4", "PO3-rig.1"]
raw_address_notation: "PO3a-A-real; PO3a-A0, 1, 2; PO3a.4; PO3-rig.1"
normalized_addresses: ["PO3a-A-real", "PO3a-A0", "PO3a-A1", "PO3a-A2", "PO3a.4", "PO3-rig.1", "PO3a-A", "PO3a", "H-bridge.11"]
address_status: "done"
blocker: "real one-kernel antiderivative transport plus physical specialization consumer"
collections: ["q3_docs"]
tags: ["po3a", "antiderivative", "volterra", "physical-specialization"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: []
strong_terms: ["two-endpoint extraction", "physical specialization", "antiderivative transport"]
empty_terms: ["new theorem package from scratch"]
false_friend_terms: ["rebuild PO3a-A0"]
opens_new_branch_terms: ["one-kernel Volterra consumer"]
neighbor_addresses: []
---

# PO3a-A-real — real one-kernel antiderivative transport plus physical specialization consumer

## Статус

- проведён local oracle pass и внешний sanity-check;
- выбран один прямой blocker без возврата к новым веткам.

## Точный блокер

Нужно заморозить один direct consumer для реального `PO3a-A` пути:
если genuine cross-sign boundary packet уже транспортирован на
antiderivative-side и имеет real one-kernel physical specialization
`((1-R)^*K(1-R)-K)`, то он должен сразу сцепляться с уже замороженным finite
matrix receiver и давать `D_partial_pm = 0`.

## Почему этот поиск нужен сейчас

Потому что это shortest path внутри `PO3a`:
не переписывать `A0/A1/A2`, не спорить о новой архитектуре, а взять уже
существующие shell-леммы и склеить их в один theorem-потребитель для
реального one-kernel Volterra packet.

## Что уже известно по этому адресу

- В Lean уже есть:
  `po3_double_telescoping`, `po3_boundary_plus_bulk_of_double_telescoping`,
  `po3_two_endpoint_expansion`,
  `po3_finite_antiderivative_physical_specialization`,
  `po3_endpoint_packet_of_antiderivative_transport`,
  `po3_boundary_zero_of_antiderivative_transport_and_matrix_receiver`.
- В note уже заморожена exact theorem-shape
  `PO3a-two-endpoint extraction`: реальный boundary defect надо довести до
  transported Volterra form, после чего остаются только left/right/two-endpoint
  bricks.
- Значит следующий ход не “новая теория”, а packaging step:
  direct consumer от real physical specialization к matrix receiver.

## Что именно мы хотим узнать поиском

- есть ли уже в repo все нужные shell-кусочки;
- хватает ли одного нового theorem-потребителя вместо новой серии пакетов;
- не спрятан ли в notes более сильный уже готовый маршрут для real one-kernel
  specialization.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a-A-real genuine defect substitution mixed difference bulk match` | `PO3a-A-real` | проверить, не закрыт ли уже real substitution packet | substitution shell | strong | вернул existing `A0/A1` shell и прямой указатель, что live mathematics уже narrowed to real substitution |
| `PO3a real defect antiderivative transport endpoint words outer factors` | `PO3a-A-real` | найти самый ранний честный handoff к endpoint words | transport -> endpoint words | strong | привёл к `PO3a-A` handoff и antiderivative transport theorem в shell |
| `PO3a two endpoint extraction Volterra form genuine boundary defect` | `PO3a-A-real` | проверить exact one-kernel route | one-kernel Volterra packet | strong | вернул note с `PO3a-two-endpoint extraction` и Lean theorem `po3_two_endpoint_expansion` |
| `PO3a outer harmlessness endpoint spaces triangular injective sign preserving` | `PO3a-A-real` | убедиться, что следующий brick после consumer-а не меняется | downstream outer layer | medium | подтвердил, что после consumer-а live brick действительно `outer-real`, не новый `A`-пакет |
| внешний web-поиск: `two-variable discrete telescoping identity mixed difference summation by parts`, `Volterra endpoint projector rank one expansion boundary defect` | `PO3a-A-real` | sanity-check на off-the-shelf theorem | local shell vs external literature | weak | готового theorem-packet не дал; это подтверждает, что лучший ход — склеить уже существующие локальные shell-леммы |

## Пустые / шумовые слова

- `new theorem package from scratch`
- `rebuild PO3a-A0`
- абстрактный “новый Volterra theorem” без привязки к существующим shell-леммам

## Новые возможные комбинации слов

- real one-kernel Volterra consumer
- antiderivative transport plus physical specialization
- two-endpoint extraction consumer
- transported boundary packet to matrix receiver

## Переход в INSIGHTS

- `docs/INSIGHTS.md`:
  synthesis block от `2026-04-21` на адресе `PO3a-A-real`.

## Следующий адресный шаг

- добавить один новый theorem в `Q3/Proofs/HBridge_PO3_Shell.lean`, который
  соединит
  `po3_finite_antiderivative_physical_specialization`
  с
  `po3_boundary_zero_of_antiderivative_transport_and_matrix_receiver`;
- после этого live brick автоматически сдвигается на `PO3a.4` / `PO3-rig.1`,
  то есть на проверку реальных outer factors и дальше на tail-zero chain.
