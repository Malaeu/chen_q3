---
status: "active"
date: "2026-04-13"
main_address: "PO3a-A3"
related_addresses: ["PO3a-A2", "PO3a-B", "PO3a.4"]
ancestor_addresses: ["PO3a-A", "PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a-B"]
raw_address_notation: "PO3a-A3; PO3a-A2; PO3a-B; PO3a.4"
normalized_addresses: ["PO3a-A3", "PO3a-A2", "PO3a-B", "PO3a.4", "PO3a-A", "PO3a", "H-bridge.11"]
address_status: "active"
blocker: "Смешанная внутренняя разность реального дефекта и происхождение L_a"
collections: ["q3_docs"]
tags: ["po3", "boundary", "mixed-difference"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: []
strong_terms: ["смешанная внутренняя разность (mixed interior difference)", "двумерная antiderivative-экстракция (two-variable antiderivative extraction)", "реальный дефект (real defect)", "ядро bulk-переноса (bulk transport kernel)"]
empty_terms: ["снова обсуждать только outer operators"]
false_friend_terms: ["считать A1 и A3 одним и тем же шагом"]
opens_new_branch_terms: ["L_a versus K_a"]
neighbor_addresses: ["PO3a-A2", "PO3a-B", "PO3a.4"]
---

# PO3a-A3 — Смешанная внутренняя разность реального дефекта и происхождение L_a

## Статус

- карточка создана;
- серия запросов проведена;
- адрес `PO3a-A3` подтверждён как отдельный слой между общим transport-пакетом и `PO3a-B`.

## Точный блокер

Смешанная внутренняя разность реального дефекта и происхождение L_a

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3a-A3`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- `PO3a-A0` и `PO3a-A1` уже закрывают только общий transport:
  double telescoping и abstract `boundary + bulk`;
- старый `PO3` note уже содержит weaker bridge:
  `PO3a-finite antiderivative mismatch criterion`;
- в нём boundary defect допускает вид
  `∑ U_j^* T^* ((I-R_a)^* K_j (I-R_a) - L_j) T V_j`
  при условии глобической отмены zero-endpoint части
  `∑ U_j^* T^* (K_j - L_j) T V_j = 0`;
- если дополнительно `J = 1` и `L_1 = K_1`, это схлопывается в более сильную
  physical Volterra normal form;
- значит реальный новый вопрос не “как снова применить transport”, а
  “откуда берётся `L_a` и можно ли его отождествить с `K_a`”.

## Что именно мы хотим узнать поиском

- есть ли уже reviewed note, где `L_a` прямо схлопывается в `K_a`;
- если нет, то зафиксирован ли уже weaker route через global zero-endpoint cancellation;
- нужно ли делить адрес на два подпакета:
  `PO3a-A3a` = mixed interior difference,
  `PO3a-A3b` = identification `L_a` versus `K_a`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a A3 mixed interior difference real defect L_a versus K_a` | `PO3a-A3` | Проверить, не заморожен ли уже прямой переход от mixed difference к `K_a` | `A3` как mixed-difference node | medium | вернул старый `PO3` note и `INSIGHTS`, но не отдельное готовое reviewed theorem |
| `(I-R_a)^*K_a(I-R_a)-L_a physical Volterra normal form` | `PO3a-A3` | Проверить, есть ли уже прямая physical specialization | `L_a` vs `K_a` | weak | готового reviewed узла не нашлось |
| `real defect mixed difference K_a L_a endpoint projector R_a` | `PO3a-A3` | Поднять именно endpoint-projector presentation | endpoint-projector wording | medium | подтвердил старую bridge-формулу через `R_a`, но не дал явного collapse `L_a=K_a` |
| `PO3a physical Volterra L_1 equals K_1` | `PO3a-A3` | Проверить, не записано ли уже нужное схлопывание как специальный случай | strong physical form | strong | вернул `PO3a-finite antiderivative mismatch criterion`, где прямо сказано: при `J=1` и `L_1=K_1` получается physical Volterra form |

## Пустые / шумовые слова

- `снова обсуждать только outer operators`;
- `снова обсуждать только raw defect` без слов `L_a` и `K_a`;
- `physical Volterra` без слов `mismatch` или `zero-endpoint`.

## Новые возможные комбинации слов

- `finite antiderivative mismatch criterion`;
- `zero-endpoint cancellation`;
- `L_a versus K_a`;
- `physical specialization J=1`.

## Переход в INSIGHTS

- добавить синтез: `A3` — это old finite antiderivative mismatch criterion, а не повтор `A1`.

## Следующий адресный шаг

- добавить shell для mismatch-expansion и global zero-endpoint cancellation;
- после этого решить, нужно ли официально дробить узел на
  `PO3a-A3a` и `PO3a-A3b`.
