---
status: "active"
date: "2026-04-21"
main_address: "PO3-square.2c1"
related_addresses: ["PO3-square.2c", "PO3-square.2c0", "PO3-square.2b1", "PO3-square.2d1"]
ancestor_addresses: ["PO3-square.2c", "PO3-square.2"]
child_or_next_addresses: ["PO3-square.2c2"]
raw_address_notation: "PO3-square.2c1; PO3-square.2c0, PO3-square.2b1, PO3-square.2d1"
normalized_addresses: ["PO3-square.2c1", "PO3-square.2c0", "PO3-square.2b1", "PO3-square.2d1", "PO3-square.2c", "PO3-square.2", "PO3-square.2c2"]
address_status: "active"
blocker: "Заморозить consumer-target после деления: canonical factorization + same pole support simple Cauchy quotient сводят `2c` к одной divisibility/uniqueness цели."
collections: ["q3_docs"]
tags: ["po3-square", "entire-divider", "quotient-target"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["PO3-square.2c1"]
strong_terms: ["quotient after division", "same pole support simple Cauchy class", "divisibility uniqueness target"]
empty_terms: ["direct entire proof right now"]
false_friend_terms: ["готовая внешняя uniqueness theorem"]
opens_new_branch_terms: ["after-division target"]
neighbor_addresses: ["PO3-square.2d1"]
---

# PO3-square.2c1 — Заморозить consumer-target после деления: canonical factorization + same pole support simple Cauchy quotient сводят `2c` к одной divisibility/uniqueness цели.

## Статус

- карточка создана;
- первая серия локальных запросов и внешний фон уже зафиксированы;
- следующий ход выделен как narrow consumer shell.

## Точный блокер

Заморозить consumer-target после деления: canonical factorization + same pole support simple Cauchy quotient сводят `2c` к одной divisibility/uniqueness цели.

## Почему этот поиск нужен сейчас

После закрытия `PO3-square.2c0` algebraic part canonical divider route уже
собрана, и дальше есть риск снова расплыться в слова про “entire uniqueness”.
Нужен точный next target: что именно analytic factorization должна кормить. Это
и есть consumer-theorem после деления.

## Что уже известно по этому адресу

- notes уже говорят буквально:
  если `J_a(r^2)=0` на square tail, то
  `U_a = J_a / E_N^{sq}` снова мероморфна с тем же pole support `Λ_a`;
- внешний поиск не дал готового theorem import для нашей quotient-задачи;
- `PO3-square.2c0` уже закрыл front-factor algebra;
- значит сейчас честный вопрос уже не “что такое divider?”, а “какая exactly
  target-теорема после деления должна закрыть весь маршрут `2c`”.

## Что именно мы хотим узнать поиском

- какая самая узкая theorem-shape соответствует phrases
  “same pole support” + “simple Cauchy quotient”;
- можно ли уже сейчас заморозить consumer theorem без analytic factorization;
- как связать `2c1` с уже закрытыми `2c0` и `2b1`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3-square.2c1 quotient same pole support divisibility uniqueness target canonical divider` | `PO3-square.2c1` | Вытащить exact theorem-shape после деления | quotient target language | strong | вернул формулу про after-division unresolved uniqueness |
| `U_a = J_a / E_N^{sq} same pole support simple Cauchy transform unresolved uniqueness theorem` | `PO3-square.2c1` | Проверить, что note уже формулирует живую стену после деления | same support / simple Cauchy class | strong | подтвердил, что это именно quotient uniqueness problem |
| `square-tail zero canonical divider quotient meromorphic same pole support live theorem target` | `PO3-square.2c1` | Проверить, не скрыт ли уже готовый импорт | route framing | medium | показал, что внешний route даёт фон, но не готовый kill theorem |

## Пустые / шумовые слова

- `direct entire proof right now`;
- `готовая внешняя uniqueness theorem`.

## Новые возможные комбинации слов

- `after-division target`;
- `same pole support simple Cauchy class`;
- `divisibility uniqueness target`.

## Переход в INSIGHTS

- синтез зафиксирован в `q3.lean.aristotle/docs/INSIGHTS.md` как адрес
  `PO3-square.2c1`.

## Следующий адресный шаг

- сначала посадить в Lean named consumer-target после деления;
- потом либо идти в `PO3-square.2c2` за analytic factorization shell, либо
  напрямую бить quotient uniqueness wall.
