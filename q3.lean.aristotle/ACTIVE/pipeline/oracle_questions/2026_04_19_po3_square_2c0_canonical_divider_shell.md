---
status: "active"
date: "2026-04-19"
main_address: "PO3-square.2c0"
related_addresses: ["PO3-square.2c", "PO3-square.2b1", "SQ1"]
ancestor_addresses: ["PO3-square.2c", "PO3-square.2"]
child_or_next_addresses: ["PO3-square.2c1"]
raw_address_notation: "PO3-square.2c0; PO3-square.2c, PO3-square.2b1; SQ1"
normalized_addresses: ["PO3-square.2c0", "PO3-square.2c", "PO3-square.2b1", "SQ1", "PO3-square.2", "PO3-square.2c1", "PO3-square.2d1"]
address_status: "active"
blocker: "Формализовать canonical square-divider shell: finite front factor и pointwise step-рекурсию делителя, чтобы `2c` реально сцепился с уже закрытым `2b1`."
collections: ["q3_docs"]
tags: ["po3-square", "entire-divider", "canonical-product"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: ["PO3-square.2c0"]
strong_terms: ["канонический square-divider (canonical square divider)", "finite front factor", "step-рекурсия делителя"]
empty_terms: ["full uniqueness theorem"]
false_friend_terms: ["сразу строить entire proof of injectivity"]
opens_new_branch_terms: ["divider step shell"]
neighbor_addresses: ["PO3-square.2d1"]
---

# PO3-square.2c0 — Формализовать canonical square-divider shell: finite front factor и pointwise step-рекурсию делителя, чтобы `2c` реально сцепился с уже закрытым `2b1`.

## Статус

- карточка создана;
- первая серия локальных запросов и внешний фон уже зафиксированы;
- следующий ход выделен как узкая Lean-оболочка.

## Точный блокер

Формализовать canonical square-divider shell: finite front factor и pointwise step-рекурсию делителя, чтобы `2c` реально сцепился с уже закрытым `2b1`.

## Почему этот поиск нужен сейчас

После закрытия `PO3-square.2b1` стало видно, что entire-divider маршрут жив
только если его сцепить с уже закрытой алгеброй quotient-collapse. Значит
следующий честный шаг внутри `2c` — не обещать full uniqueness theorem, а
заморозить ту точную algebraic shell, которая будет потреблять будущую
аналитическую factorization через canonical square-divider.

## Что уже известно по этому адресу

- локальные notes уже содержат exact analytic picture:
  square-tail set имеет canonical entire divider
  `E_N^{sq}(z)=sin(π√z)/(π√z)` с finite front correction;
- та же заметка говорит, что после деления на `E_N^{sq}` остаётся quotient с
  тем же pole support;
- внешний поиск не дал готового uniqueness-theorem для нашей задачи, но
  подтвердил классическую product identity для синуса как честный внешний
  источник фона;
- закрытый адрес `PO3-square.2b1` уже формализует algebraic step
  `E_k = (1 - z/s) E_{k+1} -> G_k = (-s) G_{k+1}`, так что сейчас надо
  посадить именно мост от canonical divider data к этой step-рекурсии.

## Что именно мы хотим узнать поиском

- какая минимальная finite/product algebra нужна, чтобы `2c` честно сцепился
  с `2b1`;
- нужно ли тащить в Lean саму transcendental identity, или пока достаточно
  algebraic shell вокруг finite front factor;
- какой именно named theorem будет самым узким полезным результатом на этом
  адресе.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3-square.2c canonical square-tail divisor E_N^{sq} quotient U_a same pole support` | `PO3-square.2c0` | Найти точный in-repo statement маршрута `2c` | factorization / quotient language | strong | вернул мартовскую note с формулировкой “quotient is again meromorphic with the same pole support” |
| `sin(pi sqrt z)/(pi sqrt z) square lattice entire divider tail zeros J_a divided by E_N^{sq}` | `PO3-square.2c0` | Проверить exact canonical product language | canonical product / explicit divider | strong | вернул апрельский synthesis про canonical entire divider square-tail set |
| `PO3 square-tail entire factorization order 1/2 divisor quotient meromorphic same support` | `PO3-square.2c0` | Проверить order/growth framing и не прячется ли там уже готовый theorem import | order / growth / pole-support | medium | подтвердил, что живое содержимое — именно low-density order-`1/2` divisor picture, а не готовая uniqueness theorem |

## Пустые / шумовые слова

- `full uniqueness theorem`;
- `сразу entire proof of injectivity`.

## Новые возможные комбинации слов

- `canonical square divider`;
- `finite front factor`;
- `divider step shell`.

## Переход в INSIGHTS

- синтез зафиксирован в `q3.lean.aristotle/docs/INSIGHTS.md` как адрес
  `PO3-square.2c0`.

## Следующий адресный шаг

- сначала посадить в Lean finite front factor и derived step-рекурсию divider;
- после этого либо идти в `PO3-square.2c1`, либо возвращать этот shell как
  вход в уже закрытый пакет `PO3-square.2b1`.
