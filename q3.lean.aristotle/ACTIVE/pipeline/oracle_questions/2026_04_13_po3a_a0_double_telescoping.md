---
status: "active"
date: "2026-04-13"
main_address: "PO3a-A0"
related_addresses: ["PO3a-A", "PO3a-B"]
ancestor_addresses: ["PO3a-A", "PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a-A1"]
raw_address_notation: "PO3a-A0; PO3a-A1; PO3a-B; PO3a.4"
normalized_addresses: ["PO3a-A0", "PO3a-A1", "PO3a-B", "PO3a.4", "PO3a-A", "PO3a", "H-bridge.11"]
address_status: "active"
blocker: "Двумерная antiderivative-экстракция реального дефекта"
collections: ["q3_docs"]
tags: ["po3", "boundary", "antiderivative"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: []
strong_terms: ["двумерная antiderivative-экстракция (two-variable antiderivative extraction)", "смешанная разность (mixed difference)", "граничная полоса (boundary strip)"]
empty_terms: ["общая красивая final formula"]
false_friend_terms: ["сразу угадывать полный Volterra вид"]
opens_new_branch_terms: ["double telescoping"]
neighbor_addresses: ["PO3a.4"]
---

# PO3a-A0 — Двумерная antiderivative-экстракция реального дефекта

## Статус

- серия запросов проведена;
- новый подузел `PO3a-A0` подтверждён как самостоятельный.

## Точный блокер

Двумерная antiderivative-экстракция реального дефекта

## Почему этот поиск нужен сейчас

Без двумерной antiderivative-экстракции `PO3a-A` остаётся только общим
лозунгом про transported Volterra form. Нужно было проверить, не лежит ли где-то
внутри проекта уже готовая формула вида
`дефект = corner + row-strip + column-strip + T^*(mixed difference)T`,
или хотя бы близкий аналог, чтобы не изобретать её повторно.

## Что уже известно по этому адресу

- в заметке `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md` уже есть
  antiderivative-якорь
  `I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N`;
- там же уже зафиксирован endpoint-дефект undoing-оператора:
  `D_a I_0^{(a)} = I`, но `I_0^{(a)}D_a = I - R_a`;
- уже доказанный в Lean shell шаг `po3_two_endpoint_expansion` закрывает
  чистую алгебру раскрытия
  `((I-R)^*K(I-R)-K)`;
- честно не хватает именно двумерной общей формулы экстракции дефекта на
  `corner + row-strip + column-strip + bulk`.

## Что именно мы хотим узнать поиском

- есть ли в проекте уже сформулированная общая двумерная telescoping-формула;
- есть ли в reviewed notes более ранний узел, где bulk mixed difference уже
  выделяется отдельно от граничных полос;
- какие слова лучше всего ведут именно к этому подшагу, а какие уводят назад в
  общий `PO3`-туман.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a-A0 double telescoping two-variable defect boundary strip corner mixed difference` | `PO3a-A0` | Проверить, не зафиксирован ли уже точный theorem-packet для двумерной экстракции | адресный узел → полная формула | weak | дал только общие `PO3`/`INSIGHTS`, готовой формулы не нашлось |
| `double Newton Leibniz discrete defect row strip column strip corner` | `PO3a-A0` | Проверить соседние формулировки через Newton–Leibniz, а не через Volterra | telescoping ↔ Newton–Leibniz | medium | вернул в `PO3`-заметку и row/column reduction; отдельного A0-узла в архиве нет |
| `PO3a mixed interior difference boundary correction finite row column support` | `PO3a-A0` | Проверить связь с уже существующим finite receiver | bulk mixed difference → finite receiver | strong | подтвердил, что ближайший живой сосед — это текущая `PO3`-ветка и shell-файл |
| внешний web-поиск: `two-dimensional summation by parts discrete telescoping identity mixed difference` | `PO3a-A0` | Быстрый внешний sanity-check на стандартность формулы | локальный язык ↔ внешний словарь | noise | полезного внешнего якоря не дал |

## Пустые / шумовые слова

- `общая красивая final formula`;
- слишком общий `PO3`;
- слишком общий `boundary correction`.

## Новые возможные комбинации слов

- `двумерное телескопирование (double telescoping)`;
- `смешанная внутренняя разность (mixed interior difference)`;
- `граничная полоса + угол (boundary strip + corner)`;
- `дискретный Newton–Leibniz для дефекта`.

## Переход в INSIGHTS

- добавить краткий синтез про новый подузел `PO3a-A0` и его роль как общего
  слоя перед подстановкой `(I-R_a)^*K_a(I-R_a)-L_a`.

## Следующий адресный шаг

- `PO3a-A1`: подставить в общую формулу реальный дефект и вычислить его
  смешанную внутреннюю разность;
- затем вернуть `PO3a-B` как зануление zero-endpoint bulk-части.
