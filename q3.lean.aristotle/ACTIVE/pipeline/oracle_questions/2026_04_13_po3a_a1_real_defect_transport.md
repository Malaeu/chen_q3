---
status: "active"
date: "2026-04-13"
main_address: "PO3a-A1"
related_addresses: ["PO3a-A0", "PO3a-B", "PO3a.4"]
ancestor_addresses: ["PO3a-A", "PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a-B"]
raw_address_notation: "PO3a-A1; PO3a-A0; PO3a-B; PO3a.4"
normalized_addresses: ["PO3a-A1", "PO3a-A0", "PO3a-B", "PO3a.4", "PO3a-A", "PO3a", "H-bridge.11"]
address_status: "active"
blocker: "Подстановка реального дефекта в A0 и выделение bulk mixed difference"
collections: ["q3_docs"]
tags: ["po3", "boundary", "transport"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: []
strong_terms: ["реальный дефект (real defect)", "смешанная внутренняя разность (mixed interior difference)", "угол + строка + столбец (corner + row strip + column strip)"]
empty_terms: ["снова обсуждать только outer operators"]
false_friend_terms: ["искать сразу полный final Volterra вид"]
opens_new_branch_terms: ["raw defect bulk boundary cap split"]
neighbor_addresses: ["PO3a.4"]
---

# PO3a-A1 — Подстановка реального дефекта в A0 и выделение bulk mixed difference

## Статус

- серия запросов проведена;
- `PO3a-A1` подтверждён как отдельный подузел между `A0` и `B`.

## Точный блокер

Подстановка реального дефекта в A0 и выделение bulk mixed difference

## Почему этот поиск нужен сейчас

После формализации общего `A0`-пакета следующий вопрос уже не общий:
нужно понять, как именно настоящий дефект вставляется в формулу
`corner + row strip + column strip + bulk`, и где потом появляется
`(I-R_a)^*K_a(I-R_a)-L_a`.

## Что уже известно по этому адресу

- ранний слой заметки уже говорит не о guessed final formula, а о split
  `raw defect = bulk + boundary + cap`;
- новый Lean-пакет `po3_double_telescoping` уже даёт общий дискретный приёмник
  `corner + row strip + column strip + bulk mixed difference`;
- значит `A1` — это именно подстановка реального дефекта в этот приёмник и
  последующее отождествление bulk-слагаемого.

## Что именно мы хотим узнать поиском

- есть ли в проекте уже более ранняя формулировка raw/bulk/boundary/cap split
  именно для настоящего дефекта;
- есть ли уже замороженное место, где row-strip / column-strip traces выписаны
  отдельно;
- какие формулировки ведут к real defect transport, а какие опять уводят в
  обсуждение одних только `U,V`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a-A1 real defect mixed interior difference endpoint strips corner` | `PO3a-A1` | Найти уже существующий пакет подстановки реального дефекта | real defect → mixed difference | medium | вернул текущую `PO3`-заметку, но готового отдельного theorem-packet не нашлось |
| `PO3a real defect row strip column strip corner transported Volterra form` | `PO3a-A1` | Проверить, не зафиксирован ли уже переход `A0 -> transported bulk + boundary` | full transport wording | weak | дал implementation-plan и общие ссылки, без готовой формулы |
| `I_0^(a) D_a I-R_a real defect bulk mixed difference boundary strip` | `PO3a-A1` | Проверить, не есть ли уже связка через `I_0^{(a)}` и `R_a` | antiderivative undoing → real defect traces | medium | вернул общие boundary/bulk split notes, но не отдельный `A1`-узел |
| `rg` по заметке: `raw defect`, `bulk + boundary + cap`, `split the raw defect` | `PO3a-A1` | Найти самый ранний внутренний язык этой подстановки | search by project vocabulary | strong | нашёл ранний фрагмент, где реальный lower-shell task формулируется именно как split raw defect и потом pull through `Δ_N` |

## Пустые / шумовые слова

- `outer operators` без слова `defect`;
- `final Volterra normal form` без слова `raw defect`;
- слишком общий `boundary correction`.

## Новые возможные комбинации слов

- `raw defect bulk + boundary + cap`;
- `pull raw split through Δ_N`;
- `mixed interior difference of real defect`;
- `transported bulk + boundary packet`.

## Переход в INSIGHTS

- добавить короткий синтез: `A1` — это не поиск `U,V`, а мост от
  `po3_double_telescoping` к transported bulk plus boundary form.

## Следующий адресный шаг

- добавить в Lean shell abstract theorem:
  если row-strip, column-strip и corner собраны в граничный пакет, а bulk
  mixed difference отождествлена с transported bulk, то весь дефект имеет вид
  `boundary + bulk`;
- после этого переходить к `PO3a-B`.
