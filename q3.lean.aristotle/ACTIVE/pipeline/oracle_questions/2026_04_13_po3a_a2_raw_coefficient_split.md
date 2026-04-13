---
status: "active"
date: "2026-04-13"
main_address: "PO3a-A2"
related_addresses: ["PO3a-A1", "PO3a-B", "PO3a.4"]
ancestor_addresses: ["PO3a-A", "PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a-B"]
raw_address_notation: "PO3a-A2; PO3a-A1; PO3a-B; PO3a.4"
normalized_addresses: ["PO3a-A2", "PO3a-A1", "PO3a-B", "PO3a.4", "PO3a-A", "PO3a", "H-bridge.11"]
address_status: "active"
blocker: "Сырой коэффициентный split для δ_{r,s}(a)"
collections: ["q3_docs"]
tags: ["po3", "boundary", "raw-defect"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: []
strong_terms: ["сырая коэффициентная разность (raw coefficient difference)", "Toeplitz-часть (Toeplitz part)", "двухполюсная структура (two-pole structure)"]
empty_terms: ["снова обсуждать только filtered defect"]
false_friend_terms: ["искать bulk сразу после фильтрации"]
opens_new_branch_terms: ["entrywise raw split"]
neighbor_addresses: ["PO3a.4"]
---

# PO3a-A2 — Сырой коэффициентный split для δ_{r,s}(a)

## Статус

- серия запросов проведена;
- новый узел `PO3a-A2` подтверждён как следующий честный уровень после `A1`.

## Точный блокер

Сырой коэффициентный split для δ_{r,s}(a)

## Почему этот поиск нужен сейчас

После `A0` и `A1` остался уже не общий транспорт, а сама формула сырой
разности `δ_{r,s}(a)`. Если не понять её структурно, то цепочка опять
остановится на абстрактных пакетах без реального bulk/boundary/cap split.

## Что уже известно по этому адресу

- `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md` уже фиксирует
  точную связь
  `\mathcal D_{a,N} = \Delta_N^* \mathcal R_{a,N}^{raw} \Delta_N`;
- там же
  `\delta_{r,s}(a) = w_{r,s}(a) - \kappa(a) q_{r,s}`;
- `src/h1_raw_bulk_match.py` поднимает реальные численные формулы:
  `q_{r,s}` зависит только от `r-s`, а `w_{r,s}(a)` построен из двух полюсов
  `(\gamma-\alpha_r)^{-1}` и `(\gamma+\alpha_s)^{-1}`;
- значит следующий реальный вопрос — как из этой разности выделить сырые
  `bulk`, `boundary`, `cap` каналы.

## Что именно мы хотим узнать поиском

- есть ли уже в проекте явный split для `δ_{r,s}(a)`;
- есть ли вычислительный артефакт, который уже отделяет Toeplitz bulk от
  near-edge / cap contribution;
- какие слова правильно описывают следующий theorem-target.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a-A2 raw coefficient difference delta r s bulk boundary cap split` | `PO3a-A2` | Найти готовый theorem-packet для разности коэффициентов | coefficient defect → operator split | weak | вернул только текущие `PO3` / `INSIGHTS`, отдельного `A2`-узла нет |
| `delta_{r,s}(a) w_{r,s}(a) kappa(a) q_{r,s} raw defect split` | `PO3a-A2` | Проверить, фиксировался ли raw split прямо по коэффициентам | explicit delta formula | weak | отдельной формулы не нашлось |
| `raw defect bulk boundary cap delta r s filtered pullback` | `PO3a-A2` | Найти переход именно от coefficient split к filtered operator | raw split → filtered split | medium | подтвердил, что проект уже жёстко стоит на языке `split raw defect, then pull through Δ_N` |
| `w_{r,s}(a) q_{r,s} coefficient formula boundary zone` | `PO3a-A2` | Поднять живые вычислительные формулы `w` и `q` | note language ↔ code language | strong | привёл к `src/h1_raw_bulk_match.py`, где `q_{r,s}` Toeplitz по `r-s`, а `w_{r,s}(a)` имеет двухполюсную структуру |

## Пустые / шумовые слова

- `filtered defect` без слова `raw`;
- `shared finite-rank basis`;
- `outer operators` без слова `delta`.

## Новые возможные комбинации слов

- `entrywise raw split`;
- `Toeplitz part + two-pole remainder`;
- `raw coefficient boundary zone`;
- `delta_{r,s} bulk boundary cap`.

## Переход в INSIGHTS

- добавить краткий синтез: `A2` — это уже coefficient-level classification of
  `δ_{r,s}(a)`, а не новый transport shell.

## Следующий адресный шаг

- добавить abstract shell: если `δ_{r,s}` раскалывается entrywise на три
  канала, то сырой и фильтрованный операторы автоматически раскалываются так же;
- затем искать уже не форму shell, а реальное правило, по которому `δ_{r,s}`
  попадает в bulk/boundary/cap.
