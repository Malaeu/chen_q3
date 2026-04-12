---
status: "active"
date: "2026-04-12"
main_address: "PO3a.3"
related_addresses: ["PO3a.2", "PO3a.4"]
ancestor_addresses: ["PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a.4", "PO3a.5"]
raw_address_notation: "PO3a.3; PO3a.2, 4, 5; H-bridge.11"
normalized_addresses: ["PO3a.3", "PO3a.2", "PO3a.4", "PO3a.5", "H-bridge.11", "PO3a"]
address_status: "active"
blocker: "Знаковая структура одного вектора граничной поправки"
collections: ["q3_docs", "math_papers"]
tags: ["po3", "boundary", "zero_mode", "one_vector"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md"]
strong_terms: ["boundary word", "sign-preserving one-vector test"]
empty_terms: ["generic operator classification"]
false_friend_terms: ["stieltjes monotonicity"]
opens_new_branch_terms: ["physical Volterra normal form"]
neighbor_addresses: ["PO3a.2", "PO3a.4", "PO3a.5"]
---

# PO3a.3 — Знаковая структура одного вектора граничной поправки

## Статус

- карточка активна;
- это рабочая память для серии запросов вокруг `PO3a.3`.

## Точный блокер

После редукции `PO3a` до первого порядка живой вопрос больше не про всю
граничную алгебру сразу. Он локализован в одном векторе:
нужно понять, может ли реальный вектор граничной поправки после действия
оператора `G_g[a]` породить запрещённую cross-sign составляющую, или его знак
вынужденно остаётся чистым.

## Почему этот поиск нужен сейчас

На этом адресе мы уже знаем общую конечномерную схему и конечную матрицу
смешивания. Но это ещё не закрывает шаг: остаётся один локальный вопрос о
знаке одного вектора. Если здесь снова спросить “вообще про boundary algebra”,
оракул уводит нас назад в слишком широкий контекст. Поэтому здесь особенно
важно держать точную формулировку и словарь именно для `PO3a.3`.

## Что уже известно по этому адресу

- `PO3a.1 -> PO3a.5` уже заморожен как жёсткий proof-packet.
- `PO3a.2` теперь сводит граничную поправку к конечному набору кирпичей.
- `PO3a.3` narrowed one step further: живой объект — знаковая структура одного
  вектора, а не полная классификация всех boundary terms.
- Первый порядок уже связан с нулевым режимом
  `v_{a,N} = T_{a,\infty,N}^* G_g[a] 1`, и старый shortcut через “общую
  монотонность” уже убит.
- Главный источник: `q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`.

## Что именно мы хотим узнать поиском

- Какие формулировки лучше всего вытаскивают из нашей базы уже найденные
  локальные reductions про `PO3a.3`, а не возвращают весь `PO3` целиком.
- Есть ли в reviewed notes или старых request nodes точный словарь для
  “одновекторного” знакового теста.
- Какие слова лучше переключают поиск с общей граничной алгебры на
  Volterra-word / endpoint / zero-mode language.
- Какие соседние адреса (`PO3a.2`, `PO3a.4`, `PO3a.5`) уже дают полезные
  зацепки, которые стоит переносить сюда.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a.3 one-vector sign test boundary word` | `PO3a.3` | Сжать поиск до локального векторного brick’а | theorem-packet → one-vector test | planned | должен вернуть поздние секции `PO3a`-note |
| `zero-mode column sign-preserving boundary generator` | `PO3a.3` | Проверить словарь нулевого режима вместо общей boundary algebra | boundary language → zero-mode language | planned | ожидаем связку с первым порядком и `v_{a,N}` |
| `physical Volterra normal form endpoint word sign` | `PO3a.3` | Проверить, помогает ли Volterra-лексика без возврата к полной физической форме | one-vector test → endpoint / Volterra words | planned | должно показать, усиливает ли этот словарь соседнюю ветку |
| `PO3a.2 corrected-column reduction PO3a.3` | `PO3a.3` | Вытянуть ближайший родительский и sibling-контекст | текущий адрес → соседние адреса | planned | нужен мост вверх-вниз по дереву |

## Пустые / шумовые слова

- `generic operator classification`
- слишком широкое `boundary algebra` без адреса
- глобальное `Cauchy injectivity` без привязки к `PO3a.3`

## Новые возможные комбинации слов

- `boundary word + one-vector`
- `zero-mode column + sign-preserving`
- `corrected-column reduction + sign test`
- `physical Volterra normal form + endpoint word`

## Переход в INSIGHTS

- После завершения серии надо оставить короткий синтез в `docs/INSIGHTS.md`
  с явной пометкой адреса `PO3a.3`.
- В итоговом insight должно быть отдельно записано:
  какие слова реально усилили `PO3a.3`,
  а какие только возвращали нас в широкое `PO3`.

## Следующий адресный шаг

- Если локальный sign test закрывается, следующий прямой адрес — `PO3a.4`.
- Если поиск показывает, что нужен возврат к форме кирпичей, откатиться к
  `PO3a.2`, а не к общему `PO3`.
- Если всплывает only physical-word route, отметить это как sibling-pressure на
  `PO3a.3` со связью на `PO3a.4/PO3a.5`.
