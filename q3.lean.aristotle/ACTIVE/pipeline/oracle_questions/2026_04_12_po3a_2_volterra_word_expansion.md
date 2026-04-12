---
status: "active"
date: "2026-04-12"
main_address: "PO3a.2"
related_addresses: ["PO3a.3", "PO3a.4"]
ancestor_addresses: ["PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a.3"]
raw_address_notation: "PO3a.2, 3, 4, 5; H-bridge.11; PO3a"
normalized_addresses: ["PO3a.2", "PO3a.3", "PO3a.4", "PO3a.5", "H-bridge.11", "PO3a"]
address_status: "active"
blocker: "Разложение граничной поправки в конечное число вольтерровых слов"
collections: ["q3_docs", "math_papers"]
tags: ["po3", "boundary", "volterra_word", "endpoint_projector"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md"]
strong_terms: ["граничное слово (boundary word)", "критерий допуска в вольтерров класс (Volterra-word admission criterion)"]
empty_terms: ["общая граничная алгебра (boundary algebra) без адреса"]
false_friend_terms: ["полная физическая вольтеррова нормальная форма как первый шаг"]
opens_new_branch_terms: ["слабый вольтерров мост (weaker Volterra bridge)"]
neighbor_addresses: ["PO3a.3", "PO3a.4", "PO3a.5"]
---

# PO3a.2 — Разложение граничной поправки в конечное число вольтерровых слов

## Статус

- карточка активна;
- это рабочая память для серии запросов вокруг `PO3a.2`.

## Точный блокер

Нужно не полное чудо, а точный слабый вольтерров мост:
показать, что настоящая граничная поправка раскладывается в конечную сумму
вольтерровых слов с конечным числом концевых проекторов, после чего включается
конечный приёмник.

## Почему этот поиск нужен сейчас

На этом адресе есть риск зациклиться между двумя слишком большими целями:
“полная физическая вольтеррова нормальная форма” и “общая формула граничной
поправки”. По состоянию маршрута это неверная постановка. Для `PO3a.2` нужен
более дешёвый и честный вопрос: хватает ли конечного счёта концевых проекторов
и критерия допуска в вольтерров класс, чтобы дойти до `PO3a.3`.

## Что уже известно по этому адресу

- Есть первый честный кандидат на источник граничного слоя:
  антидифференциальная факторизация с дефектом конца
  `R_a = 1 \otimes \operatorname{ev}_{-a}`.
- Левый выход через `R_a` частично умирает точно:
  `T_{a,\infty,N}^{+*} 1 = 0` и `T_{a,\infty,N}^{-*} 1 = 0` по ортогональности
  Фурье.
- Справа концевой функционал уже раскалывается по знаку:
  `\operatorname{ev}_{-a} \circ T_{a,\infty,N} = \ell_{+,N} P_+ + \ell_{-,N} P_-`.
- Значит живой объект здесь уже не “вся облачная граничная алгебра”, а
  конечное число слов с одним или двумя концевыми проекторами.
- Решающий decision note из `INSIGHTS`: не брать полную физическую
  вольтеррову нормальную форму как первый подшаг; сначала нужен более слабый
  мост.
- Первый боевой oracle-проход по `q3_docs` уже подтвердил эту настройку:
  все четыре локальные запроса возвращают один и тот же late packet,
  а именно связку
  `raw antiderivative factorization -> finite endpoint-projector count ->
  Volterra-word admission -> endpoint receiver`,
  плюс оболочку
  `Q3/Proofs/HBridge_PO3_Shell.lean`.
- Короткий внешний sanity-check не дал готовой внешней теоремы для этого
  ослабленного моста; значит route остаётся внутренним, а не literature-plug-in.

## Что именно мы хотим узнать поиском

- Какие формулировки уже возвращают ровно этот ослабленный мост, а не уводят
  назад к полной физической форме.
- Где у нас уже зафиксированы слова про
  “концевой проектор”, “счёт концов”, “допуск в вольтерров класс”.
- Какие запросы лучше поднимают именно `PO3a.2`, а какие надо переносить
  вверх на `H-bridge.11`.
- Какие reviewed notes или request nodes уже содержат пригодную формулировку
  для теоремы вида “конечная сумма вольтерровых слов”.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a.2 Volterra-word admission criterion endpoint projector` | `PO3a.2` | Поднять точную формулировку критерия допуска в вольтерров класс | boundary formula → admission criterion | strong hit | вернул `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md` и late note про `PO3a-Volterra-word admission criterion` |
| `weaker Volterra bridge finite endpoint-projector count PO3a.2` | `PO3a.2` | Проверить, где уже зафиксирован слабый вольтерров мост | full physical form → weaker bridge | strong hit | вернул decision note: active mainline уже зафиксирован как `raw antiderivative factorization -> finite endpoint-projector count -> Volterra-word admission -> endpoint receiver` |
| `raw antiderivative factorization endpoint defect R_a PO3a.2` | `PO3a.2` | Вернуть локальную антидифференциальную механику | factorization → endpoint defect | hit | вернул exact algebraic rewriting и снова свёл всё к тому же `PO3a`-пакету |
| `PO3a.3 zero-mode column from PO3a.2 endpoint split` | `PO3a.2` | Проверить, как быстро этот адрес передаёт управление в `PO3a.3` | boundary words → one-vector test | hit | вернул zero-mode collapse packet и `Q3/Proofs/HBridge_PO3_Shell.lean` как формальный потребитель |

## Пустые / шумовые слова

- `generic boundary algebra`
- `physical Volterra normal form` без слова `weaker`
- слишком широкое `commutator cloud`
- общий `boundary formula` без `endpoint projector`
- короткий внешний поиск без наших внутренних словарей: сигнала на готовую
  внешнюю теорему не дал

## Новые возможные комбинации слов

- `граничное слово + концевой проектор`
- `слабый вольтерров мост + счёт концов`
- `антидифференциальная факторизация + дефект конца`
- `Volterra-word admission criterion + PO3a.2`

## Переход в INSIGHTS

- После серии нужно оставить короткий синтез в `docs/INSIGHTS.md` с явной
  пометкой адреса `PO3a.2`.
- В синтезе отдельно записать:
  какие слова реально возвращают ослабленный мост,
  а какие каждый раз заворачивают к полной физической форме.
- Первый такой синтез уже добавлен 2026-04-12 после боевого oracle-прохода.

## Следующий адресный шаг

- Если слабый вольтерров мост подтверждается, прямой следующий адрес — `PO3a.3`.
- Если поиск упирается в верхний мост, подниматься на `H-bridge.11`.
- Если снова всплывает только полная физическая форма, пометить это как ложный
  первый удар, а не как mainline.
