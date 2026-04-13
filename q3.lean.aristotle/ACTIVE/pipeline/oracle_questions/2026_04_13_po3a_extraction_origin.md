---
status: "active"
date: "2026-04-13"
main_address: "PO3a-A"
related_addresses: ["PO3a.2", "PO3a-B", "PO3a.4", "H-bridge.11"]
ancestor_addresses: ["PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a-B", "PO3a.2"]
raw_address_notation: "PO3a-A; PO3a.2; PO3a-B; PO3a.4; H-bridge.11"
normalized_addresses: ["PO3a-A", "PO3a.2", "PO3a-B", "PO3a.4", "H-bridge.11", "PO3a"]
address_status: "active"
blocker: "Вывести внешний слой U_j,V_j из настоящей разности как конечную антидифференциальную extraction-форму"
collections: ["q3_docs"]
tags: ["po3", "extraction", "volterra", "outer_layer"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: []
strong_terms: ["конечная антидифференциальная экстракция (finite antiderivative extraction)", "сырая антидифференциальная факторизация (raw antiderivative factorization)"]
empty_terms: ["полная physical normal form"]
false_friend_terms: ["искать U_j,V_j как заранее заданные операторы"]
opens_new_branch_terms: ["настоящая разность -> внешний слой"]
neighbor_addresses: ["PO3a.4"]
---

# PO3a-A — Вывести внешний слой U_j,V_j из настоящей разности как конечную антидифференциальную extraction-форму

## Статус

- карточка создана;
- серия запросов ещё не отработана полностью.

## Точный блокер

Вывести внешний слой U_j,V_j из настоящей разности как конечную антидифференциальную extraction-форму

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3a-A`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- поздний пакет уже жёстко фиксирует, что `PO3a-A` — это не полная physical
  Volterra normal form, а только конечная антидифференциальная экстракция
  реальной разности;
- самый ранний точный внутренний якорь сейчас такой:
  `I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N`;
  значит sign-геометрия чиста уже на antiderivative-стороне, а boundary-дефект
  должен рождаться только при “Volterra undoing”;
- следующий формальный дефект уже тоже зафиксирован:
  `D_a I_0^{(a)} = I`, но
  `I_0^{(a)}D_a = I - R_a`,
  где `R_a` — rank-one endpoint projector;
- в текущих reviewed notes `U_j,V_j` пока не найдены как уже вычисленные
  реальные операторы; самый ранний слой, где они вообще входят, это уже
  theorem-target `PO3a-finite antiderivative mismatch criterion`;
- значит честная upstream-цель сейчас не “доказать harmlessness of known
  outer factors”, а “получить сам word-level extraction из реальной разности”.

## Что именно мы хотим узнать поиском

- есть ли где-то выше по ветке уже готовая формула, которая переносит bulk-
  сравнение на antiderivative-сторону;
- можно ли извлечь `PO3a-A` прямо из связки
  `I_0^{(a)}S = T\Delta` и `I_0^{(a)}D_a = I - R_a`;
- где именно в текущем тексте должен появиться middle kernel `L_j`,
  отвечающий за bulk-часть без endpoint-вставок.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a-A finite antiderivative extraction real difference outer layer` | `PO3a-A` | Подтвердить, что живой блокер уже сместился именно в extraction-слой | downstream receiver → upstream extraction | strong hit | вернул late `INSIGHTS` и сам `PO3a-A` как новый честный узел |
| `raw antiderivative factorization boundary correction endpoint counting` | `PO3a-A` | Проверить, есть ли готовая локальная антидифференциальная механика | raw factorization → endpoint counting | hit | снова поднял `PO3`-пакет и decision note про weaker bridge |
| `PO3a-A U_j V_j extraction from genuine boundary defect` | `PO3a-A` | Найти более раннее место появления внешнего слоя | actual origin → theorem-target origin | strong hit | показал, что самый ранний слой появления `U_j,V_j` — уже `PO3a-finite antiderivative mismatch criterion` |
| `H-bridge.11 weaker Volterra bridge raw difference extraction` | `H-bridge.11` | Проверить upstream-соседа на готовую формулу для extraction | upper bridge → actual formula | partial hit | подтвердил mainline `raw antiderivative factorization -> finite endpoint-projector count -> admission`, но новой формулы не дал |
| `PO3a-B zero-endpoint cancellation finite antiderivative extraction` | `PO3a-B` | Уточнить, где должен жить bulk-остаток без endpoint-вставок | extraction → zero-endpoint split | strong hit | ещё раз подтвердил точное разбиение `PO3a-A + PO3a-B` |

## Пустые / шумовые слова

- `полная physical normal form` как первый шаг
- поиск `U_j,V_j` как будто они уже заранее построены
- слишком общий `Volterra operators` без слов `antiderivative` и `endpoint`

## Новые возможные комбинации слов

- `Volterra undoing -> endpoint-word span`
- `antiderivative side -> endpoint defect`
- `real difference -> finite endpoint-projector count`
- `transport bulk comparison to the antiderivative side`

## Переход в INSIGHTS

- синтез добавлен в `q3.lean.aristotle/docs/INSIGHTS.md`:
  новый вывод по `PO3a-A` состоит в том, что upstream-источник внешнего слоя
  надо искать через antiderivative-factorization и defect `I_0^{(a)}D_a=I-R_a`,
  а не через поиск уже готовых операторов `U_j,V_j`.

## Следующий адресный шаг

- формально заморозить промежуточный theorem-target:
  нужно перенести и Suzuki-часть, и `Q_\infty`-часть на antiderivative-сторону,
  а потом развернуть только endpoint-defect `R_a,R_a^*`;
- после этого станет ясно, чем именно должен играть `L_j` в
  `PO3a-finite antiderivative mismatch criterion`.
