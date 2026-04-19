---
status: "active"
date: "2026-04-19"
main_address: "PO3-shell.5"
related_addresses: ["PO3-shell", "PO3-shell.4", "PO3Cert"]
ancestor_addresses: ["PO3-shell.4"]
child_or_next_addresses: ["PO3-shell.6"]
raw_address_notation: "PO3-shell.5, PO3-shell.4, PO3-shell, PO3Cert"
normalized_addresses: ["PO3-shell.5", "PO3-shell.4", "PO3-shell", "PO3Cert", "PO3-shell.6"]
address_status: "active"
blocker: "Вынести named kernel-family predicate для tagged first-zeta packet и повесить на него готовые shell-theorems без ручного hpacket : ∃ tag, ..."
collections: ["q3_docs"]
tags: ["po3", "shell", "kernel_family", "api", "witness_stack"]
insight_links: []
request_nodes: []
strong_terms: ["named kernel family predicate", "first zeta initial packet kernel", "no filtered candidate on family predicate"]
empty_terms: []
false_friend_terms: []
opens_new_branch_terms: ["kernel family api"]
neighbor_addresses: []
---

# PO3-shell.5 — Вынести named kernel-family predicate для tagged first-zeta packet и повесить на него готовые shell-theorems без ручного hpacket : ∃ tag, ...

## Статус

- карточка создана;
- search-pass уже выполнен;
- кодовый шаг ещё не начат.

## Точный блокер

Вынести named kernel-family predicate для tagged first-zeta packet и повесить на него готовые shell-theorems без ручного hpacket : ∃ tag, ...

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3-shell.5`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- в `FirstZetaWitnessStack_2026_04_19.lean` уже есть transport-layer на
  произвольный `K`:
  `po3_no_filtered_candidate_of_exists_eq_first_zeta_initial_packet_raw`
  и contradiction theorem
  `po3_false_of_exists_eq_first_zeta_initial_packet_raw_and_filtered_candidate`;
- текущая дыра теперь только интерфейсная:
  пользовательский shell-код всё ещё должен явно носить
  `hpacket : ∃ tag, K = po3_first_zeta_initial_packet_raw tag`;
- естественный следующий слой — назвать это семейство kernels отдельным
  `Prop`-предикатом и переэкспортировать уже готовые убийцы на этом уровне.

## Что именно мы хотим узнать поиском

- какие формулировки уже были бесполезны;
- какие слова могут открыть соседнюю живую ветку;
- какие локальные теоремы или reviewed notes реально усиливают `PO3-shell.5`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3 shell named kernel family predicate first zeta packet theorem not exists filtered candidate` | `PO3-shell.5` | Проверить, нет ли уже готового wrapper-предиката для family of kernels | API wrapper shape | weak | Готового named predicate не найдено; слой ещё не вынесен |
| `named predicate for witness family kernel shell consumer theorem contradiction` | `PO3-shell.5` | Проверить, есть ли уже theorem-слой именно на predicate-уровне | consumer API | weak | Есть только theorem на `∃ tag`, но не на именованном family predicate |
| `exists tag raw packet wrapped as predicate downstream shell api` | `PO3-shell.5` | Проверить, не встречалась ли такая упаковка в соседних ветках | abstraction / naming | weak | Соседнего шаблона в локальной базе не нашлось; значит делаем минимальный local API |
| `Lean predicate wrapper existential theorem reuse equality rewriting` | `PO3-shell.5` | Внешне проверить, что минимальный путь — `def ... : Prop` + reuse existing theorems | Lean implementation shape | strong | Официальные Lean docs подтверждают, что здесь достаточно named `Prop`, `rw` и `Exists` elimination |

## Пустые / шумовые слова

- `transport theorem` без `predicate` возвращает к уже закрытому `PO3-shell.4`;
- `kernel family` без `first zeta` слишком общий и уводит в другие packet-ветки.

## Новые возможные комбинации слов

- `named kernel family predicate`
- `first zeta initial packet kernel`
- `no filtered candidate on family predicate`
- `kernel family api`

## Переход в INSIGHTS

- синтез записан в `q3.lean.aristotle/docs/INSIGHTS.md`.

## Следующий адресный шаг

- определить named predicate for the initial first-zeta kernel family;
- поднять на него negated-existential и contradiction theorems;
- после этого открыть `PO3-shell.6` как финальную API-зачистку локального shell.
