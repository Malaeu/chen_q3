---
status: "done"
date: "2026-04-19"
main_address: "PO3-shell.4"
related_addresses: ["PO3-shell", "PO3-shell.3", "PO3Cert"]
ancestor_addresses: ["PO3-shell.3"]
child_or_next_addresses: ["PO3-shell.5"]
raw_address_notation: "PO3-shell.4, PO3-shell.3, PO3-shell, PO3Cert"
normalized_addresses: ["PO3-shell.4", "PO3-shell.3", "PO3-shell", "PO3Cert", "PO3-shell.5"]
address_status: "active"
blocker: "Дать transport-theorem на произвольный shell-kernel K: если K совпадает с tagged first-zeta packet, то K не может быть filtered (+,-) candidate"
collections: ["q3_docs"]
tags: ["po3", "shell", "transport", "kernel", "witness_stack"]
insight_links: ["docs/insights/h1_po3_first_zeta_witness_stub_2026_04_19.md"]
request_nodes: []
strong_terms: ["kernel transport theorem", "exists tag K equals raw packet", "not exists filtered candidate"]
empty_terms: []
false_friend_terms: []
opens_new_branch_terms: ["shell kernel transport"]
neighbor_addresses: []
---

# PO3-shell.4 — Дать transport-theorem на произвольный shell-kernel K: если K совпадает с tagged first-zeta packet, то K не может быть filtered (+,-) candidate

## Статус

- карточка закрыта как `done`;
- search-pass выполнен;
- кодовый шаг завершён и собран.

## Точный блокер

Дать transport-theorem на произвольный shell-kernel K: если K совпадает с tagged first-zeta packet, то K не может быть filtered (+,-) candidate

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3-shell.4`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- в `Q3/Proofs/PO3Cert/FirstZetaWitnessStack_2026_04_19.lean` уже есть прямой
  bridge:
  `po3_first_zeta_initial_packet_raw_ne_filtered_candidate` и его
  collapsed existential form
  `po3_no_tagged_first_zeta_initial_packet_eq_filtered_candidate`;
- текущая дыра теперь выше уровнем: downstream shell-узлы живут на произвольном
  kernel `K`, и им нужен готовый transport-theorem из гипотезы
  `K = po3_first_zeta_initial_packet_raw tag`;
- `Q3/Proofs/HBridge_PO3_Shell.lean` уже полностью закрывает generic сторону
  `po3_suzuki_filtered_pm_candidate`, так что новый узел остаётся чисто
  интерфейсным equality-transport слоем.

## Что именно мы хотим узнать поиском

- какие формулировки уже были бесполезны;
- какие слова могут открыть соседнюю живую ветку;
- какие локальные теоремы или reviewed notes реально усиливают `PO3-shell.4`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3 shell transport theorem exists tag K equals raw packet not exists filtered candidate` | `PO3-shell.4` | Проверить, нет ли уже готового theorem над произвольным `K` | theorem transport shape | weak | Готового transport-theorem не найдено; слой ещё не вынесен |
| `first zeta witness stack transport from K eq raw tag to no filtered candidate` | `PO3-shell.4` | Проверить, не реализован ли bridge в witness-stack под другим названием | local witness packaging | weak | Найден только прямой bridge на самом raw packet, но не transport на произвольный `K` |
| `direct shell consumer theorem K equals tagged packet contradiction with candidate` | `PO3-shell.4` | Проверить, нужен ли именно contradiction-form | consumer interface | medium | Подтверждено, что следующая разумная форма — theorem для `K`, а не новый raw layer |
| `Lean equality rewrite existential elimination contradiction` | `PO3-shell.4` | Внешне проверить минимальный proof pattern | Lean implementation shape | strong | Официальные Lean docs подтверждают `rw` / `simpa` и устранение `∃` как правильный минимальный путь |

## Пустые / шумовые слова

- `consumer theorem` без `kernel` снова уводит в уже закрытый `PO3-shell.3`;
- `tag bridge` без `K =` слипается с raw-level интерфейсом и не отличает transport-узел.

## Новые возможные комбинации слов

- `kernel transport theorem`
- `exists tag K equals raw packet`
- `not exists filtered candidate`
- `shell kernel transport`

## Переход в INSIGHTS

- синтез записан в `q3.lean.aristotle/docs/INSIGHTS.md`.

## Следующий адресный шаг

- открыть `PO3-shell.5` как следующий consumer-узел уже поверх transport-layer;
- использовать новый API на произвольном `K`, не возвращаясь к raw-family.
