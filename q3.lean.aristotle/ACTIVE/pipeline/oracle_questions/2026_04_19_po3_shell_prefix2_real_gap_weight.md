---
status: "active"
date: "2026-04-19"
main_address: "PO3-shell"
related_addresses: ["PO3Cert", "PO3-prefix2"]
ancestor_addresses: ["PO3", "PO2-shell"]
child_or_next_addresses: ["PO3-shell.1"]
raw_address_notation: "PO3-shell, PO3Cert, PO3-prefix2"
normalized_addresses: ["PO3-shell", "PO3Cert", "PO3-prefix2", "PO3", "PO2-shell", "PO3-shell.1"]
address_status: "active"
blocker: "Доказать theorem-level ненулевость manuscript gap sum2 при a = 1 через π-оценки и знак реального gap-weight"
collections: ["q3_docs"]
tags: ["po3", "shell", "prefix2", "gap_sum2", "pi_bounds"]
insight_links: []
request_nodes: []
strong_terms: ["manuscript gap sum2", "anti-diagonal gap 20 11", "pi bounds", "sin squared positivity"]
empty_terms: []
false_friend_terms: []
opens_new_branch_terms: ["gap weight positivity"]
neighbor_addresses: ["PO2-shell"]
---

# PO3-shell — Доказать theorem-level ненулевость manuscript gap sum2 при a = 1 через π-оценки и знак реального gap-weight

## Статус

- карточка создана;
- серия запросов ещё не отработана полностью.

## Точный блокер

Доказать theorem-level ненулевость manuscript gap sum2 при a = 1 через π-оценки и знак реального gap-weight

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3-shell`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- в shell уже есть точные мосты
  `po3_suzuki_raw_gamma_pm_prefix2_antidiagonal_gap_20_11`,
  `po3_no_suzuki_raw_gamma_pm_prefix2_of_gap_sum2_ne_zero`
  и именованный объект
  `po3_first_zeta_gap_sum2_a1_decimal28`;
- singleton-ветка для `γ₀,γ₁,γ₂` уже formalized в `PO3Cert`, но она не
  закрывает `prefix2`, потому что там остаётся возможная cross-mode
  cancellation;
- значит живой минимальный brick теперь один:
  theorem-level ненулевость двухчленной суммы `gap_sum2` при `a = 1`.

## Что именно мы хотим узнать поиском

- какие формулировки уже были бесполезны;
- какие слова могут открыть соседнюю живую ветку;
- какие локальные теоремы или reviewed notes реально усиливают `PO3-shell`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `po3 manuscript gap sum2 a=1 pi bounds real positivity prefix2` | `PO3-shell` | Проверить, нет ли уже готового bridge от named `gap_sum2` к real-оценкам | named shell object | strong | Вернул `HBridge_PO3_Shell` и `INSIGHTS`: shell уже готов, нужен не новый bridge, а одна real-лемма |
| `gap term 20 11 positivity x > 3 pi manuscript` | `PO3-shell` | Выяснить, можно ли бить напрямую через знак одного six-pole gap term | знак рациональной функции | strong | Вернул `po3_suzuki_filtered_pm_gap_term_20_11_ne_zero` и shell-gap stack; следующий ход — усиливать из `≠ 0` в знак/вещественную положительность |
| `first zeta gamma0 gamma1 pi bounds positivity a=1` | `PO3-shell` | Проверить, есть ли в локальной базе уже готовая привязка первых ordinates к `π`-окнам | конкретные witness-значения | weak | Почти пусто; это честно говорит, что интервальный мост для `γ₀,γ₁` надо строить самим |
| `pi_gt_d20 pi_lt_d20 manuscript alpha step gap weight` | `PO3-shell` | Проверить готовность numerical `π`-bounds в mathlib / shell | источник констант | strong | Подтверждено: `Real.pi_gt_d20`, `Real.pi_lt_d20` доступны и естественно садятся на `a = 1`, `α = π` |

## Пустые / шумовые слова

- `first zeta gamma0 gamma1 positivity` без упоминания `gap term` или `pi bounds` даёт шум;
- слишком общий `prefix2 positivity` не держит адрес и уводит в старые shell-описания.

## Новые возможные комбинации слов

- `gap weight positivity`
- `real six-pole sign`
- `x > 3π`
- `prefix2 real interval witness`
- `π-bounds + γ-window + manuscript gap`

## Переход в INSIGHTS

- синтез этого search-pass фиксируется в `q3.lean.aristotle/docs/INSIGHTS.md`
  как in-progress план для `PO3-shell`.

## Следующий адресный шаг

- `PO3-shell.1`:
  построить минимальную real-lemma для `a = 1`, где один `gap_weight`
  получает фиксированный знак на явном `π`-окне, а затем проверить, хватает ли
  этого уже для `po3_first_zeta_gap_sum2_a1_decimal28 ≠ 0`.
