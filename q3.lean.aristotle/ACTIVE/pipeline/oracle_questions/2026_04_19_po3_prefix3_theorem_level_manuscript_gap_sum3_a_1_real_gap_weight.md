---
status: "done"
date: "2026-04-19"
main_address: "PO3-prefix3"
related_addresses: ["PO3-shell", "PO3Cert"]
ancestor_addresses: ["PO3-shell"]
child_or_next_addresses: ["PO3-prefix3.1"]
raw_address_notation: "PO3-prefix3, PO3-shell, PO3Cert"
normalized_addresses: ["PO3-prefix3", "PO3-shell", "PO3Cert", "PO3-prefix3.1"]
address_status: "done"
blocker: "Доказать theorem-level ненулевость manuscript gap sum3 при a = 1 через положительность третьего real gap-weight"
collections: ["q3_docs"]
tags: ["po3", "prefix3", "gap_sum3", "gamma2", "pi_bounds"]
insight_links: ["docs/insights/h1_po3_first_zeta_witness_stub_2026_04_19.md"]
request_nodes: []
strong_terms: ["prefix3 honest positivity", "third real gap-weight", "gamma2 > 3 pi"]
empty_terms: []
false_friend_terms: []
opens_new_branch_terms: ["prefix3 real positivity"]
neighbor_addresses: []
---

# PO3-prefix3 — Доказать theorem-level ненулевость manuscript gap sum3 при a = 1 через положительность третьего real gap-weight

## Статус

- карточка закрыта;
- search-pass отработан достаточно для решения узла;
- blocker снят честным theorem-level файлом
  `Q3/Proofs/PO3Cert/FirstZetaPrefix3_2026_04_19.lean`.

## Точный блокер

Доказать theorem-level ненулевость manuscript gap sum3 при a = 1 через положительность третьего real gap-weight

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3-prefix3`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- `prefix2` уже закрыт честно в
  `Q3/Proofs/PO3Cert/FirstZetaPrefix2_2026_04_19.lean`;
- shell-сторона для `prefix3` уже была готова:
  `po3_suzuki_manuscript_gap_sum3`,
  `po3_no_suzuki_raw_gamma_pm_prefix3_of_gap_sum3_ne_zero`,
  `po3_no_suzuki_raw_gamma_pm_prefix3_of_first_zeta_decimal28_witness`;
- singleton-узел для `γ₂` уже был закрыт честно в
  `FirstZetaSingleton_2026_04_19.lean`;
- значит живой brick был узким:
  доказать положительность третьего manuscript gap-weight и тем самым
  ненулевость всей трёхчленной суммы.

## Что именно мы хотим узнать поиском

- какие формулировки уже были бесполезны;
- какие слова могут открыть соседнюю живую ветку;
- какие локальные теоремы или reviewed notes реально усиливают `PO3-prefix3`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `po3 prefix3 gap_sum3 a=1 honest positivity gamma2` | `PO3-prefix3` | Проверить, есть ли в локальной базе отдельная теория именно под трёхчленный witness | named shell object | weak | Ничего лучше уже существующего shell не вернуло; это подтвердило, что нового bridge-theorem не хватает |
| `first zeta gamma2 pi bounds real positivity` | `PO3-prefix3` | Понять, не нужен ли отдельный интервальный пакет для `γ₂` | интервал для третьего witness | medium | По локальному коду стало видно, что достаточно той же схемы `Real.pi_lt_d20` и `sin ≠ 0`, что и для `prefix2` |
| `manuscript gap sum3 real gap weight gamma2` | `PO3-prefix3` | Проверить, есть ли в базе сигнал на новую геометрию или cancellation branch | third weight vs new shell geometry | strong | Поиск и code-reading вместе показали, что `prefix3` = `prefix2` + один дополнительный положительный вес |

## Пустые / шумовые слова

- слишком общий `prefix3 positivity` без `gamma2` и `gap_weight` даёт только старые shell-объяснения;
- общий поиск по `first zeta` шумит и не различает `singleton/prefix2/prefix3`.

## Новые возможные комбинации слов

- `third real gap-weight`
- `gamma2 > 3 pi`
- `prefix3 honest positivity`
- `three-term manuscript gap sum`

## Переход в INSIGHTS

- итог зафиксирован в `q3.lean.aristotle/docs/INSIGHTS.md`;
- привязанный рабочий note:
  `docs/insights/h1_po3_first_zeta_witness_stub_2026_04_19.md`.

## Следующий адресный шаг

- локальный узел `PO3-prefix3` закрыт;
- следующий честный ход уже выше:
  использовать закрытый пакет `singleton/prefix2/prefix3` как готовый
  локальный kill-layer внутри `PO3-shell`.
