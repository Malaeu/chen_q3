---
status: "active"
date: "2026-04-21"
main_address: "PO3-rig.1b.cert-real"
related_addresses: ["PO3-rig.1b.cert", "PO3a.4-real", "PO3-tail.1"]
ancestor_addresses: ["PO3-rig.1b.cert", "PO3a.4-real", "PO3-rig.1b"]
child_or_next_addresses: ["PO3-tail.1"]
raw_address_notation: "PO3-rig.1b.cert-real"
normalized_addresses: ["PO3-rig.1b.cert-real", "PO3-rig.1b.cert", "PO3a.4-real", "PO3-tail.1", "PO3-rig.1b"]
address_status: "active"
blocker: "Прямой certificate-layer от outer-transport cancellation и coordinate data к scalar window law для реального Q3-side окна"
collections: ["q3_docs"]
tags: ["po3", "certificate", "outer-transport", "window-law"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: []
strong_terms: ["outer transport certificate", "compressed zero-mode column", "alternating endpoint profile", "window scalar law"]
empty_terms: ["full live v_{a,N} object in Lean", "new outer linear algebra"]
false_friend_terms: ["rebuild shell theorem", "import literature theorem for span coordinates"]
opens_new_branch_terms: ["direct PO3Cert bridge from PO3a.4-real to PO3-tail.1"]
neighbor_addresses: ["PO3-rig.1b.cert", "PO3a.4-real", "PO3-tail.1"]
---

# PO3-rig.1b.cert-real — Прямой certificate-layer от outer-transport cancellation и coordinate data к scalar window law для реального Q3-side окна

## Статус

- проведён local oracle pass по `q3_docs` и внешний sanity-check;
- адрес narrowed до одного direct certificate bridge inside `PO3Cert`;
- следующий кодовый шаг уже ясен: расширить
  `WindowLawCertificate_2026_04_19.lean` контрактом для outer-transport data
  и theorem-consumer-ом в scalar window law.

## Точный блокер

Прямой certificate-layer от outer-transport cancellation и coordinate data к scalar window law для реального Q3-side окна

## Почему этот поиск нужен сейчас

После закрытия `PO3a.4-real` и `PO3a-A2-real` следующий честный gap уже не в
shell-level linear algebra и не в packet extraction. Остался один мост:
зафиксировать, какой именно Q3-side certificate должен подать transport-zero,
coordinate values и endpoint profile, чтобы сразу получить one scalar window
law и передать его в `PO3-tail.1`.

## Что уже известно по этому адресу

- `HBridge_PO3_Shell.lean` уже содержит exact feeder
  `po3_coordinate_profile_of_outer_transport_companion_cancellation`;
  значит math side этого узла уже закрыта.
- `PO3Cert/WindowLawCertificate_2026_04_19.lean` уже содержит более ранний
  feeder-contract `PO3WindowCoordinateCertificate`, но он фиксирует только
  span-laws и shared coordinate sequence, без outer-transport cancellation.
- March note `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md` уже
  формулирует нужный target literally:
  для `v = v_{a,N}` reflection-even compressed coordinates должны породить
  window law `w_{r,0}(a) = c_{a,N,M} (-1)^r`.

## Что именно мы хотим узнать поиском

- нужен ли новый shell theorem, или уже достаточно certificate wrapper-а;
- где exactly frozen manuscript formulas for compressed zero-mode/profile live;
- можно ли провести next step как один новый `PO3Cert` structure + consumer.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3-rig.1b real Q3-side coordinate certificate outer transport companion cancellation window law` | `PO3-rig.1b.cert-real` | проверить, нет ли уже готового certificate bridge | exact feeder target | strong | вернул `INSIGHTS`, March `PO3` note и shell как уже закрытую mathematics side |
| `PO3a.4-real PO3-rig.1b certificate compressed zero-mode column alternating endpoint profile` | `PO3-rig.1b.cert-real` | уточнить связку между outer feeder и certificate layer | transport-vs-certificate interface | strong | показал, что strongest local bridge уже в `HBridge_PO3_Shell.lean`, а живой gap сидит в `PO3Cert` |
| `outer transport coordinate feeder window certificate HBridge_PO3_Shell PO3Cert` | `PO3-rig.1b.cert-real` | проверить, нужен ли новый theorem вне `PO3Cert` | shell vs certificate packaging | medium | внешнего theorem не нашлось; fastest move — новый contract в `WindowLawCertificate_2026_04_19.lean` |
| `v_{a,N}=T_{a,∞,N}^*G_g[a]1 reflection-even w_{r,0}(a) compressed coordinate formula alternating profile` | `PO3-rig.1b.cert-real` | найти exact manuscript wording для реального Q3 target | real zero-mode wording | strong | вернул March note с буквальной alternating-tail rigidity формой |
| внешний web-поиск по rank-one cancellation / coordinate profile scalar multiples | `PO3-rig.1b.cert-real` | sanity-check на off-the-shelf linear-algebra theorem | external literature vs local shell | weak | дал только общие факты о координатах на одномерном span; project-specific bridge всё равно лучше держать локально |

## Пустые / шумовые слова

- “полностью ввести живые `v_{a,N}` и `w_{r,0}(a)` прямо сейчас”;
- “искать внешнюю теорему для rank-one / coordinates”;
- “заново строить shell вокруг `PO3-rig.1b`”.

## Новые возможные комбинации слов

- outer transport certificate
- compressed zero-mode coordinate law
- alternating endpoint profile certificate
- direct PO3Cert feeder to tail law

## Переход в INSIGHTS

- `q3.lean.aristotle/docs/INSIGHTS.md`: synthesis block от `2026-04-21`
  на адресе `PO3-rig.1b.cert-real`.

## Следующий адресный шаг

- добавить в `Q3/Proofs/PO3Cert/WindowLawCertificate_2026_04_19.lean`
  новый certificate contract для outer-transport cancellation + coordinate data;
- сразу добавить theorem-consumer, который отправляет такой certificate в
  `po3_window_scalar_law`;
- после этого следующий живой узел станет уже `PO3-tail.1`, а не новый
  certificate bookkeeping.
