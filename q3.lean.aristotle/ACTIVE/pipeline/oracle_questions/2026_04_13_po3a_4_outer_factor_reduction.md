---
status: "active"
date: "2026-04-13"
main_address: "PO3a.4"
related_addresses: ["PO3a.3", "PO3a.5", "H-bridge.11"]
ancestor_addresses: ["PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a.5"]
raw_address_notation: "PO3a.4; PO3a.3, 5; H-bridge.11"
normalized_addresses: ["PO3a.4", "PO3a.3", "PO3a.5", "H-bridge.11", "PO3a"]
address_status: "active"
blocker: "Снятие внешних факторов U,V без потери identity-outer жёсткости"
collections: ["q3_docs"]
tags: ["po3", "outer_factors", "rigidity", "tail_zero"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: []
strong_terms: ["внешние множители (outer factors)", "identity-outer жёсткость (identity-outer rigidity)", "сюръективная композиция функционалов (surjective pullback of functionals)"]
empty_terms: ["полная physical Volterra normal form"]
false_friend_terms: ["достаточно одной инъективности справа"]
opens_new_branch_terms: ["снятие внешних операторов до identity-outer case"]
neighbor_addresses: ["PO3a.3", "PO3a.5"]
---

# PO3a.4 — Снятие внешних факторов U,V без потери identity-outer жёсткости

## Статус

- карточка создана;
- серия запросов ещё не отработана полностью.

## Точный блокер

Снятие внешних факторов U,V без потери identity-outer жёсткости

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`PO3a.4`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- в основной заметке `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`
  уже сидит точная цепочка:
  `physical Volterra 2×2 receiver -> identity-outer жёсткость ->
  alternating tail rigidity -> tail-zero target`;
- under physical Volterra normal form mixed block имеет форму
  `E_+ K F_-` с обратимой средней матрицей
  `K = [[-1, c_a], [0, -1]]`,
  так что vanishing mixed block вынуждает вырождение хотя бы одной стороны;
- в identity-outer specialization `U=V=I` это уже сжато до жёсткости
  `P_+ v_{a,N} = α_{+,N}(a) h_{+,N}` и
  `P_- v_{a,N} = α_{-,N}(a) h_{-,N}`,
  после чего ветка возвращается к tail-zero цели;
- на плюс-стороне перенос зависимости через внешний оператор уже формально
  закрыт в `q3/Proofs/HBridge_PO3_Shell.lean`:
  инъективное линейное отображение сохраняет неколлинеарность;
- настоящий недостающий мост сидит справа:
  для функционалов нужно снимать композицию с `V`,
  и здесь одной инъективности недостаточно —
  нужна как минимум сюръективность `V` на соответствующем хвостовом
  пространстве.
- этот правый мост теперь уже заморожен в Lean:
  в `q3/Proofs/HBridge_PO3_Shell.lean` добавлены леммы
  `mem_span_singleton_of_comp_mem_span_singleton_of_surjective`
  и
  `not_mem_span_singleton_comp_of_surjective`.

## Что именно мы хотим узнать поиском

- есть ли в наших reviewed notes уже готовая формулировка для переноса
  линейной зависимости функционалов через сюръективную композицию;
- не сидит ли этот мост уже неявно в старых узлах `PO3a` / `PO4`;
- какие слова лучше поднимают именно этот узкий шаг, а не снова уводят
  в общую physical Volterra normal form.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a.4 outer sign-preserving invertible factors identity-outer rigidity` | `PO3a.4` | Проверить, есть ли уже явный мост от реального `U,V` к identity-outer жёсткости | outer factors → identity-outer reduction | strong hit | вернул основную `PO3a`-заметку и подтвердил, что живой шаг узок |
| `H-bridge.11 identity-outer reduction U V injective sign-preserving` | `H-bridge.11` | Проверить, достаточно ли инъективности и сохранения знака | receiver shell → operator assumptions | hit | показал, что слева этого хватает, но справа для функционалов нужен более сильный перенос |
| `PO3a rigidity identity outer case tail zero target` | `PO3a.4` | Подтвердить, что снятие внешних факторов действительно возвращает ветку в tail-zero цель | rigidity → tail-zero target | strong hit | поднял exact theorem `PO3a-identity-outer rigidity returns the tail-zero target` |

## Пустые / шумовые слова

- `полная physical Volterra normal form` как первый подшаг
- расплывчатое `outer invertibility` без адреса

## Новые возможные комбинации слов

- `сюръективная композиция функционалов`
- `outer-factor stripping`
- `identity-outer reduction of receiver rigidity`
- `functional pullback under surjective map`

## Переход в INSIGHTS

- синтез добавлен в `docs/INSIGHTS.md` от `2026-04-13`:
  текущий живой brick здесь — не вся normal form, а перенос зависимости
  функционалов назад через сюръективный `V`.
- итог этой серии уже частично формализован:
  абстрактный minus-side outer bridge больше не blocker.

## Следующий адресный шаг

- добавить в Lean минимальную лемму:
  если `V` сюръективен и
  `φ.comp V ∈ 𝕜 ∙ (ψ.comp V)`,
  то `φ ∈ 𝕜 ∙ ψ`;
- после этого собрать общий bridge:
  реальные внешние факторы `U,V` не разрушают identity-outer жёсткость,
  если на плюс-стороне есть инъективность, а на минус-стороне — сюръективность.
- следующий уже совсем узкий шаг:
  проверить, какие именно свойства реальных хвостовых операторов `U,V`
  в нашей физической Volterra-форме уже дают эти две гипотезы.
