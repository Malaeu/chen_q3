---
status: "done"
date: "2026-04-21"
main_address: "PO3-square.2d2"
related_addresses: ["D3e4", "D2"]
ancestor_addresses: ["PO3-square.2d1", "PO3-square.2d", "PO3-square.2", "PO3"]
child_or_next_addresses: ["PO3-square.2d3"]
raw_address_notation: "PO3-square.2d1, 2, 3; D3e4; D2"
normalized_addresses: ["PO3-square.2d1", "PO3-square.2d2", "PO3-square.2d3", "D3e4", "D2", "PO3-square.2d", "PO3-square.2", "PO3", "PO3-square.2c2"]
address_status: "done"
blocker: "signed rightmost dominance shell for the transform-side wall"
collections: ["q3_docs"]
tags: ["po3-square", "wall", "gamma-tower", "signed-dominance"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_route_ladder_2026_04_19.md"]
request_nodes: []
strong_terms: ["signed rightmost dominance", "mirror suppression"]
empty_terms: ["finite anchor"]
false_friend_terms: ["absolute no-escape"]
opens_new_branch_terms: ["gamma-ratio dominance"]
neighbor_addresses: ["PO3-square.2c2"]
---

# PO3-square.2d2 — signed rightmost dominance shell for the transform-side wall

## Статус

- первая серия local oracle + web sanity-check проведена;
- адрес зафиксирован как новый live brick внутри `PO3-square.2d`.

## Точный блокер

Нужно заморозить следующий theorem-shell после ложной ветки
`absolute anchor`:
если signed main tower на стороне `A_k` имеет eventual нижнюю границу по норме,
а mirror tower на стороне `B_k` уходит в ноль, то равенство стены
`main_k = mirror_k` невозможно.

## Почему этот поиск нужен сейчас

Потому что это и есть прямой переход от текущей reduction-оболочки
`PO3-square.2d1` к настоящей бесконечной uniqueness-стене.
Если здесь продолжать искать finite anchor / absolute no-escape, мы снова
потратим время на ложную дверь.

## Что уже известно по этому адресу

- `PO3-square.2d0a` уже закрыт: square-tail zero переносится в bilateral
  integer-tail zero для even transform-side receiver.
- `PO3-square.2d1` уже закрыт: live wall зафиксирована как named target.
- В старой `D3e4`-линии уже есть тот же structural kill:
  при неограниченной справа поддержке fixed finite anchor невозможен, потому что
  Gamma-ratio asymptotic вытягивает абсолютную массу вправо.
- Значит absolute-weight tightness не может быть mainline для
  `PO3-square.2d`; живой brick теперь только signed cancellation.

## Что именно мы хотим узнать поиском

- где в наших notes уже есть готовый kill-certificate против finite anchor;
- какая abstract shell-формулировка минимальна и честно подключает
  `signed rightmost dominance` к противоречию;
- какие внешние sanity-check источники подтверждают, что надо бить не absolute
  mass, а geometry/uniqueness Cauchy-transform side.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3 square signed rightmost dominance gamma tower cancellation` | `PO3-square.2d2` | найти внутренний аналог новой стены | signed cancellation vs shell packaging | средний | подтвердило, что нужен новый shell target, а не ещё один packet |
| `PO3 square no finite anchor unbounded support gamma tower` | `PO3-square.2d2` | проверить, не убита ли уже absolute-anchor дверь в старых notes | absolute weights / tightness | сильный | вернуло старый `D3e4`-kill и прямо поддержало отказ от anchor-route |
| `PO3-square.2d1 even symmetric Cauchy receiver integer tail uniqueness` | `PO3-square.2d2` | связать новую цель с уже зафиксированной transform-side wall | transform-side phrasing | сильный | подтвердило, что новая live wall живёт именно поверх `2d1` |
| `signed tower mirror suppression gamma ratio asymptotic wall` | `PO3-square.2d2` | проверить, есть ли у нас готовая gamma-ratio доминантность | asymptotic dominance | средний | дал DLMF-поддержку и указал на signed dominance как next theorem-target |

## Пустые / шумовые слова

- `finite anchor`
- `absolute no-escape`
- общая `tightness`-риторика без signed structure

## Новые возможные комбинации слов

- signed rightmost dominance
- mirror suppression
- Gamma-ratio lower bound
- transform-side wall contradiction
- Cauchy uniqueness after bilateral integer-tail zero

## Переход в INSIGHTS

- `docs/INSIGHTS.md`:
  synthesis block от `2026-04-21` на адресе `PO3-square.2d2`.

## Следующий адресный шаг

- formalize minimal contradiction shell in Lean:
  `wall equality + eventual lower bound on main tower + mirror decay -> False`;
- после этого следующий уже genuinely mathematical узел:
  `PO3-square.2d3` = получить lower bound из signed rightmost dominance на
  реальной Gamma-tower стороне.
