---
status: "active"
date: "2026-04-21"
main_address: "PO3a-A2-real"
related_addresses: ["PO3a-A2", "PO3a-A-real", "PO3a.4-real"]
ancestor_addresses: ["PO3a-A-real", "PO3a-A2", "H-bridge.11"]
child_or_next_addresses: ["PO3a.4-real", "PO3-rig.1b"]
raw_address_notation: "PO3a-A2-real"
normalized_addresses: ["PO3a-A2-real", "PO3a-A2", "PO3a-A-real", "PO3a.4-real", "H-bridge.11", "PO3-rig.1b"]
address_status: "active"
blocker: "Смешанная вторая разность реального дефекта и совпадение bulk-ядра с (I-R_a)^*K_a(I-R_a)-L_a"
collections: ["q3_docs"]
tags: ["po3a", "real-defect", "mixed-packet", "filtered-pm"]
insight_links: ["q3.lean.aristotle/docs/INSIGHTS.md"]
request_nodes: []
strong_terms: ["real defect", "four-term stencil", "mixed packet", "filtered q_pm kernel"]
empty_terms: ["full final formula at once", "global outer operator theory"]
false_friend_terms: ["prove physical Volterra normal form first", "rebuild PO3a-A-real transport shell"]
opens_new_branch_terms: ["manuscript-facing named-packet consumer for filtered (+,-) family"]
neighbor_addresses: ["PO3a-A2", "PO3a-A-real", "PO3a.4-real"]
---

# PO3a-A2-real — Смешанная вторая разность реального дефекта и совпадение bulk-ядра с (I-R_a)^*K_a(I-R_a)-L_a

## Статус

- проведён local oracle pass по `q3_docs` и внешний sanity-check;
- адрес narrowed до одного direct consumer-а для filtered `(+,-)` shell;
- следующий кодовый шаг уже ясен: добавить theorem-пакет named packets для
  integer-profile `q^{+-}` семьи и не строить новую Volterra-теорию.

## Точный блокер

Смешанная вторая разность реального дефекта и совпадение bulk-ядра с (I-R_a)^*K_a(I-R_a)-L_a

## Почему этот поиск нужен сейчас

После закрытия `PO3a-A-real` следующий живой шаг уже не про transport и не про
общую философию antiderivative extraction. Нужен один manuscript-facing
consumer, который соберёт для реального `(+,-)`-дефекта весь пакет
`corner + row + column + mixed`, а затем сразу отдаст mixed-часть в уже
имеющийся one-variable shell.

## Что уже известно по этому адресу

- В notes уже зафиксирован реальный дефект
  `𝒟_{a,N} = S_{a,\infty,N}^* G_g[a] S_{a,\infty,N} - κ_{+-}(a) Δ_N^* Q_∞ Δ_N`
  и отдельно записано, что filtered defect есть pullback raw-ядра:
  `𝒟_{a,N} = Δ_N^* 𝓡^{raw}_{a,N} Δ_N`.
- В `Main_closure.tex` уже отмечено, что для filtered `(+,-)`-блока после
  перехода к `\\widetilde Q_{M,N}^{+-}` не остаётся дополнительного
  section-boundary defect.
- В Lean уже есть почти весь shell:
  `po3_named_packets_of_four_term_stencil_sub_smul`,
  `po3_four_term_stencil_q_pm_kernel_of_int`,
  `po3_mixed_packet_of_four_term_stencil_q_pm_kernel_of_int`,
  `po3_mixed_packet_of_section8_raw_kernel_pm`.

## Что именно мы хотим узнать поиском

- нужно ли доказывать новую общую Volterra-лемму, или уже достаточно
  существующего packet-shell;
- можно ли сформулировать следующий шаг как один узкий theorem про
  named packets filtered `(+,-)` family;
- есть ли внешний off-the-shelf theorem, который лучше локального consumer-а.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| `PO3a A2 real defect mixed second difference (I-R_a)^* K_a (I-R_a) - L_a` | `PO3a-A2-real` | проверить, нет ли уже прямого bulk-consumer-а | exact A2 target | strong | вернул notes и shell вокруг `PO3a-A-real`; показал, что надо бить именно mixed packet |
| `PO3a real defect double telescoping corner row column mixed packet` | `PO3a-A2-real` | проверить, не нужна ли новая A0-теория | packet decomposition | strong | указал на уже существующие `po3_double_telescoping` и named packet defs |
| `S_{a,∞,N}^* G_g[a] S_{a,∞,N} - kappa(a) Delta_N^* Q_infty Delta_N real defect` | `PO3a-A2-real` | найти точную manuscript фиксацию real defect | real defect formula | strong | вернул reviewed note `h1_po1_tail_defect_attack_2026_03_16.md` с замороженной формулой `𝒟_{a,N}` |
| `PO3a two-endpoint extraction physical specialization mixed bulk difference L_a origin` | `PO3a-A2-real` | проверить источник filtered pullback и bulk target | raw-to-filtered bridge | strong | вернул `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`, где filtered defect уже записан как `Δ_N^* 𝓡^{raw}_{a,N} Δ_N` |
| внешний web-поиск по двумерному discrete telescoping / mixed difference | `PO3a-A2-real` | sanity-check на off-the-shelf theorem | local shell vs generic analysis | weak | дал только общую формулу double telescoping; проектно лучший ход остаётся локальный consumer из уже существующего Lean shell |

## Пустые / шумовые слова

- “найти сразу final compact formula для всего дефекта”;
- “сначала доказать полную physical Volterra normal form”;
- “новая глобальная теория outer operators”.

## Новые возможные комбинации слов

- real defect filtered pullback
- named packets of filtered q_pm kernel
- manuscript-facing mixed packet consumer
- corner row column mixed shell

## Переход в INSIGHTS

- `q3.lean.aristotle/docs/INSIGHTS.md`: synthesis block от `2026-04-21`
  на адресе `PO3a-A2-real`.

## Следующий адресный шаг

- добавить в `Q3/Proofs/HBridge_PO3_Shell.lean` theorem-пакет, который
  для integer-profile `q^{+-}` filtered family выдаёт сразу весь named packet
  `corner + row + column + mixed`;
- затем использовать его как manuscript-facing bridge к реальному дефекту,
  чтобы следующий живой узел был уже не `PO3a-A2-real`, а Q3-side
  certificate into `PO3a.4-real`.
