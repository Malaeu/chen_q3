# Front map — two lanes to RH (2026-07-31)

Author: Mythos (chat canvas, dispatch answer to packet 2) · Materialized by conductor-CLI.
PNG snapshot: `2026-07-31_two_lane_rh_map.png` (verbatim canvas render).
Key structural finding encoded here: the challenger lane has NO written promotion
contract into the mainline chain — the dashed edge is the main hole of the map (K8).

```mermaid
flowchart BT
  classDef proved fill:#0b5345,stroke:#0e6655,color:#d5f5e3
  classDef open fill:#78281f,stroke:#943126,color:#fadbd8
  classDef import fill:#424949,stroke:#616a6b,color:#d5dbdb

  RH["1 · RH<br/>открыто · цель = Step 34"]:::open
  PEN["2 · Цепь пером<br/>доказано · до Step 34"]:::proved

  ROOF["Roof: ZeroEscape (R6)<br/>доказано · 4 опоры"]:::proved
  S2["S2 cluster · H2b<br/>открыто · стены mainline"]:::open
  THM510["← импорт: Thm 5.10<br/>задача владельцу · arXiv 2511.22755"]:::import

  PROMO["Promotion → mainline<br/>открыто · контракт не написан"]:::open
  MUNTZ["Müntz: Shell·PL1·PL2<br/>доказано · условный"]:::proved
  SUP["hG · hRm · hRp · habs<br/>открыто · hRm первый (гол 043)"]:::open

  PEN --> RH
  ROOF --> PEN
  S2 --> ROOF
  THM510 --> S2

  PROMO -.-> PEN
  MUNTZ --> PROMO
  SUP --> MUNTZ
```

Legend: green = доказано · red = открыто · grey = импорт · пунктир = мост без контракта.
