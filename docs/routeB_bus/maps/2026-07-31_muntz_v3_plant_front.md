# Front map — Müntz v3 plant layer (2026-07-31)

Author: Mythos (chat canvas) · Snapshot relayed by owner, materialized by conductor-CLI.
PNG snapshot: `2026-07-31_muntz_v3_plant_front.png` (verbatim as rendered in the Mythos chat).
State as of: PL2 byte-audited green; Goal 042 (PL1) issued, in execution.

```mermaid
flowchart BT
  classDef proved fill:#0b5345,stroke:#0e6655,color:#d5f5e3
  classDef open fill:#78281f,stroke:#943126,color:#fadbd8

  UNCOND["Müntz v3: безусловный слой<br/>открыто · три опоры ниже"]:::open
  PL1["PL1: роль массы 0<br/>открыто · гол 042 issued"]:::open
  PL3["PL3: мутанты<br/>открыто · после PL1"]:::open
  SUP["hG · hRm · hRp · habs<br/>открыто · supplier-фронт"]:::open
  SHELL["Shell + T4a + T5<br/>доказано · заморожен"]:::proved
  PL2["PL2: raw-pole свидетель<br/>доказано · deriv = −1/12"]:::proved

  PL1 --> UNCOND
  PL3 --> UNCOND
  SUP --> UNCOND
```

Legend: green = доказано (байт-аудит) · red = открыто.

Convention: maps are immutable dated snapshots (`YYYY-MM-DD_slug.png` + same-name `.md`
with the Mermaid source). A state change = a NEW dated pair, never an edit of an old
one — the front history stays browsable. Mermaid renders directly on GitHub, so the
map is viewable from any machine with browser access.
