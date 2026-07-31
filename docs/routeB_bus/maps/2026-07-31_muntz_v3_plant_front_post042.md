# Front map — Müntz v3 plant layer (2026-07-31, post-042)

Author of layout: Mythos · State update: conductor-CLI after Goal 042 closure.
Supersedes: `2026-07-31_muntz_v3_plant_front.md` (kept immutable).
PNG snapshot: pending next Mythos canvas render (Mermaid below is authoritative
for this state).
State as of: Goal 042 closed, PL1_MASS_BLOWUP_WITNESS_PROVED (byte-audit by
conductor: SHA match, taint 0, canon=mirror; Lean build per answer 8031 jobs PASS).

```mermaid
flowchart BT
  classDef proved fill:#0b5345,stroke:#0e6655,color:#d5f5e3
  classDef open fill:#78281f,stroke:#943126,color:#fadbd8

  UNCOND["Müntz v3: безусловный слой<br/>открыто · две опоры ниже"]:::open
  PL3["PL3: мутанты<br/>открыто · следующий кандидат"]:::open
  SUP["hG · hRm · hRp · habs<br/>открыто · supplier-фронт (большой цикл)"]:::open
  SHELL["Shell + T4a + T5<br/>доказано · заморожен"]:::proved
  PL1["PL1: роль массы ≠ 0<br/>доказано · blow-up, mass = 1/2"]:::proved
  PL2["PL2: raw-pole свидетель<br/>доказано · deriv = −1/12"]:::proved

  PL3 --> UNCOND
  SUP --> UNCOND
```

Legend: green = доказано (байт-аудит) · red = открыто.
Contrast pair complete: PL2 (mass 0 ⇒ finite mismatch) + PL1 (mass ≠ 0 ⇒ blow-up)
certify zero mass as exactly the removability mechanism.
