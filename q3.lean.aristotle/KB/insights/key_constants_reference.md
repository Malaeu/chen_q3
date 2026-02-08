---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Key Constants Reference

| Constant | Value | Decimal | Source |
|----------|-------|---------|--------|
| c* | 11/10 | 1.1 | A3_FLOOR |
| c*/4 | 11/40 | 0.275 | A3_bridge target |
| 3c*/4 | 33/40 | 0.825 | Max RKHS bound |
| w_max | 2/e | 0.735 | RKHS weight bound |
| ρ (RKHS) | (1+2/e)/2 | 0.868 | RKHS_contraction.lean |

**Note:** ρ = 0.868 (из RKHS_contraction) > 3c*/4 = 0.825, НО для small t:
||T_P|| ≤ w_max = 0.735 < 0.825 — это ДОСТАТОЧНО!

---
