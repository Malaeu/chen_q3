---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Szegő-Böttcher Theorem

### Insight: SB НЕ НУЖЕН для A3_bridge!

**Дата:** 2026-01-14 (из анализа Прошки)

**Факт из docs/PROJECT_SPECS.md:**
> "Szegő-Böttcher is optional and can be bypassed using the Rayleigh lower bound"

**Rayleigh даёт НАПРЯМУЮ:**
```
λ_min(Toeplitz[P]) ≥ min(P)
```

Это СИЛЬНЕЕ и ПРОЩЕ чем SB который даёт только асимптотику!

**Ошибка:** A3_bridge_closure_v1.md упоминал SB в контексте — это путает Aristotle.

**Правило:** НЕ упоминать SB в запросах к Aristotle для A3_bridge.

---
