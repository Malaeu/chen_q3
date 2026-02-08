---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# BREAKTHROUGH: Прошка дал полное доказательство!

### Insight: A3_bridge закрывается за ~20 строк (2026-01-14)

**Прошка показал:**
1. rayleigh_v1.lean УЖЕ содержит Lemma 1 + Lemma 2
2. Нужна только Lemma 3 (operator subtraction) — 3 строки linarith
3. RKHS cap: ρ(1) < 1/25 = 0.04 << c*/4 = 0.275

**Структура финального доказательства:**
```
Toeplitz ≥ c* = 1.1        (rayleigh_v1.lean + A3_FLOOR)
RKHS ≤ c*/4 = 0.275        (trivial от ρ(1) < 0.04)
Разница ≥ 3c*/4 > 0        (linarith)
```

**Файл:** `aristotle_input/A3_bridge_PROSHKA_SKELETON.md`

**Правило:** Когда застреваем — перечитывать Прошкины ответы. Он видит дальше.

---
