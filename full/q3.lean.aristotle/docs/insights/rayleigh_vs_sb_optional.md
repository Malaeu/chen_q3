# Optional: Rayleigh-only vs SB Discretization (Do Not Forget)

**Контекст:** В `full/sections/A3/main.tex` сейчас используется SB-дискретизация
с `M_0^{unif}` (это корректный, но "тяжёлый" путь). В протоколе
`full/q3.lean.aristotle/docs/PROJECT_SPECS.md` зафиксирован упрощённый путь:
Rayleigh lower bound даёт `λ_min(T_M[P_A]) ≥ min P_A` без SB, значит без `M_0`.

**Это не противоречие:**
- SB-путь остаётся верным (просто избыточный).
- Rayleigh-путь сильнее (оценка для всех M).

**Если когда-нибудь нужно согласовать текст с протоколом:**
1) Добавить ремарку в `full/sections/A3/main.tex`: SB-оценка optional; можно
   заменить на Rayleigh lower bound и убрать `M_0`.
2) В доказательстве Theorem A3 убрать SB-дискретизацию и сослаться на Rayleigh.

---
