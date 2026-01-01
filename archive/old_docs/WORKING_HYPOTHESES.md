# WORKING HYPOTHESES - Q3 Twin Primes Project

## Статус: Рабочие идеи, НЕ в paper

---

## 1. LAGRANGIAN PERSPECTIVE (из constrained_lagrangian.py)

### Ключевой инсайт
```
Unconstrained: μ_min ≈ 0 (eigenvector OUTSIDE cone - oscillatory sign)
Constrained:   R_cone ~ N^0.88 ~ span^3.6 → ∞
```

### Физическая интерпретация
**Cone = "закон сохранения"** который не даёт системе упасть в глобальный минимум.

Как в механике:
- Energy conservation removes inaccessible states
- Angular momentum restricts trajectories

Позитивность λ_p > 0 (от von Mangoldt) вынуждает систему оставаться на cone!

### Численные данные
```
X       N     μ_min (unconstrained)    R_cone (constrained)
500     24    7.0×10⁻⁸                 14.39
1000    35    1.1×10⁻⁷                 22.12
5000    126   1.5×10⁻⁷                 70.48
20000   342   2.0×10⁻⁷                 160.17
50000   705   2.3×10⁻⁷                 296.78
```

Power law: R_cone ~ 0.46 × N^1.05 ~ 36.2 × span^3.6

### Rank-1 Structure
```
Q ≈ q·11ᵀ + Δ_Q   (50% от rank-1)
G ≈ g·11ᵀ + Δ_G   (99.98% от rank-1!)

⟹ R(λ) почти постоянна на cone
⟹ R(1)/R_min ~ 1.1-1.4
```

### Что нужно доказать
Аналитически: R_cone ≥ c·span^α для α > 0

---

## 2. CV GROWTH HYPOTHESIS (новое!)

### Критическое открытие
```
TWINS:   E_C/E_G ~ N^2.02   ← БЫСТРЕЕ!
RANDOM:  E_C/E_G ~ N^1.67
UNIFORM: E_C/E_G ~ N^1.71

Δα = 0.35 в показателе!
```

### Причина: GAP DISTRIBUTION
```
Фактор           α      Δα от twins
────────────────────────────────────
GAP distribution  1.938   0.089   ← ГЛАВНЫЙ!
Modular 6k±1      1.914   0.113
Density           1.727   0.300
```

### cv растёт с N!
```
N      cv (coefficient of variation)
24     0.893
35     1.078
61     1.410
126    1.959
205    2.374
342    2.903
705    3.873
1224   4.820

Power law: cv ~ N^0.426
```

### Механизм cv роста
```
Local cv ≈ 0.5-1.0 (постоянен локально)

GLOBAL cv растёт из-за MIXING:
- Small gaps при low ξ (dense region)
- Large gaps при high ξ (sparse region)
= HIGH VARIANCE globally!

cv_global² = cv_local² + Var(mean gaps across regions)
           ↑ растёт с N потому что range of ξ увеличивается!
```

### Критический вывод
```
cv growth АВТОМАТИЧЕСКИЙ из ρ(p) ~ 1/log²(p)

⟹ E_C → ∞ если twin primes СУЩЕСТВУЮТ в достаточном количестве!
```

### НОВЫЙ ПУТЬ К TPC
```
┌─────────────────────────────────────────────────────────────┐
│ СТАРЫЙ ПУТЬ (BLOCK A):                                      │
│   Доказать S₂ ~ X (Hardy-Littlewood)                        │
│   Сложность: ~100 лет нерешённая                            │
├─────────────────────────────────────────────────────────────┤
│ НОВЫЙ ПУТЬ:                                                  │
│   1. E_G > 0 (нужны КАКИЕ-ТО twins, тривиально)             │
│   2. cv(gaps) → ∞ (АВТОМАТИЧЕСКИ из ρ ~ 1/log²)             │
│   3. E_C/E_G ~ N^{0.43} × N^{1.7} = N^{2.1}                 │
│   4. E_C → ∞                                                 │
│   5. TPC ✓                                                   │
│   Сложность: ВОЗМОЖНО ПРОЩЕ!                                │
└─────────────────────────────────────────────────────────────┘
```

### Задача B (слабее чем Hardy-Littlewood!)
**Доказать:** cv(twin gaps) ≥ const > 0

Это чисто вопрос о распределении gaps, не о количестве!

---

## 3. LARGE SIEVE CONNECTION

### Fourier представление E_total
```
K(ξ_p, ξ_q) = exp(-(ξ_p - ξ_q)²/(4t))

Через Fourier:
K(ξ_p, ξ_q) = √(πt) ∫ exp(-t ω²) e^{iω(ξ_p - ξ_q)} dω

⟹ E_total = √(πt) ∫ exp(-t ω²) |F(ω)|² dω

где F(ω) = Σ_p λ_p e^{iω ξ_p} = Σ_{p twin} Λ(p)Λ(p+2) · p^{iω/(2π)}
```

Это LARGE SIEVE FORM! Связь с:
- Selberg sieve как quadratic form
- Montgomery-Vaughan large sieve inequality

---

## 4. СТАТЬЯ REN (arXiv:2511.12944) — WITHDRAWN!

**Статус:** ОТОЗВАНА 23 Nov 2025

**Причина:** "An error in the final integral calculation"

**Что пытался доказать:**
```
Σ (1/p)(log(x^α/p))^k имеет положительную нижнюю границу
                        ↓
⟹ infinitely many twin primes
```

**Вывод:** Его подход не работает, но идея weighted sieve может быть полезна.

---

## 5. СИНЕРГИИ

### Lagrangian + cv growth
- Lagrangian объясняет ПОЧЕМУ cone важен
- cv growth объясняет ПОЧЕМУ twins особенные
- Вместе: twins в cone с растущим cv ⟹ R → ∞

### cv growth + Large Sieve
- cv = неоднородность gaps
- Large sieve = Fourier amplitude |F(ω)|²
- Неоднородность ⟹ Fourier не cancels ⟹ |F|² большой

### Связь с parity barrier
Наш подход ОБХОДИТ parity barrier потому что:
- Мы не сравниваем twins с primes
- Мы измеряем СТРУКТУРУ (cv) а не КОЛИЧЕСТВО

---

## ПРИОРИТЕТЫ

1. **HIGH:** Формализовать cv growth лемму
2. **HIGH:** Доказать cv(gaps) → ∞ из PNT
3. **MEDIUM:** Large sieve connection
4. **LOW:** Lagrangian — красиво но не приоритет

---

---

## 6. АНАТОМИЯ δ: Где реально живёт показатель роста

### Ключевой вопрос
```
R ~ N^δ,  где δ ≈ 0.92

Откуда берётся δ? НЕ из π, e, i!
```

### Commutator weight function
```
f(δξ) = (δξ)² · exp(-(δξ)²/(4t))

Максимум при δξ* = √(2t) ≈ 1.0

Это "сладкая зона" — пары (p,q) с |ξ_p - ξ_q| ≈ 1.0 дают максимальный вклад
```

### Decomposition E_total по расстоянию (X=100000, N=1224)
```
Range δξ       # pairs      % energy
────────────────────────────────────
[0.0, 0.3)     1,141,178    20.4%    ← близкие, много но слабые
[0.3, 0.7)     297,750      50.1%    ← ПОЛОВИНА ЭНЕРГИИ!
[0.7, 1.0)     39,850       17.9%
[1.0, 1.5)     16,050       10.2%
[1.5, ∞)       ~2000        1.4%     ← дальние, убиты exp
────────────────────────────────────
                            100%
```

### Power laws
```
E_total ~ N^{2.92}     (почти N³)
Opt_pairs ~ N^{1.89}   (почти N²)
R = E_total/E_lat ~ N^{0.92}
```

### ГДЕ ЖИВЁТ δ?
```
δ = log(E_total)/log(N) - 2

Определяется:
1. Сколько пар попадает в "сладкую зону" δξ ∈ [0.3, 1.5]
2. Как это число растёт с N

НЕ из констант π, e!
```

### Механизм для twins
```
Плотность twins: ρ(p) ~ 1/log²(p)
        ↓
Gaps между twins РАСТУТ с p
        ↓
Больше пар попадает в сладкую зону (δξ ~ 1)
        ↓
Opt_pairs ~ N^{1.89} (супер-линейно!)
        ↓
E_total ~ N^{2.92}
        ↓
R ~ N^{0.92} → ∞
```

### Три пути к δ > 0

| Путь | Что доказать | Сложность |
|------|-------------|-----------|
| Hardy-Littlewood | S₂ ~ X | ~100 лет |
| Eigenvalue spectrum | λ_k ~ k^α | Hard |
| cv-анализ | cv(gaps) → ∞ | **Возможно проще!** |

### Связь с cv
```
cv большой → gaps разнообразны
           → широкое распределение δξ
           → много пар в сладкой зоне
           → E_total растёт быстро
           → δ > 0
```

### Вывод
```
e^{iπ}+1=0 — красивая формула, НО:
- δ там НЕТ
- δ живёт в КОМБИНАТОРИКЕ ПАР
- Конкретно: сколько пар в зоне δξ ∈ [0.3, 1.5]

Euler помогает ВИЗУАЛИЗИРОВАТЬ (unit circle),
но не даёт ИНФОРМАЦИИ о росте энергии.
```

---

## FILES

- `src/constrained_lagrangian.py` — Lagrangian analysis
- `src/ratio_const_analysis.py` — Rank-1 structure analysis
- `src/delta_anatomy.py` — Анализ где живёт δ (decomposition по расстоянию)
- `paper/sections/lagrangian_perspective.tex` — убран из paper, сохранён как reference
