# RH_Q3.pdf - Извлечённая структура

## Метаданные
- **Название**: Operator Methods for the Weil Criterion: Q3
- **Автор**: Eugen Malamutmann, MD (University of Duisburg-Essen)
- **Дата**: January 17, 2026
- **DOI**: 10.5281/zenodo.17956251
- **Страниц**: 62

## Главный результат (Theorem 1.1)
**Main result (informal)**: Let Q be the quadratic form fixed in Section 5 on the Weil class W. Then:
```
Q(Φ) ≥ 0    for all Φ ∈ W
```
Via Theorem 11.1 (the Weil criterion) this positivity is equivalent to the Riemann Hypothesis.

## Модульная структура доказательства

### Цепочка модулей: (T0)+(A1')+(A2)+(A3)+(RKHS)

| Module | Key statement | Consumed by |
|--------|---------------|-------------|
| T0 | Proposition 5.1 (Guinand-Weil normalization) | Theorem 11.4, Theorem 11.2 |
| A1' | Theorem 6.3 (Density on W_K) | Theorem 11.4 |
| A2 | Lemma 7.3 / Corollary 7.4 (Lipschitz control) | Theorem 11.4 |
| A3 | Theorem 8.35 (Uniform A3 bridge) | Theorem 11.4 |
| RKHS | Corollary 8.22 (Uniform prime cap) | Theorem 11.4 |
| MAIN | Theorem 11.4 (Weil positivity on W) | Theorem 11.2 |
| WEIL | Theorem 11.1 (Weil criterion) | Theorem 11.2 |

### Диаграмма зависимостей (из статьи)
```
Weil criterion ⟸ Weil positivity on W
       ⇑
PSD on each W_K ⟸ Toeplitz barrier + uniform RKHS cap
       ⇑
cone density + Lipschitz control (uniform A3 bridge)
```

## Ключевые неравенства

### Archimedean Toeplitz barrier (A3)
```
λ_min(T_M[P_A]) ≥ c_* - C·ω_{P_A}(1/(2M))
```

### Prime contraction (RKHS)
```
t_rkhs ≥ t^{unif}_{*,rkhs}
||T_P|| ≤ ρ(t_rkhs) ≤ c_*/4
```

### Combined bound
```
λ_min(T_M[P_A] - T_P) ≥ c_*/4 > 0
```

## Нотация
- Λ - функция фон Мангольдта
- ξ_n = (log n)/(2π) - узлы выборки
- w_Q(n) = 2Λ(n)/√n - веса в функционале Вейля
- w_RKHS(n) = Λ(n)/√n
- k_t(x,y) = exp(-(x-y)²/(4t)) - heat kernel
- W_K = [-K, K] - компактное окно
- W = ⋃_{K>0} W_K - конус Вейля


## Секция 3: Global Hypotheses

### (H1) T0 — Guinand-Weil normalization
- **Источник**: Proposition 5.1
- **Зависимости**: нет

### (H2) A1' — Density of Fejér×heat cone on every W_K
- **Источник**: Theorem 6.3
- **Зависимости**: нет

### (H3) A2 — Lipschitz continuity of Q on each W_K
- **Источник**: Lemma 7.3, Corollary 7.4
- **Зависимости**: нет

### (H4) A3 — Toeplitz bridge with explicit uniform floor c_* > 0
- **Источник**: Lemma 8.19, Theorem 8.35
- **Условие**: ρ(t_rkhs) ≤ c_*/4 for t_rkhs ≥ t^{unif}_{*,rkhs}
- **Константы**: M_0^{unif}
- **Зависимости**: нет

### (H5) RKHS — Prime contraction via uniform RKHS cap
- **Источник**: Corollary 8.22
- **Зависимости**: нет

## Секция 4: Notation and Conventions

### Ключевые определения
- ξ = η/(2π) — frequency axis
- 𝕋 = ℝ/ℤ with fundamental domain [-1/2, 1/2]
- a(ξ) = log π - ℜψ(1/4 + iπξ) — Archimedean density
- a_*(ξ) = 2π a(ξ)
- ξ_n = (log n)/(2π) — prime nodes
- w_Q(n) = 2Λ(n)/√n — one-sided weight inside Q
- w_RKHS(n) = Λ(n)/√n — operator weight on W_K
- w_max := sup_n w_RKHS(n) ≤ 2/e

### Quadratic functional Q
```
Q(Φ) = ∫_ℝ a_*(ξ) Φ(ξ) dξ - Σ_{n≥2} w_Q(n) Φ(ξ_n)
```

## Секция 5: Normalization (T0)

### Proposition 5.1 (T0' — Guinand-Weil matching)
```
Q(φ) = Q_GW(φ_GW)  with η = 2πξ, φ_GW(η) = φ(η/2π)
```
- **Тип**: Определение/Нормализация
- **Зависимости**: нет
- **Используется в**: Theorem 11.4, Theorem 11.2

### Lemma 5.2 (T0: Q normalization crosswalk)
```
Q_GW(φ_GW) := ∫_ℝ (log π - ℜψ(1/4 + iη/2)) φ_GW(η) dη - Σ_{n≥2} (Λ(n)/√n)(φ_GW(log n) + φ_GW(-log n))
```
- **Зависимости**: Proposition 5.1

### Lemma 5.3 (Invariance under normalisation conventions)
- **Тип**: Техническая лемма
- **Зависимости**: Lemma 5.2

## Секция 6: Local Density (A1')

### Theorem 6.1 (A1' — density)
For every compact [-K, K] the cone {Fejér * heat approximants} is dense in C^+_even([-K, K]) in ||·||_∞.
- **Зависимости**: Theorem 6.3

### Lemma 6.2 (Compact support convolution reduction)
```
(f * g)(x) = ∫_ℝ f(y) g(x-y) dy = ∫_{-L}^{L} f(y) g(x-y) dy
```
- **Условие**: supp(f) ⊆ [-L, L], g: ℝ → ℝ
- **Зависимости**: нет

### Theorem 6.3 (A1')
Let K = [-R, R] with R > 0. For B > 0, t > 0, τ ∈ [-R, R] define:
```
Φ_{B,t,τ}(ξ) := (1/2)[Λ_B(ξ-τ) ρ_t(ξ-τ) + Λ_B(ξ+τ) ρ_t(ξ+τ)]
```
where:
- Λ_B(x) = (1 - |x|/B)_+
- ρ_t(x) = (4πt)^{-1/2} e^{-x²/(4t)}
- **Зависимости**: Lemma 6.2
- **Используется в**: Theorem 11.4


## Секция 7: Continuity of Q on Compacts (A2)

### Lemma 7.1 (Local finiteness of the prime sampler)
Fix K > 0. For every even Φ ∈ C_c(ℝ) with supp Φ ⊂ [-K, K], the prime part of Q:
```
Σ_{n≥2} (2Λ(n)/√n) Φ(ξ_n),    ξ_n := (log n)/(2π)
```
is a finite sum: only finitely many terms are non-zero.
- **Зависимости**: нет
- **Используется в**: Corollary 7.2, Lemma 7.3

### Corollary 7.2 (Lipschitz continuity on a compact window)
Let Φ_1, Φ_2 ∈ C_c([-K, K]) be even. Then:
```
|Q(Φ_1) - Q(Φ_2)| ≤ ||a^*||_{L^∞([-K,K])} 2K ||Φ_1 - Φ_2||_∞ + (Σ_{ξ_n∈[-K,K]} (2Λ(n)/√n)) ||Φ_1 - Φ_2||_∞
```
- **Зависимости**: Lemma 7.1
- **Используется в**: Corollary 7.4

### Lemma 7.3 (A2)
Fix a compact K = [-R, R]. For even nonnegative Φ supported in K define:
```
Q(Φ) := ∫_{-R}^{R} a_*(ξ) Φ(ξ) dξ - Σ_{ξ_n∈K} w_Q(n) Φ(ξ_n)
```
Then Q is Lipschitz on C^+_even(K) in ||·||_∞:
```
|Q(Φ_1) - Q(Φ_2)| ≤ (||a_*||_{L^1(K)} + Σ_{ξ_n∈K} |w(n)|) ||Φ_1 - Φ_2||_∞
```
- **Константа Липшица**: L_Q(K) := ||a_*||_{L^1(K)} + Σ_{ξ_n∈K} (2Λ(n)/√n)
- **Зависимости**: Lemma 7.1
- **Используется в**: Theorem 11.4

### Corollary 7.4 (Explicit Lipschitz modulus for Q)
Fix K = [-R, R] and set:
```
L_Q(K) := ||a_*||_{L^1(K)} + Σ_{ξ_n∈K} (2Λ(n)/√n)
```
Then for all even, nonnegative Φ_1, Φ_2 ∈ C_c(K) one has:
```
|Q(Φ_1) - Q(Φ_2)| ≤ L_Q(K) ||Φ_1 - Φ_2||_∞
```
- **Зависимости**: Corollary 7.2, Lemma 7.3
- **Используется в**: Theorem 11.4

## Секция 8: Toeplitz-Symbol Bridge (A3)

### 8.1 A3 Calibration: The Constant κ_{A3}(t_0)

### Lemma 8.1 (Period-1 normalization audit)
Let g ∈ L^1(ℝ) be even and define the period-1 symbol:
```
P_A(θ) := 2π Σ_{m∈ℤ} g(θ + m),    θ ∈ [-1/2, 1/2]
```
Then:
```
∫_{-1/2}^{1/2} P_A(θ) dθ = 2π ∫_ℝ g(ξ) dξ
```
- **Зависимости**: нет
- **Используется в**: Lemma 8.2

### Lemma 8.2 (Calibration of κ_{A3})
Let Φ(ξ) = (1 - |ξ|/B)_+ e^{-4π²t_0ξ²} be an even Fejér×heat window. Define:
```
A_k := 2π ∫_ℝ a(ξ) Φ(ξ) cos(2πkξ) dξ
P_A(θ) := A_0 + 2 Σ_{k≥1} A_k cos(2πkθ)
```
Then:
```
κ_{A3}(t_0) = 1    (independent of t_0)
```
- **Зависимости**: Lemma 8.1
- **Используется в**: Theorem 8.35

### Lemma 8.3 (Rayleigh identification)
For every even Fejér×heat window Φ:
```
⟨(T_M[P_A] - T_P)p, p⟩ = Q(Φ)
```
- **Зависимости**: Lemma 8.2
- **Используется в**: Proposition 8.4

### Proposition 8.4 (Bridge margin calibration)
Under the uniform floor c_* > 0 from Lemma 8.19 and the prime cap ρ(t_rkhs) ≤ c_*/4:
```
λ_min(T_M[P_A] - T_P) ≥ c_*/4
```
for every M ≥ M_0^{unif} in Theorem 8.35.
- **Зависимости**: Lemma 8.19, Theorem 8.35, Corollary 8.21, Corollary 8.22
- **Используется в**: Theorem 11.4

### Lemma 8.5 (Lipschitz modulus for the periodized symbol)
```
g_{B,t}(ξ) := a(ξ) (1 - |ξ|/B)_+ e^{-4π²tξ²}
P_A(θ) := 2π Σ_{m∈ℤ} g_{B,t}(θ + m)
```
Then P_A ∈ Lip(1) with:
```
ω_{P_A}(h) ≤ L_A(B,t) h,    L_A(B,t) := 2π sup_{θ∈[-1/2,1/2]} Σ_{m∈ℤ} |g'_{B,t}(θ + m)|
```
- **Зависимости**: Lemma 8.11
- **Используется в**: Theorem 8.35


### Lemma 8.12 (Core contribution)
Let 0 < r < B. Set:
```
m_r := inf_{|ξ|≤r} a(ξ),    M_B := ||a||_{L^∞([-B,B])}
```
Then:
```
A_0 ≥ 4π m_r r (1 - r/B) e^{-4π²t_sym r²} - (M_B / (2π t_sym r)) e^{-4π²t_sym r²}
```
- **Зависимости**: нет
- **Используется в**: Lemma 8.14

### Lemma 8.13 (Shift-robust core mass)
Let 0 < r < B and |τ| ≤ B - r. Then the Fejér hat satisfies:
```
∫_{τ-r}^{τ+r} Λ_B(x) dx ≥ 2r²/B
```
- **Зависимости**: нет
- **Используется в**: Lemma 8.14

### Lemma 8.14 (Archimedean floor)
```
L_A^{up}(B, t_sym) := L_A(B, t_sym)
A_0(B, r, t_sym) := 2m_r r (1 - r/B) e^{-4π²t_sym r²} - (M_B / (4π²t_sym r)) e^{-4π²t_sym r²}
```
Then:
```
min_{θ∈𝕋} P_A(θ) ≥ A_0(B, r, t_sym) - (1/2) L_A^{up}(B, t_sym)
```
- **Зависимости**: Lemma 8.12, Lemma 8.13
- **Используется в**: Lemma 8.19

### Lemma 8.15 (Core slope bound)
For a(ξ) = log π - ℜψ(1/4 + iπξ) and every r > 0:
```
inf_{|ξ|≤r} a(ξ) ≥ a(0) - L_a r,    L_a ≤ 20π
```
where a(0) = γ + π/2 + log π + 3 log 2 > 0.
- **Зависимости**: нет
- **Используется в**: Lemma 8.17, Lemma 8.23

### Lemma 8.16 (Digamma monotonicity)
For ξ > 0 the Archimedean density satisfies:
```
a'(ξ) = -2π²ξ Σ_{n≥0} (n + 1/4) / ((n + 1/4)² + π²ξ²)²
```
hence a'(ξ) < 0 and a is even and strictly decreasing on [0, ∞). Moreover, for ξ ≥ 1:
```
|a'(ξ)| ≤ 1/|ξ| + 1/(2π²|ξ|³) ≤ (11/10) · (1/|ξ|)
```
- **Зависимости**: нет
- **Используется в**: Lemma 8.17

### Lemma 8.17 (Logarithmic growth bound)
For ξ ≥ 1 one has:
```
|a(ξ)| ≤ a(0) + (11/10) log(1 + ξ)
```
- **Зависимости**: Lemma 8.16
- **Используется в**: Lemma 8.19

### Lemma 8.18 (Sample-point bounds for a)
The Archimedean density satisfies:
```
a(1/2) ≥ 29/50,    a(3/2) ≥ -3/5,    a(5/2) ≥ -11/10
```
- **Зависимости**: нет
- **Используется в**: Lemma 8.19

### Lemma 8.19 (Uniform Archimedean floor (pointwise))
Fix t_sym = 3/50 and B_min = 3. Then for every B ≥ B_min and every θ ∈ 𝕋:
```
P_A(θ) ≥ c_* := 11/10
```
- **Константа**: c_* = 11/10 = 1.1
- **Зависимости**: Lemma 8.14, Lemma 8.15, Lemma 8.17, Lemma 8.18
- **Используется в**: Proposition 8.4, Corollary 8.21, Corollary 8.22, Theorem 8.35

### Definition 8.20 (Uniform Lipschitz constant)
For B ≥ B_min set:
```
L_A(B, t_sym) := 2π sup_{θ∈[-1/2,1/2]} Σ_{m∈ℤ} |g'_{B,t_sym}(θ + m)|
L_*(t_sym) := sup_{B≥B_min} L_A(B, t_sym)
```
- **Зависимости**: Lemma 8.5
- **Используется в**: Corollary 8.21

### Corollary 8.21 (Uniform discretisation threshold)
Assume c_* > 0 in Lemma 8.19, and let C_SB = 4 be the absolute constant of Lemma 8.30. Define:
```
M_0^{unif} := ⌈(C_SB L_*(t_sym)) / c_*⌉
```
Then for every B ≥ B_min and every M ≥ M_0^{unif}:
```
λ_min(T_M[P_A]) ≥ (1/2) c_*
```
- **Зависимости**: Lemma 8.19, Lemma 8.30
- **Используется в**: Proposition 8.4, Theorem 8.35

### Corollary 8.22 (Uniform prime cap time)
Assume c_* > 0 in Lemma 8.19. Define:
```
t^{unif}_{*,rkhs} := 1
```
Then for every t_rkhs ≥ t^{unif}_{*,rkhs} the symmetrised prime operator satisfies:
```
||T_P|| ≤ ρ(t_rkhs) ≤ ρ(1) < 1/25 < c_*/4
```
- **Константа**: t^{unif}_{*,rkhs} = 1
- **Зависимости**: Lemma 8.19, Lemma 9.24
- **Используется в**: Proposition 8.4, Theorem 8.35

### Lemma 8.23 (Analytic mean bound (auxiliary))
Let t_sym = 3/50 and B_min = 3, and define:
```
A_*(t_sym) := inf_{B≥B_min} A_0(B, t_sym)
α := 4π²t_sym
```
- **Зависимости**: Lemma 8.15
- **Используется в**: Lemma 8.24

### Lemma 8.24 (Analytic Lipschitz bound (auxiliary))
Let t_sym = 3/50, B_min = 3, and L_*(t_sym) = sup_{B≥B_min} L_A(B, t_sym). For B ≥ B_min:
```
Φ_{B,t_sym}(ξ) ≤ e^{-αξ²}
|Φ'_{B,t_sym}(ξ)| ≤ (B_min^{-1} + 8π²t_sym|ξ|) e^{-αξ²}
```
Then L_*(t_sym) ≤ L_up.
- **Зависимости**: Lemma 8.23, Definition 8.20
- **Используется в**: Theorem 8.35


## Секция 9: RKHS Contraction

### Lemma 9.1 (Gershgorin floor)
Let K be an N×N Hermitian matrix with entries k(x_i, x_j). Assume:
- k(x_i, x_i) ≥ c_0 for all i
- Σ_{j≠i} |k(x_i, x_j)| ≤ ρ_K for all i
Then λ_min(K) ≥ c_0 - ρ_K.
- **Зависимости**: нет
- **Используется в**: Lemma 9.2, Proposition 9.3

### Lemma 9.2 (Spectral floor for Gram matrices)
Assume the diagonal of K obeys k(x_i, x_i) ≥ c_0 and the off-diagonal mass satisfies:
```
Σ_{j≠i} |k(x_i, x_j)| ≤ ρ_K    for every i ∈ {1, ..., N}
```
Then λ_min(K) ≥ c_0 - ρ_K.
- **Зависимости**: Lemma 9.1
- **Используется в**: Proposition 9.3

### Proposition 9.3 (Operator sandwich)
Let T_k be positive on H_k with spectral bottom at least c_0, and suppose a discretisation or truncation K satisfies the off-diagonal bound of Lemma 9.2. For f = Σ_i a_i k(·, x_i):
```
||f||²_{L²(μ)} ≤ (1/(c_0 - ρ_K)) ||f||²_{H_k},    λ_min(K) ≥ c_0 - ρ_K
```
- **Зависимости**: Lemma 9.2
- **Используется в**: Theorem 8.35

### Lemma 9.4 (Rayleigh sampling identification)
For any Fejér×heat window Φ with Dirichlet sampling polynomial p(θ) = Σ_{k∈ℤ} Φ̂(k)e^{2πikθ}:
```
⟨T_M[P_A] p, p⟩_{L²(𝕋)} - (2M + 1)⟨T_P^{(M)} p, p⟩_{L²(𝕋)} = Q(Φ)
```
- **Зависимости**: Lemma 8.3
- **Используется в**: Theorem 8.35

### Lemma 9.5 (Geometric tail bound for SK(t))
For any node set with minimal spacing δ_K > 0:
```
S_K(t) := Σ_{m≠n} e^{-(α_m - α_n)²/(4t)} ≤ 2 Σ_{j≥1} e^{-j²δ_K²/(4t)} ≤ (2e^{-δ_K²/(4t)}) / (1 - e^{-δ_K²/(4t)})
```
- **Зависимости**: нет
- **Используется в**: Theorem 9.6, Proposition 9.7

### Theorem 9.6 (Strict contraction)
If t = t_min(K) is chosen so that S_K(t_min) ≤ (1 - w_max - ε_K) / √w_max for some ε_K ∈ (0, 1 - w_max), then ||T_P||_{H_K} ≤ ρ_K < 1 with ρ_K = w_max + √w_max S_K(t_min), and hence:
```
T_A - T_P ≽ (1 - ρ_K) T_A ≽ 0    on H_K
```
- **Зависимости**: Lemma 9.5
- **Используется в**: Theorem 8.35

### Proposition 9.7 (Dataset-free RKHS schedule)
Let w_max = sup Λ(n)/√n ≤ 2/e and let δ_K denote the minimal logarithmic spacing on [-K, K] (Lemma 9.13). For:
```
S_K(t) := Σ_{m≠n} e^{-(α_m - α_n)²/(4t)} ≤ (2e^{-δ_K²/(4t)}) / (1 - e^{-δ_K²/(4t)})
```
Choose:
```
t_min(K) = δ_K² / (4 ln((2 + η_K)/η_K)),    η_K ∈ (0, 1 - w_max)
```
Then S_K(t_min(K)) ≤ η_K and therefore ||T_P||_{H_K} ≤ w_max + √w_max S_K(t_min(K)) =: ρ_K < 1.
- **Зависимости**: Lemma 9.5
- **Используется в**: Theorem 8.35

### Lemma 9.8 (Effective weight cap)
For w(p^m) = log p / p^{m/2} one has 0 ≤ w(p^m) ≤ 2/e < 3/4, with the maximum attained at p^m = e². Hence w_max ≤ 2/e < 3/4 < 1 on every compact.
- **Константа**: w_max ≤ 2/e ≈ 0.7358
- **Зависимости**: нет
- **Используется в**: Theorem 9.6, Corollary 9.11

### Lemma 9.9 (Rayleigh lower bound for ||TP||)
For the prime operator T_P = Σ_{α_n} w_RKHS(n)|k_{α_n}⟩⟨k_{α_n}| with normalized kernel vectors ||k_α|| = 1:
```
||T_P|| ≥ sup_{n:α_n∈[-K,K]} w_RKHS(n) =: w_max^{RKHS}
```
- **Зависимости**: нет
- **Используется в**: Theorem 9.6

### Lemma 9.10 (Node gap on compacts)
For α_n = (log n)/(2π) and fixed K > 0 the active set is {2, ..., ⌊e^{2πK}⌋} and the minimal spacing satisfies:
```
δ_K := min_{m≠n, α_m,α_n∈[-K,K]} |α_m - α_n| ≥ 1 / (2π(⌊e^{2πK}⌋ + 1))
```
- **Зависимости**: нет
- **Используется в**: Proposition 9.7, Lemma 9.13

### Corollary 9.11 (Two-scale decoupling (uniform))
Let t_rkhs ≥ t^{unif}_{*,rkhs} be the RKHS scale and let t_sym > 0 be the Fejér×heat parameter. If L_A(B, t_sym) ≤ L_A^* and min P_A ≥ c_* > 0, then Corollary 8.6 applies with the uniform cap ||T_P|| ≤ ρ(t_rkhs) and modulus L_A^*. Thus the symbol parameter controls the modulus ω_{P_A} (symbol barrier), while the RKHS scale controls only ||T_P|| (contraction).
- **Зависимости**: Lemma 9.8, Corollary 8.22
- **Используется в**: Theorem 8.35

### Theorem 9.12 (One-prime induction)
Upon crossing an activity threshold that introduces a single new node with weight w_new:
```
||T_P^{new}|| ≤ ||T_P^{old}|| + w_new
```
Consequently, if ||T_P^{old}|| ≤ ρ_K^{old} < 1 and ρ_K^{old} + w_new < 1, then T_A - T_P^{new} ≽ 0 on H_K.
- **Зависимости**: Lemma 9.8
- **Используется в**: Theorem 8.35

### Lemma 9.13 (Node separation)
For α_n = log n/(2π) and fixed K > 0 one has a finite active set {n : α_n ∈ [-K, K]} = {2, ..., ⌊e^{2πK}⌋} and a positive minimal gap:
```
δ_K := min_{m≠n, α_m,α_n∈[-K,K]} |α_m - α_n| ≥ 1 / (2π(⌊e^{2πK}⌋ + 1))
```
- **Зависимости**: нет
- **Используется в**: Proposition 9.7

### Lemma 9.14 (Shift-robust sampling window)
Let 0 < r ≤ δ_K and τ ∈ [-K, K]. Then for every t > 0:
```
Σ_{ξ_n∈[-K,K]} w_RKHS(n) ∫_{τ-r}^{τ+r} k_t(x, ξ_n)² dx ≤ w_max^{RKHS} + √(w_max^{RKHS}) S_K(t)
```
- **Зависимости**: Proposition 9.7
- **Используется в**: Theorem 8.35

### Lemma 9.15 (Energy identity)
For any finite sample x_1, ..., x_M and coefficients a ∈ ℝ^M:
```
||Σ_{m=1}^M a_m k_t(·, x_m)||²_{H_k} = a^⊤ (k_t(x_m, x_n))_{m,n=1}^M a
```
- **Зависимости**: нет
- **Используется в**: Lemma 9.16

### Lemma 9.16 (Off-diagonal sum bound)
For every t > 0 and K ≥ 1:
```
S_K(t) ≤ (2e^{-δ_K²/(4t)}) / (1 - e^{-δ_K²/(4t)})
```
and in particular S_K(t_min(K)) ≤ η_K.
- **Зависимости**: Lemma 9.15
- **Используется в**: Theorem 9.6


## Секция 10: Prime Cancellation (D3)

### Lemma 10.1 (Dispersion via A2/A3 data)
Assume the A3 hypotheses: P_A ∈ Lip(1) with min P_A ≥ c_0 > 0 (Lemma 8.11 and Lemma 8.33), the uniform RKHS cap ||T_P|| ≤ ρ(t_rkhs) (Corollary 8.22), and the two-scale separation of Lemma 8.32. Then there exist a scale t_sym (with t_rkhs fixed) and a sequence δ_A → 0 such that for every even RKHS test f supported in [-K, K]:
```
|Σ_{p≤A} (f(p) - 𝔼_{P∩[1,A]}f)| ≤ C(K)(ω_{P_A}(t_sym) + ε_K(t_rkhs)) =: C(K) δ_A
```
- **Зависимости**: Lemma 8.11, Lemma 8.33, Corollary 8.22, Lemma 8.32
- **Используется в**: Theorem 10.2

### Theorem 10.2 (D3: Structural contraction)
If Lemma 10.1 provides a gain δ_* > 0 after fixing the scales, then there exists δ_0 ∈ (0, δ_*) with:
```
||T_P||_{H_K} ≤ 1 - δ_0
```
Moreover, there is a constant C_{D3} > 0 (the uniform remainder in the mixed Toeplitz bound with Lipschitz symbol P_A) such that for M ≫ K³:
```
λ_min(T_M[P_A] - T_P) ≥ (1 + δ_0) log(1+K) - C_{D3}
```
- **Зависимости**: Lemma 10.1
- **Используется в**: Corollary 10.3

### Corollary 10.3 (Amplitude closure)
With the auxiliary suppressors (Roads B/C) and Theorem 10.2 we obtain:
```
Γ(K) ≥ (1 + δ_0) log(1 + K) - C_{D3}
```
closing the amplitude gate.
- **Зависимости**: Theorem 10.2
- **Используется в**: Theorem 10.6

### Theorem 10.6 (Structural prime cancellation)
Under A2 and A3 the criteria AC-D3.1 hold. Furthermore AC-D3.1 ⇒ AC-D3.2 with δ_A → 0, hence:
```
Disp_K(A) ≤ C(K) δ_A → 0    as A → ∞
```
- **Зависимости**: Lemma 8.11, Lemma 8.33, Lemma 8.34, Lemma 8.32, Corollary 8.22, Lemma 10.1
- **Используется в**: Theorem 11.3

### Corollary 10.7 (D3-lock)
Under Theorem 10.6, for any normalized RKHS test f:
```
|Σ_{p≤A} (f(p) - 𝔼_{P∩[1,A]}f)| ≤ C(K) δ_A → 0    as A → ∞
```
- **Зависимости**: Theorem 10.6
- **Используется в**: Theorem 11.3

### Proposition 10.8 (AB(K) supplied by A3)
Lemmas 8.19, 8.11, 8.34, and 8.32 ensure the AB(K) conditions with constants depending only on (K, c_*, ρ(t_rkhs)).
- **Зависимости**: Lemma 8.19, Lemma 8.11, Lemma 8.34, Lemma 8.32
- **Используется в**: Theorem 10.9

### Theorem 10.9 (Amplitude gate without explicit D3 assumptions)
Under A2/A3, Proposition 10.8 and Corollary 8.31 imply:
```
⟨(T_M[P_A] - T_P)f, f⟩ ≥ (c_*/2 - ρ(t_rkhs)) ||f||²_2
```
for every f supported in [-K, K]. In particular, if ρ(t_rkhs) < c_*/2 the mixed lower bound is positive; density and continuity then yield Q ≥ 0 on the Weil class and by Weil's positivity criterion, RH would hold.
- **Зависимости**: Proposition 10.8, Corollary 8.31
- **Используется в**: Theorem 11.4

## Секция 11: Weil Criterion Linkage and Main Theorem

### Theorem 11.1 (Weil's positivity criterion, normalized)
Let Q be the Weil functional attached to ζ(s) in the normalization of Section 5, and let W be the Weil cone described in Section 4. Then the following are equivalent:
- (i) The Riemann Hypothesis holds.
- (ii) Q(Φ) ≥ 0 for every Φ ∈ W.
- **Тип**: Эквивалентность (RH ⟺ Q ≥ 0)
- **Зависимости**: нет (классический результат)
- **Используется в**: Theorem 11.2

### Theorem 11.2 (Riemann Hypothesis)
If (T0)+(A1')+(A2)+(A3)+(RKHS) hold, then the Riemann Hypothesis is true.
- **Зависимости**: Theorem 11.4, Theorem 11.1
- **Используется в**: (Главный результат)

### Theorem 11.3 (Weil sufficiency pack)
Assume the hypotheses of Theorem 11.4, namely (T0), density (A1') on each compact [-K, K] (Theorem 6.3), continuity (A2) (Lemma 7.3), the mixed bridge (A3) (Theorem 8.35) with uniform margin c_* > 0, and prime control via the uniform RKHS cap (Corollary 8.22). Then Q(Φ) ≥ 0 for all Φ ∈ W, and hence the Riemann Hypothesis follows from Weil's positivity criterion.
- **Зависимости**: Theorem 11.4, Theorem 6.3, Lemma 7.3, Theorem 8.35, Corollary 8.22, Lemma 9.23, Lemma 9.4
- **Используется в**: Theorem 11.2

### Theorem 11.4 (Main positivity on W) — ГЛАВНАЯ ТЕОРЕМА
Assume (T0), (A1'), (A2), and the uniform A3 bridge inequality (Theorem 8.35). Then:
```
Q(Φ) ≥ 0    for every even, real, compactly supported Φ ∈ W
```
where W = ⋃_{K>0} W_K is the Weil cone from Section 4.
- **Зависимости**: Theorem 8.35, Theorem 6.3, Lemma 7.3, Proposition 5.1, Corollary 8.22
- **Используется в**: Theorem 11.2, Theorem 11.3

### Theorem 8.35 (Uniform A3 bridge) — КЛЮЧЕВАЯ ЛЕММА
For every B ≥ B_min and every M ≥ M_0^{unif}:
```
λ_min(T_M[P_A] - T_P) ≥ c_*/4 > 0
```
- **Константы**: c_* = 11/10, B_min = 3, t_sym = 3/50, M_0^{unif} = ⌈C_SB L_*(t_sym)/c_*⌉, t^{unif}_{*,rkhs} = 1
- **Зависимости**: Lemma 8.19, Corollary 8.21, Corollary 8.22, Lemma 8.5, Lemma 8.24, Proposition 9.3, Theorem 9.6
- **Используется в**: Theorem 11.4, Proposition 8.4

## Приложение A: Notation

### Критические константы (mainline)

| Константа | Значение | Источник |
|-----------|----------|----------|
| t_sym | 3/50 | Lemma 8.19 |
| B_min | 3 | Lemma 8.19 |
| c_* | 11/10 | Lemma 8.19 |
| M_0^{unif} | ⌈C_SB L_*(t_sym)/c_*⌉ | Corollary 8.21 |
| t^{unif}_{*,rkhs} | 1 | Corollary 8.22 |
| w_max | 2/e ≈ 0.7358 | Lemma 9.8 |
