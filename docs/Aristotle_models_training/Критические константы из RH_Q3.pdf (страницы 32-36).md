# Критические константы из RH_Q3.pdf (страницы 32-36)

> ⚠️ **STATUS (2026-01-24): legacy / two‑scale spec.**
> Этот файл отражает старую двухмасштабную ветку (t_sym vs t_rkhs_cap).
> **Не использовать как канон** для текущей single‑scale цепочки.
>
> Канонические ссылки:
> - `ACTIVE/chain_status.md`
> - `ACTIVE/refs/SPECS_INDEX.md`
> - `ACTIVE/refs/Q3_BLOCK_MAP.md`

## Секция 9: RKHS Contraction

### Lemma 9.10 (Node gap on compacts)
- α_n = log n / (2π)
- δ_K := min_{m≠n, α_m,α_n∈[-K,K]} |α_m - α_n| ≥ 1 / (2π(⌊e^{2πK}⌋ + 1))

### Corollary 9.11 (Two-scale decoupling)
- t_rkhs ≥ t^{unif}_{*,rkhs} — RKHS scale
- t_sym > 0 — Fejér×heat parameter
- L_A(B, t_sym) ≤ L^*_A — Lipschitz bound
- min P_A ≥ c_* > 0 — Archimedean floor
- ||T_P|| ≤ ρ(t_rkhs) — uniform cap
- ω_{P_A} (symbol barrier) — modulus

### Theorem 9.12 (One-prime induction)
- ||T_P^{new}|| ≤ ||T_P^{old}|| + w_{new}
- ρ_K^{old} < 1 и ρ_K^{old} + w_{new} < 1 ⟹ T_A - T_P^{new} ≽ 0 на H_K

### Формулы (9.12)
```
S_K(t) = 2e^{-δ_K²/(4t)} / (1 - e^{-δ_K²/(4t)})

ρ_K = w_max + √(w_max) · S_K(t_min)
```

### Lemma 9.13 (Node separation)
- δ_K := min{ξ_{n+1} - ξ_n : ξ_n, ξ_{n+1} ∈ [-K, K]} ≥ 1 / (2π(⌊e^{2πK}⌋ + 1))

### Формула (9.15)
```
t_min(K) := δ_K² / (4 ln((2 + η_K)/η_K))
```

### Lemma 9.18 (Uniform RKHS cap)
```
ρ(t) := 2 ∫_0^∞ y e^{y/2} e^{-4π²ty²} dy
     = 2[1/(8π²t) + √π/(64π³t√t) exp(1/(64π²t)) erfc(-1/(8π√t))]
```
- ρ(t) → 0 as t → ∞
- ρ(t) строго убывает

### Lemma 9.19 (Early block)
```
Σ_{n≤N} Λ(n)/√n ≤ Σ_{n≤N} log n / √n ≤ 2√N log N
```

### Lemma 9.20 (Log-Gaussian tail)
- Для t ≥ 1/(16π²) и N ≥ 2, N_0 := max{N, e²}:
```
Σ_{n>N} Λ(n)/√n · e^{-4π²t(log n)²} ≤ e^{-4π²t(log N_0)²} / (8π²t)
```

### Proposition 9.21 (Heat cap via early/tail split)
```
ρ_heat(K; t, N) := 2 Σ_{ξ_n∈[-K,K], n≤N} Λ(n)/√n · e^{-4π²t(log n)²} + tail

ρ_heat(K; t, N) ≤ 4√N log N + e^{-4π²t(log N_0)²} / (4π²t)
```

### Corollary 9.22 (Uniform prime cap at the analytic scale)
- t_rkhs ≥ t^{unif}_{*,rkhs} (из Corollary 8.22)
```
||T_P|| ≤ ρ(t_rkhs) ≤ c_*/4
```

### Lemma 9.23 (RKHS-Weil Isometry)
- (X, μ) — measure space
- k: X × X → ℝ — positive-definite kernel
- H_k — RKHS
- Φ: H_k → W — extends uniquely to isometry

### Lemma 9.24 (Closed-form upper bound for prime trace)
```
ρ(t) ≤ 2 ∫_0^∞ y e^{y/2} e^{-4π²ty²} dy
```
- С a = 4π²t и b = 1/2:
```
ρ(t) ≤ 1/(4π²t) + √π/(2(4π²t)^{3/2}) exp(1/(16π²t))
```
- При t = 1: ρ(1) < 1/25
- ||T_P|| ≤ ρ(1) < 1/25 для всех компактов

### Lemma 9.25 (Shift-robust trace cap — enhanced)
- Для K > 0, B > 0, t > 0, |τ| ≤ K:
```
||T_P[Φ_{B,t,τ}]||_{L²→L²} ≤ tr T_P = 2 Σ_{n≥2} Λ(n)/√n · e^{-4π²t(log n/(2π)-τ)²}
                          ≤ e^{πK}(ρ(t) + 2πK σ(t))
```
где:
```
ρ(t) := 2 ∫_0^∞ y e^{y/2} e^{-4π²ty²} dy
σ(t) := 2 ∫_0^∞ e^{y/2} e^{-4π²ty²} dy ≤ √π/(π√t) exp(1/(64π²t))
```

## Ключевые константы (сводка)

| Константа | Значение/Формула | Источник |
|-----------|------------------|----------|
| w_max^{RKHS} | ≤ 2/e ≈ 0.7358 | Lemma G.6 |
| δ_K | ≥ 1/(2π(⌊e^{2πK}⌋+1)) | Lemma 9.10, 9.13 |
| t_min(K) | δ_K²/(4 ln((2+η_K)/η_K)) | (9.15) |
| ρ(1) | < 1/25 = 0.04 | Lemma 9.24 |
| c_*/4 | 11/40 = 0.275 | Lemma 8.19 |


## Секция 8: Toeplitz-Symbol Bridge (страницы 24-28)

### Lemma 8.25 (Uniform bounds)
```
0 ≤ Fej_M(θ) ≤ M + 1
0 ≤ h_t(θ) ≤ C/√t
```
где:
```
Fej_M(θ) := 1/(M+1) · (sin(π(M+1)θ) / sin(πθ))²
h_t(θ) := Σ_{k∈ℤ} e^{-4π²tk²} e^{2πikθ} = 1 + 2 Σ_{k≥1} e^{-4π²tk²} cos(2πkθ)
```

### Lemma 8.26 (Lipschitz modulus)
- f ∈ C¹([-K, K]) с ограниченной производной
- f_{M,t}(x) := (f * (Fej_M * h_t))(x)
```
ω_{f_{M,t}}(δ) ≤ C ||f'||_{L^∞([-K,K])} · (√(M+1)/√t) · δ
```

### Corollary 8.27 (Modulus bound for the Arch symbol)
```
ω_{P_A}(δ) ≤ C · (√(M+1)/√t_sym + 1) · δ
```

### Lemma 8.28 (Hoffman-Wielandt and Ky Fan guard)
- A, B ∈ ℂ^{M×M} — Hermitian
- E := B - A
- λ_i^↓(A) — собственные значения в убывающем порядке
```
Σ_{i=1}^k |λ_i^↓(B) - λ_i^↓(A)| ≤ √k ||E||_F
```
где ||E||_F = √(Tr(E*E)) — норма Фробениуса

В частности:
```
|λ_min(B) - λ_min(A)| ≤ ||E||_F
```

### Corollary 8.29 (Frobenius slack for Toeplitz glue)
- T_M[P] — Toeplitz-матрица
- ||ΔT||_F ≤ ε
```
|λ_min(T_M[P + ΔP]) - λ_min(T_M[P])| ≤ ε
```
Следовательно, если A := T_M[P_A] - T_P^{cap} удовлетворяет λ_min(A) ≥ δ > 0 и ||T_P - T_P^{cap}||_F ≤ ε:
```
λ_min(T_M[P_A] - T_P) ≥ δ - ε
```

### Lemma 8.30 (Szegő-Böttcher barrier with explicit modulus) — КРИТИЧЕСКАЯ
- P_A — Archimedean symbol из §8.3
- **C_SB = 4** — абсолютная константа
```
λ_min(T_M[P_A]) ≥ min_{θ∈𝕋} P_A(θ) - C_SB · ω_{P_A}(1/(2M))
```

### 8.6 A3 locking summary

Ключевые компоненты:
1. **Lemma 8.34** — bounded-overlap control on caps
2. **Lemma 8.32** — uniform two-scale separation
3. **Corollary 8.22** — uniform RKHS prime cap: t_rkhs ≥ t^{unif}_{*,rkhs}
4. **Theorem 8.35** — combines uniform symbol floor c_* > 0 with RKHS prime cap

### Corollary 8.31 (Lock)
Под гипотезами Lemmas 8.34, 8.32 и Corollary 8.22:
- A3 lock closes with a constant depending only on the overlap bound and the uniform prime cap

### Lemma 8.32 (Two-scale separation, uniform)
- P_A — Archimedean symbol из §8.3
- t_sym — Fejér×heat parameter
- t_rkhs ≥ t^{unif}_{*,rkhs} — RKHS scale из Corollary 8.22
```
min_{θ∈𝕋} P_A(θ) ≥ c_*
```
По Lemma 8.19 и RKHS cap ||T_P|| ≤ ρ(t_rkhs) из Corollary 8.22.
**Вывод**: symbol scale t_sym и RKHS scale t_rkhs **decoupled** в uniform branch.

### Lemma 8.33 (Lipschitz symbol with positive floor implies A3 prerequisites)
- P_A ∈ Lip(1) с min_𝕋 P_A ≥ c_0 > 0
- T_{P_A} — Toeplitz operator
```
T_{P_A} ≽ c_0 I,    ||T_{P_A}||_op ≤ ||P_A||_{L^∞}
```
В частности, ρ_K ≥ ||P_A||_{L^∞} — A3-lock positivity and boundedness hypotheses hold.

### Lemma 8.34 (Combining with the RKHS cap)
- P_A — как выше
- RKHS cap (Corollary 8.22)
```
||T_P|| ≤ ρ(t_rkhs)
```
Тогда T_{P_A} одновременно удовлетворяет positivity floor и operator-norm bound для A3-lock.

### A3 input summary (uniform version)

**(A3-U.1) Uniform Arch floor**: Lemma 8.19 даёт **c_* = 11/10** на 𝕋 для всех B ≥ B_min.

**(A3-U.2) Uniform prime cap**: Corollary 8.22 даёт t^{unif}_{*,rkhs} с **ρ(t_rkhs) ≤ c_*/4** для всех t_rkhs ≥ t^{unif}_{*,rkhs}.

**(A3-U.3) Uniform discretisation**: Corollary 8.21 даёт **M_0^{unif}** такое, что λ_min(T_M[P_A]) ≥ c_*/2 для всех M ≥ M_0^{unif}.

### Theorem 8.35 (Uniform A3 bridge) — ГЛАВНАЯ ТЕОРЕМА СЕКЦИИ 8

**Условия**:
- Uniform floor c_* > 0 из Lemma 8.19
- B ≥ B_min
- **t_sym = 3/50**
- t_rkhs ≥ t^{unif}_{*,rkhs}
- M ≥ M_0^{unif} (из Corollary 8.21)

**Утверждение**:
```
λ_min(T_M[P_A] - T_P) ≥ c_*/4 > 0
```

и для ассоциированных Fejér×heat test functions:
```
Q(Φ_{B,t_sym}) ≥ 0
```

**Доказательство** (sketch):
1. Lemma 8.19: min_{θ∈𝕋} P_A(θ) ≥ c_* для всех B ≥ B_min
2. Corollary 8.21: C_SB · ω_{P_A}(1/(2M)) ≤ c_*/2 для M ≥ M_0^{unif}
3. Corollary 8.22: ||T_P|| ≤ ρ(t_rkhs) ≤ c_*/4
4. Итого: λ_min(T_M[P_A] - T_P) ≥ c_* - c_*/2 - c_*/4 = c_*/4
5. Lemma 8.10 converts matrix margin into Q(Φ_{B,t}) ≥ 0

## СВОДКА КРИТИЧЕСКИХ КОНСТАНТ ДЛЯ thm_8_35

| Константа | Значение | Источник | Роль |
|-----------|----------|----------|------|
| **c_*** | **11/10 = 1.1** | Lemma 8.19 | Archimedean floor |
| **t_sym** | **3/50 = 0.06** | Lemma 8.19 | Symbol smoothing scale |
| **B_min** | **3** | Lemma 8.19 | Minimum bandwidth |
| **C_SB** | **4** | Lemma 8.30 | Szegő-Böttcher constant |
| **M_0^{unif}** | **⌈C_SB · L_*(t_sym)/c_*⌉** | Corollary 8.21 | Discretisation threshold |
| **t^{unif}_{*,rkhs}** | **1** | Corollary 8.22 | RKHS time scale |
| **ρ(1)** | **< 1/25 = 0.04** | Lemma 9.24 | Prime cap at t=1 |
| **c_*/4** | **11/40 = 0.275** | Theorem 8.35 | Final margin |
