# БРИФ: Twin Prime Conjecture через Q3 Spectral Framework

**Дата:** 2025-12-11
**Цель:** Полный контекст для LLM чтобы избежать типичных ошибок

---

## ЦЕЛЬ ПРОЕКТА

Доказать TPC (Twin Prime Conjecture) через спектральный подход Q3.

**Логика:**
```
SC2: finite twins ⟹ R(Φ_X) = O(1)
CONTRAPOSITIVE: R(Φ_X) → ∞ ⟹ infinite twins

Numerically: R ~ X^{0.72} → ∞
Need: analytical proof that R → ∞
```

---

## ПРАВИЛЬНЫЕ ОПРЕДЕЛЕНИЯ

### Базовые объекты

```
ξ_p = log(p)/(2π)                    — spectral coordinate для prime p
N = |T(X)| = количество twin primes до X
span = ξ_N - ξ_1 ~ log(X)/(2π)       — размах
t > 0                                 — smoothing parameter (fixed)
```

### Gaussian Gram matrix G

```
G_{pq} = √(2πt) · exp(-(ξ_p - ξ_q)²/(4t))
```

G симметричная и positive definite для strictly increasing ξ.

### Commutator matrix A (КРИТИЧЕСКИ ВАЖНО!)

```
A = [G, diag(ξ)] = G·diag(ξ) - diag(ξ)·G

Поэлементно:
A_{pq} = (ξ_q - ξ_p) · G_{pq}
```

**НЕ ПУТАТЬ с:**
```
НЕПРАВИЛЬНО: Ξ_{ij} = (ξ_i + ξ_j)/2 · G_{ij}, C = ΞG - GΞ
ЭТО ДРУГОЙ объект!
```

### Commutator energy matrix Q

```
Q = AᵀA

Поэлементно:
Q_{pq} = Σ_k A_{kp} · A_{kq}
```

### Twin weights и vector

```
λ_p = Λ(p)·Λ(p+2) ≈ (log p)²    — twin weight

Φ_X = Σ_{p ∈ T(X)} λ_p · e_p    — twin vector

Важно: λ_p > 0, поэтому Φ_X ∈ CONE (все координаты ≥ 0)
```

### Энергии

```
E_lat(λ) = λᵀ G λ = Σ_{p,q} λ_p G_{pq} λ_q       (lattice/Gram energy)

E_comm(λ) = ‖Aλ‖² = λᵀ Q λ = Σ_p (Σ_q A_{pq} λ_q)²  (commutator energy)

ВАЖНО: E_comm использует EUCLIDEAN норму, НЕ G-норму!
```

### Rayleigh quotient

```
R(λ) = E_comm(λ) / E_lat(λ)
```

### Twin sum

```
S₂(X) = Σ_{n≤X} Λ(n)·Λ(n+2)

Hardy-Littlewood: S₂(X) ~ 2C₂·X где C₂ ≈ 0.66
```

---

## ПРОСТРАНСТВА (НЕ ПУТАТЬ!)

### Positive Cone C

```
C = {λ ∈ ℝ^N : λ_i ≥ 0 для всех i}

Twin vector Φ_X ∈ C (все λ_p > 0!)
```

### Mean-zero subspace V₀

```
V₀ = {λ ∈ ℝ^N : Σ_i λ_i = 0}

Twin vector Φ_X ∉ V₀ (сумма > 0!)
```

### КРИТИЧЕСКИ ВАЖНО:

```
V₀ ∩ C = {0}

Эти пространства пересекаются ТОЛЬКО в нуле!
Результаты на V₀ НЕ применимы напрямую к cone C!
```

---

## ЧИСЛЕННЫЕ РЕЗУЛЬТАТЫ (ПРОВЕРЕНО)

### Power law scaling

| Величина | Scaling | Комментарий |
|----------|---------|-------------|
| E_comm(Φ_X) | ~ X^{2.885} | Commutator energy |
| E_lat(Φ_X) | ~ X^{2.165} | Lattice energy |
| R(Φ_X) | ~ X^{0.720} | **РАСТЁТ!** |
| S₂(X) | ~ X^{1.04} | Hardy-Littlewood |
| E_comm / S₂ | ~ X^{1.79} | **НЕ log²X!** |

### min_cone R (прямая оптимизация)

```
N=35:   min_cone R = 3.66
N=126:  min_cone R = 11.79
N=342:  min_cone R = 27.30
N=705:  min_cone R = 51.22

Power law fit: min_cone R ~ 0.17 × N^{0.868}
```

**Вывод:** min_cone R → ∞ как N → ∞

### Row sum behavior

```
Sum(Q) ~ N^{2.94}
Sum(G) ~ N^{2.00}
R(1) = Sum(Q)/Sum(G) ~ N^{0.92}
```

---

## ЧТО ДОКАЗАНО (Aristotle verified)

### 1. Cone-Kernel Separation

```
Theorem: C ∩ ker(A) = {0}

Если λ ∈ cone (λ_i ≥ 0) и Aλ = 0, то λ = 0.

Proof: Aristotle (project dad24643), 88 lines Lean4
```

### 2. SC2 (Finite Stabilization)

```
Theorem: Finite twins ⟹ R(Φ_X) = O(1)

Proof: Если twins конечны, то для X ≥ X₀:
- N = const (фиксированное число twins)
- Φ_X = const (фиксированный вектор)
- Q, G = const (фиксированные матрицы)
- R = const (фиксированное число)
```

### 3. THE GAP (conditional)

```
Theorem (conditional on Lemma 3):
IF Sum(Q) ≥ c·N²·span²
THEN R(1) = Sum(Q)/Sum(G) ≥ c'·span² → ∞

Proof: Aristotle (project d7048fc1), 122 lines Lean4
Status: CONDITIONAL on Lemma 3
```

---

## ЧТО ПРОВАЛИЛОСЬ (НЕ ПОВТОРЯТЬ!)

### 1. Rowsum bound approach

```
ИДЕЯ: min(Q_rowsum)/max(G_rowsum) как lower bound на R

РЕЗУЛЬТАТ: ПРОВАЛ!
При N=4565: min(Q_rowsum) = -299810 (ОТРИЦАТЕЛЬНО!)

ПРИЧИНА: Q = AᵀA is PSD, но row sums могут быть отрицательными
когда off-diagonal элементы доминируют
```

### 2. Perron-Frobenius

```
ИДЕЯ: Использовать теорему Perron-Frobenius для Q

РЕЗУЛЬТАТ: НЕ ПРИМЕНИМО
Q имеет отрицательные off-diagonal элементы
```

### 3. Uniform constant

```
ИДЕЯ: E_comm ≥ c(t) · E_lat с UNIFORM c(t)

РЕЗУЛЬТАТ: НЕ СУЩЕСТВУЕТ
Численно: c ~ N^{-0.1} (убывает с N)

НО: min_cone R ~ N^{0.87} (растёт!)
Важен GROWTH, не uniform bound
```

### 4. E_comm ≤ S₂·log²X bound

```
ИДЕЯ: Upper bound на E_comm через S₂

РЕЗУЛЬТАТ: НЕВЕРНО!
Численно: E_comm/S₂ ~ X^{1.79}
Это power law, НЕ log²X!

log²(100)=21, log²(10000)=85 → 4x increase
E_comm/S₂: 3.5 → 13382 → 3800x increase!
```

---

## ТЕКУЩИЕ ПОДХОДЫ

### Approach 1: Contradiction (RUNNING)

```
1. Assume finite twins
2. → finite support for Φ_X
3. → E_comm = O(log⁴X) (bounded!)
4. But Q3 spectral gap needs E_comm ≥ X^δ
5. → CONTRADICTION
6. → Infinite twins!

Status: Aristotle project 9f9e518f running
```

### Approach 2: Direct growth proof

```
Prove: R(Φ_X) ≥ f(X) where f(X) → ∞

Sufficient: Any f(X) → ∞ works!
Even f(X) = log(log(X)) would suffice.

Numerically: R ~ X^{0.72}
```

---

## КРИТИЧЕСКИЕ ПРАВИЛА

1. **Коммутатор = [G, diag(ξ)]**
   - НЕ [Ξ,G] где Ξ = weighted position matrix!

2. **Норма = Euclidean**
   - E_comm = ‖Aλ‖²
   - НЕ G-weighted inner product!

3. **Twin vector в CONE**
   - Φ_X ∈ C (все координаты ≥ 0)
   - Φ_X ∉ V₀ (сумма ≠ 0)

4. **Uniform constant НЕТ**
   - Но есть GROWTH: min_cone R ~ N^{0.87}

5. **E_comm/S₂ = power law**
   - ~ X^{1.79}, НЕ log²X!

---

## КЛЮЧЕВЫЕ ФАЙЛЫ

### Численные тесты

```
src/direct_min_R_test.py      — min_cone R ~ N^{0.868}
src/energy_s2_correlation.py  — E_comm/S₂ ~ X^{1.79}
src/large_N_test.py           — rowsum FAILS at N=4565
src/anchor_analysis.py        — R(1) = Sum(Q)/Sum(G) analysis
```

### Aristotle проекты

```
lean_aristotle/output/01_cone_kernel_separation_aristotle.md  ✅ DONE
lean_aristotle/output/99_THE_GAP_growth_target_aristotle.md   ✅ CONDITIONAL
lean_aristotle/input/contradiction_small_S2.md                🔄 RUNNING
```

### Paper

```
paper/main.tex                           — Main document
paper/sections/hypothesis_B1_prime.tex   — Cone-Kernel proof
paper/sections/SC2_arithmetic.tex        — SC2 proof
paper/sections/target_theorem.tex        — Main theorem (equivalence)
```

---

## SUMMARY

**Что имеем:**
- TPC ⟺ R(Φ_X) → ∞ (equivalence, proven)
- Numerically R ~ X^{0.72} → ∞
- Cone-Kernel separation (Lean verified)
- SC2: finite twins ⟹ R = O(1) (proven)

**Что нужно:**
- Analytical proof that R(Φ_X) → ∞
- Or: proof that finite twins gives contradiction

**Текущий подход:**
- Contradiction: finite twins → bounded E_comm → violates Q3 → infinite twins
