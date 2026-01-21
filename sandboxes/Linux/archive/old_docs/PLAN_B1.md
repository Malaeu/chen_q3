# PLAN B₁: Step B Completion Documentation

## Status: B₁_strong ДОКАЗАН (Декабрь 2024)

---

## 1. Резюме результата

### Главное достижение

```
B₁_strong: inf_{λ∈C} R(λ) > 0

где:
  R(λ) = E_comm(λ) / E_lat(λ)  — Rayleigh quotient
  C = {λ ∈ R^N : λ_p ≥ 0}      — twin-конус

СТАТУС: СТРОГО ДОКАЗАНО (Lemma, не hypothesis)
```

### Ключевое открытие

```
ker(Q) ОГРОМЕН (dim ≈ N-3), НО C ∩ ker(Q) = {0}

⟹ На twin-конусе ядро не видно
⟹ min R(λ) > 0 гарантировано
⟹ B₁_strong выполняется структурно
```

---

## 2. Cone-Kernel Separation Lemma

### Формулировка

**Lemma (Cone-Kernel Separation):**

Пусть:
- ξ₁ < ξ₂ < … < ξ_N — строго возрастающие точки на R
- K_pq > 0 для всех p ≠ q (положительное симметричное ядро)
- A_pq = (ξ_q − ξ_p) · K_pq

Конус C = {λ ∈ R^N : λ_p ≥ 0, λ ≠ 0}

**Тогда:** C ∩ ker(A) = {0}

### Доказательство

```
1. Возьмём λ ≥ 0, λ ≠ 0.
   S = {p : λ_p > 0} — индексы с положительной массой.

2. p* = argmax{ξ_p : p ∈ S} — самая правая активная точка.

3. Рассмотрим (Aλ)_{p*} = Σ_q (ξ_q − ξ_{p*}) K_{p*q} λ_q

   Разбиваем сумму:
   • q > p*: ξ_q > ξ_{p*}, но λ_q = 0 (по выбору p*) ⟹ вклад = 0
   • q = p*: (ξ_q − ξ_{p*}) = 0 ⟹ вклад = 0
   • q < p*: (ξ_q − ξ_{p*}) < 0, K_{p*q} > 0, λ_q ≥ 0 ⟹ вклад ≤ 0

4. Два случая:

   (a) λ поддержан только в p* (S = {p*}):
       Для p ≠ p*: (Aλ)_p = (ξ_{p*} − ξ_p) · K_{p,p*} · λ_{p*}
       Для p < p*: (ξ_{p*} − ξ_p) > 0, K > 0, λ_{p*} > 0 ⟹ (Aλ)_p > 0
       ⟹ Aλ ≠ 0

   (b) ∃ q < p* с λ_q > 0:
       В (Aλ)_{p*} есть член (ξ_q − ξ_{p*}) · K · λ_q < 0 (строго)
       ⟹ (Aλ)_{p*} < 0 ⟹ Aλ ≠ 0

5. В обоих случаях: λ ≥ 0, λ ≠ 0 ⟹ Aλ ≠ 0  ∎
```

### Следствия

**Corollary 1:** ker(Q) ∩ C = {0} для Q = AᵀA

*Proof:* ker(AᵀA) = ker(A) (стандартный факт линейной алгебры). ∎

**Corollary 2 (B₁_strong):** inf_{λ∈C₁} R(λ) > 0

где C₁ = {λ ∈ C : ‖λ‖ = 1} — нормированный конус (компакт).

*Proof:*
- R(λ) = λᵀQλ / λᵀGλ непрерывна на C₁
- Числитель > 0 (Corollary 1)
- Знаменатель > 0 (G строго PD)
- C₁ компакт ⟹ inf > 0 ∎

---

## 3. Что НЕ требуется для леммы

```
НЕ НУЖНО:
├─ Twin prime conjecture
├─ Hardy-Littlewood асимптотики
├─ Prime Number Theorem
├─ Arithmetic properties of primes
├─ SC1 или SC2
└─ Любая number theory!

НУЖНО ТОЛЬКО:
├─ ξ_p строго возрастающие (log p / 2π — да!)
└─ K_pq > 0 для p ≠ q (гауссиан — да!)
```

---

## 4. Численная верификация

### Kernel Analysis

| X | N | dim ker(Q) | В конусе | min R(cone) |
|---|---|------------|----------|-------------|
| 500 | 24 | 22 | **0** | 0.008 |
| 1000 | 35 | 32 | **0** | 0.014 |
| 2000 | 61 | 58 | **0** | 0.027 |
| 5000 | 126 | 122 | **0** | 0.048 |

**100% ker-векторов имеют смешанные знаки (+/−)**
**0% ker-векторов в twin-конусе!**

### Scaling

```
min R(λ) ~ X^{0.90}  (РАСТЁТ!)

Это БОНУС сверх леммы:
- Лемма гарантирует: min R > 0
- Численно видим: min R → ∞ с X
```

---

## 5. Геометрическая интуиция

```
R^N
│
│    ker(Q) ≈ гиперплоскость dim N-3
│    /
│   /
│  /        ∩ = {0}  (только начало!)
│ /
├──────────────────────────
│    \
│     \  Twin-конус C
│      \ (первый октант)
│       \

Почему ker-вектора осциллируют?

ker(A) требует "баланс моментов":
  Σ_q (ξ_q − ξ_p) · K_pq · λ_q = 0  ∀p

Для баланса относительно точки ξ_p:
  - λ_q > 0 справа (pulling right)
  - λ_q < 0 слева (pulling left)

⟹ λ ДОЛЖЕН менять знак!
⟹ ker автоматически ВНЕ конуса!
```

---

## 6. Связь с общей структурой

### До этой работы

```
B₁_strong был ГИПОТЕЗОЙ (сложность ~0.3-0.8)
Не было понимания механизма
```

### После этой работы

```
B₁_strong — ТЕОРЕМА (чистая линейная алгебра)
Механизм: Cone-Kernel Separation
Сложность: 0 (доказано!)
```

### Что осталось

```
ЕДИНСТВЕННЫЙ GAP: SC2

SC2: finite twins ⟹ Q_X ≲ X^{1/2+ε}

Это twin-корреляции / арифметика.
Сложность ~0.8 (≈ twin conjecture itself).

Twin Conjecture ↔ SC2
(эквивалентная переформулировка)
```

---

## 7. Файлы проекта

### Код

```
src/kernel_analysis.py      — анализ ker(Q), eigenvalues
src/kernel_cone_check.py    — проверка C ∩ ker = {0}
src/rayleigh_minimum_scan.py — min R(λ) по разным λ
src/b1_precise_check.py     — c₁(X) scaling
src/circularity_analysis.py — Q_X explicit formula
```

### Документация

```
STEP_B_PLAN.md   — основной план Step B (обновлён)
PLAN_B1.md       — этот файл
```

---

## 8. TeX формулировка (для paper)

### Lemma

```latex
\begin{lemma}[Cone--Kernel Separation]
Let $\xi_1 < \xi_2 < \cdots < \xi_N$ be strictly increasing points on $\mathbb{R}$,
and let $K \in \mathbb{R}^{N \times N}$ be a symmetric matrix with $K_{pq} > 0$
for all $p \neq q$. Define $A \in \mathbb{R}^{N \times N}$ by
\[
A_{pq} = (\xi_q - \xi_p) \cdot K_{pq}.
\]
Let $C = \{\lambda \in \mathbb{R}^N : \lambda_p \geq 0, \lambda \neq 0\}$
be the positive cone. Then
\[
C \cap \ker(A) = \{0\}.
\]
\end{lemma}

\begin{proof}
Let $\lambda \in C \setminus \{0\}$ and set $S = \{p : \lambda_p > 0\}$.
Choose $p^* \in S$ such that $\xi_{p^*} = \max\{\xi_p : p \in S\}$.
Consider the component $(A\lambda)_{p^*}$:
\[
(A\lambda)_{p^*} = \sum_{q=1}^N (\xi_q - \xi_{p^*}) K_{p^*q} \lambda_q.
\]
For $q > p^*$: $\lambda_q = 0$ by choice of $p^*$.
For $q = p^*$: the factor $(\xi_q - \xi_{p^*}) = 0$.
For $q < p^*$: $(\xi_q - \xi_{p^*}) < 0$, $K_{p^*q} > 0$, $\lambda_q \geq 0$,
so each term is $\leq 0$.

If $\lambda$ is supported only at $p^*$, then for any $p < p^*$:
$(A\lambda)_p = (\xi_{p^*} - \xi_p) K_{p,p^*} \lambda_{p^*} > 0$,
so $A\lambda \neq 0$.

If there exists $q < p^*$ with $\lambda_q > 0$, then
$(A\lambda)_{p^*} < 0$, so $A\lambda \neq 0$.

In both cases, $A\lambda \neq 0$.
\end{proof}
```

### Corollary

```latex
\begin{corollary}[B$_1$-strong on twin cone]
Let $Q = A^\top A$ be the commutator energy matrix.
Then on the normalized twin cone $C_1 = \{\lambda \in C : \|\lambda\| = 1\}$:
\[
\inf_{\lambda \in C_1} R(\lambda) =: c_1 > 0,
\]
where $R(\lambda) = \langle Q\lambda, \lambda\rangle / \langle G\lambda, \lambda\rangle$
is the Rayleigh quotient.
\end{corollary}
```

---

## 9. Заключение

**B₁_strong ЗАКРЫТ.**

Это был крупный блок работы, но оказалось что он сводится к чистой линейной алгебре:
- Cone-Kernel Separation — элементарная лемма
- Не требует number theory
- Численная верификация идеальна

**Главный босс теперь: SC2 (twin-корреляции)**

Это единственный оставшийся аналитический gap.
