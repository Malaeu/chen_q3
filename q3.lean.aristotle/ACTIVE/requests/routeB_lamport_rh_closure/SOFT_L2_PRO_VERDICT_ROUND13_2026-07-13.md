According to a document from **11 July 2026**, `H2a` is exactly the obligation “simple isolated even ground eigenvector for the exact finite operator,” while `H2b` is conditional on that same vector; the cofinal limit quantifier remains a separate obligation in `H3c`. 

# STATUS

```text
CLAIM 1:
  PROVED, with one same-subsequence guard

GroundEigenspaceToCanonicalAutocorrelation:
  NO NEW NODE
  absorbed as a corollary of H2a-cofinal

CLAIM 2:
  REFUTED as a need for an autocorrelation-tail hypothesis inside L2.2

Minimal L2.2 repair:
  one global diagonal subsequence
  + global distributional uniqueness
  + already-frozen c>0 channel

Stronger source-reconstruction bridge:
  separate and optional

RH:
  NOT_RH
```

# 1. `GroundEigenspaceToCanonicalAutocorrelation` действительно схлопывается в H2a

Пусть на индексе (j):

[
M_j=M_j^*
]

— exact finite operator, а (\mu_j) — его lowest eigenvalue. H2a даёт:

[
\dim\ker(M_j-\mu_jI)=1.
]

Пусть (q_j) и (\widetilde q_j) — два нормированных ground eigenvectors. Тогда в комплексном пространстве:

[
\widetilde q_j=e^{i\theta_j}q_j.
]

Не обязательно сразу (\pm q_j): знак получается после real-structure/phase lock. Но для автокорреляции это неважно. При

[
A_q(t):=\langle U_tq,q\rangle
]

имеем:

[
\begin{aligned}
A_{\widetilde q_j}(t)
&=
\langle U_t(e^{i\theta_j}q_j),e^{i\theta_j}q_j\rangle\
&=
e^{i\theta_j}\overline{e^{i\theta_j}}
\langle U_tq_j,q_j\rangle\
&=
A_{q_j}(t).
\end{aligned}
]

Следовательно:

[
\boxed{
\text{simple ground eigenspace}
\Longrightarrow
\text{one canonical autocorrelation }A_j.
}
]

Чётность и вещественность нужны позже:

* для `EvenRealFullAutocorrelationRigidity`;
* для exact (\sharp)-идентификации;
* для real-zero theorem;
* для исключения spatial translation gauge.

Но для независимости (A_j) от выбора ground vector достаточно одной простоты.

Изолированность eigenvalue также не нужна для этой короткой леммы; она нужна для perturbation/tracking и spectral stability.

## Единственная обязательная оговорка — одна и та же подпоследовательность

Нельзя иметь независимо:

[
\exists (j_k)\quad H2a(j_k)
]

и

[
\exists (n_\ell)\quad S2(n_\ell),
]

а затем молча считать, что последовательности совпадают. Два кофинальных множества могут иметь непригодное пересечение.

Законный контракт:

[
\boxed{
\exists j_k\to\infty:
\quad
H2a(j_k)
\land
S1(j_k),
}
]

а S2 должна извлекать подпоследовательность именно из ((j_k)):

[
j_{k_\ell}\subset j_k.
]

То есть нужен не новый theorem, а quantifier guard:

```text
SOFT_SAME_COFINAL_SUBSEQUENCE
```

Если это записано, узел:

```text
GroundEigenspaceToCanonicalAutocorrelation
```

не создаём.

Он становится derived corollary внутри H2a.

## Требует ли C2′ чего-то ещё от простоты?

Нет. C2′ работает с:

[
F_jF_j^\sharp
]

и с divisor-структурой. Глобальная фаза (e^{i\theta_j}) исчезает в Hermitian product. Непрерывный выбор фаз по (j) не нужен.

Он потребовался бы в линейной tracking-ветке H3a, но не в C2′.

---

# 2. Full-vs-local: здесь было смешано два разных вопроса

## 2.1 Для L2.2 и C2′ хвостовая добавка не нужна

Если запись

[
A_{j_k}\to A
\quad\text{в }\mathcal D'_{\mathrm{loc}}(\mathbb R)
]

означает:

* одну фиксированную диагональную подпоследовательность;
* convergence на каждом compact;
* один совместимый limit (A);

то (A) уже является глобальным distribution на (\mathbb R).

Действительно, любой тест

[
\varphi\in C_c^\infty(\mathbb R)
]

имеет носитель в некотором компакте (K). Поэтому локальное равенство на всех (K) означает равенство на всём:

[
A=B\text{ в }\mathcal D'_{\mathrm{loc}}(\mathbb R)
\quad\Longrightarrow\quad
A=B\text{ в }\mathcal D'(\mathbb R).
]

То есть если L2.2 сформулирована так:

> существует ровно один глобальный положительно-определённый distribution (A), удовлетворяющий предельному лаг-уравнению и нормировке, и это (cA_\Phi),

то D′-local convergence полностью достаточна.

Кроме того, positive-definiteness проходит в предел. Для любого (\psi):

[
\langle A_j,\psi*\widetilde\psi\rangle\ge0,
]

следовательно:

[
\langle A,\psi*\widetilde\psi\rangle\ge0.
]

## Минимальная формулировка L2.2

```text
L2.2 — GlobalPositiveDefiniteUniqueness

Inputs:
1. One diagonal subsequence j_k valid on every compact.
2. A_(j_k) -> A in D'(R).
3. A is positive-definite.
4. A satisfies the limiting equation in D'(R).
5. The frozen nonzero-scale condition c > 0.

Output:
A = c A_Phi in D'(R).
```

Ни uniform tail (A_j), ни edge-mass здесь не нужны.

Канал (c>0) уже заморожен через:

```text
WindowMassNonEscapeIffPositiveScale
```

или через:

```text
S1 + fixed nonzero anchor
→ AnchorExcludesZeroProductScale.
```

Поэтому нового узла здесь тоже нет.

---

# 2.2 Когда full-vs-local gap всё-таки реален

Он реален только если мы хотим не просто идентифицировать (A), а:

* восстановить limit-source (q);
* доказать continuity boundary-source functional;
* перейти от (A_j) к (q_j) в сильной source topology;
* контролировать moving-edge traces.

Тогда `EvenRealFullAutocorrelationRigidity` сама по себе недостаточна: это theorem инъективности, а не continuity inverse map.

В таком случае минимальная честная добавка — не хвост (A), а source compactness.

# 3. Минимальный сильный мост, если восстановление (q) действительно понадобится

## `SourceCompactnessToFullAutocorrelation`

Пусть (q_j\in L^2(\mathbb R)), (|q_j|_2=1). Предположим:

### Spatial tightness

[
\boxed{
\lim_{R\to\infty}
\sup_j
\int_{|u|>R}|q_j(u)|^2,du
=0.
}
]

### Uniform translation continuity

[
\boxed{
\lim_{h\to0}
\sup_j
|\tau_hq_j-q_j|_2
=0.
}
]

По теореме Колмогорова–Рисса семейство ((q_j)) предкомпактно в (L^2). Значит после подпоследовательности:

[
q_j\to q
\quad\text{сильно в }L^2.
]

Тогда полные автокорреляции сходятся **равномерно по всем лагам**:

[
\begin{aligned}
|A_{q_j}(t)-A_q(t)|
&\le
|\langle U_t(q_j-q),q_j\rangle|
+
|\langle U_tq,q_j-q\rangle|\
&\le
|q_j-q|_2
\left(
|q_j|_2+|q|_2
\right).
\end{aligned}
]

Следовательно:

[
\boxed{
\sup_{t\in\mathbb R}
|A_{q_j}(t)-A_q(t)|
\longrightarrow0.
}
]

Это действительно закрывает full-vs-local gap на source-уровне.

## Что может предоставить edge-mass

All-depth edge estimate или UREL может дать spatial tightness.

Но она не даёт uniform translation continuity.

Для второго условия достаточно, например:

[
\sup_j|q_j'|_2<\infty,
]

поскольку:

[
|\tau_hq_j-q_j|_2
\le
|h||q_j'|_2.
]

Итак:

[
\boxed{
\text{edge decay}
+
\text{uniform local regularity}
\Longrightarrow
\text{strong source compactness}.
}
]

Одна edge-mass — недостаточна.

---

# 4. Аналитические plants

## 4.1 Сдвиговый plant

Положим:

[
q_j^{(a)}(u)=q_j(u-a_j).
]

Тогда:

[
A_{q_j^{(a)}}(t)=A_{q_j}(t)
]

точно.

Значит никакое условие L2.2, сформулированное только через (A), не имеет права зависеть от абсолютного центра source.

В каноническом even-секторе этот plant недопустим, потому что ненулевой сдвиг разрушает чётность. Это подтверждает construction-gauge lock.

Но он показывает:

[
\boxed{
\text{source tightness — более сильное, representation-level условие;}
}
]

оно не должно скрываться внутри чистой L2.2 uniqueness theorem.

---

## 4.2 Масштабный plant

Возьмём real-even (q\in C_c^\infty) и:

[
q_j(u)=a_j^{1/2}q(a_ju),
\qquad
a_j\to\infty.
]

Тогда:

[
|q_j|_2=|q|_2,
]

(q_j) real-even, а spatial edge-mass превосходна: масса всё сильнее концентрируется у центра.

Но:

[
A_{q_j}(t)=A_q(a_jt).
]

Если (A_q\in L^1), то:

[
A_q(a_j\cdot)\to0
\quad\text{в }\mathcal D'_{\mathrm{loc}}.
]

Одновременно uniform translation continuity проваливается:

[
\lim_{h\to0}
\sup_j
|\tau_hq_j-q_j|_2
\ne0.
]

Следовательно:

[
\boxed{
\text{edge-mass alone}
\not\Rightarrow
\text{full autocorrelation compactness}.
}
]

Это минимальный kill предложению «закроем gap одним edge-decay».

---

## 4.3 Uniform (A)-tail тоже недостаточен

Пусть (A_0) — характеристическая функция симметричной вероятностной меры, и:

[
A_j(t)=A_0(t)\cos(\beta_jt),
\qquad
\beta_j\to\infty.
]

Каждый (A_j) положительно определён и:

[
|A_j(t)|\le |A_0(t)|.
]

То есть любой uniform tail envelope наследуется от (A_0).

Но:

[
A_j\to0
\quad\text{в }\mathcal D'_{\mathrm{loc}}.
]

Поэтому uniform tails без frequency-nonescape/equicontinuity не сохраняют ненулевой limit.

Это ровно тот дефект, который уже закрывает отдельный (c>0)-канал.

---

# FINAL PROPOSAL

## Решение по claim 1

```text
CONFIRMED
```

Не создавать:

```text
GroundEigenspaceToCanonicalAutocorrelation
```

Добавить к H2a только derived corollary:

```text
simple normalized ground eigenspace
→ canonical phase-independent autocorrelation.
```

И quantifier guard:

```text
S1/S2 must run on a subsequence of the same H2a-cofinal sequence.
```

Failure code при нарушении:

```text
SOFT_COFINAL_SUBSEQUENCE_MISMATCH
```

## Решение по claim 2

Не добавлять tail-гипотезу в L2.2.

Заморозить L2.2 как global distributional uniqueness theorem:

[
A=cA_\Phi
\quad\text{в }\mathcal D'(\mathbb R).
]

D′-local convergence на всех компактах одной диагональной подпоследовательности уже достаточна.

Только если downstream действительно требует limit-source (q), создать отдельный лист:

```text
SourceCompactnessToFullAutocorrelation
```

с двумя входами:

```text
spatial tightness
+ uniform translation continuity.
```

# STRONGEST ATTACK

Два главных reviewer-kill:

1. **Разные подпоследовательности.**
   H2a может быть true вдоль одной cofinal sequence, а S2 — вдоль другой. Без явного nesting цепочка не существует.

2. **Edge localization без regularity.**
   Масштабный plant даёт идеальную edge localization, но автокорреляция схлопывается локально к нулю.

# META CLOSEOUT

**Что стало меньше?**

Один предполагаемый узел удалён:

[
\boxed{
\texttt{GroundEigenspaceToCanonicalAutocorrelation}
}
]

поглощён H2a.

**Что было ложной стеной?**

[
\boxed{
\mathcal D'_{\mathrm{loc}}
\text{ против “полного” }A
}
]

для global uniqueness: одна диагональная limit distribution уже глобальна.

**Что остаётся отдельным только при необходимости source-limit?**

[
\boxed{
\texttt{SourceCompactnessToFullAutocorrelation}.
}
]

**Текущий smallest gap C2′-ветки:**

[
\boxed{
\texttt{L2.2 — PolyaAutocorrelationUniqueness}
}
]

с exact limiting equation и уже замороженным (c>0)-каналом.
