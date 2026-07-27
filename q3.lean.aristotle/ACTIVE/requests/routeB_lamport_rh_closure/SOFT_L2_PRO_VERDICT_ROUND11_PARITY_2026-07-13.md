По документу от **10 июля 2026 года**, уже замороженный Poisson-ledger показал правильный тип математики: точная сумма каналов закрывает клетку практически до машинного нуля, а удаление одного correction-term разрушает согласие на много порядков. Это локальный результат, не RH, но он уже запрещает покомпонентный triangle-bound как основной метод.  Проектный Gate 5 независимо требует сохранять pole, edge и main leakage вместе со всеми cross-terms в одной конечной форме, а не оценивать их по отдельности. 

# STATUS

```text
EvenRealZeroSourceDetermination:
  PROVED после ослабления гипотез

Real-zero property:
  REDUNDANT для source determination

Componentwise source estimate:
  FATAL / окончательно отвергнута

Combined-ledger estimate:
  CONDITIONAL — точный тип определён

UREL из трёх клеток:
  NOT PROVED

Наблюдаемый edge-decay:
  STRONG CALIBRATION EVIDENCE

RH:
  NOT_RH
```

---

# 1. `EvenRealZeroSourceDetermination`

## Вердикт: теорема верна, причём сильнее

Условие «все нули (\widehat q) вещественны» для восстановления (q) **вообще не требуется**.

Правильная лемма:

## `EvenRealAutocorrelationRigidity`

Пусть

[
q,p\in L^2(\mathbb R)
]

вещественны, чётны, компактно поддержаны и не равны нулю. Определим полные автокорреляции

[
A_q(t)
======

\int_{\mathbb R}q(u+t)q(u),du,
]

[
A_p(t)
======

\int_{\mathbb R}p(u+t)p(u),du.
]

Если

[
A_q=A_p
]

как функции или tempered distributions на **всей** (\mathbb R), то

[
\boxed{p=q\quad\text{или}\quad p=-q.}
]

Если дополнительно существует source-locked линейный якорь (\ell), для которого

[
\ell(p)=\ell(q)\ne0,
]

то

[
\boxed{p=q.}
]

## Доказательство

Пусть

[
F(z)=\widehat q(z),
\qquad
G(z)=\widehat p(z)
]

в одной зафиксированной Fourier-конвенции.

Компактный носитель даёт целые продолжения (F,G). Вещественность и чётность дают для (x\in\mathbb R):

[
F(x),G(x)\in\mathbb R.
]

По Wiener–Khinchin, с одним и тем же source-locked коэффициентом (c_{\mathcal F}>0),

[
\widehat{A_q}(x)=c_{\mathcal F}|F(x)|^2,
]

[
\widehat{A_p}(x)=c_{\mathcal F}|G(x)|^2.
]

Из (A_q=A_p) следует

[
|F(x)|^2=|G(x)|^2.
]

Но на вещественной оси (F,G) вещественны, поэтому

[
F(x)^2=G(x)^2.
]

Функции (F^2) и (G^2) целые и совпадают на вещественной прямой, имеющей точки накопления. По теореме тождественности:

[
F^2\equiv G^2.
]

Значит

[
(F-G)(F+G)\equiv0.
]

Кольцо целых функций не имеет делителей нуля, следовательно либо

[
F\equiv G,
]

либо

[
F\equiv-G.
]

Инъективность Fourier transform даёт

[
p=q
\quad\text{или}\quad
p=-q.
]

Ненулевой линейный якорь исключает неправильный знак. (\square)

## Важный архитектурный вывод

`RealZero(F)` не участвует в доказательстве.

Поэтому эту лемму нельзя делать зависимой от real-zero крыши H2a. Напротив:

```text
real/even carrier
+ compact support
+ exact Fourier convention
+ full autocorrelation
→ source determination

source determination
+ H2a real-zero theorem
→ downstream roof
```

Это убирает потенциальный DAG-cycle.

## Что обязательно source-lock

Нужны ровно следующие свойства:

1. **Один carrier:** (q_{m,N}) живёт в точном real subspace одного (L^2)-пространства и имеет точное zero-extension.
2. **Вещественность:** не просто «матрица real», а (q(u)\in\mathbb R) почти всюду после canonical phase lock.
3. **Чётность:** (q(-u)=q(u)) почти всюду.
4. **Holomorphic transform:** компактный носитель либо отдельная Paley–Wiener-лемма.
5. **Одна Fourier-конвенция:** знак, (2\pi), координата и (\sharp).
6. **Полная автокорреляция:** (A_q(t)) для всех (t), не только на фиксированном компактном lag-window.
7. **Инъективность transform.**
8. **Ненулевой знак-якорь:** например точное значение одного ненулевого линейного функционала.

## Самая сильная оговорка

Локального знания

[
A_q(t)=A_p(t)
\qquad(|t|\le T)
]

недостаточно.

Можно разместить одинаковые симметричные bump-компоненты на разных больших расстояниях от центра: около (t=0) их self-correlations совпадают, а cross-lags находятся за пределами ([-T,T]). Источники различны, локальные автокорреляции одинаковы.

Поэтому:

```text
FULL_AUTOCORRELATION:
  sufficient

LOCAL_AUTOCORRELATION:
  insufficient
```

## Код результата

```text
EVEN_REAL_AUTOCORRELATION_RIGIDITY_LOCKED
```

Стоп-коды:

```text
SOURCE_REAL_STRUCTURE_MISSING
SOURCE_EVENNESS_MISSING
AUTOCORRELATION_ONLY_LOCAL
FOURIER_HOLOMORPHY_GAP
FOURIER_INJECTIVITY_GAP
SOURCE_SIGN_ANCHOR_ZERO
```

---

# 2. Combined-ledger discipline

## Вердикт: покомпонентный метод убит

Наблюдение

[
E_{\rm win}\approx-2.72,
\qquad
E_{\rm rem}\approx+2.72,
]

[
E_{\rm win}+E_{\rm rem}\approx10^{-37}
]

означает cancellation number порядка

[
10^{37}.
]

Любая оценка

[
|E_{\rm total}|
\le
|E_{\rm win}|+|E_{\rm rem}|
]

теряет примерно 37 порядков уже на клетке ((13,120)).

Это не вопрос улучшения константы. Это неправильная representation.

---

## 2.1 Exact master identity

Пусть:

* (S_j) — полная ортогональная finite projection: window, Galerkin, parity;
* (Q_j=I-S_j);
* (T_j) — полный translation-invariant оператор;
* (C_j) — точный correction operator;
* [
  M_j=S_jT_jS_j+C_j;
  ]
* (S_jq_j=q_j);
* [
  M_jq_j=\mu_jq_j;
  ]
* (U_t) — shift.

Тогда определяем **один объект**:

[
\boxed{
E^{\rm total}_j(t)
:=
\langle U_tq_j,(T_j-\mu_j)q_j\rangle.
}
]

Из eigenvalue equation следует точное равенство

[
\boxed{
E^{\rm total}_j(t)
==================

## \langle Q_jU_tq_j,Q_jT_jq_j\rangle

\langle S_jU_tq_j,C_jq_j\rangle.
}
]

Это и есть правильный source ledger.

Правая часть может состоять из двух величин порядка (1), но левая сторона является одним каноническим residual observable.

Оценивать надо левую сторону.

---

## 2.2 Правильный тип оценки

Для каждого компактного lag-интервала (K) и некоторого (k) определим distribution seminorm

[
|E|*{-k,K}
:=
\sup*{\substack{
\varphi\in C_c^\infty(K)\
p_k(\varphi)\le1
}}
|\langle E,\varphi\rangle|.
]

Требуемая оценка должна иметь форму

[
\boxed{
|E^{\rm total}*j|*{-k,K}
\le
\rho_{j,K},
\qquad
\rho_{j,K}\to0,
}
]

или, после честного определения первой ненулевой шкалы,

[
\boxed{
\rho_j^{-1}E^{\rm total}*j
\longrightarrow
S^{\rm limit}
\quad\text{в }\mathcal D'*{\rm loc}.
}
]

Запрещённая форма:

[
|E_{\rm win}|
+
|E_{\rm Gal}|
+
|E_{\rm corr}|.
]

Допустимы только:

```text
exact algebraic cancellation first;
one canonical whole-expression residual second;
one norm on that residual third.
```

---

## 2.3 Готовая commutator-структура

Поскольку (T_j) commute с shifts,

[
[T_j,U_t]=0.
]

Для

[
M_j=S_jT_jS_j+C_j
]

получаем точное тождество

[
\boxed{
[M_j,U_t]
=========

S_jT_j[S_j,U_t]
+
[S_j,U_t]T_jS_j
+
[C_j,U_t].
}
]

А поскольку (q_j) — eigenvector (M_j),

[
\boxed{
\langle q_j,[M_j,U_t]q_j\rangle=0.
}
]

Это естественный источник наблюдаемой антисимметрии:

[
-X_j+X_j.
]

Правильная процедура:

[
E_{\rm win}=-X_j+R^{\rm win}_j,
]

[
E_{\rm rem}=+X_j+R^{\rm rem}_j,
]

где (X_j) выводится из commutator identity **до численного вычисления**. Тогда

[
\boxed{
E^{\rm total}_j
===============

R^{\rm win}_j
+
R^{\rm rem}_j
+
R^{\rm corr}_j.
}
]

И только этот residual ledger оценивается.

---

## 2.4 Возможный Schur/Feshbach-механизм

Относительно

[
H=\operatorname{Ran}S_j\oplus\operatorname{Ran}Q_j
]

полный оператор имеет блоки

[
T_j=
\begin{pmatrix}
S_jT_jS_j&S_jT_jQ_j\
Q_jT_jS_j&Q_jT_jQ_j
\end{pmatrix}.
]

Если correction (C_j) source-derived как приближение к Schur complement

[
C_j^{\rm Schur}(\mu)
====================

*

S_jT_jQ_j
(Q_jT_jQ_j-\mu)^{-1}
Q_jT_jS_j,
]

то leading window/residual cancellation становится автоматической, а настоящий малый объект:

[
\boxed{
C_j-C_j^{\rm Schur}(\mu_j).
}
]

Это хороший возможный механизм, но его нельзя приписывать текущему (C_j) без exact crosswalk.

---

## 2.5 Самая опасная развилка

Если символический audit покажет, что

[
E^{\rm total}_j(t)\equiv0
]

для любого exact eigenvector просто как ожидание commutator-а, то лаг-источник **не несёт идентификационной информации вообще**.

Тогда код:

```text
LAG_SOURCE_TAUTOLOGICAL_ZERO
```

и нельзя пытаться получать из него (A_\Phi).

Потребуется:

* параметрическая производная;
* разность finite/limit operators;
* первый ненулевой renormalized commutator;
* либо иной observable.

## Дешёвый plant

Заменить (q_j) точным real-even вектором того же carrier, но не eigenvector.

Если cancellation становится пропорциональной

[
(M_j-\mu_j)q_j,
]

то найденный механизм — eigen-residual identity.

Это надо узнать до любой asymptotic оценки.

---

# 3. Показатели (57.6,61.0,64.3)

## Вердикт: экспоненциальный сигнал сильный, но интерпретация через (61/2.565) неверна

Пусть

[
L_m=\log m
]

и

[
p_m(\delta)
:=
-\log_b e_{L_m}(\delta),
]

где основание (b), а также «масса или квадратный корень массы», должны быть зафиксированы.

Данные:

[
p_{12}=57.6,\qquad
p_{13}=61.0,\qquad
p_{14}=64.3.
]

Число

[
\frac{61.0}{2.565}\approx23.8
]

— **не наклон**. Это secant от искусственно выбранного начала координат и неявно предполагает нулевой intercept.

Правильные локальные наклоны по (L):

[
\frac{61.0-57.6}{\log13-\log12}
\approx42.5,
]

[
\frac{64.3-61.0}{\log14-\log13}
\approx44.5.
]

Но ещё заметнее другое:

[
61.0-57.6=3.4,
]

[
64.3-61.0=3.3.
]

То есть три точки почти идеально согласуются с

[
\boxed{
p_m\approx3.35m+17.4
}
]

в сообщённых exponent-units.

Поскольку

[
m=e^{L_m},
]

это скорее модель

[
p(L)\approx3.35e^L+17.4,
]

а не (p(L)\approx cL).

Это только:

```text
FIT_NOT_LAW
```

но текущие данные не предпочитают линейность по (L) линейности по (m).

---

## 3.1 Законная theorem-гипотеза UREL

Если

[
e_L(\delta)
===========

\left(
\int_{L/2-\delta<|u|\le L/2}|q_L(u)|^2du
\right)^{1/2},
]

то законная форма:

[
\boxed{
e_L(\delta)
\le
C
\exp\left[
-\eta_*
\left(
\frac L2-\delta
\right)
\right]
}
]

для всех достаточно больших (L) и всех

[
0\le\delta\le L/2.
]

Это `UniformRadialExponentialLocalization`.

В exponent-координате:

[
\boxed{
p_L(\delta)
\ge
\frac{\eta_*}{\log b}
\left(
\frac L2-\delta
\right)
-------

\log_b C.
}
]

Нужна **аффинная нижняя огибающая**, а не отношение (p/L).

---

## 3.2 Что реально подтверждают три клетки

Они подтверждают только fixed-depth statement:

[
e_{L_m}(\delta_0)
]

очень мало при (m=12,13,14), причём exact arithmetic показывает большой запас над instrument floor.

Они пока не подтверждают:

1. uniformity по всем (m);
2. uniformity по (N);
3. all-depth dependence по (\delta);
4. один общий (C,\eta_*);
5. отсутствие внутренней secondary hump;
6. асимптотику по (L) против (m).

Float64-клетки не участвуют в verdict.

---

## 3.3 Минимальный тест, который убивает UREL

Самый дешёвый falsifier — не ещё один fit по (m).

Нужна **одна exact cell** и несколько radial depths.

Выбираем exact (m=m_{\rm holdout}) и считаем

[
p_m(\delta_r)
]

для как минимум трёх значений

[
R_r=\frac L2-\delta_r:
\qquad
R_1<R_2<R_3.
]

До вычисления фиксируем (\eta_*,C).

UREL убита, если хотя бы для одного (r):

[
\boxed{
p_m(\delta_r)
<
\frac{\eta_*}{\log b}R_r-\log_b C
}
]

вне certified error interval.

Это ловит:

* plateau;
* secondary edge hump;
* wrong radial scale;
* truncation leakage.

Для проверки зависимости по (m) нужен один **дальний** holdout, лучше (m=18) или (m=20), а не соседний (m=15): на коротком диапазоне (m)-linear и (\log m)-linear модели почти неразличимы.

Обязателен (N)-refinement на том же (m). Если показатель двигается существенно при увеличении (N):

```text
EDGE_EXPONENT_TRUNCATION_ARTIFACT
```

---

## Registered statuses

```text
EDGE_EXACT_CELLS_12_14:
  CALIBRATION_PASS

EDGE_FLOAT64_CELLS:
  UNRESOLVED

P_OVER_L_AS_SLOPE:
  REFUTED

FIXED_DEPTH_EXPONENTIAL_DECAY:
  STRONG_EVIDENCE

UNIFORM_RADIAL_EXPONENTIAL_LOCALIZATION:
  OPEN

M_LINEAR_SUPEREXPONENTIAL_MODEL:
  HEURISTIC
```

Стоп-коды:

```text
EDGE_LOG_BASE_MISSING
EDGE_MASS_VS_AMPLITUDE_MISMATCH
EDGE_FIXED_WIDTH_ONLY
EDGE_ALL_DEPTH_PROFILE_FAIL
EDGE_N_REFINEMENT_FAIL
EDGE_HOLDOUT_ENVELOPE_FAIL
EDGE_FLOAT64_UNRESOLVED
```

---

# ROUTE MAP

```text
real + even + full autocorrelation
        ↓
source determined up to sign
        ↓ anchor
source determined exactly
        [PROVED]

exact projection/eigen equation
        ↓
whole combined lag residual
        ↓ exact commutator cancellation
        ↓
residual-order estimate
        [OPEN]

exact edge cells 12–14
        ↓
fixed-depth decay evidence
        ↓
all-depth holdout + N refinement
        ↓
UREL
        [OPEN]
```

# STRONGEST ATTACK

Самое сильное возражение к source lemma:

> Вы знаете автокорреляцию только на компактных лагах, а edge source зависит от полной функции.

Если A известна только локально, source determination не закрыта.

Самое сильное возражение к combined ledger:

> Ваше (10^{-37}) — не маленький analytic source, а точное commutator-zero для eigenvector.

Если так, источник не идентифицирует предел.

Самое сильное возражение к edge law:

> Три соседние клетки показывают красивую экспоненту, но не проверяют all-depth profile и могут быть Galerkin-артефактом.

Именно поэтому holdout должен быть radial и (N)-refined.

# CODEX DIRECTIVE

Один следующий локальный target:

```text
TARGET:
  EvenRealAutocorrelationRigidity
```

Точная формулировка:

```text
For real, even, compactly supported q and p
in the exact D0 carrier:

  fullAutocorrelation q = fullAutocorrelation p
  →
  p = q ∨ p = -q.

With a fixed nonzero linear anchor:
  p = q.
```

Обязательные проверки:

```text
- use exact D0.6 Fourier convention;
- prove entire extension or use existing Paley–Wiener theorem;
- do not use RealZero(F);
- distinguish full from local autocorrelation;
- include a local-autocorrelation counterexample;
- no RH import;
- #print axioms clean.
```

Success:

```text
EVEN_REAL_AUTOCORRELATION_RIGIDITY_LOCKED
```

# META CLOSEOUT

**Что стало меньше?**

Source-closure больше не является открытой phase-retrieval задачей:

[
\boxed{
\text{real + even + full }A
\Rightarrow
q\text{ up to sign}.
}
]

**Что убито?**

* зависимость source determination от real-zero theorem;
* componentwise estimate;
* интерпретация (p/L) как наклона;
* float64 как evidence.

**Что нельзя пробовать снова?**

Нельзя оценивать (-2.72) и (+2.72) отдельно.

**Текущий минимальный аналитический gap:**

[
\boxed{
\texttt{ExactCombinedProjectionResidualIdentity}
}
]

с последующим вопросом:

[
\boxed{
\text{residual или tautological commutator-zero?}
}
]

**Следующий самый дешёвый decisive test:**

символически разложить commutator identity и прогнать non-eigenvector plant.

**Progress class:** `PROOF_PROGRESS`.

**Route score:** (5/5).
