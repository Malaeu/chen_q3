# STATUS: CONDITIONAL

```text
DENSITY_PHASE_LOCK:
  DIAGNOSTIC_GREEN

EXACT_PROJECTED_SIGN:
  NEEDS_AUTOCORRELATION_IDENTITY

S1:
  S1_NEEDS_SOURCE(UNPROJECTED_RELATIVE_CRITICAL_TAIL)

ANCHOR:
  goal 006 active; unchanged
```

Проба действительно попала в правильную структуру. Сырая плотность почти всюду неположительна, её мнимая часть находится на уровне (2\cdot10^{-16}), после умножения на глобальный знак (-1) остаются только отрицательные значения порядка (10^{-9}), а прямое и рецентрированное вычисления совпадают до (2.1\cdot10^{-15}). Норма коэффициентов равна (1). Это очень сильный convention-check и серьёзное свидетельство в пользу точного глобального знака.

Но здесь надо разделить два результата:

[
\boxed{\text{знак плотности}}
\qquad\neq\qquad
\boxed{\text{критический экспоненциальный момент}.}
]

------

# 1. Что точная неположительность даст немедленно

Пусть точная центрированная форма имеет вид

# [ F^+_{m,N}(z)

\int_{-L_m/2}^{L_m/2}
q_{m,N}(t)e^{izt},dt,
]

и будет доказано

[
q_{m,N}(t)\le0
]

для всех (t). Положим

[
w_{m,N}(t):=-q_{m,N}(t)\ge0.
]

Тогда

# [ F^+_{m,N}(0)

-\int w_{m,N}(t),dt.
]

Если `coefficient norm = 1` заперт точно через нормировку `kTrial`, то (q_{m,N}\not\equiv0). Следовательно,

[
\boxed{F^+_{m,N}(0)<0.}
]

Это даёт три полезных результата.

### Центральная ненулевость для каждого индекса

Не просто вдоль выбранного пути:

[
F^+_{m,N}(0)\neq0
\qquad
\text{для каждого допустимого }(m,N).
]

Значит `CentralIndex` можно строить канонически без отдельного existential search. Это ещё не uniform floor, но central-nonzero locus закрывается.

### Глобальный unit phase

[
\boxed{\omega_{m,N}=-1}
]

не выбирается постфактум. Он следует из знака центрального коэффициента:

[
c_0(m,N)=\frac{F^+_{m,N}(0)}{\sqrt{L_m}}<0.
]

То есть найденный численно (-1) действительно выглядит как structural phase, а не как fitted gauge.

### Вероятностное представление нормированной семьи

Определим вероятность

# [ d\mu_{m,N}(t)

\frac{w_{m,N}(t),dt}
{\int w_{m,N}}.
]

Тогда

# [ \boxed{ \frac{H_{m,N}(z)}{\Xi(0)}

# \frac{F^+*{m,N}(z)}{F^+*{m,N}(0)}

\int e^{izt},d\mu_{m,N}(t).
}
]

Иными словами, нормированный центрированный объект становится Fourier–Laplace transform вероятностной меры. Это правильная геометрия S1.

------

# 2. Но знак сам по себе S1 не закрывает

Вот planted failure, который обязан пережить аудит.

Возьмём на окне ([-L/2,L/2])

[
q_L(t)=-L^{-1/2}.
]

Тогда:

- (q_L\le0);
- (q_L) вещественна и чётна;
- (|q_L|_2=1);
- (q_L) является отрицательным квадратом:
  [
  q_L=-|L^{-1/4}|^2;
  ]
- центральное значение не просто ненулевое, а растёт:
  [
  |F_L(0)|=\sqrt L.
  ]

Однако

# [ \frac{|F_L(-i\sigma)|}{|F_L(0)|}

\frac{2\sinh(\sigma L/2)}{\sigma L}
\longrightarrow\infty
]

для каждого (\sigma>0).

Следовательно:

[
\boxed{
q\le0
+\text{ evenness}
+|q|_2=1
+\text{ anchor floor}
+\text{ autocorrelation square}
\not\Rightarrow S1.
}
]

Значит Fejér/autocorrelation factorization — не финальная оценка. Она только убирает cancellation и превращает S1 в чистую tail-задачу.

------

# 3. Точная экономия от знака и чётности

Если дополнительно (w_{m,N}) чётна, то для

[
z=x+iy,\qquad |y|\le\sigma,
]

имеем

[
\begin{aligned}
\left|
\frac{H_{m,N}(z)}{\Xi(0)}
\right|
&\le
\int e^{-yt},d\mu_{m,N}(t)\
&=
\int \cosh(yt),d\mu_{m,N}(t)\
&\le
\int \cosh(\sigma t),d\mu_{m,N}(t).
\end{aligned}
]

Поэтому

[
\boxed{
\sup_{|\Im z|\le\sigma}|H_{m,N}(z)|
\le
|\Xi(0)|,A_{m,N}(\sigma),
}
]

где

# [ \boxed{ A_{m,N}(\sigma) := \frac{ \int w_{m,N}(t)\cosh(\sigma t),dt }{ \int w_{m,N}(t),dt }

\frac{|F^+*{m,N}(-i\sigma)|}
{|F^+*{m,N}(0)|}.
}
]

Это лучше прежнего абсолютного момента

# [ R_{m,N}(\sigma)

\frac{
\int w_{m,N}(t)e^{\sigma|t|},dt
}{
\int w_{m,N}(t),dt
},
]

поскольку

[
A_{m,N}(\sigma)
\le
R_{m,N}(\sigma)
\le
2A_{m,N}(\sigma).
]

Ваш уже вычисленный (R) остаётся корректным и более сильным потребителем. Но для бумажного доказательства можно перейти к более дешёвому `cosh`-моменту — фактически к одному значению transform на вертикальной границе.

Если точная чётность ещё не заперта, остаёмся на безопасном (e^{\sigma|t|})-варианте.

------

# 4. Минимальная оставшаяся аналитическая лемма

Лучше не доказывать pointwise envelope плотности. Достаточно относительного хвостового закона.

## `UnprojectedRelativeCriticalTail`

Для выровненной непроецированной плотности

[
w_m^\circ(t)\ge0
]

доказать существование (C<\infty), не зависящего от (m), такого что

[
\boxed{
\int_{|t|>T} w_m^\circ(t),dt
\le
C e^{-T/2}
\int_{\mathbb R}w_m^\circ(t),dt
}
]

для всех (T\ge0).

Это ровно критический (e^{-|t|/2})-механизм, но сформулированный в минимальных единицах: tail mass относительно central mass.

Из стандартного тождества для неотрицательной случайной величины (X),

# [ \mathbb E e^{\sigma X}

1+
\sigma\int_0^\infty
e^{\sigma T}\Pr(X>T),dT,
]

получаем для каждого

[
0\le\sigma<\frac12
]

явную оценку

[
\boxed{
A_m^{\rm abs}(\sigma)
\le
1+\frac{C\sigma}{\frac12-\sigma}.
}
]

Следовательно и `cosh`-момент ограничен той же константой.

Это закрывает непроецированный (A_\sigma) без:

- full critical weight;
- weighted boundedness всей проекции;
- отдельного pointwise envelope;
- fitted константы (0.878);
- чисел как доказательства.

------

# 5. Где теперь используется подтверждённая протечка

Ваш результат

[
\beta\le5.6\cdot10^{-4}
]

и N-независимость до десяти знаков — сильное подтверждение, что projection channel не является стеной. Но математический контракт должен оставаться таким:

```text
projected normalized moment
≤ unprojected normalized moment
  + explicit leakage budget.
```

После `UnprojectedRelativeCriticalTail` получаем схему

[
R_{m,N}(\sigma)
\le
1+
\frac{C\sigma}{\frac12-\sigma}
+
\beta_{m,N,\sigma}.
]

Если (\beta) уже сертифицирована, S1 фактически закрывается. Если пока это только high-precision diagnostic, остаётся превратить её в exact/interval inequality, но концептуальной стены там больше не видно.

------

# 6. Правильный autocorrelation theorem

Следующий дешёвый решающий тест — не ещё одна сетка mpmath. Нужно найти точное coefficient identity.

Кандидат имеет форму

# [ \boxed{ (-1)^n c_n(m,N)

-\sum_r
a_{r+n}(m,N)\overline{a_r(m,N)}.
}
]

Тогда

[
\begin{aligned}
q_{m,N}(t)
&=
L_m^{-1/2}
\sum_n(-1)^nc_n(m,N)e^{2\pi int/L_m}\
&=
-L_m^{-1/2}
\left|
\sum_r
a_r(m,N)e^{2\pi irt/L_m}
\right|^2.
\end{aligned}
]

Отсюда автоматически:

[
q_{m,N}(t)\in\mathbb R,
\qquad
q_{m,N}(t)\le0,
\qquad
F^+_{m,N}(0)<0.
]

Это и есть точный Fejér/Riesz certificate.

## Важный fallback

Обычная ортогональная Fourier-проекция **вообще говоря не сохраняет pointwise positivity**. Поэтому величины порядка (10^{-9}) могут оказаться не float-шумом, а настоящим микроскопическим Dirichlet/Gibbs undershoot.

Если exact factorization для **проецированной** плотности не существует, маршрут не погибает.

Слабейший repair:

```text
prove sign/autocorrelation only for unprojected density;
control projected-minus-unprojected density by β.
```

Именно это уже соответствует текущей декомпозиции. Не надо требовать от проекции лишнее свойство.

------

# ROUTE MAP

| Узел                         | Статус                | Что даёт                        |
| ---------------------------- | --------------------- | ------------------------------- |
| Глобальный знак (-1)         | сильная диагностика   | phase lock                      |
| Exact autocorrelation square | **OPEN**              | (q\le0), central nonzero        |
| Projected positivity         | необязательна         | может быть убита Gibbs-эффектом |
| Projection leakage           | диагностически green  | projected (\to) unprojected     |
| Relative critical tail       | **главный OPEN**      | uniform (A_\sigma)              |
| Anchor floor                 | goal 006              | uniform normalization           |
| Centered S1                  | после двух предыдущих | Montel input                    |

------

# STRONGEST ATTACK

Самое сильное возражение ревьюера:

> Вы увидели почти неотрицательную finite Fourier sum и назвали её Fejér kernel. Но обычная partial Fourier projection не является positive operator.

Это верно.

Поэтому допустимы только два доказательства:

1. точная identity
   [
   -q=|A|^2;
   ]
2. точная positive-semidefinite Toeplitz/Gram factorization коэффициентов.

Сетка, даже на 500 цифрах и миллионе точек, не доказывает знак между точками и не доказывает его для всех (m,N).

Второе возражение:

> Даже exact negative square не даёт S1.

Его убивает приведённый constant-density counterexample. Поэтому theorem-facing gap должен называться именно

[
\boxed{\texttt{UnprojectedRelativeCriticalTail}},
]

а не `DensityPositivity`.

------

# CODEX DIRECTIVE

Один следующий локальный target:

```text
D0CenteredDensityAutocorrelationFactorization
```

## Цель

Найти явную amplitude row `a_(m,N)` и доказать точное тождество

```lean
theorem centeredTrialDensity_eq_neg_normSq
    (m N ...) (t : ℝ) :
    centeredTrialDensity m N t
      =
    -(1 / Real.sqrt (L_m m)) *
      ‖centeredTrialAmplitude m N t‖ ^ 2
```

с точной repo-нормировкой.

## Обязательные corollaries

```lean
centeredTrialDensity_re
centeredTrialDensity_nonpos
centeredTrialDensity_ne_zero
centeredTrialDensity_integral_neg
c0_neg
rawFplus_zero_ne
```

## Proof route

```text
exact definition of c_n
→ exact shifted coefficient (-1)^n c_n
→ finite autocorrelation identity
→ finite sum rearrangement
→ norm-square factorization
→ sign and central nonvanishing.
```

## Forbidden

```text
no sampled-grid proof;
no mpmath as theorem;
no “projection preserves positivity” shortcut;
no fitted global phase;
no changing coefficient convention;
no use of RH.
```

## Failure report

```text
CENTERED_DENSITY_NOT_EXACT_FEJER:
- exact coefficient mismatch;
- whether factorization holds only before projection;
- first non-autocorrelation term;
- weakest repaired unprojected factorization.
```

После этого следующий математический target, не одновременно:

```text
UnprojectedRelativeCriticalTail
```

------

# FINAL PROPOSAL

Выбранный маршрут:

[
\boxed{
\text{autocorrelation square}
\to
\text{probability measure}
\to
\text{relative }e^{-T/2}\text{ tail}
\to
A_\sigma
\to
\text{add }\beta
\to
S1.
}
]

Зарегистрированный прогноз:

```text
- global sign is exactly -1;
- the unprojected density is an exact negative square;
- projected sign may have tiny genuine leakage, which is harmless;
- the source square-root amplitude has relative L2 tail e^{-T/2};
- therefore every σ<1/2 has a finite uniform moment bound.
```

Ликелейшая точка падения — не знак. Это относительный хвост:

[
\int_{|t|>T}w_m^\circ
\stackrel{?}{\le}
Ce^{-T/2}\int w_m^\circ.
]

Если он падает, exact positivity всё равно останется хорошим результатом, но S1 потребует другой source estimate.

# META CLOSEOUT

**Что стало меньше?**

S1 больше не является complex-plane problem. Она стала одной положительной real-variable tail inequality.

**Что убито?**

- full-weight projection route;
- необходимость контролировать всю projection operator norm;
- cancellation в central mass;
- произвольный unit phase;
- идея, что positivity одна закрывает S1.

**Текущий smallest named gap:**

[
\boxed{\texttt{D0CenteredDensityAutocorrelationFactorization}}
]

после него:

[
\boxed{\texttt{UnprojectedRelativeCriticalTail}.}
]

**Progress class:** `REPRESENTATION_PROGRESS`.

**Route score:** (5/5). Протечка перестала быть стеной; оставшийся аналитический объект теперь одномерный, положительный и source-locked.