# STATUS: CONDITIONAL — MASS-FORK ПРИНЯТ, НО НАЙДЕН ОТДЕЛЬНЫЙ POISSON-КОНТРЧЛЕН

```text
PRIMARY:
  HTRIAL_FORMULA_ACCEPTED

MASS FORK:
  MELLIN_MASS_ZERO_CONFIRMED

MEASURE:
  MEASURE_CONVENTION_MATCH

ENDPOINT:
  NO_ENDPOINT_TERM_IN_MASS_IDENTITY
  STARRED_TOOTH_CONVENTION_STILL_REQUIRED_FOR_012

NEW KILL / REPAIR:
  POISSON_ORIGIN_COUNTERTERM_PRESENT

AUDIT LIMIT:
  REPORT_011_EXACT_SCALAR_LINE_UNSEEN
```

Файл `011_concrete_htrial_source_lock.answer.md` по указанному локальному macOS-пути не оказался среди доступных вложений или подключённых файлов. Поэтому SHA-256-локи, точную строку коэффициентов и нормирующий множитель я независимо не проверил. Но объект, mass-fork, мера и главный контрчлен проверяются по source-структуре и уже загруженному source-lock inspection.

------

# 1. Формула (hTrial_m=h_\lambda): принята

Первичный источник действительно задаёт:

# [ PW_\lambda

-\partial_x(\lambda^2-x^2)\partial_x
+
(2\pi\lambda x)^2,
]

локализованные чётные prolate-моды (h_{0,\lambda}), (h_{4,\lambda}), поддержанные на ([-\lambda,\lambda]), и выделяет единственную с точностью до ненулевого множителя комбинацию этих двух мод с нулевым интегралом. Индексный словарь соответствует

[
h_{0,\lambda}\longleftrightarrow\chi_0,
\qquad
h_{4,\lambda}\longleftrightarrow\chi_2.
]

Это согласуется с переданным статусом 011. ([arXiv](https://arxiv.org/html/2602.04022v1))

Пусть

[
I_{0,\lambda}
:=
\int_{\mathbb R}h_{0,\lambda}(x),dx,
\qquad
I_{4,\lambda}
:=
\int_{\mathbb R}h_{4,\lambda}(x),dx.
]

Тогда zero-mass line обязана иметь вид

# [ \widetilde h_\lambda

## I_{4,\lambda}h_{0,\lambda}

I_{0,\lambda}h_{4,\lambda},
]

с точностью до общего ненулевого множителя и знака. Действительно,

# [ \int_{\mathbb R}\widetilde h_\lambda

## I_{4,\lambda}I_{0,\lambda}

# I_{0,\lambda}I_{4,\lambda}

1. 

]

Если моды (L^2)-нормированы и ортогональны, то каноническая нормировка:

# [ h_\lambda

## \pm \frac{ I_{4,\lambda}h_{0,\lambda}

I_{0,\lambda}h_{4,\lambda}
}{
\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2}
}.
]

Именно эту строку надо сравнить с 011. Перестановка двух слагаемых меняет только глобальный знак — вероятный источник обнаруженной фазы (\omega=-1).

------

# 2. Аудит меры: несоответствия нет

В source-lock chain пространство после (E_\star) действительно является

[
L^2!\left(
[\lambda_m^{-1},\lambda_m],
\frac{du}{u}
\right),
]

а

# [ E_\star(h)(u)

\sqrt u\sum_{n\ge1}^{\star}h(nu).
]

То есть:

- (x) или (v) — **аддитивная координата источника** (h);
- (u) — **мультипликативная координата** после применения (E_\star);
- (du/u) появляется только на стороне `gTrial_m`;
- (dt=du/u) появляется после (t=\log u).

Mass-fork использует

# [ A_m

\int_0^\infty h_\lambda(v),dv,
]

а статья утверждает

[
\int_{\mathbb R}h_\lambda(x),dx=0.
]

Поскольку (h_\lambda) чётна,

# [ \int_{\mathbb R}h_\lambda(x),dx

2\int_0^\infty h_\lambda(v),dv.
]

Следовательно,

# [ \boxed{ A_m

# \frac12 \int_{\mathbb R}h_\lambda(x),dx

1. 

}
]

Здесь **нет замены переменной и нет якобиана**. (v) — просто положительная половина той же аддитивной координаты (x).

Нельзя подменять это переходом (v=e^t). При таком переходе было бы

[
dv=e^t,dt
]

и

# [ \int_0^\infty h(v),dv

\int_{\mathbb R}h(e^t)e^t,dt,
]

а не (\int h(e^t),dt). Но этот переход вообще не нужен для доказательства (A_m=0).

Вердикт:

```text
MEASURE_CONVENTION_MATCH
```

------

# 3. Mellin-множитель: точная формула и честная область

Зафиксируем:

# [ \mathcal M f(s)

\int_0^\infty f(u)u^{s-1},du.
]

Тогда в области абсолютной сходимости:

[
\begin{aligned}
\mathcal M(E_\star h)(s)
&=
\int_0^\infty
\sqrt u
\sum_{n\ge1}h(nu)
u^{s-1},du\
&=
\sum_{n\ge1}
\int_0^\infty
h(nu)u^{s-\frac12},du\
&=
\sum_{n\ge1}
n^{-s-\frac12}
\int_0^\infty
h(v)v^{s-\frac12},dv\
&=
\boxed{
\zeta!\left(s+\frac12\right)
\mathcal Mh!\left(s+\frac12\right).
}
\end{aligned}
]

Первоначально этот расчёт законен при

[
\Re s>\frac12.
]

Полюс (\zeta(s+\frac12)) находится при (s=\frac12), и его коэффициент равен

# [ \mathcal Mh(1)

# \int_0^\infty h(v),dv

A_m.
]

Поэтому доказанное

[
A_m=0
]

точно убивает Müntz-полюс:

[
\boxed{
\mathcal Mh(1)=0.
}
]

Это именно ветка Z. Никакого члена

[
A_mJ_\lambda(s)
]

в 012 не должно остаться.

Но значения

[
s=0,\pm\sigma,
\qquad
0\le\sigma<\frac12,
]

лежат вне исходной области (\Re s>1/2). Поэтому для них всё ещё нужен один из двух законных мостов:

1. Müntz continuation с проверенными гипотезами;
2. exact finite-window Dirichlet-kernel identity, который и строит 012.

Компактный носитель делает сами интегралы

[
\mathcal Mh!\left(\frac12\pm\sigma\right)
]

конечными, но не разрешает автоматически перестановку бесконечной суммы и интеграла в критической полосе.

------

# 4. Endpoint audit

Для mass identity:

[
\int_{\mathbb R}h_\lambda(x),dx=0
]

значения в точках (x=\pm\lambda) не влияют на Lebesgue-интеграл. Поэтому здесь:

```text
ENDPOINT_TERM_MISSING:
  NOT TRIGGERED
```

То же относится к Mellin-интегралам: отдельные teeth

[
u=\frac{\lambda}{n}
]

образуют множество меры ноль.

Но для **точного pointwise** определения (E_\star) half-weight критичен. Схематически:

# [ E_\star(h)(u)

\sqrt u
\left(
\sum_{nu<\lambda}h(nu)
+
\frac12
\mathbf 1_{\lambda/u\in\mathbb N},h(\lambda)
\right).
]

Особенно:

- при (u=\lambda^{-1}) и (\lambda^2=m\in\mathbb N) последний член (n=m) попадает точно в край;
- при каждом tooth (u=\lambda/k) меняется число активных слагаемых;
- точная finite-window crosswalk должна воспроизвести среднее левого и правого значений.

Поэтому правильный ledger:

```text
mass zero:
  endpoint-independent

Mellin integral:
  endpoint-independent as an integral

pointwise E_star / finite-window identity:
  starred midpoint mandatory
```

------

# 5. Самая важная находка: mass-zero не равен полному Poisson-H2

Первичный источник для чистой Poisson-симметрии требует две отдельные гипотезы:

[
f(0)=0,
\qquad
\widehat f(0)=0.
]

Причём

# [ \widehat f(0)

\int_{\mathbb R}f(x),dx.
]

Источник прямо отделяет эти два условия перед тождеством

[
E(\widehat f)(u)=E(f)(u^{-1}).
]

([arXiv](https://arxiv.org/html/2602.04022v1))

011 доказал только:

# [ \widehat h_\lambda(0)

# \int h_\lambda

1. 

]

Он не доказал:

[
h_\lambda(0)=0.
]

Более того, для стандартной prolate-нормировки второе условие вообще говоря **ложно**.

Для двух активных мод:

# [ \widehat h_{0,\lambda}(0)

\chi_0,h_{0,\lambda}(0),
]

# [ \widehat h_{4,\lambda}(0)

\chi_2,h_{4,\lambda}(0),
]

поскольку (0\in[-\lambda,\lambda]) и эти моды диагонализуют truncated Fourier operator.

Следовательно,

# [ I_{0,\lambda}

# \chi_0h_{0,\lambda}(0), \qquad I_{4,\lambda}

\chi_2h_{4,\lambda}(0).
]

Для zero-mass комбинации:

# [ \widetilde h_\lambda

I_4h_0-I_0h_4
]

получаем

[
\begin{aligned}
\widetilde h_\lambda(0)
&=
I_4h_0(0)-I_0h_4(0)\
&=
(\chi_2-\chi_0)
h_0(0)h_4(0).
\end{aligned}
]

У ненулевых чётных решений второго порядка (h_0(0)) и (h_4(0)) ненулевые: иначе одновременно (h(0)=h'(0)=0), что заставило бы решение быть тождественно нулевым. А

[
\chi_0\ne\chi_2.
]

Поэтому при стандартном index lock:

[
\boxed{
h_\lambda(0)\ne0
}
]

для конечного (\lambda).

Итак, код `H2_ZERO_CONFIRMED` надо переименовать:

```text
OLD AMBIGUOUS:
  H2_ZERO_CONFIRMED

CORRECT:
  HTRIAL_MELLIN_MASS_ZERO_CONFIRMED
```

А полный Poisson status:

```text
POISSON_ORIGIN_ZERO:
  FALSE / COUNTERTERM REQUIRED
```

------

# 6. Исправленное Poisson-тождество

Для чётной функции и Fourier convention источника Poisson summation даёт:

# [ f(0)+2\sum_{n\ge1}f(nu)

u^{-1}
\left(
\widehat f(0)
+
2\sum_{k\ge1}\widehat f(k/u)
\right).
]

После умножения на (\sqrt u/2):

# [ \boxed{ E(f)(u)

## E(\widehat f)(u^{-1}) + \frac12u^{-1/2}\widehat f(0)

\frac12u^{1/2}f(0).
}
]

Для нашего mass-zero (h_\lambda):

[
\widehat h_\lambda(0)=0,
]

поэтому:

# [ \boxed{ E(h_\lambda)(u)

## E(\widehat h_\lambda)(u^{-1})

\frac12u^{1/2}h_\lambda(0).
}
]

Это новый точный verdict:

```text
POISSON_ORIGIN_COUNTERTERM_PRESENT
```

Он **не возвращает** старого Müntz-убийцу

[
A_m u^{-1/2}.
]

Тот убит mass-zero. Новый член другой:

[
-\frac12h_\lambda(0)u^{1/2}.
]

И он потенциально хорош для маршрута: (h_\lambda(0)) пропорционален

[
\chi_2-\chi_0,
]

то есть сам связан с prolate-дефектом. Но его нельзя:

- забыть;
- назвать равным нулю;
- оценить отдельно грубой polynomial bound, потеряв cancellation;
- смешать с endpoint half-weight.

Это не endpoint term. Это **origin Poisson counterterm**.

------

# 7. Sign-route: правильный порядок

Порядок принимаю такой:

```text
012 EStarWindowedMellinCrosswalk
→ UpperEdgeSignOrKill
→ CorrectedPoissonCountertermCrosswalk
→ EStarHlambdaPhaseSignAE
→ three Mellin values
→ relative tail
```

Не начинаем с полной theta/Poisson машины. Сначала самый дешёвый убийца.

## 7.1 `EStarUpperEdgeSignOrKill`

Для

[
\frac{\lambda}{2}<u<\lambda
]

из compact support следует, что активен только (n=1):

[
2u>\lambda
\quad\Longrightarrow\quad
h_\lambda(nu)=0
\quad(n\ge2).
]

Поэтому точно:

# [ \boxed{ E_\star(h_\lambda)(u)

\sqrt u,h_\lambda(u),
\qquad
u\in(\lambda/2,\lambda).
}
]

Следовательно, постоянная фаза (E_\star(h_\lambda)) на всём окне возможна только если (h_\lambda) имеет постоянный знак на верхней половине носителя.

Это первый решающий тест:

```text
PASS:
  h_lambda has one sign on (lambda/2, lambda)

KILL:
  h_lambda changes sign there

FAILURE CODE:
  ESTAR_PHASE_SIGN_KILLED_ON_UPPER_EDGE
```

Это можно решить:

- Sturm-осцилляцией exact prolate combination;
- локализацией его последнего положительного нуля;
- interval certificate на одном explicit ODE-отрезке.

Не нужна сумма, Mellin или нули (\zeta).

------

## 7.2 Слабейший sign theorem

Для Mellin-механизма не нужна pointwise nonnegativity на всех teeth. Значения на teeth имеют меру ноль.

Поэтому правильная цель:

[
\boxed{
\texttt{EStarHlambdaPhaseSignAE}:
\quad
\exists\omega_\lambda\in{\pm1},
\quad
\omega_\lambda E_\star(h_\lambda)(u)\ge0
\text{ для почти всех }u\in I_\lambda.
}
]

Не более сильное

[
\forall u\in I_\lambda.
]

Pointwise tooth values можно закрыть отдельной конвенционной леммой позже.

Если source orientation действительно соответствует наблюдаемой фазе:

[
\omega_\lambda=-1,
]

то после доказательства:

[
w_\lambda(u)
:=
-E_\star(h_\lambda)(u)\ge0
\quad\text{a.e.}
]

и

[
\frac{w_\lambda(u),du/u}
{\int w_\lambda(u),du/u}
]

становится вероятностной мерой. Только тогда три Mellin-значения контролируют абсолютный момент.

------

# STRONGEST ATTACK

Фраза из передачи:

> «компактный носитель ([-\lambda,\lambda]) ⇒ support/decay-гипотезы для окна и Мюнца выполняются тривиально»

слишком сильна.

Компактный носитель даёт:

- (L^1)-интегрируемость;
- конечность source Mellin integrals при нужных (p>0);
- конечную сумму (E_\star(h)(u)) для каждого (u>0).

Но он не даёт автоматически:

1. clean Poisson symmetry — остаётся (h_\lambda(0))-counterterm;
2. гладкость zero-extension в (x=\pm\lambda);
3. sum–integral interchange в критической полосе;
4. uniform relative bounds на window corrections;
5. знак (E_\star(h_\lambda)).

Zero-extension prolate-моды обычно имеет boundary jump. Starred half-weights именно поэтому должны выйти из BV/distributional Poisson theorem, а не быть вставлены после вычисления.

Итак, mass-fork принят, но «весь Müntz/Poisson слой теперь тривиален» — нет.

------

# CODEX DIRECTIVE

Гол 012 не перенаправлять.

После его отчёта один следующий target:

```text
EStarUpperEdgeSignOrKill
```

## Exact statement

Для exact source-locked (h_\lambda) решить:

[
\exists\varepsilon_\lambda\in{\pm1},
\quad
\varepsilon_\lambda h_\lambda(x)\ge0
\quad
\forall x\in(\lambda/2,\lambda).
]

И вывести через exact one-term identity:

[
\varepsilon_\lambda E_\star(h_\lambda)(u)\ge0
\quad
\forall u\in(\lambda/2,\lambda).
]

## Validation requirements

```text
- exact h0/h4 coefficients from 011;
- no sampled grid as proof;
- no claim about all of I_lambda;
- locate every zero of h_lambda in (lambda/2,lambda), or prove none;
- preserve source normalization and sign.
```

## Success codes

```text
ESTAR_UPPER_EDGE_SIGN_PROVED
```

или

```text
ESTAR_PHASE_SIGN_KILLED_ON_UPPER_EDGE
```

После green результата следующий theorem:

```text
EStarCorrectedPoissonIdentity
```

с обязательным членом

[
-\frac12u^{1/2}h_\lambda(0).
]

------

# META CLOSEOUT

**Что стало меньше?**

Mass-fork окончательно закрыт:

[
\boxed{
\int_0^\infty h_\lambda(v),dv=0.
}
]

Чистый Mellin pole-term удалён.

**Что убито?**

- pointwise sign самого (h_\lambda);
- двусмысленный код `H2_ZERO_CONFIRMED`;
- предположение, что zero mass автоматически даёт clean Poisson symmetry;
- идея, что compact support автоматически закрывает critical-strip continuation.

**Что найдено?**

# [ \boxed{ E(h_\lambda)(u)

## E(\widehat h_\lambda)(u^{-1})

\frac12u^{1/2}h_\lambda(0).
}
]

Причём (h_\lambda(0)) связан с (\chi_2-\chi_0).

**Текущий smallest named gap после 012:**

[
\boxed{
\texttt{EStarUpperEdgeSignOrKill}.
}
]

**Следующий главный gap:**

[
\boxed{
\texttt{EStarHlambdaPhaseSignAE}.
}
]

**Progress class:** `REPRESENTATION_PROGRESS + FALSIFICATION_PROGRESS`.

**Route score:** (5/5). Mass-fork принят, а скрытый второй Poisson-условие обнаружено до того, как его использовали в sign/Mellin proof.