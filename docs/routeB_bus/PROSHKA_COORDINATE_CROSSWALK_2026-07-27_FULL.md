# STATUS: COORDINATE CROSSWALK PROVED

```text
MU_FORMULA:
  CORRECTED

λ^(3/2) HYPOTHESIS:
  YES as a possible asymptotic of the raw t-mode normalization;
  NO as the coordinate factor in μ.

019 SEMANTIC DIAGNOSIS:
  T_TO_X_MODE_NORMALIZATION_MISMATCH

RESIDUAL:
  correctly remains blocked
```

Формула

[
\mu_j=\frac{I_j}{h_j(0)}
]

сама по себе была правильной. Ошибка 019 в другом: (I_j) бралось у **L²-нормированной функции в (x)-координате**, а (h_j(0)) — у иначе масштабированной ODE-функции в (t=x/\lambda)-координате. Отчёт 019 это уже установил напрямую: сохранённые (I_j) совпадают с центрами независимо L²-нормированных мод, но не с центрами конструктора 013.

Источник действительно начинает с

# [ \widetilde h_{j,\lambda}(x)

\operatorname{PS}_{j,0}
\left(2\pi\lambda^2,\frac{x}{\lambda}\right),
]

после чего функцию нормируют в (L^2([-\lambda,\lambda],dx)). Lean-контракт также требует, чтобы (I_j), (h_j(0)) и (\chi_j) относились к одной и той же L²-нормированной (x)-функции:

[
I_0=\chi_0h_0(0),\qquad
I_4=\chi_2h_4(0).
]

------

# 1. Точный пересчёт (t\leftrightarrow x)

Фиксируем конвенцию:

[
t\in[-1,1],\qquad x=\lambda t,
]

# [ \widehat f(y)

\int_{\mathbb R}f(x)e^{2\pi ixy},dx.
]

Пусть (\varphi_j(t)) — **сырая функция конструктора 013** в (t)-координате, в любой ненулевой амплитудной нормировке. Введём:

[
N_j
:=
\left(
\int_{-1}^{1}|\varphi_j(t)|^2dt
\right)^{1/2},
]

[
J_j
:=
\int_{-1}^{1}\varphi_j(t),dt,
\qquad
c_j:=\varphi_j(0).
]

Фазу выбираем так, чтобы (J_j>0). Тогда соответствующая source-функция, L²-нормированная в (x)-единицах, равна

# [ \boxed{ h_{j,\lambda}^{x}(x)

\frac{1}{\sqrt{\lambda},N_j}
\varphi_j!\left(\frac{x}{\lambda}\right),
\qquad |x|<\lambda.
}
]

Endpoint midpoint не влияет ни на норму, ни на интеграл.

## Норма

Поскольку (dx=\lambda,dt),

# [ \left| \varphi_j!\left(\frac{\cdot}{\lambda}\right) \right|_{L^2(dx)}

\sqrt{\lambda},N_j.
]

Поэтому L²-renormalization multiplier:

# [ \boxed{ a_j

\frac{1}{\sqrt{\lambda},N_j}.
}
]

## Центральное значение

# [ \boxed{ h_{j,\lambda}^{x}(0)

\frac{c_j}{\sqrt{\lambda},N_j}.
}
]

## Интеграл в (x)-единицах

[
\begin{aligned}
I_j^x
&=
\int_{-\lambda}^{\lambda}
h_{j,\lambda}^{x}(x),dx\
&=
\frac{\lambda}{\sqrt{\lambda}N_j}
\int_{-1}^{1}\varphi_j(t),dt.
\end{aligned}
]

Следовательно,

# [ \boxed{ I_j^x

\frac{\sqrt{\lambda},J_j}{N_j}.
}
]

## No-fit Fourier multiplier

Теперь нормировка полностью сокращается:

# [ \boxed{ \mu_j

# \frac{I_j^x}{h_{j,\lambda}^{x}(0)}

\lambda,\frac{J_j}{c_j}.
}
]

Итак, исправленная формула:

# [ \boxed{ \mu_j

\lambda
\frac{\displaystyle\int_{-1}^{1}\varphi_j(t),dt}
{\varphi_j(0)}.
}
]

Никакого fitted scalar. Никакого (\sqrt{2\pi}). Никакого использования сохранённого (I_j^x) вместе с сырым (c_j).

------

# 2. Операторное подтверждение фактора (\lambda)

Положим (y=\lambda s). Тогда

# [ \widehat{h_j^x}(\lambda s)

\frac{\sqrt{\lambda}}{N_j}
\int_{-1}^{1}
\varphi_j(t)e^{2\pi i\lambda^2st},dt.
]

Если dimensionless finite-Fourier operator конструктора записан без prefactor:

# [ (\mathcal K_\lambda\varphi)(s)

\int_{-1}^{1}
\varphi(t)e^{2\pi i\lambda^2st},dt
]

и

# [ \mathcal K_\lambda\varphi_j

\kappa_j\varphi_j,
]

то сравнение с

# [ h_j^x(\lambda s)

\frac{\varphi_j(s)}
{\sqrt{\lambda}N_j}
]

даёт

[
\boxed{
\mu_j=\lambda\kappa_j.
}
]

При (s=0):

[
\kappa_j=\frac{J_j}{c_j},
]

поэтому снова

[
\boxed{
\mu_j=\lambda\frac{J_j}{c_j}.
}
]

Если библиотечный operator уже определён с prefactor (\lambda),

[
\lambda\int_{-1}^{1}
\varphi(t)e^{2\pi i\lambda^2st}dt,
]

его eigenvalue уже является (\mu_j). Это надо записать как поле `operator_prefactor`, а не угадывать.

------

# 3. Что произошло в 019

Старая строка фактически считала

# [ \mu_j^{\rm old}

\frac{I_j^x}{c_j},
]

где (c_j) было сырым центральным значением конструктора.

Но

[
I_j^x=a_j\lambda J_j,
]

поэтому

# [ \mu_j^{\rm old}

# a_j \left( \lambda\frac{J_j}{c_j} \right)

\boxed{
a_j\mu_j.
}
]

То есть огромные числа (27)–(180) — это почти не Fourier multipliers, а пропущенные mode-amplitude multipliers

[
a_j=\frac{1}{\sqrt{\lambda}N_j}.
]

Именно поэтому backend A и B разошлись уже в (y=0) на (96)–(99%).

------

# 4. Проверка гипотезы (\lambda^{3/2})

## Точный coordinate ledger

От одной только замены (x=\lambda t):

| Величина                       | Множитель                                           |
| ------------------------------ | --------------------------------------------------- |
| (dx)                           | (\lambda)                                           |
| L²-норма raw pullback          | (\sqrt{\lambda})                                    |
| L²-normalization amplitude     | (1/\sqrt{\lambda}) — дополнительно деление на (N_j) |
| нормированный интеграл (I_j^x) | (\sqrt{\lambda},J_j/N_j)                            |
| нормированный центр (h_j^x(0)) | (c_j/(\sqrt{\lambda}N_j))                           |
| ratio (\mu_j)                  | (\lambda J_j/c_j)                                   |

Следовательно:

[
\boxed{
\text{Jacobian + L² normalization дают }\sqrt{\lambda}
\text{ в интеграле, не }\lambda^{3/2}.
}
]

И

[
\boxed{
\mu_j\text{ несёт ровно один явный factor }\lambda.
}
]

## Где всё-таки появляется класс (\lambda^{3/2})

Он может появляться в **сырой нормировке Frobenius/ODE-моды**:

[
N_j(\lambda)=|\varphi_j|_{L^2(-1,1)}.
]

Из данных 019 можно диагностически восстановить:

# [ N_j

\frac{1}{a_j\sqrt{\lambda}}.
]

Для (h_0) получаем приблизительно

# [ N_0\lambda^{3/2}

0.0926,\ 0.0896,\ 0.0889
]

на (m=13,53,257). Для (h_4):

# [ N_4\lambda^{3/2}

0.1309,\ 0.0970,\ 0.0904.
]

То есть данные действительно совместимы с

[
\boxed{
N_j(\lambda)\asymp C_j\lambda^{-3/2}
}
]

в больших клетках.

Но это:

```text
FIT_NOT_LAW
```

и это свойство конкретной сырой Frobenius-нормировки, не coordinate identity.

При таком поведении:

# [ a_j

\frac1{\sqrt{\lambda}N_j}
\asymp
C_j^{-1}\lambda.
]

Именно линейный рост (a_j\sim11\lambda), а не (\lambda^{3/2}), виден в ошибочных (\mu_j^{old}).

### Вердикт по гипотезе

```text
λ^(3/2) in inverse raw t-mode norm:
  DIAGNOSTICALLY PLAUSIBLE

λ^(3/2) as correction to μ:
  FALSE

exact μ correction:
  multiply dimensionless J/c by λ
```

------

# 5. Канонический packet прямо в (t)-координате

Это самый безопасный способ больше не смешивать нормировки.

После фазового выравнивания (J_0,J_4>0) source packet

# [ h_\lambda

\frac{I_4h_0-I_0h_4}
{\sqrt{I_0^2+I_4^2}}
]

можно записать непосредственно через сырые ODE-моды:

# [ \boxed{ h_\lambda(\lambda t)

\frac{
J_4\varphi_0(t)-J_0\varphi_4(t)
}{
\sqrt{\lambda},
\sqrt{
J_0^2N_4^2+J_4^2N_0^2
}
}.
}
]

Здесь использована точная ортогональность двух prolate-мод.

Эта формула:

- инвариантна относительно независимого масштабирования (\varphi_0,\varphi_4);
- имеет L²-норму (1);
- имеет нулевую массу тождественно:
  [
  \int h_\lambda=0;
  ]
- не использует сохранённые (I_j) из другой нормировки.

Это также дешёвый object judge для 018.

## Поправка к статусу 018

018 остаётся независимым от Poisson residual как численная проверка знака **того packet, который реально вычислял 013**. Но его идентификация с каноническим source packet не автоматична: scale factors двух мод различались, например (38.95) против (27.55) при (m=13). Поэтому independent modal rescaling не является общим скаляром.

Точный ledger:

```text
018_INSTRUMENT_AND_COVERAGE_GREEN
018_TESTED_PACKET_SINGLE_SIGN_DIAGNOSTIC_GREEN
018_CANONICAL_SOURCE_PACKET_IDENTITY:
  RECHECK_REQUIRED
```

Достаточно сравнить старый packet с boxed raw-(t) формулой. Если разность на arithmetic floor — полный повтор 018 не нужен. Если нет — 320 полос надо прогнать ещё раз на исправленном packet.

------

# UPDATED PATCH — шаги 1–2

```text
PATCH:
019R_T_TO_X_COORDINATE_AND_MODE_NORMALIZATION_LOCK

STATUS:
diagnostic / object lock / not theorem / not RH

FOURIER CONVENTION:
  t in [-1,1]
  x = lambda*t
  y = lambda*s

  Fourier_x[h](y)
    = integral_R h(x) * exp(2*pi*i*x*y) dx

  C = 2*pi*lambda^2

No sqrt(2*pi) prefactor.
If a library operator has an explicit prefactor, record it exactly.
```

## STEP 1 — SAME-MODE COORDINATE AND NORMALIZATION LOCK

```text
For each j in {0,4}, preserve the exact raw constructor mode

  phi_j(t), t in [-1,1].

Do not first rescale its center.

Compute from that same function:

  N_j
    = sqrt(integral_-1^1 |phi_j(t)|^2 dt)

  J_j
    = integral_-1^1 phi_j(t) dt

  c_j
    = phi_j(0)

Choose one global real phase eps_j in {+1,-1}
so that eps_j*J_j > 0.

Replace:

  phi_j <- eps_j*phi_j
  J_j   <- eps_j*J_j
  c_j   <- eps_j*c_j.
```

Construct the x-space source mode:

```text
  h_j_x(x)
    = phi_j(x/lambda) / (sqrt(lambda)*N_j)
      for |x| < lambda

  h_j_x(0)
    = c_j / (sqrt(lambda)*N_j)

  I_j_x
    = sqrt(lambda)*J_j/N_j
```

Build three independent scale checks:

```text
  scale_L2
    = 1 / (sqrt(lambda)*N_j)

  scale_integral
    = I_j_saved / (lambda*J_j)

  scale_center
    = h_j_L2_saved(0) / c_j
```

Required:

```text
  scale_L2
  = scale_integral
  = scale_center
```

within the registered precision budget.

Do not average these scales.
Do not fit one to another.

Then compute:

```text
  mu_from_t
    = lambda * J_j / c_j

  mu_from_x
    = I_j_x / h_j_x(0)

  mu_from_saved_source
    = I_j_saved / h_j_L2_saved(0)
```

Required:

```text
  mu_from_t
  = mu_from_x
  = mu_from_saved_source

  0 < mu_j <= 1
```

for the source phase and these two even modes.

### Canonical packet — two independent routes

Route A:

```text
  D_x = sqrt(I0_x^2 + I4_x^2)

  htrial_A(x)
    = (I4_x*h0_x(x) - I0_x*h4_x(x)) / D_x
```

Route B, directly from raw t modes:

```text
  htrial_B(lambda*t)
    =
    (J4*phi0(t) - J0*phi4(t))
    /
    (sqrt(lambda)
      * sqrt(J0^2*N4^2 + J4^2*N0^2))
```

Required:

```text
  htrial_A = htrial_B
  integral htrial_A = 0
  ||htrial_A||_2 = 1
```

without forcing any of these values.

Also verify:

```text
  <h0_x,h4_x> = 0
```

to the precision expected from the ODE/Legendre solver.

Failure codes:

```text
T_TO_X_L2_SCALE_MISMATCH
SOURCE_INTEGRAL_SCALE_MISMATCH
SOURCE_CENTER_SCALE_MISMATCH
PROLATE_MODE_ORTHOGONALITY_INSTRUMENT_GAP
CANONICAL_PACKET_NORMALIZATION_MISMATCH
```

------

## STEP 2 — NO-FIT FOURIER K1 IN EXPLICIT COORDINATES

### Backend A — direct transform from raw (t)-mode

```text
hat_hj_A(y)
  =
  sqrt(lambda)/N_j
  * integral_-1^1
      phi_j(t) * exp(2*pi*i*lambda*y*t) dt
```

For even real modes:

```text
hat_hj_A(y)
  =
  2*sqrt(lambda)/N_j
  * integral_0^1
      phi_j(t)*cos(2*pi*lambda*y*t) dt
```

### Dimensionless compressed eigenvalue

Define:

```text
kappa_j = J_j/c_j
mu_j    = lambda*kappa_j
```

The exact dimensionless operator statement is:

```text
integral_-1^1
  phi_j(t)*exp(2*pi*i*lambda^2*s*t) dt
    =
  (mu_j/lambda) * phi_j(s)
```

for strict interior (|s|<1).

Equivalently:

```text
hat_hj_A(y) = mu_j*h_j_x(y)
```

for strict interior (|y|<lambda).

### Backend B — global prolate continuation

If `Phi_j_global_t(s)` is normalized so that

```text
Phi_j_global_t(s) = phi_j(s)
```

for (|s|<1), use:

```text
hat_hj_B(y)
  =
  mu_j
  / (sqrt(lambda)*N_j)
  * Phi_j_global_t(y/lambda)
```

for all (y).

Do not use the zero-extended localized mode outside the band.

### Mandatory K1 checks

At (y=0):

```text
hat_hj_A(0)
  = I_j_x
  = mu_j*h_j_x(0)
  = hat_hj_B(0)
```

without manually assigning any value.

Inside band, compare at:

```text
y = 0
y = lambda/4
y = lambda/2
y = lambda*(1-1e-8)
```

At (y=\lambda):

```text
use the interior-limit/global-continuation value;
do not use the midpoint-valued zero extension.
```

Outside band, compare independent backends at:

```text
lambda*(1+1e-8)
2*lambda
5*lambda
```

with the existing oscillatory-quadrature guards.

### Corrected canonical transform

```text
hat_htrial(y)
  =
  (I4_x*hat_h0(y) - I0_x*hat_h4(y)) / D_x
```

Mandatory:

```text
hat_htrial(0) = 0
```

without forced cancellation.

Do not form the Fejér residual until all same-mode and Fourier K1 checks pass.

Return exactly one primary code:

```text
PROLATE_COORDINATE_AND_NORMALIZATION_LOCK_GREEN

T_TO_X_MODE_NORMALIZATION_MISMATCH

COMPRESSED_FOURIER_LAMBDA_FACTOR_MISMATCH

CANONICAL_PACKET_MISMATCH

GLOBAL_PROLATE_CONTINUATION_MISMATCH

GLOBAL_CONTINUATION_FLOOR_UNRESOLVED
```

------

# STRONGEST ATTACK

Не чинить старые числа операцией вроде

```text
mu_old / lambda
```

или

```text
mu_old / lambda^(3/2).
```

Это снова fitting.

Причина: пропущенный multiplier

[
a_j=\frac1{\sqrt{\lambda}N_j}
]

mode-dependent. В 019 он различается между (h_0) и (h_4). Поэтому единственный корректный repair:

[
\boxed{
\text{recompute }J_j,N_j,c_j
\text{ from the same raw mode}.
}
]

Затем:

[
\boxed{
\mu_j=\lambda J_j/c_j.
}
]

# FINAL PROPOSAL

Следующий цикл не должен пытаться считать residual.

Порядок:

```text
1. Rebuild same-mode t→x crosswalk.
2. Construct canonical packet by Route A and raw-t Route B.
3. Decide whether 018 tested the canonical packet.
4. Recompute μ = λJ/c.
5. Pass inside/outside Fourier K1.
6. Only then restart Fejér ladder and residual.
```

# META CLOSEOUT

**Что стало меньше?**

019 mismatch свёлся к одному точному равенству:

# [ \boxed{ \mu_j

\lambda
\frac{\int_{-1}^{1}\varphi_j(t),dt}
{\varphi_j(0)}.
}
]

**Что убито?**

- (\mu=I_{\rm L2}/h_{\rm raw}(0));
- (\lambda^{3/2}) как correction factor для (\mu);
- попытка чинить mismatch одной общей константой;
- автоматическая идентификация packet 018 с source packet.

**Что подтвердилось частично?**

Сырые ODE/Frobenius-моды диагностически имеют норму порядка

[
N_j\asymp\lambda^{-3/2},
]

что объясняет линейно растущий missing amplitude multiplier. Но это отдельный normalization asymptotic, не Fourier coordinate law.

**Текущий smallest named gap:**

[
\boxed{\texttt{ProlateTToXSameModeNormalizationCrosswalk}.}
]

После него:

[
\boxed{\texttt{CanonicalPacketFourierK1}.}
]