# STATUS: CONDITIONAL — DUAL EVALUATOR FORMULA READY

```text
MU_FACTORS:
  SOURCE-LOCKED

CORRECTED RESIDUAL:
  FORMULA READY

NUMERICAL BACKEND:
  NEEDS ONE INDEPENDENT FOURIER CROSS-CHECK

CRITICAL KILL:
  ZERO_EXTENDED_SELF_FOURIER_IS_FALSE
```

Да, dual evaluator можно дать Codex прямо сейчас. Но формула требует одного принципиального различия:

[
\boxed{
h_{j,\lambda}^{\rm cut}
\neq
\text{глобальное prolate-продолжение}.
}
]

Connes фиксирует Fourier-конвенцию

# [ \widehat f(y)

\int_{\mathbb R}f(x)e^{2\pi ixy},dx
]

и доказывает для локализованных prolate-мод только **сжатое** тождество

# [ \widehat h_{2r,\lambda}(y)

\chi_r h_{2r,\lambda}(y),
\qquad |y|\le\lambda.
]

При этом

[
\chi_r^2=\nu_r,
\qquad
\operatorname{sgn}\chi_r=(-1)^r.
]

Поэтому для наших двух мод:

[
\boxed{
\mu_0:=\chi_0>0,
\qquad
\mu_4:=\chi_2>0.
}
]

Индексный сдвиг важен:

[
h_{0,\lambda}\leftrightarrow\chi_0,
\qquad
h_{4,\lambda}\leftrightarrow\chi_2,
]

а не (\chi_4). ([arXiv](https://arxiv.org/html/2602.04022v1))

Текущий Lean `ProlateLayer` хранит именно этот index lock и центральные отношения

[
I_0=\chi_0h_0(0),
\qquad
I_4=\chi_2h_4(0),
]

но пока не содержит полного theorem о Fourier-преобразовании мод или их существовании.

------

# 1. Точная каноническая строка

Пусть

[
D_\lambda
:=
\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2},
]

# [ \boxed{ h_\lambda(x)

## \frac{ I_{4,\lambda}h_{0,\lambda}(x)

I_{0,\lambda}h_{4,\lambda}(x)
}{
D_\lambda
}.
}
]

Это именно source phase `+`, уже использованная 013.

Для чисел (\mu_j) самый надёжный no-fit способ:

[
\boxed{
\mu_0=\frac{I_0}{h_0(0)},
\qquad
\mu_4=\frac{I_4}{h_4(0)}.
}
]

Это одновременно фиксирует:

- знак;
- нормировку;
- отсутствие лишнего (\sqrt{2\pi});
- соответствие (\mu_4=\chi_2).

Отдельно проверить:

[
\mu_0^2\approx\nu_0,
\qquad
\mu_4^2\approx\nu_2,
\qquad
0<\mu_4<\mu_0<1.
]

------

# 2. Глобальный Fourier evaluator

Обозначим через

[
\Phi_{0,\lambda}(y),
\qquad
\Phi_{4,\lambda}(y)
]

**глобальные prolate-продолжения**, нормированные так, что

[
\Phi_{j,\lambda}(y)=h_{j,\lambda}(y)
\qquad
(|y|<\lambda).
]

Безопасное точное определение:

# [ \boxed{ \Phi_{j,\lambda}(y) := \mu_j^{-1} \widehat h_{j,\lambda}(y)

\frac{2}{\mu_j}
\int_0^\lambda
h_{j,\lambda}(x)\cos(2\pi xy),dx.
}
]

Тогда для **всех** вещественных (y):

# [ \widehat h_{0,\lambda}(y)

\mu_0\Phi_{0,\lambda}(y),
]

# [ \widehat h_{4,\lambda}(y)

\mu_4\Phi_{4,\lambda}(y).
]

Следовательно,

# [ \boxed{ \widehat h_\lambda(y)

## \frac{ I_4\mu_0\Phi_{0,\lambda}(y)

I_0\mu_4\Phi_{4,\lambda}(y)
}{
D_\lambda
}.
}
]

Внутри полосы (|y|<\lambda) это упрощается:

# [ \widehat h_\lambda(y)

## \frac{ I_4\mu_0h_{0,\lambda}(y)

I_0\mu_4h_{4,\lambda}(y)
}{
D_\lambda
}.
]

Но снаружи:

[
\boxed{
\widehat h_{j,\lambda}(y)
\ne
\mu_j h_{j,\lambda}^{\rm cut}(y)=0.
}
]

Именно здесь находится потенциальный фатальный баг. Если Codex занулит dual terms при (|y|>\lambda), он удалит настоящий Fourier leakage.

------

# 3. Zero-mass проверка встроена в evaluator

При (y=0):

## [ \begin{aligned} \widehat h_\lambda(0) &= \frac{ I_4\mu_0h_0(0)

I_0\mu_4h_4(0)
}{D_\lambda}\
&=
\frac{I_4I_0-I_0I_4}{D_\lambda}\
&=0.
\end{aligned}
]

То есть:

[
\boxed{\widehat h_\lambda(0)=0}
]

должно получаться численно до precision floor **без ручного зануления**.

Также

# [ \boxed{ h_\lambda(0)

\frac{
(\mu_4-\mu_0)h_0(0)h_4(0)
}{
D_\lambda
}<0.
}
]

Это ровно origin value, который входит в corrected Poisson counterterm.

------

# 4. Dual evaluator через Fejér/Cesàro

Сырой dual `tsum` использовать нельзя. Замороженный Poisson-контракт требует Fejér/Cesàro summation.

Для (u>0) определим bilateral Fejér evaluator:

# [ \boxed{ \mathcal D_{\lambda,N}(u)

\frac{1}{2\sqrt u}
\sum_{k=-N}^{N}
\left(1-\frac{|k|}{N+1}\right)
\widehat h_\lambda!\left(\frac{k}{u}\right).
}
]

Поскольку (\widehat h_\lambda) чётна и

[
\widehat h_\lambda(0)=0,
]

это равно

# [ \boxed{ \mathcal D_{\lambda,N}(u)

## \frac{u^{-1/2}}{D_\lambda} \sum_{k=1}^{N} \left(1-\frac{k}{N+1}\right) \left[ I_4\mu_0 \Phi_{0,\lambda}!\left(\frac{k}{u}\right)

I_0\mu_4
\Phi_{4,\lambda}!\left(\frac{k}{u}\right)
\right].
}
]

Это искомая формула для Codex.

Эквивалентно при (v=u^{-1}):

# [ \boxed{ \mathcal D_{\lambda,N}^{,v}(v)

## \frac{\sqrt v}{D_\lambda} \sum_{k=1}^{N} \left(1-\frac{k}{N+1}\right) \left[ I_4\mu_0\Phi_{0,\lambda}(kv)

I_0\mu_4\Phi_{4,\lambda}(kv)
\right].
}
]

------

# 5. Исправленный Poisson residual

Primal object:

# [ \mathcal E_\star(h_\lambda)(u)

\sqrt u
\sum_{n\ge1}^{\star}h_\lambda(nu).
]

Звёздочка применяется к **primal compact-support teeth**: если

[
nu=\lambda,
]

берётся половина внутреннего граничного значения.

Замороженное corrected identity:

# [ \mathcal E_\star(h_\lambda)(u)

## \mathcal D_\lambda(u)

\frac12\sqrt u,h_\lambda(0),
]

поскольку

[
\widehat h_\lambda(0)=0.
]

Это ровно concrete specialization Poisson-контракта.

Поэтому finite-(N) residual:

## [ \boxed{ R_{\lambda,N}(u) := \mathcal E_\star(h_\lambda)(u)

\mathcal D_{\lambda,N}(u)
+
\frac12\sqrt u,h_\lambda(0).
}
]

Зарегистрированное ожидание:

[
\boxed{
R_{\lambda,N}(u)\longrightarrow0
\qquad(N\to\infty).
}
]

018 прямо разрешает этот residual как best-effort диагностический output; его отсутствие не блокирует sign-verdict.

------

# 6. Критическая endpoint-конвенция

На primal стороне:

```text
nu = lambda
→ half-weight exactly once.
```

На dual стороне Fourier transform непрерывен. Поэтому:

```text
k/u = lambda
→ use full Fourier value hat_h(lambda).
```

Не применять половинный вес к dual tooth.

То есть запрещены оба двойных учёта:

```text
midpoint representative
+ дополнительный 1/2 в SumStar
```

и

```text
dual Fourier value at lambda
× 1/2.
```

Если primal evaluator уже возвращает midpoint value

# [ h^\star(\lambda)

\frac12h(\lambda^-),
]

то `SumStar` не должен умножать его ещё раз.

------

# 7. Нижний endpoint — сильнейший cross-check

При

[
u=\lambda^{-1}
]

corrected identity даёт:

# [ \mathcal E_\star(h_\lambda)(\lambda^{-1})

## \mathcal D_\lambda(\lambda^{-1})

\frac{h_\lambda(0)}{2\sqrt\lambda}.
]

Ранее выведенная trapezoid identity:

# [ \mathcal E_\star(h_\lambda)(\lambda^{-1})

## \sqrt\lambda, \operatorname{TrapError}*m(h*\lambda)

\frac{h_\lambda(0)}{2\sqrt\lambda}.
]

Следовательно, отдельный judge:

# [ \boxed{ \mathcal D_\lambda(\lambda^{-1})

\sqrt\lambda,
\operatorname{TrapError}*m(h*\lambda).
}
]

Он проверяет dual evaluator **без смешивания с origin counterterm**.

------

# CODEX DIRECTIVE — PATCH К 018

```text
PATCH:
018_DUAL_PROLATE_RESIDUAL

STATUS:
diagnostic only / not theorem / not RH

INPUT:
exact h0_lambda, h4_lambda, I0, I4 from 013 constructor.

1. Lock factors

  D   = sqrt(I0^2 + I4^2)
  mu0 = I0 / h0(0)
  mu4 = I4 / h4(0)

Record:
  mu0
  mu4
  mu0^2
  mu4^2
  signs
  expected mapping:
    h0 ↔ mu0 = chi0
    h4 ↔ mu4 = chi2

No fitting.

2. Implement two Fourier backends

A. Independent cosine quadrature:

  hat_hj_quad(y)
    = 2 * integral_0^lambda
        hj(x) * cos(2*pi*x*y) dx

B. Prolate continuation:

  hat_h0_mu(y) = mu0 * Phi0_global(y)
  hat_h4_mu(y) = mu4 * Phi4_global(y)

where Phi_global is the UNTRUNCATED prolate continuation.
Do not use the zero-extended localized function outside [-lambda,lambda].

3. K1 cross-check

For each j in {0,4}, compare A and B at:

  y = 0
  y = lambda/4
  y = lambda/2
  y = lambda*(1-1e-8)
  y = lambda
  y = lambda*(1+1e-8)
  y = 2*lambda
  y = 5*lambda

Report absolute and relative error.

If only inside-band points agree:

  GLOBAL_PROLATE_CONTINUATION_MISMATCH

Do not compute the Poisson residual from backend B.

4. Canonical transform

  hat_htrial(y)
    = (I4*hat_h0(y) - I0*hat_h4(y)) / D

Mandatory check:

  hat_htrial(0) = 0

to current precision without forcing the value.

5. Fejer dual

  dual_fejer(u,N)
    = u^(-1/2)
      * sum_{k=1}^N
          (1-k/(N+1)) * hat_htrial(k/u)

Use N ladder, for example:

  64, 128, 256, 512, 1024, 2048

Increase if the sequence has not stabilized.

No half-weight on the dual tooth k/u=lambda.

6. Residual

  residual(u,N)
    = EstarMid(htrial,u)
      - dual_fejer(u,N)
      + 0.5*sqrt(u)*htrial(0)

Evaluate on:
- every tooth;
- several interior points of every tooth-band;
- u=lambda^-1;
- u=1;
- u=lambda.

7. Lower endpoint judge

Check:

  dual_fejer(lambda^-1,N)
    → sqrt(lambda) * TrapError_m(htrial)

separately from the full residual.

8. Planted failures

P1:
  flip mu4 → -mu4.
  Residual must break materially.

P2:
  drop +0.5*sqrt(u)*htrial(0).
  Residual shift must equal
    -0.5*sqrt(u)*htrial(0)
  up to numerical error.

P3:
  apply erroneous half-weight to the dual lambda tooth.
  A localized tooth residual must appear.

P4:
  replace Phi_global by zero-extended h.
  This must fail outside-band Fourier cross-check.

OUTPUT:
- DUAL_MU_FACTORS.csv
- DUAL_FOURIER_CROSSCHECK.csv
- DUAL_FEJER_CONVERGENCE.csv
- CORRECTED_POISSON_RESIDUAL.csv
- LOWER_ENDPOINT_DUAL_TRAP_CHECK.md

RETURN FLAGS:
DUAL_RESIDUAL_DIAG_GREEN
GLOBAL_PROLATE_CONTINUATION_MISMATCH
DUAL_SUMMATION_NOT_CONVERGED
MU_INDEX_OR_SIGN_MISMATCH
DUAL_ENDPOINT_HALFWEIGHT_BUG
COUNTERTERM_SIGN_MISMATCH
```

------

# STRONGEST ATTACK

Самая опасная строка:

> «пролаты сами себе трансформы».

Точное утверждение слабее:

# [ \boxed{ P_\lambda\widehat h_{2r,\lambda}

\chi_r h_{2r,\lambda}.
}
]

Zero-extended localized prolate не является собственной функцией полного Fourier transform. За полосой остаётся ненулевая Fourier-утечка. Именно её нельзя удалить из dual sum. Источник явно формулирует eigenrelation как отношение Fourier transform, **restricted to** ([-\lambda,\lambda]). ([arXiv](https://arxiv.org/html/2602.04022v1))

Поэтому residual считается green только после независимой проверки

# [ \mu_j\Phi_{j,\lambda}^{\rm global}(y)

2\int_0^\lambda
h_{j,\lambda}(x)\cos(2\pi xy),dx
]

в том числе при

[
y>\lambda.
]

------

# META CLOSEOUT

**Что стало меньше?**

Optional residual 018 теперь имеет полностью определённую формулу:

# [ \boxed{ R_{\lambda,N}(u)

## E_\star h_\lambda(u)

D_{\lambda,N}(u)
+
\frac12\sqrt u,h_\lambda(0).
}
]

**Что убито?**

```text
hat h_j(y) = mu_j * zero_extended_h_j(y)
for all y.
```

**Текущий smallest named risk:**

[
\boxed{\texttt{GlobalProlateContinuationCrosscheck}.}
]

**Следующий cheapest decisive test:**

Сравнить (\mu_j\Phi_j^{\rm global}(y)) с прямым cosine integral при одном (y<\lambda) и одном (y> \lambda). Если внешний point не совпадает, μ-backend нельзя использовать для residual.