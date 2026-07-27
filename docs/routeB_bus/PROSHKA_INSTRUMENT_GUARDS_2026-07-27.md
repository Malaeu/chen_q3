Worked for 3m 56s

# STATUS: REPRESENTATION_PROGRESS



```
GLOBAL_SELF_FOURIER_CLAIM:
  KILLED

COMPRESSED_PROLATE_EIGENRELATION:
  ACCEPTED

OUTSIDE_BAND_FOURIER_LEAKAGE:
  REQUIRED

018 FULL-WINDOW SIGN:
  PRIMARY JUDGE

DUAL POISSON RESIDUAL:
  SECONDARY DIAGNOSTIC
```

Это именно правильная самокоррекция. Источник фиксирует только сжатую Fourier-связь; текущий Lean-слой также хранит центральные отношения и индексный lock, но не утверждает глобальное self-Fourier равенство.

018 не задерживаем ради residual. Его основная задача остаётся прежней: решить, сохраняет ли
$$
E_\star(h_\lambda)(u)
=
\sqrt u\sum_{n\ge1}^{\star}h_\lambda(nu)
$$
один знак на всех tooth-bands окна. Residual остаётся `best effort`, как и записано в goal.

## Два последних instrument-гварда

### 1. Ноль Fourier transform проверять относительно cancellation scale

Недостаточно вывести только абсолютное число
$$
|\widehat h_\lambda(0)|.
$$
Поскольку ноль получается вычитанием двух больших членов, надо также вывести
$$
\boxed{
\varepsilon_0
=
\frac{
|\widehat h_\lambda(0)|
}{
D_\lambda^{-1}
\left(
|I_4\mu_0\Phi_0(0)|
+
|I_0\mu_4\Phi_4(0)|
\right)
}.
}
$$
Green означает:



```
ε0 decreases with precision
and reaches the expected arithmetic floor.
```

Иначе маленький абсолютный residual может быть просто cancellation-limited вычислением.

### 2. Poisson residual тоже нормировать относительно компонентов

Кроме абсолютного
$$
R_{\lambda,N}(u)
=
E_\star(h_\lambda)(u)
-
\mathcal D_{\lambda,N}(u)
+
\frac12\sqrt u\,h_\lambda(0),
$$
нужен scale-free показатель:
$$
\boxed{
r_{\lambda,N}(u)
=
\frac{|R_{\lambda,N}(u)|}{
|E_\star(h_\lambda)(u)|
+
|\mathcal D_{\lambda,N}(u)|
+
\frac12\sqrt u\,|h_\lambda(0)|
+
\varepsilon_{\rm floor}
}.
}
$$
Это отделяет настоящий Poisson mismatch от огромной cancellation между dual term и положительным origin-контрчленом.

------

# Решающее дерево после 018

## Ветка A



```
ESTAR_PHASE_SIGN_KILLED
```

Обнаружен устойчивый положительный открытый интервал.

Тогда:

- `EStarHlambdaPhaseSignAE` убит;
- вероятностное представление через $-E_\star(h_\lambda)\,du/u$ убито;
- три Mellin-значения больше не контролируют абсолютный момент;
- corrected Poisson crosswalk остаётся полезным самостоятельным theorem, но не спасает sign-route.

Repair:
$$
\frac{
\int |E_\star(h_\lambda)(u)|e^{\sigma|\log u|}\,du/u
}{
\left|\int E_\star(h_\lambda)(u)\,du/u\right|
}
$$
оценивать напрямую, без positivity.

## Ветка B



```
ESTAR_FULL_WINDOW_DIAG_SINGLE_SIGN
```

И одновременно:



```
DUAL_RESIDUAL_DIAG_GREEN
```

Тогда перо получает реальную цель:
$$
\boxed{\texttt{DualThetaDominance}}
$$
с правильным знаком:
$$
E_{\rm dual}(\widehat h_\lambda)(v)
\le
-\frac{|h_\lambda(0)|}{2\sqrt v},
\qquad
1\le v\le\lambda.
$$
После этого запускается замороженный `CorrectedPoissonCountertermCrosswalk`.

## Ветка C



```
GLOBAL_PROLATE_CONTINUATION_MISMATCH
```

Внутри полосы μ-backend совпадает с cosine quadrature, снаружи — нет.

Это не математическое опровержение Poisson. Это означает, что используемый `Phi_global` — не тот глобальный continuation или его масштаб/аргумент неверен. Residual из μ-backend запрещается; sign-вердикт 018 остаётся независимым.

## Ветка D



```
DUAL_SUMMATION_NOT_CONVERGED
```

Cosine и μ-backends согласованы, но Fejér ladder не стабилизируется.

Тогда открыт только summation-mode вопрос:



```
Fejér rate / Abel summation / insufficient N.
```

Нельзя объявлять ошибку контрчлена или Poisson-конвенции без plant failure.

------

# STRONGEST ATTACK

Теперь самый опасный numerical failure находится не в математике, а в вычислении
$$
2\int_0^\lambda
h_j(x)\cos(2\pi xy)\,dx
$$
при $y>\lambda$.

Из-за сильной осцилляции обычная quadrature может ложно «подтвердить» нулевую утечку. Поэтому внешний crosscheck считается действительным только при одном из условий:



```
- arbitrary precision with interval subdivision;
- oscillatory quadrature with an independent convergence ladder;
- agreement of two genuinely different quadrature schemes.
```

Сравнение двух реализаций, которые используют один и тот же PSWF backend, независимым судьёй не является.

------

# FINAL PROPOSAL

Ничего нового в очередь не добавляем.



```
018:
  primary → full-window sign or kill

optional secondary:
  global Fourier crosscheck
  → Fejér dual
  → corrected residual
  → lower-endpoint dual/trapezoid judge
```

Green residual должен пережить все четыре планта. Особенно важен plant:



```
replace global continuation by zero extension
→ outside-band crosscheck and residual must break.
```

Это доказывает, что прибор действительно видит ту Fourier-утечку, которую прежняя фраза случайно уничтожала.

# META CLOSEOUT

**Что стало меньше?**

Неопределённое «пролаты сами себе трансформы» заменено точной двухслойной структурой:
$$
\boxed{
P_\lambda\widehat h_j=\mu_jh_j
}
$$
и
$$
\boxed{
(I-P_\lambda)\widehat h_j
\text{ — настоящая глобальная утечка}.
}
$$
**Что убито?**

- глобальная self-Fourier идентификация zero-extended mode;
- зануление dual terms при $|y|>\lambda$;
- half-weight на dual tooth;
- ручное присваивание $\widehat h_\lambda(0)=0$.

**Текущий судья:**
$$
\boxed{\texttt{EStarFullWindowSignOrKill}.}
$$
**Progress class:** `FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS`.

**Route score:** $5/5$. Прибор теперь устроен так, что старая ошибочная модель обязана провалиться на planted test, прежде чем новая модель получит green.