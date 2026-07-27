Worked for 7m 4s

# STATUS: CONDITIONAL



```
G3_MINIMAL_SUFFICIENT_METHOD:
  (a) CERTIFIED_INTERVAL_SUBDIVISION

(b) OSCILLATORY_QUADRATURE:
  fallback if interval dependency explodes

(c) TWO_FLOAT_QUADRATURES:
  insufficient at the current floor
```

**Выбираем (a).** Но с важной оговоркой:
$$
\boxed{
\text{нужен настоящий interval enclosure, а не просто }mp.dps\uparrow
+\texttt{quadsubdiv}.
}
$$
020 уже показал, почему вариант (c) недостаточен: composite Gauss и независимый Simpson согласились только на масштабе $10^{-15}$, после чего честный verdict остался `FLOOR_UNRESOLVED`.

При этом same-mode crosswalk, три формулы для $\mu$, канонический пакет A/B и внутренний Fourier K1 уже прошли; значит G3 теперь действительно изолирован как чистая внешнеполосная численная проблема.

------

# Почему именно (a)

У `mpmath.iv` базовая interval-арифметика действительно предназначена для гарантированного включения точного результата последовательности поддерживаемых interval-операций. Но сама документация предупреждает, что interval-поддержка экспериментальна и не все функции корректно её поддерживают. Обычные `quad(..., error=True)` и `quadsubdiv` дают численную оценку ошибки/адаптивное уточнение, а не автоматически proof-grade enclosure интеграла. [![img](https://www.google.com/s2/favicons?domain=https://mpmath.org&sz=128)mpmath.org+1](https://mpmath.org/doc/current/contexts.html?utm_source=chatgpt.com)

Поэтому минимальный достаточный прибор:
$$
\boxed{
\text{interval values of the exact mode}
+
\text{deterministic subdivision}
+
\text{rigorous cellwise integral enclosure}.
}
$$
Не нужен второй quadrature algorithm, если первый уже возвращает доказанный интервал.

------

# Точная цель G3

Для каждой моды $j\in\{0,4\}$ сравниваем:
$$
A_j(y)
=
\frac{2\sqrt\lambda}{N_j}
\int_0^1
\varphi_j(t)\cos(2\pi\lambda yt)\,dt
$$
с global-continuation backend:
$$
B_j(y)
=
\frac{\mu_j}{\sqrt\lambda N_j}
\Phi_j^{\rm global}(y/\lambda).
$$
На каждой внешней точке строятся интервалы:
$$
A_j(y)\in I_A,
\qquad
B_j(y)\in I_B,
$$
и непосредственно:
$$
A_j(y)-B_j(y)\in I_\Delta:=I_A-I_B.
$$

## Минимальный green



```
0 ∈ I_delta
diam(I_delta) ≤ tau_G3
interval width shrinks under precision/subdivision refinement
all planted failures remain visible
```

Здесь $\tau_{G3}$ надо выбрать **до результата** и привязать не к относительной ошибке почти нулевого числа, а к будущему Fejér/residual-бюджету.

Для dual sum
$$
D_N(u)
=
u^{-1/2}
\sum_{k=1}^N
w_{k,N}\widehat h(k/u)
$$
достаточный propagated budget:
$$
\boxed{
u^{-1/2}
\sum_{k=1}^N
w_{k,N}\,\operatorname{rad}I_k
\le
\tau_{\rm dual}.
}
$$
То есть не требуется обязательно определить 700-значное ненулевое leakage-значение. Достаточно доказать, что его неопределённость слишком мала, чтобы испортить residual.

------

# Два разных допустимых green-вердикта

## 1. Ненулевая утечка сертифицирована

Если
$$
0\notin I_A
$$
хотя бы в одной внешней точке, получаем:



```
G3_EXTERNAL_LEAKAGE_NONZERO_CERT
```

Это лучший результат: он одновременно убивает zero-extension plant.

## 2. Утечка не отделена от нуля, но строго мала

Если
$$
0\in I_A,
\qquad
\sup_{z\in I_A}|z|\le\tau_{\rm leak},
$$
и propagated Fejér budget проходит, получаем:



```
G3_EXTERNAL_LEAKAGE_SMALL_BOUND
```

Для residual этого достаточно. Ненулевость leakage сама по себе не является потребителем.

------

# Как делить интервал

Не отдавать весь $[0,1]$ одному interval-вызову.

Разбить в нулях осциллирующего множителя:
$$
\cos(2\pi\lambda yt)=0
\quad\Longleftrightarrow\quad
t_r=\frac{2r+1}{4\lambda y}.
$$
То есть partition:
$$
\{0,1\}
\cup
\left\{
\frac{2r+1}{4\lambda y}
:
0<t_r<1
\right\}.
$$
На каждом cell косинус имеет фиксированный знак. Для крайнего случая
$$
y=5\lambda,\qquad \lambda^2=m=257
$$
это лишь порядка $10m\approx2570$ первичных cells — нормальный объём.

Самый простой гарантированный интегратор на cell $J=[a,b]$:
$$
\int_J f(t)\,dt
\in
(b-a)\,f(J),
$$
где $f(J)$ — interval range. Это грубо, но rigorously safe. Cells рекурсивно делятся, пока суммарная ширина enclosure не проходит $\tau_{G3}$.

Interval-Simpson или interval-Chebyshev можно добавить потом как ускорение. Для минимального gate они не нужны.

------

# Precision ladder

Начальную точность привязать к реально измеренной conditioning scale:
$$
\boxed{
p_0
=
\max\left(
100,\,
\left\lceil-\log_{10}a_j\right\rceil+80
\right),
}
$$
где
$$
a_j=\frac1{\sqrt\lambda N_j}
$$
— same-mode L² scale.

Затем:



```
p0
p0 + 100
p0 + 200
```

или удвоение, если interval width не сокращается.

Для $m=257$ report показывает scale порядка $10^{-699}$, поэтому 80–100 digits заведомо недостаточно; нужен порядок 800 digits или выше.

------

# STRONGEST ATTACK

Самая важная ловушка:

> Interval quadrature exact only if the supplied integrand itself is enclosed.

Если `phi_j(t)` приходит из обычного floating ODE solver как одно приближённое число, а затем это число оборачивается в `iv.mpf`, вы сертифицируете интеграл **приближённой функции**, не точной prolate-моды.

Поэтому хотя бы одно должно быть interval-safe:

1. interval enclosure Legendre coefficients + interval evaluation;
2. interval ODE enclosure с interval initial/eigenvalue data;
3. rigorous remainder bound между используемым numerical mode и exact mode.

Это обязательный source-lock.

Также не присваивать:
$$
\mu_j:=1.
$$
020 показывает лишь, что три no-fit пути дают число, неотличимое от $1$ на текущем floor. Нужно нести interval
$$
\mu_j=\lambda J_j/c_j
$$
и при желании пересекать его с теоретическим ограничением $0<\mu_j\le1$, но не заменять единицей.

------

# Когда нужен вариант (b)

Переключаться на oscillatory Filon/Levin/Clenshaw–Curtis scheme только при статусе:



```
G3_INTERVAL_DEPENDENCY_BLOWUP
```

то есть когда:

- precision растёт;
- cells дробятся;
- interval width не сокращается из-за dependency explosion.

Тогда (b) должен иметь **явный remainder bound**. Просто более стабильное point estimate снова будет только диагностикой.

------

# Почему (c) не надо повторять

Две обычные квадратуры полезны как planted sanity check, но не решают arithmetic-floor problem. В 020 они уже дали именно такой результат: обе схемы оказались на уровне $10^{-15}$, поэтому нельзя было отличить истинную утечку от общего численного пола.
$$
\boxed{
\text{agreement of two zeros is not a leakage certificate.}
}
$$

------

# CODEX DIRECTIVE



```
PATCH:
020R_G3_INTERVAL_EXTERNAL_FOURIER_CERT

PRIMARY METHOD:
certified interval enclosure with phase-zero subdivision

DO NOT:
- rerun two float quadratures as the primary judge;
- use mp.quad(error=True) as a rigorous error bound;
- wrap float ODE values into zero-width intervals;
- force mu = 1;
- form Fejer residual before G3 passes.

For each m in {13,53,257},
mode in {h0,h4},
y in {lambda*(1+1e-8), 2*lambda, 5*lambda}:

1. Build interval-enclosed exact canonical mode data:
   N_j, J_j, c_j, mu_j, phi_j(t).

2. Partition [0,1] at:
     t_r = (2r+1)/(4*lambda*y).

3. Enclose:
     A_j(y)
       = 2*sqrt(lambda)/N_j
         * integral_0^1 phi_j(t) cos(2*pi*lambda*y*t) dt.

4. Enclose:
     B_j(y)
       = mu_j/(sqrt(lambda)*N_j)
         * Phi_global_j(y/lambda).

5. Output:
     IA, IB, IDelta=IA-IB,
     diameters,
     contains_zero flags,
     propagated dual error budget.

6. Precision ladder:
     p0 = max(100, ceil(-log10(scale_L2))+80)
     p0, p0+100, p0+200.

7. Plants:
   - zero-extension backend;
   - mu4 sign flip;
   - wrong dual half-weight;
   - omitted origin counterterm remains reserved for residual stage.

RETURN EXACTLY ONE:

G3_EXTERNAL_LEAKAGE_NONZERO_CERT

G3_EXTERNAL_LEAKAGE_SMALL_BOUND

GLOBAL_PROLATE_CONTINUATION_MISMATCH

G3_INTERVAL_DEPENDENCY_BLOWUP

G3_MODE_INPUT_NOT_INTERVAL_CERTIFIED
```

# FINAL PROPOSAL

$$
\boxed{
\textbf{Минимально достаточно: (a), но в certified interval форме.}
}
$$

Не ordinary high-precision `mpmath`, а:



```
intervalized exact mode
+ phase-aligned subdivision
+ rigorous enclosure
+ downstream error budget.
```

Вариант (b) — только fallback. Вариант (c) уже исчерпан текущим `FLOOR_UNRESOLVED`.

# META CLOSEOUT

**Что стало меньше?**

G3 больше не требует «увидеть» микроскопическую утечку. Достаточно либо отделить её от нуля, либо доказать, что её абсолютный вклад ниже Fejér/residual budget.

**Что убито?**

- ещё один float64 crosscheck;
- relative-error gate около нуля;
- `mu := 1`;
- interval arithmetic поверх несертифицированной ODE-функции.

**Текущий smallest named gap:**
$$
\boxed{\texttt{G3ExactModeIntervalEnclosure}.}
$$
После него cellwise integration — уже механическая часть.