Worked for 13m 46s

# STATUS: FATAL для контракта v1



```
AUDIT_011_ACCEPTED_WITH_RENAMING

MUNTZ_MASS_FORK:
  Z — PROVED

POISSON_ORIGIN_FORK:
  P — COUNTERTERM REQUIRED

ARISTOTLE_CONTRACT_V1:
  FATAL
```

Точные коды:



```
HTRIAL_FORMULA_ACCEPTED
HTRIAL_MELLIN_MASS_ZERO_CONFIRMED
MEASURE_CONVENTION_MATCH
NO_ENDPOINT_TERM_IN_MASS_IDENTITY

H2_LABEL_COLLISION
SHA_LOCK_AUDIT_PARTIAL
CONCRETE_SPECIALIZATION_MISMATCH

ZETA_RAW_POLE_VALUE_MISMATCH
T4_FALSE_AS_STATED
T5_FALSE_AT_s_EQ_1_OVER_2
```

Текущий контракт Aristotle нельзя отправлять без исправления. В T4 проблема не в отсутствующем API: математическое утверждение ложно.

------

# 1. Аудит 011 по пяти пунктам

## 1.1 Формула $hTrial_m$

Формула заперта согласованно:
$$
h_\lambda
=
\frac{
I_{4,\lambda}h_{0,\lambda}
-
I_{0,\lambda}h_{4,\lambda}
}{
D_\lambda
},
\qquad
D_\lambda
=
\sqrt{I_{0,\lambda}^{2}+I_{4,\lambda}^{2}}.
$$
Она присутствует в:

- `D0_5_GROUND_AND_TRIAL_TYPES.md`, строки 55–69;
- `PEN_3_3_G04_OBJECT_DICTIONARY.md`, строки 79–104;
- 011, строки 92–137.

Первичный excerpt говорит только: это единственная с точностью до множителя линейная комбинация $h_0,h_4$ с нулевым интегралом. Нормированная строка выше затем вынуждена линейной алгеброй и ортонормированностью двух мод.
$$
\boxed{\texttt{HTRIAL\_FORMULA\_ACCEPTED}}
$$
Но Lean Stage 2 всё ещё принимает `hTrial_m` как свободный параметр. Формула source-locked, но конкретный prolate-конструктор ещё не материализован в Lean. Это корректно отмечено в 011. См. 011_concrete_htrial_source_lock.answer.md и Stage-2 Lean file.

------

## 1.2 Масса

Для $n=0,4$:
$$
h_{n,\lambda}(-v)=h_{n,\lambda}(v),
\qquad
\operatorname{supp}h_{n,\lambda}\subseteq[-\lambda,\lambda].
$$
Поэтому:
$$
\int_0^\infty h_{n,\lambda}(v)\,dv
=
\frac12
\int_{-\lambda}^{\lambda}h_{n,\lambda}(v)\,dv
=
\frac12I_{n,\lambda}.
$$
Подстановка в комбинацию даёт:
$$
\begin{aligned}
A_m
&:=
\int_0^\infty hTrial_m(v)\,dv\\
&=
\frac{
I_4(I_0/2)-I_0(I_4/2)
}{D_\lambda}\\
&=0.
\end{aligned}
$$
Это identity-grade proof: две точные интегральные строки, чётность и арифметика. Никаких сеток.
$$
\boxed{\texttt{HTRIAL\_MELLIN\_MASS\_ZERO\_CONFIRMED}}
$$

------

## 1.3 Мера и якобиан

Здесь несоответствия нет.

Источник пишет:
$$
\int_{\mathbb R}h_\lambda(x)\,dx=0.
$$
Müntz mass использует:
$$
A_m=\int_0^\infty h_\lambda(v)\,dv.
$$
Переменные $x$ и $v$ — одна и та же **аддитивная** координата. Замены $v=e^t$ здесь нет. Следовательно, якобиана нет.

Ровно чётность даёт:
$$
A_m
=
\frac12\int_{\mathbb R}h_\lambda(x)\,dx
=
0.
$$
Мера
$$
\frac{du}{u}
$$
появляется только после применения $E_\star$, на мультипликативной стороне `gTrial_m`.
$$
\boxed{\texttt{MEASURE\_CONVENTION\_MATCH}}
$$

------

## 1.4 Endpoint terms

Midpoint-значения в $\pm\lambda$ не меняют Lebesgue-интеграл: это конечное множество меры ноль.

Поэтому в mass identity нет потерянного endpoint term:
$$
\boxed{\texttt{NO\_ENDPOINT\_TERM\_IN\_MASS\_IDENTITY}}.
$$
Но midpoint half-weight остаётся обязательным в:

- pointwise $E_\star(h)(u)$;
- comb teeth $u=\lambda/n$;
- Poisson identity;
- boundary split.

То есть:



```
mass integral:
  endpoint-insensitive

pointwise E_star:
  endpoint-sensitive
```

------

## 1.5 Критический semantic collision: `H2_ZERO`

011 пишет:



```
H2_ZERO_CONFIRMED
H2-ZERO, not H2-POLE
```

Но authoritative dictionary использует `H2-ZERO` для другого утверждения:
$$
h_\lambda(0)=0.
$$
И он доказывает обратное:
$$
h_\lambda(0)
=
\frac{
(\chi_2-\chi_0)
h_{0,\lambda}(0)h_{4,\lambda}(0)
}{D_\lambda}
<0.
$$
Следовательно:



```
H2-INTEGRAL-ZERO:   PASS
H2-ZERO:            FAIL
H2-POLE/CORRECTION: SELECTED
```

Это не косметическое переименование. Если сохранить один код, следующий агент может ошибочно удалить origin-Poisson counterterm
$$
-\frac12u^{1/2}h_\lambda(0).
$$
Правильное разделение:



```
MUNTZ_MASS_ZERO:
  ∫₀∞ hλ(v)dv = 0

POISSON_ORIGIN_ZERO:
  hλ(0) = 0        — FALSE
```

См. строки 235–285 в PEN_3_3_G04_OBJECT_DICTIONARY.md.

------

## 1.6 SHA-аудит

Совпали заявленные SHA для:



```
D0_5_GROUND_AND_TRIAL_TYPES.md
PEN_3_3_G04_OBJECT_DICTIONARY.md
D0KTrialStage2.lean
EStarWindowedMellinCrosswalk.lean  — относительно отчёта 012
```

Но архив содержит только excerpt, а не полный `fulltext.md`, и не содержит указанные в 011:



```
D0KTrialStage3.lean
PROSHKA_MELLIN_CROSSWALK_2026-07-27.md
```

Поэтому все шесть immutable locks из ACTIONS LOG независимо перепроверить по этому архиву нельзя.
$$
\boxed{\texttt{SHA\_LOCK\_AUDIT\_PARTIAL}}
$$
Для формулы массы это не мешает: необходимые dictionary/D0.5-файлы и excerpt присутствуют.

------

# 2. Предварительный аудит T1–T5

Исходный контракт требует T4 для сырой функции
$$
s\longmapsto
\zeta\!\left(s+\frac12\right)
M_h\!\left(s+\frac12\right)
$$
на всём полупространстве
$$
\Re s>-\frac12,
$$
включая $s=1/2$, а T5 требует сырого равенства также в этой точке. ARISTOTLE_TASK_EStarMuntzContin…

| Узел | Вердикт                                                      |
| ---- | ------------------------------------------------------------ |
| T1   | **VIABLE**                                                   |
| T2   | **VIABLE для abstract class; нужен boundary repair для $h_\lambda$** |
| T3   | **VIABLE**                                                   |
| T4   | **FALSE AS STATED**                                          |
| T5   | **FALSE AT $s=1/2$**                                         |
| PL   | **VIABLE**                                                   |



------

## T1 — жив

Если
$$
u>b,
$$
то для каждого $n\ge1$:
$$
nu\ge u>b,
$$
значит $h(nu)=0$, и
$$
E_\star h(u)=0.
$$
Правый хвост поддержан на компактном интервале, отделённом от нуля, поэтому holomorphy по параметру $s$ стандартна.

------

## T2 — математика правильная, но класс v1 не тот

Для глобально Lipschitz $h$, поддержанной в $[a,b]$, zero-mass действительно даёт:
$$
\sup_{0<u<1}
\left\|
\sum_{n\ge1}h(nu)
\right\|<\infty.
$$
Риманова сумма:
$$
u\sum_{n\ge1}h(nu)
$$
отличается от $\int h=0$ на $O(u)$; деление на $u$ даёт $O(1)$.

Но конкретная $h_\lambda$:

- поддержана в $[0,\lambda]$ на положительной половине, а не вдали от нуля;
- имеет $h_\lambda(0)\ne0$;
- midpoint zero-extension имеет скачок в $\lambda$;
- не является globally Lipschitz или `ContDiff ℝ 1`.

Поэтому setup v1 не специализируется на канонический source-объект.

Слабейший repair:



```
support in [0,b]
Lipschitz on [0,b), not at midpoint endpoint b
one explicit terminal-cell bound
```

или BV-версия.

------

## T3 — жив

Из T2:
$$
|E_\star h(u)|\le C\sqrt u.
$$
Следовательно integrand левого хвоста имеет порядок
$$
u^{\Re s-\frac12}.
$$
Он интегрируем около нуля именно при
$$
\Re s>-\frac12.
$$
Для производной появляется дополнительный $|\log u|$, который остаётся интегрируемым локально в том же открытом полупространстве.

------

# 3. Фатальный контрпример к T4

Возьмём треугольный bump
$$
\phi(t)=\max(1-4|t|,0)
$$
и положим
$$
h_0(v)
=
\phi\!\left(v-\frac54\right)
-
\phi\!\left(v-\frac94\right).
$$
Тогда $h_0$:

- глобально Lipschitz;
- компактно поддержана вдали от нуля;
- удовлетворяет всем регулярностным требованиям v1;
- имеет нулевую массу:

$$
M_{h_0}(1)
=
\int_0^\infty h_0(v)\,dv
=
0.
$$

Но:
$$
\begin{aligned}
M_{h_0}'(1)
&=
\int_0^\infty h_0(v)\log v\,dv\\
&=
\int_{-1/4}^{1/4}
\phi(t)
\left[
\log\!\left(t+\frac54\right)
-
\log\!\left(t+\frac94\right)
\right]dt\\
&<0.
\end{aligned}
$$
Последнее строго отрицательно, потому что второй логарифм в каждой внутренней точке больше первого.

Теперь используем residue:
$$
(w-1)\zeta(w)\longrightarrow1.
$$
Значит:
$$
\zeta(w)M_{h_0}(w)
=
\bigl((w-1)\zeta(w)\bigr)
\frac{M_{h_0}(w)}{w-1}
\longrightarrow
M_{h_0}'(1)\ne0.
$$
Но сырое pointwise-значение в $w=1$:
$$
\operatorname{riemannZeta}(1)\,M_{h_0}(1)
=
\operatorname{riemannZeta}(1)\cdot0
=
0.
$$
Следовательно сырая функция
$$
w\mapsto\operatorname{riemannZeta}(w)M_{h_0}(w)
$$
даже **не непрерывна** в $w=1$, не говоря о differentiability.

Mathlib действительно рассматривает `riemannZeta` как функцию с некоторым конечным convention-value в точке $1$, доказывает differentiability только вне $1$, а также содержит `riemannZeta_residue_one`. [![img](https://www.google.com/s2/favicons?domain=https://leanprover-community.github.io&sz=128)Lean Community+1](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html?utm_source=chatgpt.com)
$$
\boxed{\texttt{ZETA\_RAW\_POLE\_VALUE\_MISMATCH}}
$$
Это не `ZETA_POLE_API_GAP`. Контракт требует ложный theorem.

------

# 4. Почему T5 тоже ложна

Положим:
$$
w=s+\frac12.
$$
Полюсная точка $w=1$ соответствует:
$$
s=\frac12.
$$
`Gwin`, `Rminus`, `Rplus` после T1–T3 аналитичны в этой точке. Абсолютное identity на $\Re s>1/2$ поэтому продолжает **предел**
$$
M_h'(1),
$$
а не сырое значение
$$
\operatorname{riemannZeta}(1)M_h(1)=0.
$$
Значит T5 со старой правой частью в точке $s=1/2$ в общем случае ложно.

Identity-theorem API в Mathlib есть: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. Проблема не там. [![img](https://www.google.com/s2/favicons?domain=https://leanprover-community.github.io&sz=128)Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Uniqueness.html?utm_source=chatgpt.com)

------

# 5. Ещё два замечания к 012

В машинно доказанном absolute-region theorem параметр `hmass` фактически не используется:

lean



```
have hmass_locked := hmass
clear hmass_locked
```

после чего доказательство идёт только через Mellin split и absolute-region factorization. См. строки 561–588 в EStarWindowedMellinCrosswalk.lean.

Это нормально математически:



```
absolute-region factorization:
  zero mass не нужна

critical-strip continuation:
  zero mass load-bearing
```

Но theorem name `zeroMass_decomposition_abs` сильнее реального контракта.

Также plant 012 — индикатор $(0,1]$, а не Lipschitz bump. Он доказывает pole-window growth, но не является plant-ом T2. Новый треугольный PL всё ещё нужен.

------

# 6. Правильный ремонт T4–T5

Определить removable extension:
$$
\mathcal Z_h(w)
=
\begin{cases}
\zeta(w)M_h(w), & w\ne1,\\[1mm]
M_h'(1), & w=1.
\end{cases}
$$
В Lean:

lean



```
noncomputable def ZetaMellinReg (w : ℂ) : ℂ :=
  if w = 1 then deriv (Mellin h) 1
  else riemannZeta w * Mellin h w
```

Тогда доказывать:
$$
\mathcal Z_h
\quad\text{analytic on }\{\Re w>0\},
$$
и:
$$
G_{\rm win}(s)
=
\mathcal Z_h\!\left(s+\frac12\right)
-
R^-(s)-R^+(s)
$$
для всех
$$
\Re s>-\frac12.
$$
После этого отдельный raw-product corollary:
$$
s\ne\frac12
\Longrightarrow
G_{\rm win}(s)
=
\zeta\!\left(s+\frac12\right)
M_h\!\left(s+\frac12\right)
-R^-(s)-R^+(s).
$$

------

# STRONGEST ATTACK

Самое сильное reviewer objection теперь двойное:

1. **Pole value:** zero mass удаляет principal part, но не присваивает сырой Mathlib-функции правильное removable value.
2. **Wrong test class:** theorem для globally Lipschitz функции, поддержанной вдали от нуля, не является theorem для конкретного midpoint prolate packet.

Оба возражения фатальны для v1.

------

# FINAL PROPOSAL

Не отправлять Aristotle исходный task.

Я подготовил исправленную версию, где:

- mass fork остаётся Z;
- Poisson origin fork остаётся P;
- Mellin analytic domain — $\Re w>0$, а не entire;
- midpoint endpoint вынесен в terminal-cell budget;
- zeta product заменён на removable extension;
- добавлен контрпример, который обязан убить старую формулировку.

ARISTOTLE_TASK_EStarMuntzContinuation_v2_REPAIRED.md

PROSHKA_AUDIT_011_AND_MUNTZ_CONTRACT_2026-07-27.md

011_concrete_htrial_source_lock.answer.md

012_estar_windowed_mellin_crosswalk.answer.md

## CODEX / Aristotle directive



```
Do not execute EStarMuntzZeroMassContinuation_Standalone v1.

Reason:
T4 and T5 are false at the zeta pole because the raw pointwise product
riemannZeta(w) * Mellin(h)(w) does not carry its removable value at w=1.

Execute:
ARISTOTLE_TASK_EStarMuntzContinuation_v2_REPAIRED.md

First decisive target:
ZetaMellinReg analytic on Re(w)>0.

Forbidden:
Do not “solve” the pole by proving only punctured differentiability and then
silently claim the value at w=1.
```

# META CLOSEOUT

**Что стало меньше?**

Вместо неопределённого `ZETA_POLE_API_GAP` осталась точная задача:
$$
\boxed{
\texttt{ZetaMellinRegAnalytic}
}
$$
с заранее известным правильным значением в полюсе.

**Что убито?**

- T4 для сырого произведения;
- T5 в $s=1/2$;
- `Mellin h is entire` для конкретной $h_\lambda$;
- global Lipschitz source class;
- двусмысленный код `H2_ZERO_CONFIRMED`.

**Что заморожено?**
$$
\boxed{
\int_0^\infty h_\lambda(v)\,dv=0
}
$$
как точная mass identity.

**Следующий cheapest decisive test:**

Формализовать PL2. Он обязан опровергнуть любую попытку вернуть raw-product T4.

**Progress class:** `FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS`.

**Route score:** $5/5$. Масса принята; ложный pole contract уничтожен до того, как Aristotle начал доказывать неверный theorem.