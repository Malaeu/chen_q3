Worked for 18m 37s

# STATUS



```
ANCHOR_BRIDGE_PROVED
ANCHOR_SOURCE_RATIO_OPEN
S1_SOURCE_MOMENT_OPEN
PROJECTED_DENSITY_SIGN_OPEN_DIAGNOSTIC
```

Я проверил сам `D0AnchorFloor.lean`. Мост чистый:
$$
V_0\in E_{m,N}
\Rightarrow
\langle V_0,P_{m,N}g_m\rangle=\langle V_0,g_m\rangle,
$$
после чего точная Stage-3-нормировка даёт coefficient floor, `rawFplus(0)` floor, ненулевую проекцию и `CentralIndex`. Никакой дополнительной фазы или скаляра в `hbind` нет. Проверка прошла без `sorry`/`admit`; профиль аксиом стандартный: `propext`, `Classical.choice`, `Quot.sound`. 006_anchor_floor.answer

Точное уточнение статуса: **машиной доказан anchor receiver**. Конкретный uniform floor для канонического пути закроется после source-оценки. Но source-задачу теперь можно сделать слабее, чем «отдельно нижняя масса + отдельно верхняя норма».

------

# ГЛАВНОЕ СЖАТИЕ: НЕ НУЖНЫ ДВЕ ОТДЕЛЬНЫЕ КОНСТАНТЫ

Положим
$$
g_m:=gTrial_m,
$$
Для точного проектированного объекта:
$$
\left|F^+_{m,N}(0)\right|
=
\frac{M_m}{\|P_{m,N}g_m\|_2}.
$$
Так как $P_{m,N}$ — ортогональная проекция,
$$
\|P_{m,N}g_m\|_2\le N_m.
$$
Следовательно,
$$
\boxed{
\left|F^+_{m,N}(0)\right|
\ge
\frac{M_m}{N_m}.
}
$$
Поэтому слабейшая аналитическая anchor-лемма — не пара
$$
M_m\ge a,
\qquad
N_m\le C,
$$
а одно scale-invariant неравенство:
$$
\boxed{
M_m\ge \delta N_m>0.
}
$$
То есть настоящий вычисляющий объект:
$$
\boxed{
\rho_m
:=
\frac{
\left|\int_{I_m}g_m(u)\,du/u\right|
}{
\|g_m\|_2
}.
}
$$
Достаточно доказать
$$
\inf_m\rho_m>0.
$$
Это слабее прежнего пакета и не требует контролировать абсолютный масштаб $g_m$.

------

# ЧТО ТАКОЕ ПЛАТО $c\approx0.8785$

Точное finite-$(m,N)$ значение есть
$$
\mathfrak c_{m,N}
:=
\frac{M_m}{\|P_{m,N}g_m\|_2}
=
|F^+_{m,N}(0)|.
$$
Если при фиксированном $m$
$$
P_{m,N}g_m\longrightarrow g_m
\quad\text{в }L^2,
$$
то
$$
\mathfrak c_{m,N}
\longrightarrow
\frac{M_m}{N_m}
=
\rho_m.
$$
Поэтому наиболее естественная структурная идентификация плато:
$$
\boxed{
c
=
\lim_m
\frac{\|g_m\|_1}{\|g_m\|_2}
}
$$
после глобального выравнивания знака, при существовании предела.

Это не выглядит пока как стандартная именованная константа. Это **limiting $L^1/L^2$-ratio**, то есть мера эффективной ширины источника.

Если далее найдётся точное представление
$$
w_m:=\omega_m g_m=|A_m|^2\ge0,
\qquad |\omega_m|=1,
$$
то
$$
\boxed{
c
=
\lim_m
\frac{\|A_m\|_2^2}{\|A_m\|_4^2}.
}
$$
Это inverse-participation-type ratio. Именно его надо пытаться вычислить в замкнутой форме, а не подгонять $0.8785$ к случайным комбинациям $\pi$ и $\Gamma$.

------

# ANCHOR И S1 ТЕПЕРЬ ИМЕЮТ ОДИН ЗНАМЕНАТЕЛЬ

Перейдём в логарифмическую координату
$$
t=\log u,
\qquad
t\in[-L_m/2,L_m/2].
$$
Пусть $G_m(t)$ — источник $g_m$ в этой координате. Для $0\le\sigma<1/2$ определим
$$
T_m(\sigma)
:=
\int
|G_m(t)|e^{\sigma|t|}\,dt.
$$
Для проектированного объекта после сокращения общей нормировки:
$$
A_{m,N}(\sigma)
=
\frac{
\int
|P_{m,N}G_m(t)|e^{\sigma|t|}\,dt
}{
M_m
}.
$$
Разложение:
$$
P_{m,N}G_m
=
G_m+(P_{m,N}-I)G_m
$$
даёт
$$
\boxed{
A_{m,N}(\sigma)
\le
\frac{T_m(\sigma)}{M_m}
+
\frac{
\int |(P_{m,N}-I)G_m(t)|e^{\sigma|t|}\,dt
}{
M_m
}.
}
$$
То есть
$$
\boxed{
A_{m,N}(\sigma)
\le
A_m^\circ(\sigma)+\beta_{m,N}(\sigma).
}
$$
Где:
$$
A_m^\circ(\sigma)
:=
\frac{T_m(\sigma)}{M_m}
$$
— непроецированный source ratio;
$$
\beta_{m,N}(\sigma)
$$
— уже измеренная протечка.

Ваш результат
$$
\beta\le5.6\cdot10^{-4}
$$
и N-независимость до десяти знаков подтверждают правильность именно этой декомпозиции. Но theorem-facing остаток теперь только:
$$
\boxed{
\forall\sigma<\frac12,\qquad
\sup_m A_m^\circ(\sigma)<\infty.
}
$$

------

# ЕСЛИ ЗНАКОПОСТОЯННОСТЬ ТОЧНА

Предположим, что из цепочки $E^\star$ получается точная глобальная фаза
$$
\omega_m\in\mathbb C,
\qquad |\omega_m|=1,
$$
такая, что
$$
w_m(t):=\omega_mG_m(t)\ge0
\quad\text{почти всюду}.
$$
Тогда:
$$
M_m=\|w_m\|_1,
\qquad
N_m=\|w_m\|_2,
$$
и весь источник превращается в положительную меру
$$
d\mu_m(t)
=
\frac{w_m(t)\,dt}{\|w_m\|_1}.
$$
Тогда два оставшихся условия имеют прозрачный вид:

### Anchor

$$
\boxed{
\frac{\|w_m\|_1}{\|w_m\|_2}\ge\delta.
}
$$

Это anti-concentration inequality.

### S1

$$
\boxed{
\int e^{\sigma|t|}\,d\mu_m(t)
\le A_\sigma,
\qquad
\sigma<\frac12.
}
$$

Это uniform exponential tightness.

Следовательно, весь аналитический фронт `ANCHOR + S1` становится:
$$
\boxed{
\text{anti-concentration}
+
\text{uniform exponential moments}.
}
$$
Не две независимые теории.

------

# ЕСЛИ $E^\star$ ДАЁТ КВАДРАТ

Самый сильный вариант:
$$
\boxed{
w_m(t)=|A_m(t)|^2.
}
$$
Тогда:
$$
M_m=\|A_m\|_2^2,
$$
То есть требуемый пакет сжимается до:
$$
\boxed{
\frac{\|A_m\|_2^2}{\|A_m\|_4^2}\ge\delta,
}
$$
Это лучший возможный computing object. Не надо раскрывать квадрат нормы $E^\star$-суммы в огромную двойную сумму, если amplitude $A_m$ доступна напрямую.

------

# ЕЩЁ БОЛЕЕ ДЕШЁВАЯ НОРМОВАЯ ОЦЕНКА

Даже без точной $L^4$-формулы:
$$
\|w_m\|_2^2
\le
\|w_m\|_\infty\|w_m\|_1.
$$
Поэтому
$$
\frac{\|w_m\|_1}{\|w_m\|_2}
\ge
\sqrt{
\frac{\|w_m\|_1}{\|w_m\|_\infty}
}.
$$
Достаточно доказать:
$$
\|w_m\|_1\ge m_0>0,
\qquad
\|w_m\|_\infty\le B_0<\infty.
$$
Тогда
$$
\boxed{
\delta=\sqrt{\frac{m_0}{B_0}}.
}
$$
Это потенциально дешевле, чем вычислять точную $L^2$-норму `gTrial`.

------

# MELLIN-МАРШРУТ ДЛЯ $A_\sigma$

В multiplicative coordinate положим
$$
\mathcal M_m(s)
:=
\int_{I_m}
w_m(u)u^s\,\frac{du}{u}.
$$
Поскольку
$$
e^{\sigma|\log u|}
=
\max(u^\sigma,u^{-\sigma})
\le
u^\sigma+u^{-\sigma},
$$
получаем
$$
\boxed{
A_m^\circ(\sigma)
\le
\frac{
\mathcal M_m(\sigma)+\mathcal M_m(-\sigma)
}{
\mathcal M_m(0)
}.
}
$$
Значит из $E^\star$-цепочки нужны закрытые формы только для трёх Mellin-значений:
$$
\boxed{
\mathcal M_m(0),\qquad
\mathcal M_m(\sigma),\qquad
\mathcal M_m(-\sigma).
}
$$
Если $w_m$ чётна в log-coordinate, numerator упрощается до cosh-момента.

Это предпочтительнее generic weighted-$L^1$ оценки: здесь используется точная структура $E^\star$.

------

# STRONGEST ATTACK

Сейчас нельзя ещё писать:



```
q ≥ 0 по построению.
```

Проба относится к **projected normalized density**
$$
q_{m,N},
$$
а anchor source — к **unprojected**
$$
g_m.
$$
Это разные объекты:
$$
g_m
\longrightarrow
P_{m,N}g_m
\longrightarrow
\frac{P_{m,N}g_m}{\|P_{m,N}g_m\|}
\longrightarrow
q_{m,N}.
$$
Обычная Fourier-проекция не сохраняет pointwise positivity. Поэтому возможны два сценария:



```
A. Точная autocorrelation identity существует для q_{m,N}.
   Тогда projected sign theorem жив.

B. Sign точен только для unprojected g_m.
   Малые отрицательные значения q_{m,N} — настоящий projection undershoot.
```

Текущий Lean-пакет прямо не использует и не доказывает фазу или знак; численная positivity-таблица помечена как diagnostic. 006_anchor_floor.answer

Поэтому mpmath должен решить только инструментальный вопрос:



```
Уходят ли отрицательные aligned values при росте precision?
```

Если они стабилизируются около ненулевого отрицательного значения, получаем:



```
PROJECTED_SIGN_KILLED
```

Но маршрут не падает. Repair:



```
unprojected sign
+ exact central-mode preservation
+ certified projection leakage β
→ S1.
```

Это уже достаточная схема.

Самый сильный algebraic judge — не сетка, а coefficient identity:
$$
\boxed{
-(-1)^nc_n
=
\sum_r a_{r+n}\overline{a_r}.
}
$$
Она немедленно дала бы
$$
-q_{m,N}(t)
=
\left|
\sum_r a_re^{2\pi irt/L_m}
\right|^2.
$$
Если такой identity нет в source construction, слово «Фейер» пока остаётся гипотезой.

------

# FINAL PROPOSAL

Замораживаем единый аналитический target:

## `EStarRelativeSourcePackage`

Для каждого path-index $m$ доказать:
$$
0<M_m,
$$
с одной $\delta>0$, и для каждого $\sigma<1/2$:
$$
\boxed{
T_m(\sigma)\le A_\sigma M_m
}
$$
с $A_\sigma<\infty$, не зависящим от $m$.

После этого:
$$
\text{ratio anchor theorem}
\Rightarrow
|F^+_{m,N}(0)|\ge\delta,
$$
и
$$
A_m^\circ(\sigma)+\beta_{m,N}(\sigma)
\Rightarrow
S1\text{-strip}.
$$
То есть один source package закрывает оба фронта.

------

# CODEX DIRECTIVE

Один следующий локальный Lean-target:



```
D0AnchorFloorFromUnprojectedMassNormRatio
```

## Statement

Добавить corollary к уже доказанному theorem:

lean



```
theorem D0AnchorFloorFromUnprojectedMassNormRatio
    (D : CoefficientFamily)
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star : ...)
    (hbind : ...)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hmass_pos :
      0 <
        Real.sqrt (L_m i) *
          ‖inner ℂ (V_n_m i 0)
            (gTrial_m i hTrial_m hE_star)‖)
    (hratio :
      δ * ‖gTrial_m i hTrial_m hE_star‖
        ≤
      Real.sqrt (L_m i) *
        ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star)‖) :
    gTrial_m_N i hTrial_m hE_star ≠ 0 ∧
      (∃ ci : CentralIndex D, ci.1 = i) ∧
      δ ≤ Real.sqrt (L_m i) * ‖D.kTrial i 0‖ ∧
      δ ≤ ‖rawFplus D i 0‖
```

## Route

Set
$$
C:=\|g_m\|,
\qquad
a:=\delta\|g_m\|.
$$
From `hmass_pos`, infer $g_m\neq0$, hence $C>0$ and $a>0$. Apply

lean



```
D0AnchorFloorFromUnprojectedCentralMass
```

with:



```
hbound = le_rfl
hmass  = hratio
```

then simplify:
$$
\frac{\delta\|g_m\|}{\|g_m\|}=\delta.
$$

## Forbidden



```
no new axiom;
no separate constants a,C in the final consumer;
no numerical plateau;
no sign assumption;
no projection lower bound;
no theorem weakening.
```

## Validation

Bash



```
lake env lean Q3/Proofs/RouteB/D0AnchorFloor.lean
lake build
#print axioms D0AnchorFloorFromUnprojectedMassNormRatio
```

## Success code



```
ANCHOR_RATIO_RECEIVER_PROVED
```

После этого бумажный фронт окончательно называется:
$$
\boxed{
\texttt{EStarRelativeSourcePackage}
}
$$
а не двумя отдельными «mass lower» и «norm upper» задачами.

------

# META CLOSEOUT

**Что стало меньше?**

Две source-оценки для anchor заменены одной:
$$
\boxed{
\frac{|\int g_m\,du/u|}{\|g_m\|_2}\ge\delta.
}
$$
ANCHOR и S1 используют одну и ту же central mass.

**Что убито?**

- необходимость отдельно контролировать абсолютный масштаб $g_m$;
- необходимость exact $L^2$-формулы, если доступны mass + $L^\infty$;
- перенос численной знакопостоянности projected $q$ на unprojected $g$;
- трактовка mpmath как доказательства знака.

**Что нельзя повторять?**

Не доказывать более сильные absolute bounds, пока ratio bound решает потребитель.

**Текущий smallest named gap:**
$$
\boxed{
\texttt{EStarPhaseAlignedRepresentation}
}
$$
после него:
$$
\boxed{
\texttt{EStarRelativeAntiConcentration}
+
\texttt{EStarRelativeExponentialMoment}.
}
$$
**Следующий cheapest decisive test:**

Найти или опровергнуть exact autocorrelation/square identity в определении $E^\star hTrial_m$, отдельно для unprojected source и projected density.

**Progress class:** `REPRESENTATION_PROGRESS`.

**Route score:** $5/5$.

Lean-файл anchor bridge
 006_anchor_floor.answer.md  /Users/emalam/GitHub/chen_q3/docs/006_anchor_floor.answer.md