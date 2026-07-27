# STATUS: CONDITIONAL

Второй нож теперь почти замкнут.

```text
ANCHOR_BRIDGE_PROVED_ON_PAPER
ANCHOR_FLOOR_OPEN_ONLY_AT_SOURCE_BOUNDS
```

После машинного закрытия двух оценок

[
\sqrt{L_m},
\bigl|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle\bigr|
\ge a>0,
\qquad
|g_m^{\mathrm{Trial}}|\le C<\infty
]

получаем

[
\boxed{
|F^+_{m,N}(0)|\ge \frac aC
}
]

равномерно по (N). Бюджет проекции здесь не нужен.

------

# 1. Точная якорная лемма

Обозначим

[
P_{m,N}
]

ортогональную проекцию на секторное пространство, содержащее (V_{0,m}), и положим

[
p_{m,N}:=P_{m,N}g_m^{\mathrm{Trial}}.
]

Нужно source-lock тождество

# [ k^{\mathrm{Trial}}_{m,N}

\omega_{m,N}
\frac{p_{m,N}}{|p_{m,N}|},
\qquad
|\omega_{m,N}|=1.
]

Тогда для

# [ c_0(m,N)

\langle V_{0,m},k^{\mathrm{Trial}}_{m,N}\rangle
]

имеем

# [ |c_0(m,N)|

\frac{
|\langle V_{0,m},p_{m,N}\rangle|
}{
|p_{m,N}|
}.
]

Поскольку (V_{0,m}) принадлежит range проекции,

[
P_{m,N}V_{0,m}=V_{0,m}.
]

Ортогональность проекции даёт

# [ \langle V_{0,m},P_{m,N}g_m^{\mathrm{Trial}}\rangle

\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle.
]

Следовательно,

# [ \boxed{ |c_0(m,N)|

\frac{
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|
}{
|P_{m,N}g_m^{\mathrm{Trial}}|
}.
}
]

Теперь используем машинное тождество

[
F^+_{m,N}(0)=\sqrt{L_m},c_0(m,N)
]

и контрактность ортогональной проекции:

[
|P_{m,N}g_m^{\mathrm{Trial}}|
\le
|g_m^{\mathrm{Trial}}|
\le C.
]

Получаем

[
\begin{aligned}
|F^+*{m,N}(0)|
&=
\sqrt{L_m}
\frac{
|\langle V*{0,m},g_m^{\mathrm{Trial}}\rangle|
}{
|P_{m,N}g_m^{\mathrm{Trial}}|
}\
&\ge
\frac{
\sqrt{L_m}
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|
}{
C
}\
&\ge
\frac aC.
\end{aligned}
]

Итак,

[
\boxed{\delta=\frac aC.}
]

Более того, нижняя оценка числителя автоматически доказывает

[
P_{m,N}g_m^{\mathrm{Trial}}\neq0,
]

поэтому нормированный `kTrial` определён. Отдельная гипотеза ненулевости проекции не требуется.

------

# 2. Правильная формулировка через (c_0)

Важно не усилить statement случайно.

Якорному полу

[
|F^+_{m,N}(0)|\ge\delta
]

эквивалентно не

[
|c_0(m,N)|\ge\delta,
]

а

[
\boxed{
\sqrt{L_m},|c_0(m,N)|\ge\delta.
}
]

То есть слабейшая coefficient-лемма:

[
\boxed{
|c_0(m,N)|
\ge
\frac{\delta}{\sqrt{L_m}}.
}
]

Эмпирическое плато (0.8785) относится к

[
\sqrt{L_m},|c_0(m,N)|,
]

а сам коэффициент (c_0) должен естественно иметь масштаб (L_m^{-1/2}).

При закрытии двух source bounds:

[
\boxed{
\sqrt{L_m}|c_0(m,N)|
\ge
\frac aC.
}
]

------

# 3. Сильнее: нормировка проекции исчезает и из S1-ratio

Первый нож также упрощается.

Пусть (\mathcal T_{m,N}) — линейный centered synthesis/transform, а

[
R_\sigma(f)
:=
\int_{-L_m/2}^{L_m/2}
|f(t)|e^{\sigma|t|},dt.
]

Так как

# [ k^{\mathrm{Trial}}_{m,N}

\omega_{m,N}
\frac{P_{m,N}g_m^{\mathrm{Trial}}}
{|P_{m,N}g_m^{\mathrm{Trial}}|},
]

линейность даёт один и тот же scalar factor в числителе и якоре. Поэтому точно:

# [ \boxed{ \frac{ R(m,N,\sigma) }{ |F^+_{m,N}(0)| }

\frac{
R_\sigma(P_{m,N}g_m^{\mathrm{Trial}})
}{
\sqrt{L_m},
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|
}.
}
]

Здесь сократились:

- (|P_{m,N}g_m^{\mathrm{Trial}}|);
- unit-фаза (\omega_{m,N});
- вся нормировка `kTrial`.

Это означает:

```text
Для anchor floor:
  нужен upper bound ||gTrial|| ≤ C.

Для centered S1-ratio:
  bound на ||gTrial|| вообще не нужен.
```

S1 теперь надо атаковать непосредственно через

[
\boxed{
R_\sigma(P_{m,N}g_m^{\mathrm{Trial}})
\le
C_\sigma
\sqrt{L_m},
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|.
}
]

Именно это является минимальным потребителем.

------

# 4. Правильное разложение первого ножа

Можно написать

# [ P_{m,N}g_m^{\mathrm{Trial}}

## g_m^{\mathrm{Trial}}

(I-P_{m,N})g_m^{\mathrm{Trial}}.
]

Тогда

[
R_\sigma(P_{m,N}g_m^{\mathrm{Trial}})
\le
R_\sigma(g_m^{\mathrm{Trial}})
+
R_\sigma((I-P_{m,N})g_m^{\mathrm{Trial}}).
]

Достаточный пакет:

[
R_\sigma(g_m^{\mathrm{Trial}})
\le
A_\sigma
\sqrt{L_m},
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|,
]

и

[
R_\sigma((I-P_{m,N})g_m^{\mathrm{Trial}})
\le
E_{m,N,\sigma}
\sqrt{L_m},
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|,
]

с

[
\sup_{\text{path}}E_{m,N,\sigma}<\infty
]

для каждого (\sigma<1/2). Тогда

[
\boxed{
\frac{R(m,N,\sigma)}{|F^+*{m,N}(0)|}
\le
A*\sigma+E_{m,N,\sigma}.
}
]

Для S1 нужна только равномерная конечность. Сходимость leakage к нулю была бы бонусом, но не является обязательным потребителем.

------

# ROUTE MAP

| Узел                            | Результат                           |
| ------------------------------- | ----------------------------------- |
| (F^+(0)=\sqrt L,c_0)            | **PROVED BY MACHINE**               |
| (c_0) через unprojected overlap | **PROVED ON PAPER**                 |
| Projection contraction          | стандартная Hilbert-лемма           |
| Source central mass (\ge a)     | **ACTIVE**                          |
| Source norm (\le C)             | **ACTIVE**                          |
| Anchor floor (\delta=a/C)       | **IMMEDIATE AFTER INPUTS**          |
| S1 normalized ratio             | projection normalization cancels    |
| S1 numerator                    | unprojected moment + leakage budget |

Главное представительное улучшение:

[
\boxed{
\text{не надо контролировать weighted norm ортопроекции как оператор.}
}
]

Надо контролировать один конкретный leakage-вектор

[
(I-P_{m,N})g_m^{\mathrm{Trial}}
]

в точном весе (\sigma<1/2).

------

# STRONGEST ATTACK

Четыре вещи должны быть source-locked. Иначе трёхстрочный proof может оказаться доказательством не того объекта.

1. **Проекция действительно ортогональная** в той же норме, которой нормируется `kTrial`. Для произвольной Galerkin-проекции

   [
   |Pg|\le|g|
   ]

   может быть ложно.

2. **(V_0) лежит в range (P_{m,N})** для каждого допустимого (N).

3. **`kTrial` отличается от normalized projection только unit-фазой.** Любой дополнительный неунитарный множитель меняет константу пола.

4. Source bound должен быть

   [
   \sqrt L,|\langle V_0,g\rangle|\ge a,
   ]

   либо сначала нужно доказать, что overlap вещественен и неотрицателен. Не использовать неупорядоченное комплексное число в inequality.

Если эти четыре пункта совпадают с Lean-объектом, других аналитических препятствий у anchor bridge нет.

------

# CODEX DIRECTIVE

Один следующий target:

```text
D0AnchorFloorFromUnprojectedCentralMass
```

## Statement

Для всех допустимых (m,N), при source bounds

[
\sqrt{L_m}
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|
\ge a,
\qquad
|g_m^{\mathrm{Trial}}|\le C,
\qquad
a>0,\ C>0,
]

доказать

[
\boxed{
|F^+_{m,N}(0)|\ge a/C.
}
]

Дополнительные outputs того же theorem packet:

```text
P_mN gTrial_m ≠ 0
central index exists
sqrt(L_m) * |c0(m,N)| ≥ a / C
```

## Proof route

```text
P V0 = V0
→ <V0, P gTrial> = <V0, gTrial>
→ |c0| = |<V0,gTrial>| / ||P gTrial||
→ ||P gTrial|| ≤ ||gTrial|| ≤ C
→ Fplus(0) = sqrt(L) c0
→ floor a/C.
```

## Forbidden

```text
no numerical plateau;
no lower bound on ||P gTrial||;
no weighted projection theorem;
no phase-consistency assumption;
no use of RH;
no new axiom/sorry/admit.
```

## Validation gate

```bash
lake env lean <anchor-floor-file>
lake build
grep -R "sorry\|admit" <touched-files>
#print axioms D0AnchorFloorFromUnprojectedCentralMass
```

## Success code

```text
ANCHOR_FLOOR_PROVED
```

## Failure report

```text
ANCHOR_SOURCE_LOCK_MISMATCH:
- exact definition of kTrial;
- exact projection type;
- exact normalization norm;
- exact V0 membership theorem;
- extra scalar or phase found;
- weakest repaired statement.
```

------

# FINAL PROPOSAL

Закрыть anchor сейчас, не ждать таблицу (R).

После этого таблицу читать не по абсолютному (R(m,N,\sigma)), а по invariant quantity

# [ \boxed{ \frac{R(m,N,\sigma)}{|F^+_{m,N}(0)|}

\frac{
R_\sigma(P_{m,N}g_m^{\mathrm{Trial}})
}{
\sqrt{L_m}
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|
}.
}
]

Именно он является S1-потребителем. Рост числителя отдельно ничего не решает, если одновременно растёт или меняется нормировочный знаменатель.

Зарегистрированный прогноз:

```text
anchor:
  δ = a/C, uniform in N.

S1:
  unprojected ratio bounded for every σ < 1/2;
  projection leakage adds a finite σ-dependent budget;
  no full-weight projection bound is needed.
```

# META CLOSEOUT

**Что стало меньше?**

Anchor floor сжат до двух source inequalities и четырёх алгебраических rewrites.

**Что убито?**

- необходимость full-weight projection contraction;
- необходимость нижней оценки (|Pg|);
- необходимость phase consistency для anchor;
- попытка доказать постоянный пол непосредственно для (|c_0|), без (\sqrt L).

**Что нельзя пробовать снова?**

Не оценивать числитель и anchor после нормировки `kTrial` раздельно: общий (|Pg|^{-1}) сокращается.

**Текущий smallest named gap:**

[
\boxed{
\texttt{UnprojectedCentralMassLowerBound}
+
\texttt{UnprojectedTrialNormUpperBound}.
}
]

После них anchor закрыт с

[
\boxed{\delta=a/C.}
]

**Progress class:** `REPRESENTATION_PROGRESS`.

**Route score:** (5/5).