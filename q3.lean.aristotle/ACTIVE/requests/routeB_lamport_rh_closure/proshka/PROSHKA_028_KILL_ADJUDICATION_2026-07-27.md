Worked for 7m 54s

# STATUS



```
028_KILL_CODE:
  REJECTED / DOWNGRADED

HONEST PRIMARY CODE:
  BAND_TAIL_DOMINATED_AT_K026

SECONDARY:
  REGISTERED_POSITIVITY_PREDICTION_FALSIFIED

DUAL_THETA_DOMINANCE:
  OPEN

J_SOURCE:
  SEMANTICALLY_GREEN

J_CHECKER:
  REDERIVATION_GAP

K_ESCALATION:
  AUTHORIZED

LEMMA_A_027:
  UNAFFECTED
```

Твой главный аудит верен: **028 доказал точное поражение выбранного достаточного сертификата при текущем $K$, но не контрпример к `DualThetaDominance`.**

------

# 1. Код `DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL` завышен

Обозначим точную сумму на полосе через
$$
S_r(z)=P_{r,K}(z)+R_{r,K}(z),
$$
где
$$
|R_{r,K}(z)|\le r\varepsilon_{\Psi,K},
$$
а рационализированный finite core удовлетворяет
$$
P_{r,K}(z)
\in
\bigl[
P^{\rm center}_{r,K}(z)-E_{\rm core},
P^{\rm center}_{r,K}(z)+E_{\rm core}
\bigr].
$$
Тогда есть два разных критерия.

## Критерий доказательства положительности

Чтобы доказать
$$
S_r(z)\ge0,
$$
достаточно:
$$
\boxed{
P^{\rm center}_{r,K}(z)
-E_{\rm core}
-r\varepsilon_{\Psi,K}
\ge0.
}
\tag{PASS}
$$
Именно этот sufficient theorem был целью 028:
$$
P_{r,K}\ge r\varepsilon_{\Psi,K}.
$$
Он не был заявлен как эквивалентность.

## Критерий настоящего убийства

Чтобы доказать
$$
S_r(z)<0
$$
и тем самым действительно убить `DualThetaDominance`, нужно:
$$
\boxed{
P^{\rm center}_{r,K}(z)
+E_{\rm core}
+r\varepsilon_{\Psi,K}
<0.
}
\tag{KILL}
$$
Но 028 проверил третье выражение:
$$
\boxed{
P^{\rm center}_{r,K}
+E_{\rm core}
-r\varepsilon_{\Psi,K}<0.
}
\tag{028}
$$
Генератор буквально строит

Python



```
upper_target = center + core_error - r * tail_upper
```

и сертифицирует отрицательность этого полинома.

Из `(028)` следует только:
$$
P^{\rm center}_{r,K}+E_{\rm core}
<
r\varepsilon_{\Psi,K}.
$$
То есть sufficient lower certificate `(PASS)` невозможен при текущем $K$. Из этого **не следует** `(KILL)`.

Это классическая ошибка converse:
$$
\neg(\text{достаточное условие})
\centernot\Rightarrow
\neg(\text{утверждение}).
$$

------

# 2. Точный арифметический аудит чисел 028

Здесь есть ещё одна важная поправка к твоему сообщению.

Числа
$$
-1.7061156407616692\cdot10^{-93},
$$
в таблице 028 — это максимумы Bernstein-коэффициентов **уже после вычитания**
$$
r\varepsilon_{\Psi,K}.
$$
Это не максимумы $P_{\rm center}+E_{\rm core}$. Отчёт описывает именно adjusted target.

Поэтому для полных полос получаем:

### $r=256$

$$
\max(P_{\rm center}+E_{\rm core})
\le
-1.7061156407616692\cdot10^{-93}
+
1.7075585134074942\cdot10^{-93}
$$

А безопасный upper bound на точную сумму:
$$
S_{256}
\le
P_{\rm center}+E_{\rm core}
+
256\varepsilon_\Psi
$$
даёт примерно
$$
\boxed{
S_{256}
\lesssim
1.7090013860533192\cdot10^{-93}.
}
$$

### $r=255$

Аналогично:
$$
\max(P_{\rm center}+E_{\rm core})
\le
\boxed{
1.2103552227474\cdot10^{-96},
}
$$
а
$$
\boxed{
S_{255}
\lesssim
1.7020987181872436\cdot10^{-93}.
}
$$
Поэтому приведённый тобой диапазон
$$
S\in[-3.4\cdot10^{-93},\,1.5\cdot10^{-96}]
$$
из опубликованного сертификата не следует. Для такого узкого верхнего конца потребовалась бы дополнительная **односторонняя** информация о знаке хвоста, которой 028 не доказывает.

На маленьком внутреннем интервале 028 действительно доказал:
$$
P_{\rm center}+E_{\rm core}
\le-10^{-97}.
$$
Но текущий tail allowance там порядка
$$
1.7\cdot10^{-93},
$$
то есть примерно на четыре порядка больше. Поэтому и этот witness пока не определяет знак точной суммы.

------

# 3. Что на самом деле проверил независимый checker

Checker математически корректно перепроверяет **именно** утверждение:
$$
P_{\rm center}+E_{\rm core}
-r\varepsilon_\Psi<0.
$$
Он заново строит adjusted polynomial и требует отрицательности его верхних Bernstein-коэффициентов.

Для interior witness он перепроверяет отрицательность только finite core:
$$
P_{\rm center}+E_{\rm core}<0.
$$
Он нигде не строит decisive expression
$$
P_{\rm center}+E_{\rm core}
+r\varepsilon_\Psi.
$$
Поэтому:



```
FINITE_CORE_THETA_CERT_CHECK_OK
```

означает:

> Сертификат точно доказывает записанное рациональное неравенство.

Он не означает:

> Записанное неравенство является контрпримером к DualThetaDominance.

Это **не arithmetic bug**, а semantic verdict bug.

------

# 4. Правильное понижение кода

Убираем:



```
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL
```

Заменяем на:



```
BAND_TAIL_DOMINATED_AT_K026
```

Расшифровка:



```
- current minimal-K sufficient lower certificate fails;
- finite core has a certified negative interior subinterval;
- the exact full-mode sum remains unresolved because the two-sided
  tail allowance dominates the negative core margin;
- DualThetaDominance is neither proved nor killed.
```

Дополнительный честный результат:



```
REGISTERED_POSITIVITY_PREDICTION_FALSIFIED
```

Мой прогноз, что обе приоритетные полосы сразу пройдут `(PASS)`, действительно опровергнут. Это принимаю без ремонта задним числом.

Но формулировка



```
CERT_ROUTE_DEAD
```

тоже пока слишком сильна. Умер только сертификат с **текущим минимальным cut $K$**. Та же exact finite-core route при большем $K$ ещё жива.

------

# 5. Аудит источника $J_0,J_4$

## Вердикт: системного сдвига из-за $J$ не найдено

028 не использует «core integral вместо full-mode integral» в опасном смысле.

### Что делает source

Для каждой моды строится Legendre expansion в raw gauge:
$$
a_0=1.
$$
Это зафиксировано непосредственно в конструкторе коэффициентов: recurrence начинается с `current = 1` при degree $0$, для обеих мод.

После этого `normalization_data` вычисляет:
$$
s_j
=
\frac1{\sqrt{\|{\rm finite\ core}\|_2^2+
\|{\rm tail}\|_2^2}},
$$
причём tail $L^2$-норма входит настоящим interval budget. Затем определяется
$$
\boxed{
J_j=2s_j.
}
$$
Почему это full-mode identity:

- коэффициент при $P_0$ равен $1$;

- для каждого $\ell\ge1$
  $$
  \int_{-1}^{1}P_\ell(t)\,dt=0;
  $$

- весь бесконечный tail состоит из Legendre-мод положительной степени;

- следовательно tail в $J_j$ вносит **точно ноль**, а не малую ошибку.

Поэтому для полной нормированной моды:
$$
\int_{-1}^{1}s_j\phi_j(t)\,dt
=
2s_j.
$$
Скрипт 027 явно фиксирует эту логику и выводит:
$$
\frac{s_j\phi_j}{J_j}
=
\frac{s_j\phi_j}{2s_j}
=
\frac{\phi_j}{2}.
$$
Отсюда exact normalized difference:
$$
\Psi
=
\frac{\phi_4}{J_4}
-
\frac{\phi_0}{J_0}
=
\frac{\phi_4-\phi_0}{2}.
$$
028 именно так строит:

Python



```
psi = (mode[4] - mode[0]) / 2
```

и отдельно вычисляет
$$
\varepsilon_\Psi
=
\frac{\varepsilon_4}{J_{4,\rm lower}}
+
\frac{\varepsilon_0}{J_{0,\rm lower}}.
$$
Итак:



```
J_CORE_VS_FULL_SHIFT:
  NOT FOUND
```

Твоё предположение было правильным первым подозреваемым, но оно не подтвердилось.

------

## Один реальный J-аудит gap всё же есть

Независимый checker не выводит $J_j$ заново из coefficient balls и finite-plus-tail normalization. Он читает сохранённые интервалы `positive_source_integrals` и `tail_epsilons`, проверяет только их знак и пересобирает отношение
$$
\varepsilon_{\rm upper}/J_{\rm lower}.
$$
То есть:



```
J_FORMULA:
  GREEN

J_INDEPENDENT_CHECKER_REDERIVATION:
  MISSING
```

Это не объясняет observed $10^{-93}$-баланс и не инвалидирует generator, потому что source hashes зафиксированы. Но перед следующим decisive verdict checker следует усилить:



```
coefficient balls
→ finite L2 interval
→ tail L2 interval
→ scale interval
→ J=2·scale
→ epsilon=scale·|a_K|
```

и только затем формировать $\varepsilon/J$.

------

# 6. $K$-эскалация авторизована

$$
\boxed{
\texttt{K\_ESCALATION\_AUTHORIZED}
}
$$

Это законный exact proof move, не sign-grid и не смена theorem-shape.

026 доказал ratio cone
$$
0<\rho_k\le\frac12
$$
после $K_0$, живой continued-fraction tail и finite-plus-tail normalization. Значит при углублении cut хвостовая allowance уменьшается геометрически; terminal condition $\rho=0$ по-прежнему не используется.

При текущем масштабе нужно уменьшить allowance примерно на $10^4$, чтобы она стала меньше interior core margin $10^{-97}$. Консервативная оценка
$$
\rho\le\frac12
$$
говорит, что около 15 дополнительных коэффициентов уже дают нужный порядок. Берём запас:
$$
\boxed{
\Delta K=20
}
$$
для обеих мод.

Это означает:
$$
K_0^{(0)}:437\longrightarrow457,
\qquad
N^{(0)}:874\longrightarrow914,
$$
Если первый проход не решает знак, разрешён ровно один второй cut:
$$
\boxed{\Delta K=40.}
$$
После этого — stop. Никакой новой бесконечной лестницы.

------

# 7. Новые decisive критерии

Для каждого $r\in\{255,256\}$ и каждого rational subinterval строить две envelope-функции:
$$
L_{r,K}
:=
P^{\rm center}_{r,K}
-E_{\rm core,K}
-r\varepsilon_{\Psi,K},
$$

## Настоящий PASS

Если exact Bernstein certificate даёт:
$$
\boxed{
L_{r,K}\ge0
}
$$
на обеих полных полосах и соответствующих tooth-values, то:



```
DUAL_THETA_DOMINANCE_PROVED_PRIORITY_BANDS
```

## Настоящий KILL

Если на некотором строгом rational interval:
$$
\boxed{
U_{r,K}<0,
}
$$
то только тогда:



```
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL
```

с точным отрицательным upper bound.

## Иначе



```
K_ESCALATION_INCONCLUSIVE
```

После $\Delta K=40$ это принудительно вызывает representation shift, а не ещё один cut.

------

# 8. Зарегистрированный прогноз

Записываю до нового результата:



```
PREDICTION:
  the negative minimal-K finite core is compensated by the omitted
  recessive tail;

  after ΔK=20:
    no true U<0 certificate appears;
    at least one of r=255,256 closes nonnegative, or both contract
    to an interval containing zero.

LIKELIEST FAILURE:
  exact sampling value is extremely close to zero at the lower endpoint,
  so even ΔK=40 remains inconclusive.
```

То есть я **не** прогнозирую настоящий kill на следующем cut.

------

# 9. Что делать при настоящем kill

Только если будет доказано
$$
U_{r,K}<0
$$
на открытом rational interval, sign-route умирает на клетке $m=257$.

Тогда включается заранее зарегистрированный repair:
$$
\boxed{
\texttt{EStarPositivePartMomentBudget}
}
$$
или эквивалентный direct consumer:
$$
\boxed{
\sup_m
\frac{
\int |E_\star h_\lambda(u)|
e^{\sigma|\log u|}\,du/u
}{
\left|\int E_\star h_\lambda(u)\,du/u\right|
}
<\infty.
}
$$
Exact interval mode позволяет сертифицировать positive-part leakage по клеткам, не требуя глобальной знакопостоянности.

Но **pivot сейчас преждевременен**. Сначала decisive $K$-эскалация.

------

# 10. Лемма A не затронута

$$
\boxed{
\texttt{HLAMBDA\_LAST\_POSITIVE\_ZERO\_LT\_ONE\_PROVED}
}
$$

остаётся в силе для
$$
m\in\{13,53,257\}.
$$
027 использовал:

- certified $\Theta_4$-barrier;
- exact finite Legendre cores;
- явный sup-tail allowance;
- Sturm–Wronskian transport на $[1,\lambda]$.

Он не использовал lower-half sampling inequality 028.

Поэтому:



```
LEMMA_A:
  UNCHANGED

SCOPE:
  FINITE_CELL {13,53,257}

COFINAL_FAMILY:
  NOT CLAIMED
```

------

# STRONGEST ATTACK

Даже успешный $\Delta K=20$ решит только две приоритетные полосы клетки $m=257$. Он не докажет:

- все остальные bands и teeth;
- клетки $m=13,53$;
- uniform statement по кофинальному пути.

И второй риск: новый checker обязан вывести $J$ и $\varepsilon$ из coefficient/tail data, а не доверять сохранённым интервалам. Иначе следующий `PASS` останется с audit defect, хотя текущая формула $J$ математически корректна.

------

# CODEX DIRECTIVE



```
TARGET:
029_DecisiveFiniteCoreThetaOrder_KEscalation

STATUS:
CHALLENGER / NOT_RH
exact interval/rational certificate
no sign grid

RETRACT:
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL from goal 028

REPLACE WITH:
BAND_TAIL_DOMINATED_AT_K026

INPUTS:
- exact Theta intervals from 026;
- live continued-fraction tail;
- exact coefficient balls;
- canonical Psi convention;
- bands r=256,255;
- witness interval from 028.

STEP 0 — strengthen checker:
Recompute from coefficient balls:
  finite_L2_sq
  tail_L2_sq interval
  scale
  J = 2*scale
  epsilon = scale*|last coefficient|
  epsilon_Psi

Do not trust stored J/epsilon intervals as primitive inputs.

STEP 1:
Increase coefficient cut by ΔK=20:
  degree 0: Ncut=914
  degree 4: Ncut=920

Use the same certified Theta intervals.
Use live recessive continued-fraction boundary.
Do not set terminal ratio to zero.

STEP 2:
Rebuild exact rational:
  Psi core
  E_core
  epsilon_Psi
  band polynomials

For r in {256,255}, construct:

  L = P_center - E_core - r*epsilon_Psi
  U = P_center + E_core + r*epsilon_Psi

Check:
- both full bands;
- all relevant teeth;
- old strict witness interval.

STEP 3:
If neither decisive, repeat exactly once with ΔK=40.
No third escalation.

RETURN EXACTLY ONE:

DUAL_THETA_DOMINANCE_PROVED_PRIORITY_BANDS
  iff L >= 0 on both full bands and teeth.

DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL
  iff U < 0 on a strict rational interval.

K_ESCALATION_INCONCLUSIVE
  otherwise.

FORBIDDEN:
- no inference from failure of L>=0 to U<0;
- no adjusted-target verdict mislabeled as lemma kill;
- no sign samples;
- no mu:=1;
- no coefficient centers as exact;
- no cofinal claim;
- no pivot before a true U<0 certificate.
```

# META CLOSEOUT

**Что стало меньше?**

Ложный «kill B» сжат до точного факта:
$$
\boxed{
\text{minimal-}K
\text{ sufficient certificate is tail-dominated.}
}
$$
**Что действительно убито?**

- мой registered prediction о немедленном PASS;
- текущий $K=K_0$ lower-certificate;
- трактовка checker PASS как counterexample к B.

**Что не пробовать?**

- не запускать pivot сейчас;
- не принимать отрицательность finite core за отрицательность full mode;
- не увеличивать precision при фиксированном $K$;
- не делать больше двух cut-эскалаций.

**Текущий smallest named gap:**
$$
\boxed{
\texttt{DecisiveFullSumEnvelope}_{r=255,256}.
}
$$
**Next cheapest decisive test:**
$$
\boxed{
\Delta K=20,\quad
L_{r,K}\text{ и }U_{r,K}
\text{ exact Bernstein}.
}
$$
**Progress class:** `FALSIFICATION_PROGRESS + REPRESENTATION_PROGRESS`.

**Route score:** $5/5$. Сертификат арифметически верен; исправлена только его логическая интерпретация.