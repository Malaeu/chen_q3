# `PO3-square.2` attack note — infinite-support square-tail injectivity

## Статус

Рабочая note открыта.

Это не доказательство и не новая theorem-level упаковка.
Это карта штурма для главной стены маршрута.

## Где этот узел в цепочке

См. также:

- [`h1_po3_route_ladder_2026_04_19.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_route_ladder_2026_04_19.md)

Там `PO3-square.2` отмечен как первый genuinely infinite-support injectivity
brick после локальной shell-механики и конечных редукций.

## Рабочая theorem-shape

После маршрута

- `PO3-rig.*`
- `PO3-tail.*`
- `PO3-cauchy.*`
- `PO3-square.1`

остаётся объект вида:

- even square-support receiver;
- vanishing on the square tail:
  `J_a(r^2) = 0` для всех достаточно больших `r`.

Нужно получить жёсткий вывод:

- либо receiver тривиален;
- либо surviving infinite-support branch невозможен в точной формулировке
  текущего маршрута.

## Почему это стена

Потому что здесь впервые одновременно:

1. поддержка бесконечная;
2. нет редукции к конечной матрице;
3. локальный witness уже недостаточен;
4. нужен глобальный uniqueness / injectivity argument.

То есть это не очередной shell-step, а главный математический риск ветки.

## Точный theorem-packet после square-to-Cauchy reduction

Ниже зафиксирован рабочий пакет, который сжимает square-tail form к
even symmetric Cauchy form.

### `PO3-square.2d0`  `[Exact reduction under convergence assumptions]`

Пусть

- `J(z)` задаётся Cauchy-type representation по квадратной поддержке
  `\Lambda = {x^2 : x ∈ X ⊂ (0,\infty)}`;
- сумма определена в достаточно сильном смысле, чтобы можно было подставлять
  `z = w^2` и перегруппировывать члены;
- определён transform-side receiver
  `\widetilde H(w) := J(w^2)`.

Тогда:

1. `\widetilde H` имеет exact even symmetric Cauchy form
   \[
   \widetilde H(w)
   =
   \sum_{x\in X}\frac{b_{x^2}}{2x}
   \left(\frac{1}{x-w}+\frac{1}{x+w}\right);
   \]
2. `\widetilde H(-w)=\widetilde H(w)`;
3. если
   \[
   J(r^2)=0 \qquad \forall r>N,
   \]
   то
   \[
   \widetilde H(r)=0 \qquad \forall r>N,
   \]
   и по чётности также `\widetilde H(-r)=0`.

Смысл:

- квадратный хвост редуцируется к integer-tail;
- стену больше не надо формулировать как “injectivity on squares”;
- она превращается в even symmetric Cauchy uniqueness on integers.

### `PO3-square.2d0-finite`  `[Finite-support kill]`

Если в `PO3-square.2d0` множество `X` конечно, то:

1. `\widetilde H` — рациональная функция с конечным числом полюсов;
2. бесконечно много хвостовых нулей на integers forcing
   `\widetilde H \equiv 0`;
3. значит все соответствующие coefficients `b_{x^2}` равны нулю.

Итог:

- finite-support branch стены уже убит полностью;
- после reduction живым остаётся только infinite-support случай.

### `PO3-square.2d1`  `[Live infinite-support target]`

После `PO3-square.2d0` и `PO3-square.2d0-finite` реальная стена принимает
точную форму:

пусть
\[
\widetilde H(w)
=
\sum_{x\in X}\frac{c_x}{x-w}
+
\sum_{x\in X}\frac{c_x}{x+w}
\]
есть even symmetric Cauchy receiver с бесконечной поддержкой, и
\[
\widetilde H(r)=0 \qquad \forall r>N.
\]

Нужно доказать:
\[
\widetilde H \equiv 0.
\]

Это и есть честная infinite-support injectivity wall после reduction.

Shell-status now:

- this target is now named explicitly in Lean by
  `po3_square2d1_target`;
- the reduction shell from square-tail zero plus evenness to that target is
  closed by
  `po3_square2d1_target_of_even_square_tail_zero`.

So the remaining live burden at `2d1` is no longer definitional; it is purely
the infinite-support uniqueness argument.

## Что уже реально закрыто этим пакетом

После принятия `PO3-square.2d0` пакет даёт три конкретных выигрыша:

1. square-tail ставится в более знакомую integer-tail форму;
2. finite-support case закрывается сразу;
3. живая цель переписывается в одну clean Cauchy uniqueness statement.

То есть саму стену этот пакет ещё не пробивает, но очень сильно очищает её
формулировку.

## Осторожность по формулировке

Для finite-support часть theorem честная без оговорок.

Для infinite-support часть reduction нужно явно хранить условия сходимости /
регулярности:

- где определён `J`;
- в каком смысле сходится Cauchy sum;
- можно ли безопасно переходить к `J(w^2)` и симметричной записи по `±x`.

Иначе `PO3-square.2d0` надо читать как theorem-target with assumptions, а не
как уже доказанный строгий statement.

### `PO3-square.2d0a`  `[Shell half closed]`

Чистая algebraic half-step теперь уже формализована в Lean:

- если `transformReceiver r = squareReceiver (r^2)` на `r ≥ 0`,
  то square-tail zero переходит в integer-tail zero;
- если дополнительно transform-side receiver чётный, то получаем и
  bilateral integer-tail zero на `±r`.

Это закрыто в
[`Q3/Proofs/HBridge_PO3_Shell.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/HBridge_PO3_Shell.lean)
леммами
`po3_transform_tail_zero_of_square_tail_zero`
и
`po3_bilateral_transform_tail_zero_of_even_square_tail_zero`.

То есть `2d0` больше не начинается с тумана:
его zero-transfer shell уже собран, и живой burden остаётся только на
analytic / infinite-support стороне.

## Штурм `2a` — finite-support approximation

Идея:

- сначала доказать максимально жёсткий finite-support analogue;
- затем аппроксимировать infinite-support object конечными truncation;
- контролировать предел так, чтобы zero-on-square-tail сохранялся достаточно
  сильно;
- вытянуть injectivity через устойчивость.

Плюс:

- использует уже знакомую finite machinery.

Риск:

- может развалиться на предельном переходе;
- нужно достаточно сильное пространство / норма / компактность.

## Штурм `2b` — Newton / divided differences

Идея:

- использовать квадратную Newton/divided-difference башню;
- переводить vanishing on `{r^2}` в каскад нулей у divided differences;
- пробовать форсировать зануление всех tail coefficients.

Плюс:

- максимально близко к уже собранному square-tail language.

Риск:

- бесконечная башня может потребовать сильной оценки роста,
  а не только формальной алгебры.

### `PO3-square.2b0`  `[Shell bridge closed]`

Первый Newton-side пакет теперь уже формализован в Lean:

- shifted square nodes заданы явно;
- sampled tail одного fixed receiver-а на этих узлах задан явно;
- one-step и iterated Newton/divided differences заданы как отдельные объекты;
- square-tail zero формально переводится в нулевую башню iterated divided
  differences.

То есть внутри `2b` больше не осталось definitional тумана.
Живой Newton-side burden теперь уже только в следующем шаге:
получить из этой нулевой башни настоящий uniqueness / contradiction theorem.

### `PO3-square.2b1`  `[Quotient-collapse shell closed]`

Следующий честный узкий шаг внутри square-route уже не про всю uniqueness-стену,
а про одну алгебраическую развилку:

- если после деления на общий square-tail divisor внутренняя цепочка
  `J_{a,k}` даёт разные normalized quotients, ordering-route ещё жив;
- если же normalized quotients всегда только скалярно кратны, эта дверь надо
  убить немедленно.

Точный текущий target:

- заморозить в Lean абстрактную лемму вида
  `G_k = - s_{k+1} G_{k+1}`
  из отношений
  `J_{k+1} = J_k / (z - s_{k+1})`
  и
  `E_k = (1 - z / s_{k+1}) E_{k+1}`;
- после этого у square-tail ordering mainline уже не останется притворного
  “внутреннего семейства подпространств”: вся цепочка после quotient-нормировки
  схлопывается в одну линию.

Статус:

- этот shell теперь уже реально посажен в Lean в виде
  `po3_square_normalized_quotient_collapse`
  и
  `po3_square_normalized_quotients_are_scalar_multiples`;
- значит наивная внутренняя ordering-дверь внутри square-chain закрыта
  формально, а не только на уровне заметок.

## Штурм `2c` — canonical entire divider

Идея:

- построить canonical entire divider по квадратному хвосту;
- делить receiver на square-tail divisor;
- сравнивать рост, порядок, симметрию и допустимый support profile.

Плюс:

- это естественный uniqueness route, если current receiver реально entire-side
  или почти entire-side.

Риск:

- надо аккуратно доказать, что текущий receiver попадает в правильный класс
  функций, где деление и рост контролируются.

### `PO3-square.2c0`  `[Canonical divider shell closed]`

Первый честный подшаг внутри `2c` теперь уже формализован:

- finite front correction factor
  `po3_square_front_factor`
  задан явно;
- его successor-рекурсия посажена как
  `po3_square_front_factor_succ`;
- abstract canonical divider data
  `base(z) = front_N(z) * E_N(z)`
  упакованы в
  `po3_square_tail_divider_data`;
- из этих данных формально выведена pointwise step-рекурсия делителя вне
  finite front-zero set:
  `po3_square_tail_divider_step_of_nonvanishing_front`.

То есть `2c` уже сцепился с `2b1`: как только аналитическая factorization
будет реально доказана, step-рекурсия делителя дальше станет механикой.

## Штурм `2d` — transform transfer

Идея:

- не бить injectivity в текущей записи;
- перевести утверждение в другой transform-side, где uniqueness выглядит
  более линейно или более спектрально;
- потом вернуть вывод обратно.

Плюс:

- иногда это радикально упрощает theorem-shape.

Риск:

- можно потратить время на красивый, но бесполезный перенос.

## Приоритет штурмов

Текущий порядок я бы ставил так:

1. `2b` — Newton/divided differences;
2. `2a` — finite-support approximation;
3. `2c` — canonical entire divider;
4. `2d` — transform transfer.

Причина:

- `2b` ближе всего к уже замороженной square-tail machinery;
- `2a` остаётся естественным backup, если tower уже почти хватает;
- `2c` может оказаться сильнейшим, но обычно требует более тяжёлой аналитики;
- `2d` полезен как резерв, если текущая формулировка окажется неудобной.

## Ближайший practical выход

Пока shell не добит окончательно, эта note остаётся подготовительной.

После `PO3-shell.5/.6` следующий честный шаг:

1. выбрать `2b` как primary attack;
2. выписать exact input list для square-tail divided-difference route;
3. отдельно отметить, какие growth / regularity assumptions действительно
   нужны, а какие пока лишь интуитивно кажутся правдой.
