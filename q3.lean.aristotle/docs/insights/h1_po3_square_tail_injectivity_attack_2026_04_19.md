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
