# ОТВЕТ 027 — HLAMBDA OUTER LOBE GATE

`HLAMBDA_LAST_POSITIVE_ZERO_LT_ONE_PROVED`

Статус: `CHALLENGER / NOT_RH`. Verdict относится ровно к трём
сертифицированным клеткам `m in {13,53,257}`; это не cofinal-family theorem.
`STATE` не изменён, `BUS_010_VOID` соблюдён.

## Метод и нормировка

Потреблены exact-mode интервалы 026. Для каждой степени заново построен
интервальный Legendre-core из сертифицированного `Theta`-шара и вычислена
ровно одна требуемая точка `t=1/sqrt(m)`. Sign-grid не использовался.

В сырой нормировке `a0=1`. Все остальные Legendre-члены имеют положительную
степень и нулевой интеграл на `[-1,1]`, поэтому

```text
J0_raw = J4_raw = 2.
```

Положительный L2-scale каждой моды сокращается отдельно и точно в
`phi_j/J_j`. Тем же сокращением

```text
epsilon_j/J_j = |a_(j,K)|/2.
```

То есть хвост не удалён: его строго положительная allowance явно вычтена из
point margin.

## Два скаляра

| `m` | `Theta4-(17*pi^2/4)m` | `Psi_K(1/sqrt(m))` | tail allowance | строгий point margin |
|---:|---:|---:|---:|---:|
| 13 | `>178.9` | `4.394699567751...` | `4.173581362502e-4` | `4.394282209615...` |
| 53 | `>763.1` | `8.705153535562...` | `2.758190767220e-18` | `8.705153535562...` |
| 257 | `>3742.1` | `19.078168783983...` | `6.670150442998e-96` | `19.078168783983...` |

Все числа — outward-rounded Arb balls; полные шары записаны в JSON.
Следовательно, в каждой из трёх клеток доказаны:

```text
Theta4_lower > (17*pi^2/4)*lambda^2
Psi_K(1/lambda) > eps4_K/J4 + eps0_K/J0.
```

## Инстанцирование pen theorem

Подстановка этих двух строгих скаляров в уже замороженный
Sturm–Wronskian transport из `PROSHKA_PEN_REDUCTIONS_2026-07-27.md`
даёт

```text
h_lambda(x) < 0,  1 <= x < lambda.
```

Точка `x=lambda` обработана отдельно замороженным midpoint/phase relation,
поэтому итог в каждой сертифицированной клетке:

```text
h_lambda(x) <= 0,  1 <= x <= lambda.
```

Прямой Sturm к комбинации, `mu:=1`, ослабление теоремы и truncated
eigenvector как exact mode не использовались.

## Артефакты и следующий адрес

```text
hlambda_outer_lobe_gate_audit.py
HLAMBDA_OUTER_LOBE_GATE_AUDIT.json
HLAMBDA_OUTER_LOBE_GATE_AUDIT.csv
```

Следующий живой адрес:

```text
RouteB.028 / FiniteCoreThetaOrderWithTailBudget
```

На нём требуется выбрать один proof-grade backend для конечных band/tooth
полиномов: Sturm, Bernstein, rational interval subdivision или exact SOS.
