# TWO SIGN LEMMAS — POST-026 VERDICT

Статус: `CHALLENGER / NOT_RH`.

Источник полного pen-аудита:
`proshka/PROSHKA_PEN_REDUCTIONS_2026-07-27.md`.
Численные результаты 022/024 не используются как доказательства.

## Registered predictions

1. Прямой Sturm к `h_lambda` не типизируется: это комбинация двух разных
   собственных функций. Ожидалось сведение к outer-lobe ratio и одному
   point-gate.
2. Corrected Poisson переносит знак, но не создаёт его. Ожидалось сведение к
   signed quadrature-order theorem для режимов `0/4`.

Оба прогноза подтвердились.

## Lemma A — HlambdaLastPositiveZeroLtOne

```text
REDUCED_TO(HlambdaOuterLobeGate)
```

Paper-proved transport:

```text
Theta4 > (17*pi^2/4) lambda^2
and
I0*h4(1)-I4*h0(1) > 0
imply
h_lambda(x) < 0 for 1 <= x < lambda.
```

Механизм: Sturm comparison даёт первый нуль `h4` левее `1`; point-gate
помещает оба положительных нуля левее `1`; Wronskian делает
`h4/h0` строго возрастающим на внешней лопасти.

После 026 eigenvalue-часть строго сертифицирована для
`m in {13,53,257}` с положительными запасами `>178.9`, `>763.1`, `>3742.1`.
Открыт scalar point determinant

```text
I0*h4(1)-I4*h0(1) > 0,
```

а для cofinal family нужен параметрический или равномерный сертификат обоих
скаляров. Поэтому глобальный verdict не повышается до `PAPER_PROVED`.

## Lemma B — DualThetaDominance

```text
REDUCED_TO(FiniteCoreThetaOrderWithTailBudget)
```

Corrected Poisson и zero-mass дают точную эквивалентность

```text
E_dual(hhat_lambda)(v) <= -|h_lambda(0)|/(2*sqrt(v))
iff
E_star(h_lambda,v^(-1)) <= 0.
```

После сокращения нормировок это

```text
S_lambda(z) = sum_n^star Psi_lambda(n*z) >= 0,
lambda^(-2) <= z <= lambda^(-1).
```

На каждой tooth-band остаётся конечный полином `P_(r,K)` и явный бюджет

```text
|S_lambda-P_(r,K)| <= r*epsilon_(Psi,K),
```

с отдельным midpoint-бюджетом `(r-1/2)*epsilon_(Psi,K)` на tooth.
026 теперь поставляет proof-grade exact-mode и хвостовые шары для трёх
контрольных `m`, но не доказывает полиномиальные inequalities на всех полосах
и не даёт cofinal certificate family.

## Strongest attack

- A не применяет Sturm к канонической комбинации; он применён только к
  отдельным режимам и их ratio.
- A-point действительно концентрирует остаток исходного знака в одной точке;
  это честный scalar wall, а не закрытие.
- B является representation progress, но ещё не conceptual sign theorem:
  positivity конечных полиномов должна быть доказана Sturm/Bernstein/SOS или
  рациональным interval subdivision.
- Ни отсутствие контрпримера, ни 51 floor-запись не являются доказательством
  знака.

## Adjudication

```text
KILLED: neither lemma
PAPER_PROVED: the two reduction theorems only
OPEN:
  HlambdaOuterLobeGate
  FiniteCoreThetaOrderWithTailBudget
```
