# ОТВЕТ 031 — BAND RIGIDITY + PRIORITY POSITIVE-PART BUDGET

`BAND_ZERO_KILLED_PRIORITY_LEAKAGE_BUDGET_PROVED`

Вторичные флаги:

```text
JACOBI_DIVIDED_DIFFERENCE_IDENTITY_PROVED
EXACT_TOOTH_ALIAS_IDENTITY_PROVED
```

Статус: `CHALLENGER / NOT_RH`. Scope: единственная конечная клетка
`m=257`, `λ=√257`, полосы `r=256,255`. Кофинального вывода и вывода RH
нет.

## Theorem A — BandResponseZeroRigidity

Пусть

```text
Psi(t) = sum_(k>=0) c_k t^k,
S_r(z) = sum_(n=1)^r Psi(nz).
```

На `|z|<1/r` абсолютная сходимость даёт

```text
S_r(z) = sum_(k>=0) c_k (sum_(n=1)^r n^k) z^k.
```

Если `S_r` равна нулю на непустом открытом интервале, теорема
тождественности зануляет её на диске. Для каждого `k≥0`
`sum_(n=1)^r n^k>0`, поэтому все `c_k=0` и `Psi` тождественно равна нулю
на `|t|<1`.

Для `r=255,256` это сталкивается с source-locked свидетелем 027:

```text
Psi(1/sqrt(257))
  >= 19.078168783983037557719600972028097425...
     - 2.75e-244
  > 0.
```

Следовательно, обе предложенные band-zero идентичности невозможны.

## Theorem B — Jacobi divided difference

После общей source-phase строки

```text
b_(j,q) = (-1)^q a_(j,2q)
```

обе моды удовлетворяют одному оператору

```text
(L_Theta b)_q
  = p_(2q) b_(q-1)
    + (2q(2q+1) + G c_(2q) - Theta) b_q
    + r_(2q) b_(q+1),
```

где

```text
p_n = G (n-1)n / ((2n-3)(2n-1)),
r_n = G (n+1)(n+2) / ((2n+3)(2n+5)).
```

Из `L_Theta0 b0=0`, `L_Theta4 b4=0`,
`b0_0=b4_0=1` и `delta=(b4-b0)/2` точно следует

```text
L_Theta4(delta) = ((Theta4-Theta0)/2) b0,
delta_0 = 0.
```

Симметризующие веса:

```text
omega_q = 1/(4q+1),
omega_q r_(2q) = omega_(q+1) p_(2q+2).
```

Для любого конечного `Q` checker посимвольно проверил Green ledger

```text
sum_(q=0)^Q omega_q
  [Y_q (L delta)_q - delta_q (L Y)_q]
= a_Q [Y_Q delta_(Q+1) - delta_Q Y_(Q+1)]
 - a_-1 [Y_-1 delta_0 - delta_-1 Y_0].
```

Нижний член сохранён явно и равен нулю только из
`a_-1=omega_0 p_0=0`. Терминальный член
`a_Q=omega_Q r_(2Q)` остаётся живым; terminal ratio не занулялся.
При `(L_Theta4 Y)_q=A_(r,q)(z)/omega_q` это даёт требуемое
представление `S_r` через forcing pairing и полный boundary ledger.
Знакового вывода из представления не сделано.

## Theorem C — точный S↔E crosswalk

Source-lock:

```text
h_lambda = (I4*h0-I0*h4)/D,
E_star(h_j,1/v)/I_j
  = [sum_n^star phi_j(nz)]/(lambda*sqrt(v)*J_j),
z = 1/(lambda*v).
```

По линейности и определению
`Psi=phi4/J4-phi0/J0`:

```text
E_star(h_lambda,1/v)
  = -(I0*I4/D)/(lambda*sqrt(v)) S_lambda(z)
  = -(I0*I4/D) sqrt(z/lambda) S_lambda(z).
```

При `u=1/v=lambda*z` имеем `du/u=dz/z`. Так как `λ²=257`,
две priority-полосы точно разбивают

```text
[1/lambda,lambda/255]
  = lambda * [1/257,1/255].
```

Из exact-rational lower envelopes сертификата 030 прочитаны

| `r` | `epsilon_r=max(0,-lower_full_sum_r)` |
|---:|---:|
| 256 | `2.241863140765617915e-237` |
| 255 | `2.241862772864156905e-237` |

Полные числители и знаменатели сохранены без округления в
`PRIORITY_BAND_POSITIVE_PART_CERT.json`. На каждой полосе
`max(-S_lambda,0)≤epsilon_r`; интегрирование
`u^(-sigma-1/2) du` даёт ровно

```text
Delta_prio(sigma)
<= (I0*I4/D) lambda^(-sigma-1/2)
   * sum_(r in {255,256}) epsilon_r
     * [(1/r)^(1/2-sigma)-(1/(r+1))^(1/2-sigma)]
     / (1/2-sigma).
```

Контрольные значения правой части, делённой на `I0*I4/D`:

| `sigma` | bound / `(I0*I4/D)` |
|---:|---:|
| 0 | `2.734009186878142160e-241` |
| 0.10 | `3.606840015055700528e-241` |
| 0.25 | `5.465341262982886754e-241` |
| 0.40 | `8.281475866564449128e-241` |
| 0.45 | `9.511986754001643271e-241` |

Конечное множество зубьев имеет меру ноль и не меняет интеграл. Из этого
не сделано утверждение о поточечном знаке на зубьях.

## Exact tooth alias

Для composite-trapezoid functional

```text
T_r(Psi)
  = [Psi(0)/2 + sum_(n=1)^(r-1) Psi(n/r) + Psi(1)/2]/r
```

покомпонентно доказано

```text
S_star_r = r*T_r(Psi) - Psi(0)/2.
```

Это точечная alias-идентичность, не band-zero утверждение.

## Планты P1–P8

| Plant | Результат |
|---|---|
| P1 `Psi=1` | `S_r=r`; band-zero отвергнут |
| P2 `Psi=t^(2k)` | точный множитель `sum n^(2k)` сохранён |
| P3 witness 027 | вывод `Psi≡0` сталкивается со строгим положительным свидетелем |
| P4 `Psi=t²-1/3` | масса ноль, но `S_star_r=(r+1)/(6r)≠0` |
| P5 Jacobian | при `S=-1`, `u∈[1/4,1]`, `sigma=0`: правильное значение `1`, без `/u` — `7/12` |
| P6 sign flip | положительная и отрицательная leakage меняются ролями |
| P7 tooth mutation | Lebesgue budget неизменен, поточечный знак меняется |
| P8 recurrence collision | `Theta4=Theta0`, одна нормированная solution ⇒ `delta=0`, forcing `=0` |

Все восемь плантов стреляют.

## Независимый checker

Checker использует только Python stdlib, не импортирует generator 031,
generator 030, `flint` или Arb. Он:

- сверяет source SHA-256;
- независимо пинит SHA-256 сертификата 030;
- заново читает exact-rational lower envelopes и вычисляет `epsilon_r`;
- exact-rational replay делает для common recurrence, divided difference,
  symmetrizing weights и конечного Green ledger;
- символически проигрывает P1–P8 и tooth alias.

```text
PASS BAND_ZERO_KILLED_PRIORITY_LEAKAGE_BUDGET_PROVED
P1 PASS P2 PASS P3 PASS P4 PASS P5 PASS P6 PASS P7 PASS P8 PASS
JACOBI_DIVIDED_DIFFERENCE_IDENTITY_PROVED
EXACT_TOOTH_ALIAS_IDENTITY_PROVED
```

Артефакты:

```text
PRIORITY_BAND_POSITIVE_PART_CERT.json
priority_band_positive_part_certificate.py
check_priority_band_positive_part_certificate.py
```

SHA-256 сертификата:

```text
86191e9eb8772dd013dbeb7347c1484b910109dbe5a4a2b24562e43211b937c9
```

`STATE` не изменён. Bus 010 не создан.
