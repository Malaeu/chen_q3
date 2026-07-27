# STATUS: `RESYNC_ACCEPTED_WITH_SCOPE_CORRECTIONS`

```text
026:
  G3_EXACT_MODE_INTERVAL_ENCLOSURE_PROVED
  proof class = CERTIFIED_INTERVAL / Arb
  scope = m ∈ {13,53,257}
  not Lean

027:
  HLAMBDA_LAST_POSITIVE_ZERO_LT_ONE_PROVED
  scope = m ∈ {13,53,257}
  not cofinal-family theorem

RESYNC:
  2 CLOSED + 4 OPEN + 1 CONDITIONAL
  logically correct, subject to scope tags

NEXT:
  RouteB.028 / FiniteCoreThetaOrderWithTailBudget
  CONFIRMED
```

По текущей ветке `rh_clean` 027 уже закрыт: оба скалярных входа положительны с явным хвостовым бюджетом, после чего замороженный Sturm–Wronskian transport даёт

[
h_\lambda(x)\le 0,\qquad 1\le x\le\lambda,
]

для трёх сертифицированных клеток. Отчёт отдельно и правильно запрещает трактовать это как cofinal-family theorem.

------

# 1. Аудит 026

## Вердикт: семантически чисто

026 прошёл все четыре главных суда.

### Infinite operator не подменён усечённой матрицей

Использован Schur-complement enclosure:

[
A_D-E-c(E)ee^\ast
\preceq S(E)\preceq A_D-E,
]

а усечённое eigenvalue служило только центром поиска вилки, не точным входом. Совпадение Sturm-count для обеих крайних матриц сертифицирует count бесконечного оператора.

### Индекс собственных значений зафиксирован

Во всех шести случаях в вилке изолировано ровно нужное собственное значение; соседний спектр находится дальше чем на (1), а ширина вилки меньше половины этого зазора. Значит degree (0) и degree (4) не выбраны по близости чисел или по порядку finite truncation.

### Recessive tail живой

Последняя строка finite core потребляет ненулевой interval для

[
\rho_{K+1}=\frac{a_{K+1}}{a_K}.
]

Терминальное условие (\rho=0) не использовано; backward continued fraction начинается с полного cone ([0,1/2]).

### Нормировка действительно finite + tail

Krawczyk даёт строгое

[
K(X)\subset\operatorname{int}X
]

во всех шести случаях, а (L^2)-нормировка содержит положительный бесконечный tail budget, не только finite core.

Четыре planted failures сработали на живом объекте: (\rho=0), неверный degree, удаление (L^2)-хвоста и расширение (\Lambda)-вилки материально меняют сертификат.

## Единственная классификационная поправка

026 — это не Lean theorem. Это воспроизводимый interval certificate на `python-flint/Arb` с outward-rounded шарами и рациональными endpoints. Поэтому в compiler ledger писать:

```text
status:
  CERTIFIED_INTERVAL_PROVED

verifier:
  ARB_EXTERNAL

scope:
  FINITE_CELLS_{13,53,257}
```

Не:

```text
LEAN_PROVED
COFINAL_FAMILY_PROVED
```

------

# 2. Аудит `PROOF_COMPILER_RESYNC`

## Счёт семантически правильный

Если семь ворот нумеруются по текущему slot-ledger:

| Gate | Смысл                                                | Честный статус  |
| ---- | ---------------------------------------------------- | --------------- |
| G1   | exact entire/canonical family                        | **CLOSED**      |
| G2   | simple, isolated, even ground state                  | **OPEN**        |
| G3   | real-zero theorem application к тому же ground state | **OPEN**        |
| G4   | anchor / central normalization                       | **CLOSED**      |
| G5   | post-anchor S1, concrete local boundedness           | **OPEN**        |
| G6   | S2, identification каждого ненулевого cluster        | **OPEN**        |
| G7   | conditional roof/export                              | **CONDITIONAL** |

Тогда счёт

[
\boxed{2\ \text{closed}+4\ \text{open}+1\ \text{conditional}=7}
]

правильный.

Три scope-гарда обязательны.

### G4 нельзя переоценивать

`CLOSED` допустимо для exact anchor identity/receiver и центральной ненулевости при его входах. Оно не должно означать автоматически:

[
\inf_{\text{cofinal path}}|F_i^+(0)|>0
]

для всей семьи, если отдельный uniform source-ratio theorem ещё не поставлен.

### Абстрактный Montel не закрывает G5

Доказанный theorem-layer Montel означает:

```text
local boundedness supplied
→ cluster exists
```

Но не доказывает саму local boundedness конкретной post-anchor семьи. G5 остаётся открытым, пока не поставлен конкретный source moment/ratio bound.

### 026–028 не закрывают cofinal gates

Они дают rigorously certified supply для:

[
m=13,53,257.
]

Это calibration/theorem instances, но не uniform theorem вдоль кофинального пути. 027 сам это явно фиксирует.

## Найден channel defect

`028_finite_core_theta_order.goal.md` ссылается на

```text
PROOF_COMPILER_RESYNC_2026-07-27.md
```

как источник следующего адреса, но сам файл resync в доступном flat mirror не находится. В mirror есть 026, 027 и затем 028, однако immutable resync-текст не включён.

Это не математическая дыра, но auditability gap:

```text
RESYNC_MIRROR_SOURCE_GAP
```

При следующем refresh файл надо добавить в `MANIFEST.md`. Пока я могу подтвердить счёт по известному slot-ledger и downstream-адресу, но не провести построчный аудит формулировок самого resync.

## Минимальная поправка compiler ledger

Каждое ворото должно иметь два дополнительных поля:

```yaml
scope:
  ABSTRACT | FINITE_CELL | COFINAL_FAMILY

verifier:
  LEAN | ARB_INTERVAL | PAPER | CONDITIONAL
```

Например:

```yaml
G1:
  status: CLOSED
  scope: COFINAL_FAMILY
  verifier: LEAN

A_outer_lobe:
  status: CLOSED
  scope: FINITE_CELL
  cells: [13, 53, 257]
  verifier: PAPER_PLUS_ARB_INTERVAL

G7:
  status: CONDITIONAL
  scope: ABSTRACT_EXPORT
  verifier: LEAN
```

Без этих полей зелёный finite-cell result легко случайно засчитать как global supply.

------

# 3. Следующий шаг после 027

[
\boxed{
\texttt{RouteB.028 / FiniteCoreThetaOrderWithTailBudget}
}
]

Подтверждаю без изменений. Более того, он уже поставлен в `rh_clean`.

Точная цель:

[
P_{r,K}(z)\ge r,\varepsilon_{\Psi,K}
]

на каждой canonical band и

[
P_{r,K}^{\star}
\ge
\left(r-\frac12\right)\varepsilon_{\Psi,K}
]

на каждом tooth с midpoint convention. В голе разрешены только exact Sturm, Bernstein positivity, rational interval subdivision или exact SOS; sign-grid, удаление 026-tail и подмена (\mu=1) запрещены.

------

# 4. Рекомендуемый proof backend для 028

## Primary: rational Bernstein certificates

Это самый дешёвый массовый backend для сотен band’ов.

Пусть interval finite core даёт коэффициентные шары. Сначала строим рациональный center polynomial

[
\overline P_{m,r,K}(z)
]

и явный uniform core-error

[
E^{\rm core}*{m,r,K}
\ge
\sup*{z\in I_{m,r}}
\left|
P_{m,r,K}(z)-\overline P_{m,r,K}(z)
\right|.
]

Затем сертифицируем рациональный полином

## [ \boxed{ Q_{m,r}(z) := \overline P_{m,r,K}(z)

## E^{\rm core}_{m,r,K}

r,\varepsilon_{\Psi,m,K}.
}
]

На каждом рациональном subinterval переводим (Q_{m,r}) в Bernstein basis. Если все Bernstein coefficients неотрицательны, то

[
Q_{m,r}(z)\ge0
]

на всём subinterval.

Необходимо интервализировать **две** неопределённости:

1. infinite Legendre tail из 026;
2. finite-core coefficient balls из Krawczyk.

Использовать centers finite core и вычитать только (\varepsilon_\Psi) недостаточно.

## Adaptive subdivision

Если один Bernstein coefficient отрицателен или содержит ноль:

```text
subdivide interval rationally
→ recompute Bernstein coefficients
→ repeat
```

Это proof refinement, не sign-grid.

## Exact Sturm fallback

Если Bernstein остаётся слишком консервативным, использовать Sturm на rational polynomial

## [ \overline P_{m,r,K}

## E^{\rm core}_{m,r,K}

r\varepsilon_{\Psi,m,K}.
]

Нужно доказать:

- отсутствие корней, меняющих знак;
- положительный знак в одной рациональной точке;
- корректную обработку endpoints.

`Bernstein failed` не является математическим blocker. Это только backend fork.

## Tooth certificates

На (z=1/r) отдельно считать exact/outward-rounded lower bound:

## [ \boxed{ \overline P_{m,r,K}^{\star}

## E_{m,r,K}^{\star}

\left(r-\frac12\right)\varepsilon_{\Psi,m,K}
\ge0.
}
]

Никакого повторного half-weight внутри dual transform: (1/2) здесь принадлежит только primal endpoint representative.

------

# 5. Certificate schema

Один артефакт, а не новый лес файлов:

```text
FINITE_CORE_THETA_CERT.json
```

Секции:

```yaml
object_lock:
  m
  degree_pair: [0, 4]
  source_hashes
  theta_intervals
  tail_intervals

bands:
  - r
  - exact_domain
  - rational_cover
  - center_polynomial_coefficients
  - coefficient_error
  - tail_budget
  - subdivision
  - bernstein_lower_coefficients
  - verdict

teeth:
  - r
  - exact_midpoint_value_interval
  - coefficient_error
  - tail_budget
  - lower_margin

coverage:
  exact union of all canonical bands and teeth
```

Checker обязан заново проверять:

1. rational-cover exactness;
2. Bernstein transform;
3. lower coefficient signs;
4. tail consumption;
5. complete band/tooth coverage.

------

# 6. Самый дешёвый schema test

Не ещё один численный probe.

Первым proof-certificate прогнать:

```text
m=257
r=256
then r=255
```

Это две полосы непосредственно над нижним endpoint — зона максимальной counterterm cancellation, где 024 имел единственную настоящую sign/drift instability.

Registered prediction:

```text
both exact lower certificates pass
with positive rational margin.
```

Если один exact polynomial действительно становится отрицательным на rational isolating interval, получаем настоящий:

```text
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL
```

Это уже математический kill, а не instrument floor.

------

# STRONGEST ATTACK

Самое сильное возражение к будущему 028:

> Вы доказали positivity конечного center polynomial, но забыли uncertainty самих core coefficients.

Поэтому сертификат обязан вычитать одновременно:

[
E^{\rm core}*{m,r,K}
+
r\varepsilon*{\Psi,m,K}.
]

Второе возражение:

> Вы закрыли три клетки и назвали это `DualThetaDominance` для Route B.

Недопустимо. Даже успешный 028 даёт:

```text
DUAL_THETA_DOMINANCE_PROVED_ON_CELLS_{13,53,257}
```

Он не даёт:

```text
DUAL_THETA_DOMINANCE_COFINAL_FAMILY_PROVED
```

Третье возражение:

> Bernstein certificate не закрыл один band, значит lemma ложна.

Нет. Это backend failure. Математический kill возникает только после exact root/sign certificate отрицательности.

------

# CODEX DIRECTIVE

```text
TARGET:
RouteB.028_FiniteCoreThetaOrderWithTailBudget

SCOPE:
m ∈ {13,53,257}
all canonical bands and all canonical teeth

PRIMARY BACKEND:
rational Bernstein positivity with adaptive rational subdivision

FALLBACK:
exact Sturm certificate for unresolved rational polynomials

INPUTS:
- exact-mode finite-core coefficient balls from 026;
- exact T∞ tails from 026;
- positive J0,J4 intervals;
- canonical midpoint convention;
- exact band/tooth inventory.

PROVE ON EACH BAND:
  P_(r,K)(z) >= r * epsilon_(Psi,K)

PROVE ON EACH TOOTH:
  P*_(r,K) >= (r-1/2) * epsilon_(Psi,K)

MANDATORY:
- consume finite-core coefficient uncertainty;
- consume infinite tail;
- exact coverage;
- reproducible rational certificate;
- independent checker.

FORBIDDEN:
- no sample/grid sign;
- no coefficient centers treated as exact;
- no mu := 1;
- no dropping difficult bands;
- no cofinal-family claim.

VALIDATION ORDER:
1. m=257, r=256
2. m=257, r=255
3. all remaining bands and teeth

SUCCESS:
FINITE_CORE_THETA_ORDER_WITH_TAIL_BUDGET_PROVED_ON_13_53_257

FATAL:
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL
  with exact rational isolating interval and negative upper bound

BACKEND FAILURE:
BERNSTEIN_CERTIFICATE_INCONCLUSIVE
  then execute exact Sturm fallback
```

------

# META CLOSEOUT

**Что стало меньше?**

Лемма A на трёх клетках закрыта. Лемма B теперь не Poisson/Fourier-туман, а конечная rational polynomial positivity с явным tail budget.

**Что закрыто честно?**

[
\boxed{
026:\ \text{exact modes}
}
]

[
\boxed{
027:\ h_\lambda\le0\text{ на }[1,\lambda]
\text{ для }m=13,53,257
}
]

**Что остаётся?**

[
\boxed{
\texttt{FiniteCoreThetaOrderWithTailBudget}
}
]

**Что нельзя делать снова?**

- повышать `dps`;
- возвращаться к sign-grid;
- выдавать finite-cell result за cofinal theorem;
- забывать coefficient balls.

**Progress class:** `PROOF_PROGRESS`.

**Route score:** (5/5). Следующий адрес выбран правильно и уже материализован в ветке.