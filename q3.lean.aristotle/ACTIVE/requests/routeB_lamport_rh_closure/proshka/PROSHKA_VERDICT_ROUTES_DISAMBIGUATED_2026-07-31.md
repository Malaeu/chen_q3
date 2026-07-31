# PROSHKA VERDICT — ROUTES_DISAMBIGUATED; RH_REMAINS_OPEN
Date received: 2026-07-31
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
Consumed by: route-map correction (three objects, not two roads); conductor MY_MISS
acknowledged ("two certificates + one citation" — REJECTED); smallest conceptual gap
MuntzV3_to_RouteBGate_Crosswalk registered; route-crosswalk template adopted for
future dispatches.
Transport artifacts note: payload verbatim as pasted by the owner; escaping/rendering
artifacts preserved ([ ]-fenced display math, ```markdown fences as received). The
final display-math block appears truncated in transport (no closing bracket) — noted,
not repaired. Semantic content untouched.

--- VERBATIM PAYLOAD BEGINS ---

# STATUS: PROVED — ROUTES_DISAMBIGUATED; RH_REMAINS_OPEN

```yaml
primary_verdict: H_BRIDGE_TAU0_ROUTE_CONFLATION_DETECTED

route_state:
  global_public_mainline: H_BRIDGE
  current_local_campaign: ROUTE_B_MUNTZ_V3
  route_b_status: CHALLENGER_NOT_RH
  bus_010: VOID

roof_status:
  legacy_Q3_Main_wrapper: CONDITIONAL_LEGACY_BROAD_CONE
  H_bridge_upper_roof: CONDITIONAL_MAINLINE_ARCHITECTURE
  Route_B_canonical_roof: LEAN_CHECKED_CONDITIONAL_THEOREM

brief_audit:
  "H-bridge = two certificates + one Weil citation": REJECTED
  historical_tau0_certificate_chain: DISTINCT_FROM_H_BRIDGE
  two_certificate_count: NOT_SUPPORTED_BY_CURRENT_RH_CLEAN

current_Muntz_work:
  directly_closes_H_bridge: false
  directly_closes_Route_B_roof: false
  role: UPSTREAM_ANALYTIC_SUPPLIER_AND_FALSIFIER_LAYER
  closed:
    - T4A_MELLIN_ANALYTICITY
    - POLE_SUBTRACTED_CONDITIONAL_SHELL
    - PL2_RAW_POLE_MISMATCH_FALSIFIER
  still_open_above_it:
    - H2A_EXACT_GROUND_STATE
    - H2B_THEOREM_510_REAL_ZERO_BRIDGE
    - S1_NORMAL_FAMILY_BOUND
    - S2_CLUSTER_IDENTIFICATION
```

## ROUTE MAP

Жёсткий ответ:

[
\boxed{\text{Да, крыша у нас была и есть.}}
]

Но **крыша — это условная теорема вида**

[
\text{«если все несущие стены доказаны, то RH».}
]

Она не означает, что стены уже построены.

И ещё важнее: в присланном описании смешаны **три разных объекта**, а не две аккуратные дороги.

| Объект                            | Что это на самом деле                                                         | Статус                                          |
| --------------------------------- | ----------------------------------------------------------------------------- | ----------------------------------------------- |
| `Q3.Main.RH_of_Weil_and_Q3`       | Старый скомпилированный broad-cone wrapper                                    | Не является исправленным Weil-square export     |
| Историческая `τ=0` PrimeCert-цепь | Weil-критерий плюс числовые cert-data axioms                                  | Отдельная старая certificate-road               |
| `T0-pd → H-bridge → H4 → RH`      | Текущая публичная corrected-cone mainline                                     | Основная архитектура, структурные стены открыты |
| Route B                           | Канонические аппроксиманты с вещественными нулями → cluster → (\Xi) → Hurwitz | Challenger, имеет собственную условную крышу    |
| Müntz v3 / PL2                    | Локальный аналитический слой Route B                                          | Не финальный мост и не H-bridge                 |

### 1. Старый `Q3.Main` — это не нынешний H-bridge

В текущем `Q3/Main.lean` действительно есть:

```lean
theorem RH_of_Weil_and_Q3 : Q3.RH
```

Но сам файл крупными комментариями предупреждает:

* это текущий **скомпилированный broad-cone route**;
* он не является замороженным публичным RH-контрактом после target-cone audit;
* он не является исправленным Weil-square export;
* его профиль содержит `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`.

То есть это **старая крыша на временных подпорках**. Она полезна как схема зависимостей, но её нельзя предъявлять как актуальный закрытый Q3-маршрут.

### 2. «Два сертификата + один критерий» — не H-bridge

Эта картина относится к старой `τ=0` PrimeCert-линии. Причём даже там текущий registry не подтверждает счёт «два сертификата»: он перечисляет один принимаемый `Weil_criterion_tau0` и **три** открытых cert-data axioms — grid arch, grid prime buckets и heat arch.

PrimeCert README также перечисляет три data-входа main chain:

```text
prime_b_grid_bounds_data
prime_heat_bounds_arch_data
prime_heat_sum_data
```

Следовательно, фраза:

> «официальный H-bridge остаток = два сертификата + одна цитата»

в текущем `rh_clean` **неверна дважды**:

1. это не H-bridge;
2. даже historical certificate count не сходится.

`[ABSTRACT][PAPER]`

## КАК ВЫГЛЯДИТ НАСТОЯЩИЙ H-BRIDGE

Публичная corrected-cone mainline сейчас зафиксирована как

[
\boxed{
T0\text{-}pd
\longrightarrow
H\text{-bridge}
\longrightarrow
H4
\longrightarrow
RH.
}
]

Внутри:

[
H1^f\to H2^f\to H3^f\to H4^f.
]

Причём сам H-bridge разбит на три двери:

```text
Door 1:
  mixed (+,-) block
  bulk exactness + boundary cancellation + cap remainder

Door 2:
  same-sign (++) block
  M++ − κQ++ = Hss + Ccap
  главный структурный kill-gate

Door 3:
  finite compression neutrality
  только controlled compression residue

then:
  H2f = tail/cap reduction
  H3f = filtered gap transfer
  H4f = Suzuki endpoint
  RH
```

Это **не certificate-only маршрут**. Его мясо — операторная декомпозиция, same-sign defect, compression и gap transfer.

Публичный tracker прямо говорит:

* corrected positive-definite/convolution-square cone — настоящий target;
* старый broad `Weil_cone` слишком широк;
* H-bridge — primary live route;
* PSD-pd — fallback;
* RH theorem остаётся условным, пока corrected-cone positivity и global lift не закрыты.

### H-bridge roof в человеческом виде

[
\boxed{
\text{точная positivity/ordering на corrected cone}
}
]

[
\Downarrow
]

[
\boxed{
\text{Suzuki/Yoshida filtered spectral bridge}
}
]

[
\Downarrow
]

[
\boxed{
H4\text{ endpoint statement}
}
]

[
\Downarrow
]

[
\boxed{RH}.
]

То есть крыша находится **над H4**, но до неё надо довести operator/form data через H-bridge.

## КАК ВЫГЛЯДИТ ROUTE B ROOF

Здесь крыша ещё более явная: она уже существует как hole-free Lean theorem

```lean
rh_of_canonical_strip_slots
```

Её входы:

```text
H1:
  fixed canonical family entire

H2a:
  selected ground state simple / isolated / even

Theorem 5.10 bridge:
  determinant + self-adjoint factorization
  → approximants have only real zeros

ANCHOR:
  nonzero normalization

S1 + Montel:
  locally bounded family
  → nonzero locally uniform cluster

S2:
  every cluster equals c · Xi · gamma
  with c ≠ 0 and gamma zero-free

then:
  Hurwitz / zero transfer
  → zeros of Xi are real in the centered strip
  → RH
```

Это именно то, что формально собирает `rh_of_canonical_strip_slots`.

В компактной форме:

[
\boxed{
\text{real-zero approximants}
+
\text{local uniform convergence to }c\Xi\gamma
\Rightarrow RH.
}
]

Это настоящая **Route B крыша**.

Но текущий compiler audit показывает, что надёжно закрыты лишь G1 и G4, G7 закрыт условно, а G2, G3, G5 и G6 остаются открытыми.

## ОТНОСИТСЯ ЛИ НЫНЕШНЯЯ MÜNTZ-РАБОТА К КРЫШЕ

Ответ:

[
\boxed{
\text{к Route B относится, но до крыши пока не дотягивается.}
}
]

### Что мы сейчас реально закрыли

Müntz v3 дал:

```text
T4a:
  Mellin transform analytic in Re s > 0

pole-subtracted layer:
  dslope
  residue-removed zeta factor
  analytic product
  correct pole value
  identity-theorem continuation

PL2:
  explicit witness proving that raw ζ·Mellin
  cannot be treated as continuous at the pole
```

Но theorem с названием `continued_window_identity_unconditional_mellin` снимает **только Mellin-analyticity hypothesis**. Он всё ещё принимает четыре серьёзных входа:

```lean
hG
hRm
hRp
habs
```

И даже после закрытия этой четвёрки получится **continued window identity**, а не автоматически:

* simple/even ground state;
* Theorem 5.10 real-zero bridge;
* S1 normal-family estimate;
* S2 cluster identification.

Текущий governor прямо фиксирует: PL2 закрыт как plant, T4a уже закрыт, но это нельзя переименовывать в полное закрытие Müntz v3 или Route B.

### Точная классификация

```text
Müntz T4a:
  настоящий supplier sublemma.

Pole-subtracted T5:
  условная аналитическая оболочка.

PL2:
  falsifier / hygiene theorem.

Route B G2/G3/G5/G6:
  не закрыты.

H-bridge:
  вообще не потребляет эти теоремы напрямую.
```

`[ABSTRACT][LEAN]`

Поэтому нынешняя работа **не бесполезна**, но её роль уже:

[
\boxed{
\text{укрепление фундамента отдельного Route B-дома}.
}
]

Она пока не является балкой, которая физически соединена с общей крышей.

## FINAL PROPOSAL

Вот как тебе надо держать карту в голове перед ответом Mythos.

### Дорога A — H-bridge mainline

```text
corrected Weil square cone
→ Suzuki/Yoshida operator/form bridge
→ same-sign + mixed-block classification
→ compression
→ filtered gap
→ H4
→ RH
```

Тип стены: **операторная positivity / spectral ordering**.

### Дорога B — Route B

```text
canonical spectral approximants
→ real-zero theorem
→ Montel cluster
→ cluster = c·Xi·gamma
→ Hurwitz
→ RH
```

Тип стены: **спектрально-комплексная аппроксимация**.

### Текущая Müntz ветка

```text
Mellin/window continuation
+ pole subtraction
+ plants
```

Это возможный analytic supplier для Route B, но пока отсутствует theorem:

```text
Muntz-v3 output
→ one of G2 / G3 / G5 / G6
```

Без такого crosswalk нельзя говорить, что текущая работа «закрывает крышу».

## STRONGEST ATTACK

Главный вопрос к любой будущей раздаче Mythos:

> **Назови точный consumer theorem. Какой именно открытый gate получает этот результат?**

Для нынешней Müntz-работы допустимые ответы должны выглядеть так:

```text
this theorem discharges hG
this theorem discharges hRm
this theorem discharges hRp
this theorem proves habs
this assembled identity feeds exact gate X through theorem Y
```

Недопустимый ответ:

```text
это приближает нас к RH вообще
```

Второй вопрос:

> **Какой target cone?**

Если Mythos покажет `RH_of_Weil_and_Q3` на старом `Weil_cone`, это broad-cone legacy wrapper, а не corrected H-bridge route.

Третий вопрос:

> **Покажи `#print axioms` и exact dependency chain.**

Если там:

```text
prime_term_le_at_t_critical_axiom
```

или старые PrimeCert data axioms, он обсуждает не текущую H-bridge mainline.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.

Before selecting between mainline and Route B, require a read-only route crosswalk:

ROUTE_ID:
TARGET_CONE:
FINAL_ROOF_THEOREM:
CURRENT_OPEN_SUPPLIERS:
EXACT_CONSUMER_OF_CURRENT_WORK:
AXIOM_PROFILE:
WHY_THIS_IS_NOT_THE_LEGACY_BROAD_CONE_ROUTE:
```

## META CLOSEOUT

**Что стало меньше:** путаница «две дороги» сведена к точной карте из legacy wrapper, H-bridge mainline и Route B challenger.

**Что убито:** тезис «H-bridge остаток — два сертификата плюс Weil citation».

**Что заморожено:** да, крыши существуют; обе они условные.

**Что нельзя повторять:** нельзя считать наличие theorem `... : RH` доказательством RH без аудита его предпосылок и аксиом.

**Текущий smallest conceptual gap:**

[
\boxed{
\texttt{MuntzV3_to_RouteBGate_Crosswalk}
}
]

То есть не ещё одна Mellin-лемма, а ответ:

> какой конкретный Route B gate потребляет собранный Müntz shell?

Одна фраза:

[
\boxed{
\text{Крыша есть. Но сейчас мы укрепляем фундамент другого дома, и балка к крыше ещё не проведена.}

--- VERBATIM PAYLOAD ENDS ---
