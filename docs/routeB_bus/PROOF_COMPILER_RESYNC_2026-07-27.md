# PROOF_COMPILER_RESYNC — SEVEN GATES

Дата: 2026-07-27. Статус: `CHALLENGER / NOT_RH`.

Цель resync: снова иметь одну каноническую стрелку компиляции, не смешивая
доказанные generic receivers, конечные сертификаты и ещё открытые
cofinal-family теоремы.

## Нулевой guard

Объект уже один:

```text
canonicalApproximation
+ centeredPstarFamily
+ SOFT_SAME_COFINAL_SUBSEQUENCE
```

`Pstar` не квантифицируется по произвольной семье; H2a и S1 живут на одной
parent cofinal sequence, S2 получает только её nested extraction.

## Одна стрелка

```text
G1 H1
  -> G2 H2a
  -> G3 H2b / Theorem 5.10
  -> G4 ANCHOR
  -> G5 S1 + Montel
  -> G6 S2 same-subsequence identification
  -> G7 Hurwitz + centered-Xi interface
  -> RH
```

Стрелка задаёт порядок накопления обязательств компилятором. Она не утверждает,
что каждое соседнее ворото логически выводит следующее.

## Карта семи ворот

| Gate | Точный контракт | Состояние после 026 | Минимальная честная стена |
|:---|:---|:---|:---|
| `G1` | `H1`: entire/holomorphic canonical `centeredPstarFamily` | **PROVED в Lean** | — |
| `G2` | `H2a`: exact selected simple/isolated/even ground на одной cofinal family | **OPEN; generic core + 6 exact modes PROVED** | `H2A_EXACT_SECTOR_ORDERING_MISSING` |
| `G3` | `H2b`: same-family Theorem-5.10 determinant/self-adjoint bridge | **OPEN; generic algebra PROVED** | `H2B_EXACT_THEOREM510_FACTORIZATION_MISSING` |
| `G4` | `ANCHOR`: canonical nonzero normalization | **PROVED в Lean** | — |
| `G5` | `S1 + Montel`: local bound и nonzero strip-cluster | **OPEN; Montel core + anchor receivers PROVED** | `CENTERED_S1_WEIGHTED_PROJECTION_GAP` |
| `G6` | `S2`: every nonzero cluster equals `c*Xi*gamma` на той же subsequence | **OPEN; types/guard only** | body of `GlobalPositiveDefiniteUniqueness` |
| `G7` | strip Hurwitz transfer + Xi/RH interface | **PROVED conditional в Lean** | upstream `G2,G3,G5,G6` |

Итог compiler count:

```text
closed outright:       G1, G4
closed conditionally:  G7
open with proved core: G2, G3, G5
open typed main wall:  G6
```

## Что именно изменил 026

026 поставил запрещённый ранее exact-mode input честным способом:

```text
interval Sturm
+ Schur tail resolvent
+ exact even-index isolation
+ live continued fraction
+ Krawczyk containment
+ finite-plus-tail normalization.
```

Получены шесть exact-mode enclosures для
`m in {13,53,257}`, degrees `0/4`.

Это:

- закрывает `G3ExactModeIntervalEnclosure` на шести контрольных пакетах;
- закрывает eigenvalue-часть `HlambdaOuterLobeGate` на этих пакетах;
- снабжает `FiniteCoreThetaOrderWithTailBudget` proof-grade хвостами.

Это не:

- cofinal theorem;
- exact even-vs-odd sector ordering выбранной H2a-family;
- Theorem-5.10 bind;
- доказательство двух знаковых лемм;
- RH.

## Две знаковые леммы

```text
HlambdaLastPositiveZeroLtOne
  = REDUCED_TO(HlambdaOuterLobeGate)

DualThetaDominance
  = REDUCED_TO(FiniteCoreThetaOrderWithTailBudget)
```

Ни одна не убита. Полностью доказаны только reduction theorems.

После 026 ближайшие exact подзадачи идут строго так:

```text
1. outer point determinant:
     I0*h4(1)-I4*h0(1) > 0;
2. exact polynomial certificates P_(r,K) on bands and teeth;
3. assemble the resulting relative moment bound into G5/S1.
```

Новая sign-grid или ещё одна decimal ladder запрещены: следующий прогресс
должен быть Sturm/Bernstein/SOS/rational interval proof.

Следующая уже материализованная транзакция —
`027_hlambda_outer_lobe_gate.goal.md`; этот resync её только ставит первой в
очередь и не исполняет.

## Taint / dependency summary

```text
G2 OPEN ----\
             +--> G7 conditional roof --> RH not exported
G3 OPEN ----/
G5 OPEN ----\
             +--> G6 OPEN -------------/
```

`rh_of_canonical_strip_slots` остаётся правильной hole-free сборкой.
Она не превращается в unconditional RH, пока четыре открытых ворот не
получат concrete same-family proofs.

## Архитектурный firewall

Глобальный public mainline остаётся:

```text
T0-pd -> H-bridge -> H4 -> RH.
```

Эта семиворотная карта — точный Route-B challenger compiler и возможный
supplier к общей крыше. Resync не повышает Route B до mainline и не меняет
`ROUTE_B_STATE`.

Машинная версия:
`PROOF_COMPILER_SEVEN_GATES_2026-07-27.json`.
