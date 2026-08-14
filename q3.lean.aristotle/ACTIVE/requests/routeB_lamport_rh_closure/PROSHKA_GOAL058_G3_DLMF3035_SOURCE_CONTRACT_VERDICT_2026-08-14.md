# Proshka verdict — Goal 058 G3 DLMF 30.3.5 source contract

- Date: 2026-08-14
- Living chat: `RH_März_2026 / Документирование конструктора`
- Chat turn: `request-6a7afc0e-2aec-83eb-a9ca-469b44c84f83-27`
- Natural reasoning time shown by UI: `4m 9s`
- Request attachment: `GOAL058_G3_DLMF3035_EVEN_CHARACTERISTIC_SOURCE_CONTRACT_2026-08-14.md`
- Request attachment local SHA-256: `52fd2acfc21763b6880cf7d6461046a0753dbf619e44608ae7db702bf9f9530d`
- `Answer now` / `Jetzt antworten`: not used

# STATUS: CONDITIONAL — RIGHT BRANCH READY; FULL SOLUTION-SET IFF NOT MATERIALIZED

```yaml
PRIMARY: DLMF3035_RIGHT_BRANCH_READY_FULL_SOLUTION_SET_IFF_MISSING
PRIMARY_COUNT: 1

RIGHT_BRANCH:
  verdict: ACCEPT
  code: DLMF3035_RIGHT_BRANCH_CROSSWALK_READY
  scope: ABSTRACT
  verifier: CONDITIONAL

FULL_SOLUTION_SET_IFF:
  verdict: NOT_MATERIALIZED
  code: G3_DLMF3035_SOURCE_THEOREM_NOT_LEAN_MATERIALIZED
  scope: COFINAL_FAMILY
  verifier: PAPER

EXECUTION: false
ARISTOTLE: NOT_AUTHORIZED
G1: OPEN
G3: OPEN
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Right branch

`DLMF3035_RIGHT_BRANCH_CROSSWALK_READY`: **ACCEPT**.

Это sound и noncircular в точном ограниченном смысле «готово к
материализации», а не «уже доказано под DLMF-именем». Текущая цепь строит
правую ветвь только из literal Jacobi-коэффициентов и contraction machinery:

```text
mode4BackwardTail
→ terminal-independent limit
→ mode4RightTailLimit
→ Riccati law
→ uniqueness in [0,1/2]
→ square-summable tail row
→ uniqueness of the square-summable Hermitian branch.
```

После literal тождеств DLMF 30.3.7

```text
alpha_(2q)         = mode4JacobiUpper G q
beta_(2q) - Lambda = mode4JacobiCenter G Lambda q
gamma_(2q)         = mode4JacobiLower G q
```

DLMF right-ratio map совпадает с `mode4TailMap`; terminal-zero approximants
совпадают с `mode4BackwardTail`, а предел — с `mode4RightTailLimit`. Эта цепь
не использует `mode4RootFunction`, characteristic equation, supplied root,
endpoint counts или desired solution-set theorem, поэтому circularity нет.
Граница обязательна: только current production domain с `hm`, `hK`, `hsep`,
`Λ ≤ 20`; split degree равен `2*(K-1)`, не `2*K`.

## Full solution-set iff

Полный DLMF 30.3.5 solution-set iff: текущего noncircular Lean-supplier нет.
Никакая current-tree theorem не доказывает полный контракт

```lean
mode4DLMF3035EvenCharacteristicEquation
    G Λ (2 * (K - 1))
  ↔
∃ j : ℕ,
  mode4ClassicalEvenEigenvalue G j = Λ
```

Локальный будущий adapter

```text
characteristic equation ↔ mode4RootFunction = 0
```

не является solution-set theorem. Текущие DLMF 30.8 coefficient-row
crosswalks идут от supplied row к project root и не дают обратного направления
или полноты solution set. Внутренний `mode4ClassicalEvenEigenvalue` определён
через finite-limit carrier; его идентификация с независимым classical
DLMF/Sturm–Liouville spectrum остаётся paper contract, а не Lean theorem.
Поэтому попытка получить полный iff только из current-tree объектов либо
вставляет DLMF 30.3.5 как binder, либо определяет source equation через project
root и становится tautological.

Typed stop остаётся:

```text
G3_DLMF3035_SOURCE_THEOREM_NOT_LEAN_MATERIALIZED
```
