# PROSHKA MAP 807341E7 — factual audit

## STATUS: CONDITIONAL — CORE MAP PASSES; STATUS/SCOPE REPAIR REQUIRED

```yaml
PRIMARY: MAP_807341E7_FACTUAL_AUDIT_REPAIR_REQUIRED

MUNTZ_4_OF_4: PASS
MUNTZ_SORRY_ADMIT: NONE
MUNTZ_PROJECT_AXIOMS: NONE
MUNTZ_STANDARD_AXIOMS:
  - propext
  - Classical.choice
  - Quot.sound

FOUR_OPEN_FRONTS: PASS_WITH_SCOPE_REPAIR
GOAL_051_SCOPE: PASS
H2B_CLOSED: false
H2A_STILL_REQUIRED: true
ROUTE_PROMOTION: false
RH_CLAIMED: false

MAP_GLYPH_REPAIRS_REQUIRED:
  - T_ROOF
  - G4_ANCHOR
  - BETA5B
  - BETA8D
  - SLOT_H2B_SPLIT

G6_DESCRIPTION_OVERCLAIM: true
GOAL_052_MANIFEST_CARD_MISSING: true
```

## 1. Müntz действительно 4/4

**PASS.**

- `hRm` закрыт commit-ом `d3ca3c9e…`: exact-class `Rminus` analyticity и Mellin absolute payload.
- `habs` и окончательная exact-class assembly закрыты commit-ом `79d80630…`. Этот commit явно перечисляет `hG`, `hRm`, `hRp`, `habs`, сообщает full standalone build `8050` jobs, отсутствие holes и стандартный axiom profile.
- `continued_window_identity_v3Class` буквально потребляет все четыре supplier-а в одном theorem.
- Ledger подтверждает **4/4**, отсутствие holes и зависимости только от стандартной тройки.

Точная формулировка:

```text
sorry/admit-free: YES
project-axiom-free: YES
literally axiom-free: NO
standard Lean axioms only: YES
```

Я не перезапускал `lake build` в своей среде; это **pinned-source + committed validation ledger audit**.

## 2. Четыре open-front указаны правильно, но два описаны слишком оптимистично

Набор фронтов можно оставить:

```text
G2 — H2a
G3 — H2b
G5 — S1 / Montel supply
G6 — Müntz → S2
```

Canonical roof действительно требует отдельные `SlotH2a`, `SlotS1`, `Theorem510RealZeroBridge` и `SlotS2`.

Но нужны две правки:

- **G5** — это не только «знак-supplier». Concrete local boundedness и производство **ненулевого cluster** всё ещё открыты. Lean закрывает generic Montel machinery, не concrete family supply.
- **G6** — не «формально вставить window identity в S2». `SlotS2` требует идентифицировать **каждый ненулевой cluster** как `c·Xi·γ0` с фиксированным zero-free gauge. Для этого нужны same-family, cofinal, normalization и locally-uniform tail control. Аналитичность четырёх Müntz-компонент этого не даёт.

То есть четыре front-а остаются четырьмя, но **G6 — полноценная S2-стена**, не thin wiring.

## 3. Goal 051 описан правильно

**PASS.**

Goal 051 — только **M1**, то есть positive-definite weighted self-adjoint operator → similar Hermitian matrix → real charpoly spectrum. Verdict прямо фиксирует:

- M1 ещё не материализован в Lean;
- M1 не закрывает весь CvS §5;
- H2b не закрыт;
- H2a `SIMPLE_EVEN` остаётся обязательным;
- M2/M3 и при необходимости M4 остаются;
- Route B не повышается.

Поэтому строка:

```text
M1 = β6/β8d keystone only
```

корректна.

## 4. В §4 есть реальные status-glyph drift

Нужно исправить минимум следующее:

1. **`T-Roof`** сейчас `⏳`, хотя `rh_of_canonical_strip_slots` уже Lean-proved как условный theorem. Должно быть `✅ conditional theorem`.
2. **G4 Anchor**: production Lean доказывает `SlotAnchor ... 0`, а не anchor в `i/4`. `centeredXi 0 ≠ 0` пока отдельный blocker.
3. **β5b** должен быть `✅`: plain quotient descent уже Lean-proved.
4. **β8d** должен быть `✅`: `zerosRealOn_of_hermitian_charpoly_mul` уже Lean-proved. M1 нужен для отдельного weighted-self-adjoint → Hermitian bridge.
5. **SlotH2b** надо разделить: conditional `selectedFamily_realZeros` — Lean theorem из H1 + H2a + h510; concrete `Theorem510RealZeroBridge` supplier — открыт.
6. Commit `79d80630` реален, но в pinned `MANIFEST.md` нет отдельной пары `052_*.goal.md` / `052_*.answer.md`. Поэтому в MAP лучше написать **commit-labeled Goal 052**, пока bus-card не материализован.

## Итог

Математическое ядро MAP сохраняется. Навигатор требует docs-only repair.

Не менять Lean и route state. Исправить только **MAP.md**, сохранив:

```text
exactly four open-front buckets
CHALLENGER / NOT_RH
Bus 010 VOID
Müntz 4/4
M1 ≠ H2b closure
```
