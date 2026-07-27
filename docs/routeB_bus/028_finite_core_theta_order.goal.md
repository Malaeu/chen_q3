# ГОЛ 028 — FINITE CORE THETA ORDER WITH TAIL BUDGET

Статус: `CHALLENGER / NOT_RH`. `BUS_010_VOID`.

Основание: 026 поставил exact-mode cores и хвостовые шары; 027 закрыл
`HlambdaOuterLobeGate` на `m in {13,53,257}`. Следующий адрес из
`PROOF_COMPILER_RESYNC_2026-07-27.md`:

```text
FiniteCoreThetaOrderWithTailBudget
```

## Цель

Для каждого `m in {13,53,257}` построить proof-grade сертификаты конечных
полиномов `P_(r,K)` на всех canonical `(B-band)` и `(B-tooth)` интервалах,
включая отдельный midpoint-бюджет:

```text
P_(r,K) >= r * epsilon_(Psi,K)              on each band,
P_(r,K) >= (r-1/2) * epsilon_(Psi,K)        at each tooth midpoint.
```

Разрешён ровно проверяемый backend: exact Sturm, Bernstein-basis positivity,
rational interval subdivision или exact SOS.

## Запреты

- no sign grid;
- no float/high-precision sample promoted to proof;
- no `mu:=1`;
- no removal of the 026 exact-mode tail;
- no weakening of the canonical band/tooth coverage.

## Выход

Отчёт `028_finite_core_theta_order.answer.md` и воспроизводимый certificate
artifact. Если ни один backend не выбран без изменения theorem shape,
зафиксировать честную развилку backend-ов, не выдавая её за blocker.
