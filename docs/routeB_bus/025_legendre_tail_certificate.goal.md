# ГОЛ 025 — LEGENDRE RECESSIVE TAIL CERTIFICATE (директива Прошки дословно)

От: Mythos, из вердикта Прошки PROSHKA_PEN_GO_2026-07-27 (перо получило GO;
приборных sign-ходов больше НЕТ; это ПАРАЛЛЕЛЬНАЯ дорожка к 023/residual).
Статус: CHALLENGER / NOT_RH. BUS_010_VOID.

```text
TARGET:
G3ExactModeIntervalEnclosure_LegendreRecessiveTail

PRIMARY THEOREM:
LegendreRecessiveTailCertificate

LOCKED PARAMETERS:
- spheroidal order = 0
- degree n = 0 or 4
- DLMF parameter G = gamma^2
- DLMF eigenvalue Lambda
- project eigenvalue Theta = Lambda + G

PROVE / CERTIFY:
1. exact DLMF A_k, B_k, C_k recurrence;
2. K0 condition:
     N0 >= 5
     N0*(N0+1) - Lambda_upper >= 31*G/24;
3. invariant ratio cone [0,1/2];
4. contraction <= 3/16;
5. interval continued-fraction tail;
6. sup, L2, derivative and Fourier tail bounds;
7. finite core whose final row consumes the tail-ratio interval;
8. normalization using the full finite-plus-tail budget.

FORBIDDEN:
- no terminal ratio = 0;
- no finite eigenpair identified with infinite mode;
- no mu := 1;
- no float values wrapped in zero-width balls;
- no further sign grid.

VALIDATION PLANTS:
- replacing tail interval by {0} must alter the certified core;
- n=4 replaced by n=2 must fail source lock;
- deleting the L2 tail must fail normalization enclosure;
- widening Lambda interval must widen the ratio enclosure according to (I).

SUCCESS:
G3_EXACT_MODE_INTERVAL_ENCLOSURE_PROVED

FAILURE:
G3_COARSE_EIGENVALUE_INTERVAL_MISSING
G3_TAIL_CORE_INTERVAL_NEWTON_GAP
G3_NORMALIZATION_TAIL_BUDGET_GAP
```

## Конверт Mythos
Полные формулы сертификата (p_k, r_k, d_k; конус ρ∈(0,1/2]; сжатие 3/16;
диаметр ½·(3/16)^L + (12/(13G))·(Λ₊−Λ₋); хвосты T1/T∞/T2/T′/TF) — в
вердикте proshka/PROSHKA_PEN_GO_2026-07-27.md, раздел 3; следовать им
дословно. Грубый interval для Λ — из Rayleigh / Gershgorin+tail resolvent /
interval Sturm; собственное значение усечённой матрицы как zero-width input
ЗАПРЕЩЕНО. Отчёт: 025_legendre_tail_certificate.answer.md (+ код из списка).
STATE не трогать. Зеркало по правилу 014 после закрытия.
