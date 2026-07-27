# ГОЛ 027 — HLAMBDA OUTER LOBE GATE (директива Прошки дословно)

От: Mythos, из PROSHKA_PEN_REDUCTIONS_2026-07-27.md (перо: лемма A сведена
к двум скалярам; транспорт Sturm–Wronskian ДОКАЗАН пером).
ЗАВИСИМОСТЬ: исполнять ПОСЛЕ закрытия 026 — входы берутся из его выхода.
Статус: CHALLENGER / NOT_RH. BUS_010_VOID.

```text
TARGET:
HlambdaOuterLobeGate

INPUTS:
- certified interval for project eigenvalue Theta4  (из 026);
- exact finite Legendre cores phi0_K, phi4_K        (из 026);
- certified sup-tail bounds eps0_K, eps4_K          (из 026);
- positive source integrals J0, J4.

PROVE:
1. Theta4_lower > (17*pi^2/4)*lambda^2.
2. Psi_K(1/lambda) > eps4_K/J4_lower + eps0_K/J0_lower,
   где Psi_K(t) = phi4_K(t)/J4 - phi0_K(t)/J0.
3. Instantiate the paper theorem:
   h_lambda(x) <= 0 for all x in [1, lambda].

FORBIDDEN:
- no grid sign;
- no direct Sturm theorem on h_lambda;
- no truncated eigenvector as exact mode;
- no mu := 1;
- no theorem weakening.

VALIDATION:
- exact/rational or outward-rounded inequalities;
- tail interval genuinely consumed;
- endpoint midpoint handled separately.

SUCCESS:
HLAMBDA_LAST_POSITIVE_ZERO_LT_ONE_PROVED

FAILURE:
HLAMBDA_EIGENVALUE_BARRIER_GAP
HLAMBDA_OUTER_POINT_DETERMINANT_GAP
```

Отчёт: 027_hlambda_outer_lobe_gate.answer.md. Пером доказанный транспорт
(§2.1–2.3 вердикта) НЕ переписывать и НЕ ослаблять — только подставить два
скаляра. STATE не трогать. Зеркало по правилу 014 после закрытия.
