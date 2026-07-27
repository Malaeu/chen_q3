# ГОЛ 028 — FINITE CORE THETA ORDER WITH TAIL BUDGET (директива Прошки дословно)

От: Mythos, из proshka/PROSHKA_RESYNC_AUDIT_2026-07-27.md (аудит: 026/027
приняты со scope-тегами; 028 подтверждён как следующий адрес).
Статус: CHALLENGER / NOT_RH. BUS_010_VOID.

## Пред-шаг (закрыть RESYNC_MIRROR_SOURCE_GAP)
Добавить в зеркало и MANIFEST.md: PROOF_COMPILER_RESYNC_2026-07-27.md,
proshka/PROSHKA_RESYNC_AUDIT_2026-07-27.md, PROSHKA_PEN_REDUCTIONS,
027_answer. В compiler-ledger добавить поля scope (ABSTRACT | FINITE_CELL |
COFINAL_FAMILY) и verifier (LEAN | ARB_INTERVAL | PAPER | CONDITIONAL);
026/027 маркировать FINITE_CELL_{13,53,257}, не LEAN/COFINAL.

```text
TARGET:
RouteB.028_FiniteCoreThetaOrderWithTailBudget

SCOPE:
m in {13,53,257}; all canonical bands and all canonical teeth.

PRIMARY BACKEND:
rational Bernstein positivity with adaptive rational subdivision.
FALLBACK:
exact Sturm certificate for unresolved rational polynomials.

INPUTS:
- exact-mode finite-core coefficient balls from 026;
- exact Tinf tails from 026;
- positive J0, J4 intervals;
- canonical midpoint convention;
- exact band/tooth inventory.

PROVE ON EACH BAND:   P_(r,K)(z) >= r * epsilon_(Psi,K)
PROVE ON EACH TOOTH:  Pstar_(r,K) >= (r - 1/2) * epsilon_(Psi,K)

MANDATORY:
- consume finite-core coefficient uncertainty E_core AND infinite tail
  (вычитать ОБА: E_core + r*epsilon_Psi);
- exact coverage of all bands/teeth;
- reproducible rational certificate: FINITE_CORE_THETA_CERT.json
  (object_lock / bands / teeth / coverage по схеме Прошки);
- independent checker: rational-cover exactness, Bernstein transform,
  lower coefficient signs, tail consumption, полнота покрытия.

FORBIDDEN:
- no sample/grid sign; no coefficient centers treated as exact;
- no mu := 1; no dropping difficult bands; no cofinal-family claim.

VALIDATION ORDER (registered prediction: оба проходят с положительным
рациональным запасом):
1. m=257, r=256
2. m=257, r=255
3. all remaining bands and teeth.

SUCCESS:
FINITE_CORE_THETA_ORDER_WITH_TAIL_BUDGET_PROVED_ON_13_53_257
FATAL:
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL
  (+ exact rational isolating interval and negative upper bound)
BACKEND FAILURE:
BERNSTEIN_CERTIFICATE_INCONCLUSIVE -> execute exact Sturm fallback.
```

Отчёт: 028_finite_core_theta_order.answer.md + FINITE_CORE_THETA_CERT.json.
Успешный 028 = DualThetaDominance PROVED_ON_CELLS_{13,53,257}; НЕ
cofinal-теорема. STATE не трогать. Зеркало по правилу 014 после закрытия.
