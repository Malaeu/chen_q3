# ГОЛ 029 — DECISIVE K-ESCALATION (директива Прошки дословно)

От: Mythos, из proshka/PROSHKA_028_KILL_ADJUDICATION_2026-07-27.md.
Вердикт судьи: kill-код 028 ОТОЗВАН → в леджере заменить на
BAND_TAIL_DOMINATED_AT_K026 (+ REGISTERED_POSITIVITY_PREDICTION_FALSIFIED).
DualThetaDominance: OPEN. Лемма A (027) не затронута.
Статус: CHALLENGER / NOT_RH. BUS_010_VOID.

```text
TARGET:
029_DecisiveFiniteCoreThetaOrder_KEscalation

RETRACT:
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL from goal 028
REPLACE WITH:
BAND_TAIL_DOMINATED_AT_K026

INPUTS:
- exact Theta intervals from 026;
- live continued-fraction tail;
- exact coefficient balls;
- canonical Psi convention;
- bands r=256,255;
- witness interval from 028.

STEP 0 — strengthen checker:
Recompute from coefficient balls:
  finite_L2_sq; tail_L2_sq interval; scale; J = 2*scale;
  epsilon = scale*|last coefficient|; epsilon_Psi.
Do not trust stored J/epsilon intervals as primitive inputs.

STEP 1:
Increase coefficient cut by dK=20:
  degree 0: Ncut=914;  degree 4: Ncut=920.
Same certified Theta intervals; live recessive continued-fraction
boundary; terminal ratio = 0 запрещён.

STEP 2:
Rebuild exact rational: Psi core, E_core, epsilon_Psi, band polynomials.
For r in {256,255} construct:
  L = P_center - E_core - r*epsilon_Psi
  U = P_center + E_core + r*epsilon_Psi
Check: both full bands; all relevant teeth; old strict witness interval.

STEP 3:
If neither decisive, repeat exactly once with dK=40. No third escalation.

RETURN EXACTLY ONE:
DUAL_THETA_DOMINANCE_PROVED_PRIORITY_BANDS   (iff L >= 0 везде выше)
DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL      (iff U < 0 on strict rational interval)
K_ESCALATION_INCONCLUSIVE                    (otherwise; после dK=40 -> representation shift)

FORBIDDEN:
- no inference from failure of L>=0 to U<0;
- no adjusted-target verdict mislabeled as lemma kill;
- no sign samples; no mu:=1; no coefficient centers as exact;
- no cofinal claim; no pivot before a true U<0 certificate.
```

Registered prediction судьи (до результата): негативное минимальное ядро
компенсируется отброшенным recessive-хвостом; после dK=20 настоящего U<0
не появится; вероятный провал — значение столь близко к нулю, что и dK=40
останется inconclusive.

Отчёт: 029_decisive_k_escalation.answer.md + обновлённый
FINITE_CORE_THETA_CERT.json (checker по STEP 0). STATE не трогать.
Зеркало по правилу 014 после закрытия.
