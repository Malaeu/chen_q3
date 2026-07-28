# ГОЛ 031 — BAND RIGIDITY + PRIORITY POSITIVE-PART BUDGET (контракт Прошки дословно)

От: Mythos, из proshka/PROSHKA_031_DIRECTIVE.md. Ключевое: кандидат
S_r ≡ 0 на полосе УБИТ пером (BandResponseZeroRigidity: степенные суммы
Σn^k > 0 ⇒ все c_k = 0 ⇒ Ψ ≡ 0 — противоречие с 027: Ψ(1/√257) > 0,
запас 19.078). EDGE_FACTOR_REQUIRED=false ⇒ ветка (c) НЕ запускается;
вместо неё — positive-part budget. Запрещено навсегда: доказывать
S_r≡0 на открытой полосе. Статус: CHALLENGER / NOT_RH. BUS_010_VOID.
Исполнять ПОСЛЕ 032. Ниже — контракт судьи дословно.

```text
# GOAL 031 — BAND RIGIDITY + PRIORITY POSITIVE-PART BUDGET

STATUS:
CHALLENGER / NOT_RH
FINITE CELL m=257 ONLY
No cofinal-family claim.

PRIMARY TARGET:
031_PriorityBandPositivePartBudget

PURPOSE:
1. Kill the proposed exact identities
     S_255 ≡ 0
     S_256 ≡ 0
   on open bands.

2. Replace pointwise sign on the two priority bands by an exact weighted
   positive-leakage budget consumable by the repaired S1 route.

3. Record the Jacobi divided-difference identity as the nonzero symbolic
   discriminator. Do not use it to claim a sign.

====================================================
SOURCE LOCKS
====================================================

Consume:

- 027_hlambda_outer_lobe_gate.answer.md
- 028R_finite_core_theta_order_audit.answer.md
- 029_decisive_k_escalation.answer.md
- 030_coupled_full_sum_response.answer.md
- COUPLED_FULL_SUM_RESPONSE_CERT.json
- coupled_full_sum_response_certificate.py
- exact source phase
- exact midpoint convention

====================================================
THEOREM A — BAND RESPONSE ZERO RIGIDITY
====================================================

Prove:

If Psi is analytic on |t|<1 and

  S_r(z) = sum_(n=1)^r Psi(n*z)

vanishes on a nonempty open interval contained in |z|<1/r,
then Psi vanishes identically on |t|<1.

Instantiate at:

  r = 255
  r = 256

Consume the certified 027 witness:

  Psi(1/sqrt(257)) > 0.

Conclude:

  neither exact band-zero identity is possible.

====================================================
THEOREM B — SOURCE RECURRENCE
====================================================

Using the exact phase-correct rows, prove:

  L_Theta4(delta)
    = ((Theta4 - Theta0)/2) * b0,

where:

  delta = (b4 - b0)/2,
  b0_0 = b4_0 = 1.

Derive the exact finite-Q Green identity with:

- correct symmetrizing weights;
- explicit lower boundary term;
- explicit terminal boundary term;
- no terminal ratio set to zero.

This is a representation result only.
It must not emit PASS/KILL for DualThetaDominance.

====================================================
THEOREM C — S-TO-E CROSSWALK
====================================================

For

  z = 1/(lambda*v),
  u = 1/v = lambda*z,

prove exactly:

  E_star(h_lambda,u)
    = -(I0*I4/D) * sqrt(z/lambda) * S_lambda(z).

For 0 <= sigma < 1/2 define:

  Delta_prio(sigma)
    =
    integral_(u=1/lambda)^(lambda/255)
      max(E_star(h_lambda,u),0)
      * u^(-sigma) du/u.

Prove:

  Delta_prio(sigma)
  <=
  (I0*I4/D) * lambda^(-sigma-1/2)
  * sum_(r in {255,256})
      eps_r
      *
      [
        (1/r)^(1/2-sigma)
        -
        (1/(r+1))^(1/2-sigma)
      ]
      /
      (1/2-sigma),

where:

  eps_r = max(0, -lower_full_sum_r)

is read as an exact rational from the 030 certificate.

Teeth have Lebesgue measure zero and do not enter this integral.
Do not infer any pointwise tooth sign from that fact.

====================================================
K1 PLANTS
====================================================

P1 — constant:
  Psi(t)=1 gives S_r=r.
  The zero-rigidity detector must reject band-zero.

P2 — monomial:
  Psi(t)=t^(2k) gives

    S_r(z)
    =
    z^(2k) * sum_(n=1)^r n^(2k).

  The power-sum multiplier must remain exact.

P3 — 027 witness:
  Any path deriving Psi≡0 must collide with

    Psi(1/sqrt(257)) > 0.

P4 — zero mass:
  Psi(t)=t^2-1/3 has zero integral but nonzero star sum.

P5 — Jacobian:
  For control S(z)=-1 on one rational band, the transformed positive-part
  integral must match the closed form.
  Dropping du/u = dz/z must fail.

P6 — sign crosswalk:
  Flip S to -S.
  Positive and negative leakage roles must interchange.

P7 — tooth mutation:
  Change finitely many tooth values.
  The Lebesgue positive-part budget must remain unchanged,
  while pointwise DualThetaDominance changes.

P8 — recurrence collision:
  Set Theta4=Theta0 and use the same normalized recessive solution.
  The divided-difference forcing and delta must both collapse to zero.

====================================================
PRIMARY VERDICT CODES
====================================================

BAND_ZERO_KILLED_PRIORITY_LEAKAGE_BUDGET_PROVED

iff:
- Theorem A is proved;
- Theorem C is proved;
- all K1 plants fire;
- exact 030 rational enclosures are consumed.

BAND_RESPONSE_RIGIDITY_PROOF_GAP

iff:
- the analytic/power-sum injectivity theorem is not completed.

S_TO_E_WEIGHT_CROSSWALK_GAP

iff:
- the exact scalar, variable change, or Jacobian does not source-lock.

PRIORITY_ENCLOSURE_NOT_SPENDABLE

iff:
- the exact 030 lower envelopes cannot be converted into the one-sided
  leakage budget.

RECURRENCE_PHASE_LOCK_MISMATCH

iff:
- the two phased coefficient rows do not satisfy one common recurrence.

JACOBI_GREEN_IDENTITY_GAP

iff:
- the divided-difference recurrence is proved but the boundary ledger is not.

SECONDARY FLAGS:

JACOBI_DIVIDED_DIFFERENCE_IDENTITY_PROVED
EXACT_TOOTH_ALIAS_IDENTITY_PROVED

====================================================
FORBIDDEN
====================================================

- no S_r≡0 claim on an open band;
- no new dps/depth ladder;
- no coefficient centers as exact;
- no zero mass => tooth zero inference;
- no deletion of midpoint conventions;
- no pointwise DualThetaDominance claim from an integral budget;
- no finite-cell => cofinal-family promotion;
- do not modify Lemma A / result 027.

====================================================
VALIDATION
====================================================

- independent checker imports neither generator nor Arb;
- exact rational replay of 030 lower envelopes;
- symbolic replay of all K1 plants;
- source hashes locked;
- STATE untouched;
- BUS_010 not created.
```

Отчёт: 031_priority_band_positive_part.answer.md (+ артефакты по VALIDATION).
STATE не трогать. Зеркало по правилу 014 после закрытия.
