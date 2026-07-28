# STATUS: OPEN — BAND-ZERO IDENTITY KILLED; 031 RETARGETED (конспект Mythos; полный текст: uploads чата 2026-07-28)

```yaml
BAND_ZERO_CANDIDATE: KILLED (EXACT_BAND_ZERO_IDENTITY_IMPOSSIBLE)
EDGE_FACTOR_REQUIRED: false  ->  ветка (c) не запускается
NEXT: 031_PriorityBandPositivePartBudget
CLAIMS: band_response_zero_rigidity ABSTRACT/PAPER ·
  psi_nonzero_m257 FINITE_CELL/ARB · priority_positive_part_budget FINITE_CELL/ARB
```

## Теорема BandResponseZeroRigidity (перо, доказано)
Ψ аналитична на |t|<1, S_r(z)=Σ_{n=1..r}Ψ(nz). Если S_r=0 на непустом
открытом подынтервале ⇒ (тождественность) S_r≡0 на |z|<1/r ⇒ разложение
S_r(z)=Σ_k c_k (Σ_{n=1..r} n^k) z^k; степенные суммы Σn^k>0 ⇒ все c_k=0
⇒ Ψ≡0. Противоречие с 027: Ψ(1/√257)>0 (полная мода, запас 19.078).
⇒ S_255≢0, S_256≢0. Моя (Mythos) гипотеза band-тождества опровергнута.

## Что вместо: числа 030 объясняет малый НЕнулевой фактор
Кандидат-дискриминатор (называть, не занулять): Jacobi divided-difference
Green identity: L_{Θ4}δ = ((Θ4−Θ0)/2)·b0;
S_r(z) = ((Θ4−Θ0)/2)⟨Y_{r,z},b0⟩_ω + B_{r,z} (boundary ledger).
D_r(z) := ⟨Y,b0⟩ + 2B/(Θ4−Θ0) — DISCRIMINATOR (факторизовать/оценивать).
Trapezoid: S*_r = r·T_r(Ψ) − ½Ψ(0); exact tooth zero ⇔ T_r(Ψ)=Ψ(0)/(2r)
(только зубья, не полосы). Poisson переводит, знака не создаёт.

## Контрфакт (мой вопрос): даже при band-нуле осталось бы 239 полос
(r=16 частичная, 17..254 полные) + 238 зубьев; всё FINITE_CELL.

## Прогнозы (зарегистрированы): R1 rigidity убивает band-zero; R2 δ-строка
удовлетворяет точному inhomogeneous Jacobi recurrence; R3 priority
positive-leakage budget крошечный и проходит; R4 никакого cofinal/полного
знака из 031. Вероятное падение: source-lock скаляра S↔E или terminal
boundary ledger; при затыке Green — budget не блокировать (Thm C независим).

## Контракт 031 — дословно в 031_priority_band_positive_part.goal.md
(Thm A rigidity + Thm B recurrence + Thm C crosswalk/budget; планты P1–P8;
коды: BAND_ZERO_KILLED_PRIORITY_LEAKAGE_BUDGET_PROVED · ..._PROOF_GAP ·
S_TO_E_WEIGHT_CROSSWALK_GAP · PRIORITY_ENCLOSURE_NOT_SPENDABLE ·
RECURRENCE_PHASE_LOCK_MISMATCH · JACOBI_GREEN_IDENTITY_GAP; флаги:
JACOBI_DIVIDED_DIFFERENCE_IDENTITY_PROVED · EXACT_TOOTH_ALIAS_IDENTITY_PROVED)

Meta: убито S_255≡0/S_256≡0/auto-edge-factor; smallest gap =
RemainingWindowPositivePartOrSignSupplier; score 5/5.
