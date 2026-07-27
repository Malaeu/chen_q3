# STATUS: COORDINATE CROSSWALK PROVED

```text
MU_FORMULA: CORRECTED
λ^(3/2) HYPOTHESIS: YES as raw t-mode normalization asymptotic; NO as coordinate factor in μ
019 SEMANTIC DIAGNOSIS: T_TO_X_MODE_NORMALIZATION_MISMATCH
RESIDUAL: correctly remains blocked
```

Формула μ_j = I_j/h_j(0) была правильной. Ошибка 019: I_j бралось у L²-нормированной x-функции, а h_j(0) — у сырой ODE t-функции. Источник: h̃_j(x)=PS_{j,0}(2πλ², x/λ), затем L²-нормировка в dx; Lean-контракт требует I_j, h_j(0), χ_j от ОДНОЙ И ТОЙ ЖЕ L²-нормированной x-функции.

## 1. Точный пересчёт t↔x
t∈[−1,1], x=λt. φ_j(t) — сырая мода конструктора 013 в любой нормировке.
N_j=(∫_{−1}^1|φ_j|²dt)^{1/2}, J_j=∫_{−1}^1 φ_j dt, c_j=φ_j(0); фаза: J_j>0.
h_j^x(x)=φ_j(x/λ)/(√λ·N_j) при |x|<λ. Норма: ‖φ(·/λ)‖_{L²(dx)}=√λ·N_j ⇒ множитель a_j=1/(√λ N_j).
h_j^x(0)=c_j/(√λ N_j). I_j^x=√λ·J_j/N_j.
NO-FIT MULTIPLIER: μ_j = I_j^x/h_j^x(0) = **λ·J_j/c_j**. Без √(2π), без сохранённого I вместе с сырым c.

## 2. Операторное подтверждение λ
y=λs: ĥ_j^x(λs)=(√λ/N_j)∫φ_j(t)e^{2πiλ²st}dt. Безпрефакторный K_λφ=∫_{−1}^1 φ e^{2πiλ²st}dt, K_λφ_j=κ_jφ_j ⇒ μ_j=λκ_j; при s=0: κ_j=J_j/c_j ⇒ μ_j=λJ_j/c_j. Если библиотечный оператор с префактором λ — его eigenvalue уже μ_j; записать полем operator_prefactor, не угадывать.

## 3. Что произошло в 019
μ_old = I_j^x/c_j = a_j·(λJ_j/c_j) = a_j·μ_j. Числа 27–180 — почти не Fourier-множители, а пропущенные амплитудные a_j=1/(√λN_j). Отсюда расхождение бэкендов уже в y=0 на 96–99%.

## 4. Проверка гипотезы λ^{3/2}
Coordinate ledger: dx→λ; L²-норма raw pullback→√λ; амплитуда нормировки→1/√λ (и /N_j); I_j^x→√λ·J_j/N_j; центр→c_j/(√λN_j); μ→λJ/c.
⇒ Якобиан+L²-нормировка дают √λ в интеграле, НЕ λ^{3/2}; μ несёт ровно ОДИН λ.
Где λ^{3/2} живёт: в сырой Frobenius-норме N_j(λ). Из данных 019: N_0·λ^{3/2}≈0.0926/0.0896/0.0889 (m=13/53/257), N_4·λ^{3/2}≈0.1309/0.0970/0.0904 ⇒ совместимо с N_j≍C_jλ^{−3/2} — FIT_NOT_LAW, свойство сырой нормировки, не координатный закон. Тогда a_j≍C_j^{-1}λ — линейный рост (~11λ), он и виден в μ_old.
Вердикт: λ^{3/2} в обратной сырой норме — DIAGNOSTICALLY PLAUSIBLE; λ^{3/2} как поправка к μ — FALSE; точная поправка: dimensionless J/c умножить на λ.

## 5. Канонический пакет прямо в t-координате
После фазировки J_0,J_4>0:
**h_λ(λt) = (J₄φ₀(t) − J₀φ₄(t)) / (√λ·√(J₀²N₄² + J₄²N₀²))** (использована точная ортогональность мод).
Инвариантен к независимому рескейлу φ; ‖·‖₂=1; ∫h_λ=0 тождественно; не использует сохранённые I_j. Дешёвый object judge для 018.

### Поправка к статусу 018
018_INSTRUMENT_AND_COVERAGE_GREEN · 018_TESTED_PACKET_SINGLE_SIGN_DIAGNOSTIC_GREEN · 018_CANONICAL_SOURCE_PACKET_IDENTITY: RECHECK_REQUIRED.
Модальные рескейлы различались (38.95 vs 27.55 при m=13) — не общий скаляр. Сравнить старый packet с raw-t формулой: разность на арифметическом полу ⇒ повтор 018 не нужен; иначе — 320 полос заново на исправленном пакете.

[UPDATED PATCH 019R и STRONGEST ATTACK — вынесены в гол 020 дословно.]

# STRONGEST ATTACK
Не чинить старые числа делением на λ или λ^{3/2} — это снова fitting: пропущенный a_j mode-dependent (различается между h₀ и h₄). Единственный ремонт: пересчитать J,N,c от ТОЙ ЖЕ сырой моды; затем μ=λJ/c.

# FINAL PROPOSAL (порядок)
1 rebuild same-mode t→x crosswalk · 2 canonical packet Route A и raw-t Route B · 3 решить, тестировал ли 018 канонический пакет · 4 μ=λJ/c · 5 inside/outside Fourier K1 · 6 только затем Fejér/residual.

# META
019 mismatch сведён к одному равенству: **μ_j = λ·∫φ_j/φ_j(0)**.
Убито: μ=I_L2/h_raw(0); λ^{3/2} как поправка μ; починка одной константой; автоматическая идентификация packet 018 с source packet.
Smallest gaps: ProlateTToXSameModeNormalizationCrosswalk → CanonicalPacketFourierK1.
