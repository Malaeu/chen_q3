# ГОЛ 020 — 019R: T→X SAME-MODE NORMALIZATION LOCK + FOURIER K1

От: Mythos, по вердикту Прошки proshka/PROSHKA_COORDINATE_CROSSWALK_2026-07-27.md.
Статус: CHALLENGER / NOT_RH. BUS_010_VOID. Report-only / object lock / не теорема.
Диагноз 019: T_TO_X_MODE_NORMALIZATION_MISMATCH — I_j брали у L²-нормированной
x-функции, c_j у сырой t-моды; пропущенный множитель a_j=1/(√λ·N_j) mode-dependent.

## КОНВЕНЦИЯ (зафиксировать в отчёте)
t∈[−1,1], x=λt, y=λs; Fourier_x[h](y)=∫_ℝ h(x)e^{2πixy}dx; C=2πλ²;
БЕЗ √(2π)-префактора. Если у библиотечного оператора есть префактор —
записать его полем operator_prefactor, не угадывать.

## STEP 1 — SAME-MODE LOCK
Для j∈{0,4}: взять ОДНУ И ТУ ЖЕ сырую моду φ_j(t) конструктора 013 (без
предварительного рескейла центра). Из неё:
  N_j=√(∫_{−1}^1|φ_j|²dt), J_j=∫_{−1}^1 φ_j dt, c_j=φ_j(0);
  фаза ε_j∈{±1}: ε_j·J_j>0; заменить φ_j←ε_jφ_j (и J,c).
x-мода: h_j_x(x)=φ_j(x/λ)/(√λ·N_j); h_j_x(0)=c_j/(√λN_j); I_j_x=√λ·J_j/N_j.
ТРИ независимых scale-чека (НЕ усреднять, НЕ подгонять):
  scale_L2=1/(√λN_j) · scale_integral=I_j_saved/(λJ_j) · scale_center=h_j_L2_saved(0)/c_j
  — обязаны совпасть в бюджете точности.
μ тремя путями: mu_from_t=λJ_j/c_j · mu_from_x=I_j_x/h_j_x(0) ·
  mu_from_saved=I_j_saved/h_j_L2_saved(0) — совпасть; 0<μ_j≤1.
Канонический пакет ДВУМЯ маршрутами:
  Route A: D_x=√(I0_x²+I4_x²); htrial_A=(I4_x·h0_x−I0_x·h4_x)/D_x.
  Route B (сырые t-моды): htrial_B(λt)=(J₄φ₀(t)−J₀φ₄(t))/(√λ·√(J₀²N₄²+J₄²N₀²)).
Обязательно: htrial_A=htrial_B · ∫htrial_A=0 · ‖htrial_A‖₂=1 — без форсажа;
  ⟨h0_x,h4_x⟩=0 в точности солвера.
ПРЕ-ЧЕК 018 (решает, нужен ли повтор 320 полос): сравнить пакет, который
реально считал 013/018, с htrial_B; разность на арифметическом полу ⇒
018_CANONICAL_IDENTITY_CONFIRMED, повтор НЕ нужен; иначе — доложить,
повтор полос отдельным голом.
Failure codes: T_TO_X_L2_SCALE_MISMATCH · SOURCE_INTEGRAL_SCALE_MISMATCH ·
SOURCE_CENTER_SCALE_MISMATCH · PROLATE_MODE_ORTHOGONALITY_INSTRUMENT_GAP ·
CANONICAL_PACKET_NORMALIZATION_MISMATCH.

## STEP 2 — NO-FIT FOURIER K1 (явные координаты)
Backend A (прямой, из сырой t-моды):
  hat_hj_A(y)=(√λ/N_j)∫_{−1}^1 φ_j(t)e^{2πiλyt}dt
            = (2√λ/N_j)∫_0^1 φ_j(t)cos(2πλyt)dt (чётные вещественные).
Compressed eigenvalue: κ_j=J_j/c_j, μ_j=λκ_j; точное безразмерное утверждение:
  ∫_{−1}^1 φ_j(t)e^{2πiλ²st}dt = (μ_j/λ)·φ_j(s) при |s|<1 (строго внутри);
  эквивалентно hat_hj_A(y)=μ_j·h_j_x(y) при |y|<λ.
Backend B (глобальное продолжение, нормировка Phi_j_global_t(s)=φ_j(s) при |s|<1):
  hat_hj_B(y)=μ_j/(√λN_j)·Phi_j_global_t(y/λ) для ВСЕХ y.
  Zero-extended моду снаружи полосы НЕ использовать.
K1-чеки: y=0 (трёхчлен hat_A(0)=I_j_x=μ_j·h_j_x(0)=hat_B(0), без присваиваний);
  внутри: y=λ/4, λ/2, λ(1−1e−8); при y=λ — interior-limit/продолжение, НЕ
  midpoint zero-extension; снаружи: λ(1+1e−8), 2λ, 5λ — с осцилляторными
  гвардами G3 из 019 (независимые квадратуры!).
Канонический transform: hat_htrial=(I4_x·hat_h0−I0_x·hat_h4)/D_x;
  обязательный hat_htrial(0)=0 без форсажа (ε₀-гвард G1 из 019).
Fejér/residual НЕ запускать, пока все same-mode и Fourier K1 не зелёные.

## ЗАПРЕТ (STRONGEST ATTACK Прошки)
НЕ чинить старые числа делением μ_old на λ или λ^{3/2} — a_j mode-dependent;
единственный ремонт: пересчитать J,N,c от той же сырой моды.

## ПОРЯДОК (FINAL Прошки)
1 crosswalk · 2 пакет A/B · 3 решение по 018-идентичности · 4 μ=λJ/c ·
5 Fourier K1 · 6 только затем Fejér/residual (следующим голом).
Замороженный Lean-контракт Пуассона остаётся замороженным; получит номер
после K1-green.

## Отчёт
020_prolate_coordinate_lock.answer.md: все чеки таблицами, ε₀, коды.
РОВНО ОДИН primary: PROLATE_COORDINATE_AND_NORMALIZATION_LOCK_GREEN ·
T_TO_X_MODE_NORMALIZATION_MISMATCH · COMPRESSED_FOURIER_LAMBDA_FACTOR_MISMATCH ·
CANONICAL_PACKET_MISMATCH · GLOBAL_PROLATE_CONTINUATION_MISMATCH ·
GLOBAL_CONTINUATION_FLOOR_UNRESOLVED.
STATE не трогать. Зеркало по правилу 014 после закрытия.
