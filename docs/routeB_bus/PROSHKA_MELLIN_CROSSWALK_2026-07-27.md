# STATUS: CONDITIONAL — REPRESENTATION_PROGRESS

```text
ESTAR_CHAIN_LOCKED
GTRIAL_NEGATIVE_SQUARE_KILLED
HTRIAL_FORMULA_ACTIVE
UNWINDOWED_MELLIN_MULTIPLIER_CORRECT_CONDITIONAL
WINDOWED_MELLIN_RATIO_OPEN
```

Инспекция зафиксировала: E_star h(u)=√u Σ_{n≥1} h(nu), g_m = 1_[λ⁻¹,λ]·E_star h_m, λ_m=√m, затем g_{m,N}=P_{m,N}g_m. В цепочке нет сопряжения/свёртки/квадрата ⇒ negative-square для gTrial из Stage 1–2 не следует. Замкнутых Mellin-форм нет. Главный вывод: Меллин — правильный вычисляющий объект, но ОКОННАЯ ПОПРАВКА НЕ КОСМЕТИКА: в критической полосе может быть порядка ζ-члена.

## 1. Точный Mellin-множитель
p=s+1/2. Формально M(E_star h)(s)=ζ(s+1/2)·Mh(s+1/2) — точно в области абс. сходимости; продолжается в полосу |Re s|<1/2 ЧЕРЕЗ ТЕОРЕМУ МЮНЦА, ЕСЛИ ∫₀^∞ h = 0 (нулевая масса убивает u^{-1/2}-полюс) + гладкость/убывание.

## 2. Обязательная развилка H2-ZERO vs H2-POLE
H2-ZERO: A_m:=∫h_m=0 ⇒ тождество законно при |Re s|<1/2; точки 0,±σ в полосе.
H2-POLE: A_m≠0 ⇒ Мюнц-объект E_star° h = E_star h − A_m u^{-1/2}; фактический gTrial несёт явный pole-term A_m·J_λ(s), J_λ(s)=∫_{λ⁻¹}^λ u^{s-3/2}du=(λ^{1/2-s}−λ^{s-1/2})/(1/2−s); J_λ(−σ)/J_λ(0)≍λ^σ=m^{σ/2}. НЕЗАНУЛЁННЫЙ ПОЛЮС САМ ВОССОЗДАЁТ m^{σ/2}-РОСТ.
Registered prediction: либо ∫hTrial_m=0 точно, либо точная pole-cancellation; иначе centered S1 снова получает m^{σ/2}.

## 3. Exact window identity — сначала он
G_m(s):=M(g_m)(s) = ∫₀^∞ h_m(v) v^{p−1} D_{λ,p}(v) dv, где D_{λ,p}(v)=Σ_{v/λ≤n≤vλ} n^{−p} — конечная Dirichlet-window сумма. Это ПЕРВОЕ машинное reference identity. Только затем: G_m(s)=ζ(s+1/2)Mh(s+1/2) − R_m^−(s) − R_m^+(s) в H2-ZERO (R^−=∫₀^{λ⁻¹}, R^+=∫_λ^∞ от E_star h·u^{s−1}); в H2-POLE добавляется A_mJ_λ(s), tails — от регуляризованного E_star°.

## 4. Сильнейший planted failure для phase-route
∫h=0, h≢0, ω·h≥0 ⇒ 0=ω∫h=∫ωh>0 — противоречие. ⇒ НЕНУЛЕВОЙ zero-mass hTrial НЕ МОЖЕТ иметь постоянный знак/фазу. Правильный target: ω_m·E_star(hTrial)(u)≥0 на [λ⁻¹,λ] — знак рождается из СУММЫ (theta/Poisson), не из поточечного знака h.
Логика: zero mass + pointwise sign h → FATAL; zero mass + E_star-level sign → viable; nonzero mass → полюс обязан сократиться.

## 5. Три значения Меллина
Если ω_m g_m =: w_m ≥ 0 на окне: T_m(σ)/G_m^ω(0) ≤ (G_m^ω(σ)+G_m^ω(−σ))/G_m^ω(0); достаточный S1: sup_m этого отношения < ∞ для каждого σ<1/2. БЕЗ sign-теоремы не работает: |G(±σ)| идёт не в ту сторону (cancellation может занизить три значения при огромном абсолютном моменте).

## 6. Норма через Mellin–Plancherel
‖g_m‖₂² = (1/2π)∫_ℝ |G_m(it)|² dt ⇒ ρ_m = |G_m(0)| / (‖G_m(i·)‖_{L²}/√(2π)). В zero-mass ветке G_m(it)=ζ(1/2+it)Mh_m(1/2+it) − R_m(it). Всё из одного объекта: масса=G(0), S1-моменты=G(±σ) (вещественный интервал ζ(1/2±σ)), норма=вертикаль ζ(1/2+it) через Планшереля.

## ROUTE MAP
E_star линейный — PROVED · square на gTrial — KILLED · формула hTrial — ACTIVE · ∫hTrial=0 или полюс — NEXT DECISION · unwindowed ζ-multiplier — CONDITIONAL (Мюнц) · exact window kernel — PROVABLE NOW · phase/sign E_star h — OPEN (theta) · three-value S1 ratio — OPEN · norm ratio — OPEN · projected S1 — CONDITIONAL GREEN (+β).

## STRONGEST ATTACK
1) «ζ·Mh написано там, где ряд не сходится абсолютно» — недопустимо без: zero-mass/Мюнц-контртерма; теоремы продолжения; точной window-tail декомпозиции; равномерных ОТНОСИТЕЛЬНЫХ (не абсолютных) оценок хвостов.
2) «Три точных значения не контролируют абсолютный момент без sign-теоремы» — верно; phase/sign закрывается ДО трёхзначного механизма.

## FINAL PROPOSAL
Текущий goal (формула hTrial) НЕ перенаправлять. После его отчёта один target: EStarWindowedMellinCrosswalk:
1) finite-window identity G_m(s)=∫h v^{s−1/2}D_{λ,s+1/2}(v)dv;
2) ровно одна ветка: ESTAR_MUNTZ_ZERO_MASS_GREEN (∫h=0, ζ-multiplier) либо ESTAR_MUNTZ_POLE_CORRECTED_GREEN (явный A_mJ_λ);
3) точные определения R_m^±;
4) никакой «малости» поправок без отдельной relative bound.
Planted-failure validation: контрольный h≥0 с ∫h≠0 обязан показать G(−σ)/G(0)≍λ^σ; bounded ratio = имплементация потеряла полюс.
Failure codes: ESTAR_ZERO_MASS_SOURCE_MISSING · ESTAR_POLE_COUNTERTERM_OBJECT_MISMATCH · ESTAR_WINDOW_CORRECTION_DOMINATES · ESTAR_PHASE_ALIGNMENT_KILLED.

## META CLOSEOUT
Весь source front ANCHOR+S1 = одна функция G_m(s)=M(gTrial_m)(s): масса в 0, моменты в ±σ, норма на вертикали.
Убито: negative-square из линейности; перенос projected sign на source; формальная перестановка Σ/∫ в полосе; «window correction мала» без доказательства; pointwise phase-sign zero-mass hTrial.
Smallest gaps: hTrialExactFormulaAndMassFork → EStarWindowedMellinCrosswalk.
Cheapest decisive test: ∫₀^∞ hTrial_m(v)dv =? 0.
Progress class: REPRESENTATION_PROGRESS. Route score: 5/5.
