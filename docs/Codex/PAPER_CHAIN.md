# Бумажная цепь до RH — леджер доказательств (сжатая версия, состояние 2026-09-27 вечер)

Полная версия до сжатия (1859 строк, с происхождением вердиктов): `git show 43e31284:docs/Codex/PAPER_CHAIN.md`.

Крыша: `Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi` (`Goal058DirectGroundZeroEscape.lean:27`) — одна семья F с hzeros, hentire, hconv ⇒ RH.
F = selected Ferrers tracked ground transform вдоль одного tail reindex, c = 2πm, m = N = k+2; координата s = −Lz/2π.
Инвариант: одна и та же F во всех звеньях (`STOP: TWO_DIFFERENT_FAMILIES_USED`).
Статусы: PAPER_PUBLISHED (статья) · PAPER_OWN (наш текст; rev = проверен независимо) · PROSHKA_ONLY (вердикт без перепроверки) · LEAN (доказано в Lean) · OPEN · KILLED(shape) (опровергнута именно эта форма утверждения, не звено).

| Звено | Что утверждается | Бумага | Lean / локатор |
|---|---|---|---|
| G0 | объект, координата, нормировка, расписание m=N=k+2 | OPEN частично: selected trial scale закреплён (G4, 06.10); итоговая same-family сборка не завершена | семья определена в TailReindex |
| G1 · hfloorEv | одна постоянная β>0 для trial-complement floor | **KILLED(shape)** для буквальной выбранной семьи: единичные y_j⊥q_j с Re⟨y_j,(K_j−a_j)y_j⟩≤U_j→0 | `INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25` + `FLOOR_KILL_INDEPENDENT_AUDIT_2026-09-25`; constant-β приёмник есть, вход невозможен |
| G1 · hratioEv | residualEnergy/β² < 1 eventually | OPEN; constant-β wrapper неприменим, нужен cellwise ‖r_j‖/δ_j + новый потребитель | условный приёмник есть |
| G1 · hoddEv | β₀‖x‖² ≤ Re⟨x,(K−a)x⟩ на нечётном секторе | OPEN; мост из hfloorEv верен условно (PAPER_OWN rev), но его вход убит | условный приёмник есть |
| G2 | нули лагранжева многочлена строки вещественны | LEAN, **условно на G1** | `CCMFiniteWeilParity.lean:161` |
| G2b | перенос вещественности на Prop-5.9 transform той же строки | LEAN | `Proposition59GroundLagrangeZeroSetBridge.lean:231` |
| hentire | каждая F_k целая | LEAN | `G6N1SelectedFerrersTrackedGroundTransform.lean:761` |
| G3 | F трекает projected trial: нормировка × kernelL2 × √ratio → 0 на компактах | **OPEN — главная стена** (master:1278) | нет формулировки |
| hmode | sup‖w_m − D_n‖ ≤ C_n/m, центр 1/h0(0), 3/h4(0), моды 0/4, полное окно | PAPER_OWN rev + PROSHKA PROVED_PAPER (RPT:1120-1220) | hmode⇒W5/N2 в кандидате; сам hmode не Lean |
| hχ / hθ | следствия hmode | PAPER_OWN rev | hχ кандидат; формализация не завершена |
| G3c | projected trial → continuum trial (projection tail) | PAPER_OWN rev для той же selected shell при HMODE/chi и G4: O(m^(-1/4)) residual достаточен на открытой критической полосе (06.10) | существующий условный receiver; свежей сборки нет |
| G4 | CCM Lemma 7.3: k_λ → Ξ равномерно на полосах | PAPER_PUBLISHED arXiv:2511.22755 §7 L7.3 p.31; selected-shell scalar/phase crosswalk PAPER_OWN rev при принятом HMODE/chi (06.10) | импорт отсутствует |
| G5 | одна семья: вещественные нули + F → Ξ ⇒ RH (Гурвиц) | LEAN (3 стандартные аксиомы) | `Goal058DirectGroundZeroEscape.lean:27` |
| Сборка | tail reindex + G3 + G3c + G4 ⇒ hconv для той же F | OPEN | нет |

**Итог:** 14 звеньев. Закрыто на бумаге 8: LEAN 4 (G2 — условно на G1, G2b, hentire, G5), PAPER_PUBLISHED 1 (G4; selected-shell crosswalk проверен при HMODE/chi), PAPER_OWN rev 3 (hmode, hχ/hθ, selected-shell G3c). KILLED(shape) 1 (hfloorEv, constant-β). OPEN 5 (G0 частично, hratioEv, hoddEv, G3, Сборка). RH не доказана; `PX_RH_CLAIM: NOT_MADE`.

## Главное наблюдение
CCM в §8 arXiv:2511.22755 (p.32) называют ровно два недостающих шага своей программы:
«prove that its smallest eigenvalue … is simple and that its corresponding eigenvector ξλ is even» — это наш G1;
«establish that kλ provides a sufficiently accurate approximation to (a scalar multiple of) ξλ» — это наш G3 (+G3c).
Сопоставление с нашими объектами — вывод читателя, crosswalk матриц не записан. G1 и G3 — ядро RH, остальное — сантехника цепи.
25.09 убит постоянный complement floor: Weil-форма зануляет плоскость G, G'' (Ĝ(z) = −4ξ_ζ(1/2−iz), (G'')^ = −z²Ĝ ⇒ W(G,f) = W(G'',f) = 0 для любого оконного синтеза f; audit:58-78), и компрессия этой плоскости даёт кофинальные y_j⊥q_j с квотой ≤ U_j → 0.
Замена: cellwise масштаб δ_j>0 на каждой поздней ячейке буквального дополнения, затем полный residual ‖r_j‖/δ_j → 0 и новый cellwise consumer; δ_j нельзя подставлять в constant-β wrapper. Положительные δ_j этим kill не опровергнуты и не доказаны.

## Открытые звенья

### G0 · нормировка
- Selected trial scalar/phase закреплены в G4 (06.10); координата конечного преобразования s = −Lz/2π и расписание m=N=k+2 заданы в TailReindex.
- Открыто: довести итоговую сборку одной и той же ground-семьи F; trial crosswalk не заменяет G1/G3 и эту сборку.

### G1 · complement / cellwise floor (прежняя программа, OPEN)
- Носитель: фиксированный `P : CCMLemma73PreAnchorPort`, i_j = cofinal index, m_j = N_j = φ_P(j)+2, K_j = sourceCCMFiniteMatrix i_j, q_j = selectedFerrersFiniteCCMRow P j, a_j = Re(q_j*K_jq_j), r_j = (K_j−a_j)q_j.
- Открытое утверждение: для всех y⊥q_j (комплексно) `Re[y*(K_j−a_j)y] = Σ_u (K_j(u,u)−a_j)|y_u|² + 2Σ_u b_u Re(conj(y_u)(Hy)_u) ≥ δ_j‖y‖²`, δ_j>0 на всех поздних ячейках; затем ‖r_j‖/δ_j → 0 (полный residual) и проверенный cellwise consumer. Loewner-алгебра закрыта (`CCMFiniteWeilSourceCommutator.lean:282-341`, `G6N1SelectedFerrersHilbertPairing.lean:171-224`).
- Первый конкретный знак (CELLWISE_COMPLEMENT_SIGN, OPEN_FIRST_SIGN): единичный z_j⊥q_j с ‖K_jz_j‖≤ε_j→0; нужно τ_j = z_j*K_jz_j − q_j*K_jq_j > 0 и Schur `D_j − η_jη_j*/τ_j ≻ 0` на {q_j,z_j}⊥. Неположительный кофинальный свидетель τ_j убил бы cellwise positivity — не получен.
- Принятые PAPER-представления (не знаки): τ_j = −𝔏_m/ρ_m² (NULLPLANE_LEAKAGE_SIGN); 𝔏_m = T(m)+𝓡(m), |𝓡|≤B(m), |M_{m,k}(s_n)|≤2√m (COUPLED_DEFECT_SIGN); Robin-единственность и секант (ADJOINT_GREEN_MIX); веса W_k с одним переходом знака, k_*(m)/√m→√(3π/2) (SIGNED_ROBIN_KERNEL); Q_m = κ_m⁴𝒫_m(E₀,E₄), энергии в Robin-интервалах ширины ≤ G_m4^{−m}/8 (FULL_SCALAR_SIGN_CHAIN); 𝒬_m = a_mκ_mC_N − κ_m⟨v⊥,η⊥⟩_μ, a_m > 1+1/M (ABEL_CUMULATIVE_FORCING).
- Далее приняты: условный cone-критерий (GROUND_CENTERED_ABEL_DISCRIMINANT); чётность plane-axis (CONE_AXIS_GROUND_ANGLE); ρ_* ≥ ε_m/√(1+ω_*⁴) > 0 для первой пропущенной пары (PLANE_PROJECTIVE_DISPLACEMENT); абсолютная сходимость пропущенных рядов в форме Вейля (FIRST_OMITTED_COMPRESSION); 0 < 𝔈₀₀ ≤ 4Ω_m^{−4}𝔈₁₁ (COMPRESSION_SPECTRAL_SPREAD); |𝒪_m−𝒫_m^>| < ℓ_mE/16 при m≥2¹⁶ (LOG_SYMBOL_TRANSFER); same-side при ν>√m ≤ 2(log m)m^{−1/4}E₁₁ (DIVISOR_COLLAPSED_PRIME_CORRELATION).
- Спуск первого знака: τ_j → 𝔏_m → Q_m/p_c → Abel 𝒬_m → cone/axis → плоскость r → 𝔍_m → transfer (T) → 𝒫^all → same-side / prime-square → 𝒱^[0] → lag → SV → panel / first-node / log-peak → PC → C128. Текущее состояние C128 — в «Текущем фронте».
- Нижние ступени (PAPER, частично): |𝒰^(2)−𝒱| ≤ 12(1+log log m)E₁₁ (PRIME_SQUARE_HIGH_FREQUENCY); |R_{ε,m}| < 6E₁₁ (LARGE_PRIME_SQUARE_INTERIOR_OVERLAP); маржа lag 9E₁₁/80 только на 65536≤m≤e^120 (CONTINUOUS_LAG_DECAY); ∫|ρ′| ≤ E₁₁/√6 в |ξ|≤m/L² (HALF_LINE_DENSITY_VARIATION); |U^lattice−U^[K]| ≤ η_mE₁₁ < E₁₁/48 (LATTICE_VARIATION_WITNESS); U^[K] = 𝔉_m − 4𝒜_m (FINITE_COEFFICIENT_PANEL_MARGIN); |𝔭_m−𝔭_m^log| < 1/(6L) (FIRST_NODE_PEAK); контурное Z_m = Y_m+𝓔_m (LOGARITHMIC_MOMENT_PEAK). C₀=128, C_int=134, C₂=146 условны.
- Следующий ход: совместное выполнение двух условий C128 на одной исходной ячейке, либо знак индивидуального T_m (MT128); глобальный трек DOM — отдельно (см. фронт).

### G1 · hoddEv
- Открыто: β₀‖x‖² ≤ Re⟨x,(K−a)x⟩ для всех нечётных x eventually на той же F.
- Условный мост (PAPER_OWN rev, 25.09): независимый complement floor β и η = ‖(I−J)q/2‖² < 1/2 ⇒ hoddEv с β₀ = β; требует K=K* (доказано для CCM); η→0 лишь условно на hmode/hχ (`G6N1SelectedFerrersOddMassDecay.lean:1169`).
- Не поставщик: constant hfloorEv убит; действующие поставщики (`G6N1SelectedFerrersH2aSourceQuantities.lean:503`, `G6N1SelectedFerrersWeightedResidualComplementFloor.lean:174`) строят complement floor из odd floor — обратная подстановка циклична.
- Odd-sector floor на текущей source-полке KILLED (08-30). Повторный вход требует новой математики: прямая odd-коэрцитивность или signed odd head/tail Feshbach с равномерными константами — оба кандидаты, не доказаны и не авторизованы (ODD_SECTOR_FLOOR_DISCRIMINATOR:379,403).

### G1 · hratioEv
- Открыто: residualEnergy/β² < 1 eventually; в текущей форме неприменимо (β константа убита).
- Замена: ‖r_j‖/δ_j → 0 с полным residual относительно именно cellwise масштаба; нельзя заменять оценку полного остатка одной его частью.
- Следующий ход: только после δ_j>0; сформулировать и проверить новый cellwise consumer.

### G3 · tracking (стена, RH-уровень)
- Открыто: C_K(m,N)‖r‖/Δ + Tail + NormalizationError → 0 (master:1284-1289); равномерный decay joint defect r = (A/Z)[(K−aI)b − (K−aI)e], Z>0 (RQ:52-54 — тождество, не оценка).
- Частично: paired-window Mellin identity, Rminus crosswalk, Euler identity — PAPER_OWN rev (BRIEF_2026-09-22_FOKAS_PAIRED_WINDOW, REPORT_2026-09-22_FOKAS_RMINUS_CROSSWALK; FN:91-92 — представление, не оценка).
- Lean Fokas step 1: Mellin–Green тождество с нижним краем, перенос строки через sTrial к Mellin/Gwin с фазой (−1)^n при `CCMLemma73PreAnchorPort`; конечная paired-window формула при явной MellinConvergent каждого слагаемого — для выбранного источника не закрыта.
- SOURCE_TRANSFER (Mac, 03531e2a, PAPER): ошибка точной строки ≤ (Z·α+E)/(Z−E), без деления source-ошибки на gap; при hmode/hχ и хвостовых оценках вклад E исчезает. Открыта скорость m_j^{H/2}·√(log m_j)·α_j → 0 (достаточна для G3); m4/m8/m13: 0.03089/0.05534/0.06052 — диагностика, не хвост.
- Долг: «exact ground = trial» — не опровергнуто, не доказано. Живые механизмы: Fokas 1 (Mellin/Abel–Plana) или 2 (граничный член Штурма–Лиувилля), BRIEF:44-51.
- UNVERIFIED: контроль t−V = 3√2/4 (источник вывода не найден); ответ Прошки на Fokas-запрос в bus не сохранён.
- Прежний достаточный поставщик (OPEN, не текущий шаг): на исходной кофинальной семье построить независимые пороги μ_j с положительным B_{μ,j} на всём qhat_j⊥ и знаком Шура σ_j≤0; затем для тех же порогов доказать R_j²=r_j*B_{μ,j}^{−2}r_j=O_n(m_j^{−2n}) при каждом n. Это достаточный поставщик (T7), не установленный результат; точная форма и проверка — в текущем фронте.
- Уточнение потребителя 06.10 (PAPER rev): для конечной крыши нужны только компакты |Im z|<1/2. При прежних согласованных (T1)–(T6) достаточно α_m=O(m^(−1/4)(log m)^A), фиксированное A≥0; all-height T7 сильнее необходимого. Эта оценка α не доказана. [Вывод и независимая проверка](../routeB_bus/source_observability_2026-09-28/CRITICAL_STRIP_PROJECTION_SOURCE_AUDIT_2026-10-06.md).

### G3c · selected-shell projection (PAPER checked, 06.10)
- При принятом HMODE/chi и G4 исходный scaled trial h_m отличается от H=4h_CCM на всём окне на O(λ^-2). Точное E_star даёт ||f_m−K||=O(λ^-1/2), K=E_star(H), λ=√m.
- Фиксированный K чётен в log u по Пуассону, его логарифмическая производная в L². Концы окна совпадают, поэтому Fourier tail ≤ L||K'||/(2π(N+1)). Контрактивность той же проекции даёт ||(I−P)f_m||=O(m^-1/4)+O(log m/m).
- Множитель √log(m)m^(σ/2) оплачивается для каждого σ<1/2. Центр сохранён проекцией, его нормировка оплачена G4. Это selected trial, не ground F; произвольная production family всё ещё требует crosswalk в итоговой сборке. Независимый PAPER проход без существенных замечаний; Lean не запускался. [Вывод и источники](../routeB_bus/source_observability_2026-09-28/CRITICAL_STRIP_PROJECTION_SOURCE_AUDIT_2026-10-06.md).

### G4 · crosswalk
- Selected-shell crosswalk проверен на PAPER (06.10): a72 q=(chi0 A4 h4−3 chi2 A0 h0)/16 реализует CCM «suitably normalized» h_λ, с точной нулевой массой и пределом h_CCM при HMODE/chi. λ=√(k+2), c=2πλ²; chi2 обозначает полную моду 4.
- Production scale a73=4a72 даёт предел 4h_CCM, поскольку Mellin(E h_CCM)(−iz)=centeredXi(z)/4. Это не тождество trial=ground и не свежая Lean-сборка. [Формулы, первоисточник и независимая проверка](../routeB_bus/source_observability_2026-09-28/CRITICAL_STRIP_PROJECTION_SOURCE_AUDIT_2026-10-06.md).

### Сборка → hconv
- Открыто: одна теорема для той же F вдоль tail reindex из G3 + G3c + G4 ⇒ hconv ⇒ потребитель. Порядок: δ_j и масштаб → ‖r_j‖/δ_j + consumer → G3; G4/G3c параллельно; затем сборка; Lean после бумаги.

## Текущий фронт 06.10: отрицательное дно полной CCM
- Новый условный consumer, та же полная K_m и исходная последовательность; прежняя таблица G1/G3 остаётся OPEN.
- PAPER_OWN rev: гипотетический ноль w=delta+i gamma, delta>0, через source pair и оплаченный cutoff/Fourier projection даёт lambda_min≤−c m^delta/(log m)^(2delta) на каждой поздней ячейке. Сам ноль не утверждается.
- OPEN SP: для каждого eta>0 получить lambda_min≥−C_eta m^eta eventually. SP исключит каждый такой ноль; RH ещё не доказана.
- Тот же full-carrier signed механизм доведён до exact exceptional Schur / finite source Gram: G_low=C*C+P*P, L0 — low pair differences. Проверено J+(r−epsilon)I≤H(r)≤J+(r+kappa)I, J=G_low−L0*L0; epsilon polylog, kappa bounded. Открыто Z(C_eta m^eta)=L0(G_low+C_eta m^eta I)^−1L0*≤I на неограниченных исходных good cells. Следующий тест — прямой signed relative-form/coherent-block estimate совместных d,h из одной Phi; fixed-positive norm transfer STALLED (answer6), все Schur coupling сохранены.
- [Ответ10](../routeB_bus/source_observability_2026-09-28/PROSHKA_NEGATIVE_BOTTOM_NORMING_INLINE_2026-10-06.md), [аудит и своя попытка](../routeB_bus/source_observability_2026-09-28/NEGATIVE_BOTTOM_GROWTH_AUDIT_2026-10-06.md), [вопрос1 новой фазы, уже обработан](../routeB_bus/source_observability_2026-09-28/PROSHKA_NEGATIVE_GROWTH_PHASE_2026-10-06.md).

## Убито / не повторять
- 06.10, causal dressing answer1: A=R(I−R)Z даёт W(Au)≥−(240+36cA)||u||², но carrier-wide subpolynomial inverse comparison KILLED при eta<1: верхняя мода имеет ||Av_m||²+D_arch(Av_m)≤(5000/pi)(log m)²/m. Это не bottom-вектор и не опровержение signed F commutator. [Ответ](../routeB_bus/source_observability_2026-09-28/PROSHKA_CAUSAL_DRESSING_INLINE_2026-10-06.md), [проверка и вопрос2, ответ получен](../routeB_bus/source_observability_2026-09-28/CAUSAL_DRESSING_AUDIT_2026-10-06.md).
- 06.10, answer2: перенос D_F≤D_Z+a0 D_arch+C m^eta KILLED при eta<1/2 на каждой поздней ячейке (исходный двухмодовый синус). Собственная Landau-попытка PAPER_OWN rev: scalar J_m≤C_eta m^eta на неограниченной исходной подпоследовательности доказан без RH; это не общий good cell для всего V_m. Full-carrier оценка OPEN; вопрос3 отправлен. [Ответ](../routeB_bus/source_observability_2026-09-28/PROSHKA_ENDPOINT_FACTOR_INLINE_2026-10-06.md), [проверка, доказательство, вопрос3](../routeB_bus/source_observability_2026-09-28/ENDPOINT_FACTOR_AUDIT_2026-10-06.md).
- 06.10, answer3 PAPER rev: exact C=diag(d)+[diag(h),Hdiscrete]/pi, ||C||≤4R_m; uniform twisted Perron+MTY даёт R_m≤C sqrt(m)L³ exp(−.001(L/log L)^(1/3)). Полный floor улучшен на любую степень log; arch remainder≤20 и polylog head/top coupling=o(1). Общий signed slack S(C_eta m^eta)−T≥0 OPEN; exponent остаётся 1/2−o(1). [Ответ и аудит](../routeB_bus/source_observability_2026-09-28/JOINT_HILBERT_AUDIT_2026-10-06.md).
- 06.10, answer4 PAPER rev: signed zero Gram + uniform near-line/tail bounds + Chourasiya–Simonic density дают regular ker Lsrc с codim≤C m/L^5 и floor −C L^10 logL. Endpoints и все coupling сохранены; точный Schur на ran Lsrc* размерности≤C m/L^5 остаётся OPEN. Это spectral count, не bottom floor. [Ответ, аудит и вопрос5](../routeB_bus/source_observability_2026-09-28/EXCEPTIONAL_SCHUR_AUDIT_2026-10-06.md).
- 06.10, answer5 PAPER rev: weighted zero density даёт ||W_{>mL²}||≤3e6/sqrtL на полном carrier. Старый jet-majorized Q-test KILLED при 0<eta<1/2 на endpoint Dirichlet vector, где actual shifted H положителен. Endpoint-only блок actual Schur положителен с сохранённой поправкой; low-row sign/SP OPEN. [Ответ, аудит, своя попытка и вопрос6](../routeB_bus/source_observability_2026-09-28/HIGH_ZERO_TAIL_AUDIT_2026-10-06.md).
- 06.10, answer6 PAPER rev: fixed E=xi(2−iz) uniform observation lift имеет superpolynomial cost даже против low positive Gram+sI; gamma-neutralized canonical kernel имеет отрицательную grid-диагональ (rational certificate), zero-free entire gauge не чинит HB. Своя проверка: proposed exceptional-only Hardy defect≥c m^delta при fixed off-zero, поэтому all-eta target RH-equivalent; norm-transfer STALLED, не CCM kill. [Аудит, источники и вопрос7](../routeB_bus/source_observability_2026-09-28/SHIFTED_XI_KERNEL_AUDIT_2026-10-06.md).
- 06.10, answer7 PAPER rev: sum C_l²≤64L^5I, но sign-blind Cotlar/independent positive packet envelopes требуют ≥sqrt(m)logL/(1000L^9). Actual source даёт отрицательную дальнюю корреляцию на middle mode; это не exceptional witness и не новый floor. Собственная endpoint Hankel identity сохраняет отрицательную projection-loss поправку; вопрос8 — signed bound на actual J_r v. [Аудит и точный вопрос](../routeB_bus/source_observability_2026-09-28/SIGNED_PACKETS_AUDIT_2026-10-06.md).
- 06.10, answer8 PAPER rev: Type-I signed quadrature даёт polylog cost на X=m/L^8; весь H=rI−C_II+F, ||F||≤O(m^1/4 L^3/2 logL). Это remainder, НЕ floor: signed C_II на (v,J_r v) открыт вместе с continuous compensator. Multiplicative same-frequency differencing имеет zero curvature; собственная additive-shift/CRT lemma проверена, вопрос9 направлен на этот остаток. [Аудит, источники, точный вопрос](../routeB_bus/source_observability_2026-09-28/SMALL_DIVISOR_AUDIT_2026-10-06.md).
- Weak negative-bottom overlap STALLED после ответа10: residual upper и scalar resolvent не дают lower rho; norming-weight alias не поставщик. Условно при off-line zero rho сверхполиномиально мал; это не безусловное опровержение overlap. См. NEGATIVE_BOTTOM_GROWTH_AUDIT и WEAK_OVERLAP_SPECTRAL_MEASURE (06.10).
- 06.10, ответ9: direct-theta multiplication P_m(Gf) STALLED на полном signed localization defect. На явных чётных source-null CARRIER-векторах L‖(1−P)Gf‖²→‖G‖²/2, относительная утечка→1/2: carrier-uniform O(m^(−1/4)log^A m) repair убит. Это не bottom-векторы, OS не опровергнута; [аудит](../routeB_bus/source_observability_2026-09-28/DIRECT_THETA_LOCALIZATION_AUDIT_2026-10-06.md).
- 06.10, ответ8: sign-definite полный Robin Green difference исключён на каждой reference-ячейке (минимум 2 положительных и 6m−4 отрицательных направлений). При matched HMODE/chi/T1–T6 dist(qhat,span{eta,beta})→1: full-carrier замена source-coordinate двумя boundary moments невозможна. Ни один вывод не решает bottom-restricted OS; [аудит](../routeB_bus/source_observability_2026-09-28/OS_ROBIN_BOUNDARY_AUDIT_2026-10-06.md).
- 06.10, ответ 7: TERMWISE поточечный знак каждого boundary-return сдвига опровергнут на фактическом theta-источнике; знак суммарной плотности не решён. Möbius-forcing rewrite STALLED: после возврата дополнения остаётся исходная Type II self-correlation. U и SOURCE_TRANSFER не убиты; [аудит](../routeB_bus/source_observability_2026-09-28/BOUNDARY_STALL_SOURCE_OS_AUDIT_2026-10-06.md).
- Постоянный hfloorEv (одна β>0 для буквального complement floor): near-null плоскость G, G'' даёт квоту ≤U_j→0 — `INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25` (+ audit).
- RAW_R6 value-anchor envelope: max(D_+^raw, D_-^raw) ≤ −4Γ_mR⁴ < 0; прямоугольник и первый знак НЕ убиты — `TWO_ENERGY_FULL_QUARTIC_SIGN_2026-09-25`.
- Фиксированное source-усечение как «малый хвост»: L|ẽ^[A]−e|²/E ≥ c_A m³/L³ → ∞ при фиксированном A — `SOURCE_CORE_EVEN_PREFIX_CANCELLATION_2026-09-27`.
- C128 на 128 ≤ log m ≤ 272−8√254: условно исключена (H_m ≥ E_O > 0); вне этого окна не решено — `SOURCE_CORE_FIXED_128_PREFIX_COHERENCE_2026-09-27`.
- PDA128 (4L²𝒜_m + 2LO_m ≤ S_m): кофинально ℛ_m < −2S_m; знак 𝒬_m этим не решён — `SOURCE_CORE_FIXED_128_COUPLED_PROJECTED_DILATION_ACTION_2026-09-27`.
- PIB128 (4L²W_m + 2LO_m ≤ S_m): VAVG128 + прежнее ⇒ кофинально 𝒬_m < −S_m; знак T_m не решён — `SOURCE_CORE_FIXED_128_PATH_VARIANCE_COMPENSATION_2026-09-27`.
- MG128 (𝔐_m ≥ −1 eventually): Σw_m[pE_m − (log m)B_m] = (2p/π² − 256 + o(1))MH < 0; C128/floor не затронуты — своя дедукция, PAPER_CHAIN «Фиксированные even-offset окна исходного B_m».
- Непроецированная norm-релаксация L²Z_m^+ ≤ C(E_m+E_{m−1}): Z_m^+ ~ C_h t_m², энергия убывает быстрее — `SOURCE_CORE_FIXED_128_SIGNED_MESH_TRANSPORT_2026-09-27`.
- Раздельная norm-оценка endpoint/bulk приращения: их проецированные хвосты не в ℓ², сумма в ℓ² — `SOURCE_CORE_FIXED_128_PROJECTED_MESH_INCREMENT_BUDGET_2026-09-27` (исход OPEN).
- Отдельный lower-order бюджет |S₃| ≤ C(1+log L)E₁₁: для простых p отношение → ∞; сумма 𝒱^[0] не решена — `INTERIOR_SQUARE_CORE_AFTER_ENDPOINT_2026-09-26`.
- Unweighted-L² интерфейс для Z_g: e^{u/2}Z_g(u) → −1/2 при u → −∞, Z_g ∉ L² — `DIVISOR_COLLAPSED_PRIME_CORRELATION_2026-09-26`.
- Pointwise positivity плотности на reference m2: строго исключена (Arb); это не выбранный источник — `fokas_k_sign_2026-09-25/NORMALIZED_CORRELATION.md`.
- Выигрыш L²/m² от Chebyshev-primitive на верхней половине carrier: сокращается алгебраически (9a,b) — `SIGNED_CHEBYSHEV_PRIMITIVE_2026-09-25`.
- Глобально N_s ≤ (1−ε)P_s с фиксированным ε>0: атом n=2 дал бы запрещённый finite-stencil minorant — `REPORT_2026-09-27_LONG_LAG_CRITICAL_RATIO.md`.
- Pointwise перенос длинной связи на фиксированный короткий путь: отношение endpoint-весов f₀ неограниченно — там же.
- Ambient nearest-prime bridge как сжатие на независимых рёбрах: f₀(x+t)/f₀(x+log p) → ∞ — `REPORT_2026-09-27_PRIME_BRIDGE_ENDPOINT_KILL.md`.
- M_I ≥ 0 и замена M_I на |M_I|: смешанный член имеет оба знака на гладких компактных профилях — `REPORT_2026-09-27_PRIME_BRIDGE_MIXED_SIGN.md`.
- «Оплата» ΣM_j ≥ N_out + ΣS_j − P_s как независимая оценка: она ровно эквивалентна DOM ≡ RH — там же.
- Coupled finite-stencil CSS (signed squares) для канонического ядра: класс пуст, сдвиги канонического теста — радикальные векторы — `COUPLED_SIGNED_SQUARE_CERTIFICATE_FOR_THE_CANONICAL_KERNEL_2026-09-05`.
- Enlarged scalar certificate с независимыми профилями: двухлепестковый канал с отрицательным scalar floor; «только два difference gauges» опровергнуто — `POLE_GAUGE_CLASS_CERTIFICATE_2026-09-07`.
- Предложенная RH-обструкция к source-ядру (Q1c): опровергнута — положительный квадрат с ядром = zero ideal существует без RH — `KERNEL_2026-09-08`.
- Буквальное even-time Suzuki kernel identity: печатное продолжение на отрицательное время зануляет преобразование на чётных тестах — `SECOND_EXPRESSION_SUZUKI_KERNEL_IDENTITY_2026-09-06`.
- «Недостающий логарифм» резервуара как равномерное преимущество атома: периодический ведущий член амплитуды (log p)/(π√p) — `RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06` (Q2).
- (P−) как строго более слабая замена RH: знак возвращается через верхнюю оценку второго уровня, это RH-эквивалент — `SIGNFREE_RITZ_INSIDE_CCM_UNIFORM_ERROR_ATOM_2026-09-04`.
- Частичное пиннингование вещественных нулей как идентификация Ξ: не идентифицирует; нужен полный контроль zero-divisor — `GROUND_TRANSFORM_ZERO_PINNING_AND_REAL_ZERO_IDENTIFICATION_2026-09-04`.
- Один endpoint-атом как Rouché-сертификат прямоугольника: ложен; нужна полная граница — `WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM_2026-09-04`.
- Чистый Nyquist Euler–Maclaurin L^{−2} механизм second-mode overlap: убит (причина: UNVERIFIED, только заголовок) — `SECOND_MODE_OVERLAP_OF_THE_XI_ROW_2026-09-04`.
- Selected Ferrers odd-sector floor на текущей source-полке: источник не содержит равномерного odd shifted floor — `SELECTED_FERRERS_ODD_SECTOR_FLOOR_DISCRIMINATOR_2026-08-30`.
- R2 moving Krylov–Feshbach: KILL (причина: UNVERIFIED, только заголовок) — `R2_MOVING_KRYLOV_FESHBACH_DISCRIMINATOR_2026-08-29`, `..._BINDING_REPAIR_2026-08-30`.
- Прямая Lean-цепь Satz9 для G3: первый расходуемый вывод уже полная равномерная оценка — `G3_SATZ9_LIBRARY_WALL_NEXT_ACTION_2026-08-30`; прямой Satz9/Fuchs (DB:21-25).
- Source architecture 08-13, все три варианта требуют новой теории (причина: UNVERIFIED, только заголовок) — `SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13`.
- F1 «коммутирует + простой ⇒ чётное основное», F2 «нечётный tail floor ⇒ complement floor», F3 (contracts:137-145); GLOWER без моста компрессии не поставщик (Goal058:149-157).
- «⟨Kq,q⟩ мало ⇒ ‖(K−a)q‖ мало»; контроль P₂ (ℋ(1/2) = −2/5) — PAPER_CHAIN G3 (исх. стр. 1371-1376).

## История фронта (B): перенос источника, теперь STALLED
Прежние шаги и критерий смерти сохранены в истории NEXT (bd2d0834). (A) двухплоскостный полиномиальный зазор отложен:
нулевая башня D^{2k}G ((G^{(k)})^ = (iz)^k·Ĝ) делает δ_j ≥ c·m^{−a}, вероятно, ложным (панель 28.09).
Ниже — состояние 27.09, заморожено до записанного тупика (B).
- Шаг 0 (28.09, диагностика): у опорных строк m=8,12,16,24 численные α≈0.05534,0.05959,0.05758,0.05321; полная чётная башня и пять Rayleigh-квот теперь досчитаны до m=24 (100 dps, λ₁≈2.69·10⁻⁵⁴, λ₂−λ₁≈4.28·10⁻⁴⁸). Это конечные mpmath-данные, не асимптотика или interval certificate; `source_observability_2026-09-28/README.md`.
- Проверенный ответ [REQ-2026-09-28-ROUTEB-SOURCE-OBSERVABILITY](../routeB_bus/PROSHKA_QUEUE.md): в (T1)–(T4) нет многорядного S_m; γ-критерий из прежней версии шага 0 снят как неопределённый, а ядро одной строки при r≥2 не убивает (B). Проверены rank-nullity, оценка пары E/√2, тождество ρ_ref²+α²=1 и условная нижняя оценка ρ_sel; [точный источник и пределы проверки](../routeB_bus/proshka/PROSHKA_GOAL058_ROUTEB_SOURCE_OBSERVABILITY_SOURCE_AND_AUDIT_2026-09-28.md). При согласованных гипотезах (T5) E/Z→0; решающий открытый бумажный шаг — ко-финальная (T7) для α на выбранной семье и отдельная простота/чётность G1. Ни G1, ни G3, ни RH не закрыты.
- Ответ [REQ-2026-09-28-ROUTEB-ALPHA-T7-RATE](../routeB_bus/PROSHKA_QUEUE.md), вариант C: достаточный кофинальный поставщик (T7) требует на той же полной K_j и опорной qhat_j порогов μ_j с B_{μ,j}≥d_jI>0 и σ_j=a_j−μ_j−r_j*B_{μ,j}^{−1}r_j≤0 на каждой поздней ячейке, затем R_j²=r_j*B_{μ,j}^{−2}r_j=O_n(m_j^{−2n}) для каждого n. [Независимо проверены](../routeB_bus/proshka/PROSHKA_GOAL058_ROUTEB_ALPHA_T7_RATE_SOURCE_AND_AUDIT_2026-09-28.md) достаточность через Шур и собственный вектор и абстрактная невозможность вывести скорость из прежних общих оценок. M1–M3 для исходной CCM-семьи не доказаны; T7 не доказана и не опровергнута. G1/G3/RH остаются OPEN.
- 01.10, аудит порога (PAPER, без смены статуса): если β_j=λ_min((Q_jK_jQ_j)|qhat_j⊥), то M1+M2 эквивалентны λ₀(K_j)≤μ_j<β_j. Порог μ_j=a_j делает M2 автоматическим, но M1 превращается в β_j>a_j — именно прежний знак на всём дополнении; для рациональной reference-аппроксимации m=8 он опровергнут интервальным свидетелем из `INDEPENDENT_ENERGY_SHIFT.md`. Точную чётность qhat_j здесь не предполагаем и не используем: M1 проверяется на полном комплексном дополнении. Это выявляет недостающий источник для порога, но не опровергает перенос источника (B).
- 01.10, расширенная DIAGNOSTIC: при m=8,12,16,24 численное β_m−a_m<0 на полном комплексном qhat_m⊥ (значения и residual в `source_observability_2026-09-28/README.md`); около 99.5–99.7% α_m² приходится на собственный вектор K_m с полным энергетическим индексом 3. Значит, точечный кандидат μ=a не проходит эти reference-ячейки. Следующий аналитический дискриминатор: определить источник-согласованный спектральный проектор P_m на эту возбуждённую ветвь и оценить ‖P_m qhat_m‖; нижняя оценка ≥c m^{−p} вдоль неограниченной подпоследовательности опровергла бы T7 (H>2p). Кофинальная отделённость ветви и такой нижний предел не доказаны; ниже порога выбранной семьи эти данные не меняют статус B.

### Уточнение владельца 06.10: конкретный чётный trial и нечётный знак
- U_m=min Rayleigh span{c_m(G),c_m(G″)}, N=m, L=log m. Требуются одновременно M_m=A_m^-−U_mI≻0 и Ψ_m(U_m)>0. G1 остаётся OPEN.
- Для m=8 Arb-сертификат с точным рациональным нечётным вектором даёт R_odd<U_8; независимый повтор подтвердил. Это одна конечная ячейка, не опровержение позднего хвоста.
- Прошка построил явный нечётный y_m с max(|y_m*K_m^-y_m|,|y_m*A_m^-y_m|)≤B_m и e^(Cm/log m)B_m→0 для каждого фиксированного C>0. Оплачена ошибка |U_m−Ũ_m|≤C_G m^(3/2)√log(m)e^(−πm/2); Ũ — только вспомогательное сравнение.
- Открытый дискриминатор: U_m>B_m на неограниченной исходной семье (достаточно Ũ_m>B_m+Γ_m). Нужна нижняя оценка полной signed двухмерной формы; нижняя оценка Fourier L2-хвоста её не заменяет. [Доказательства, проверки, пределы вывода](../routeB_bus/source_observability_2026-09-28/ODD_TRIAL_SIGN_2026-10-06.md).

- Ответ 3/10 проверен на PAPER: точная чётная image-поправка, uniform mass `E_m≽μ_m diag(1,T_m^4)` и exterior error `R_m/μ_m→0`. Signed prime matrix остаётся OPEN. Для `d_m=κ_m−λmax(E_m^(−1/2)P_mE_m^(−1/2))` исходное M≻0 требует `d_m≤(C0 B_m+R_m)/μ_m→0`; знак d_m не установлен. [Ответ и проверка](../routeB_bus/source_observability_2026-09-28/ODD_TRIAL_SIGN_2026-10-06.md).

- Ответ 4/10 проверен: signed prime/full form заменяются auxiliary полосой m<n≤3m с relative error o(exp(−c m/log m)), c<π²/2. Исходные K,U не меняются. Точный cutoff даёт Δ≥1/(32m); достаточно d_hat≥−1/(128m) на неограниченной исходной подпоследовательности, чтобы опровергнуть этот U. Эта арифметическая оценка OPEN; конечные m8/12/16 её не доказывают. [Вывод и аудит](../routeB_bus/source_observability_2026-09-28/ODD_TRIAL_SIGN_2026-10-06.md).

- Ответ 5/10 проверен: точное разложение Vaughan даёт P_hat=P_low+V+End+Err, |Err|≤eps E_hat, eps=o(1/m), для комплексной исходной плоскости. End сохраняется явно; низкие аргументы и билинейная корреляция V не оценены. Достаточный совместный порог R≤(κ+1/(256m))E_hat на одной неограниченной исходной подпоследовательности остаётся OPEN. Это вспомогательная оценка, не знак и не закрытие G1.

- Ответ 6/10 проверен: обращение Мёбиуса полного theta-источника даёт локальное Type II forcing с relative error o(1/m). Два фиксированных критических нуля доказывают, что остаток нельзя отбросить на всей прямой; это не знак оконной формы. Собственный full-band boundary-block rewrite и ошибка rho→PX проверены; signed C−F остаётся OPEN. [Аудит, alias-return и вопрос 7/10](../routeB_bus/source_observability_2026-09-28/MOBIUS_PROJECTION_AUDIT_2026-10-06.md).

- Ответ 7/10: bounded boundary-return механизм STALLED, см. «Убито». Текущий единичный шаг внутри B — доказать OS для ВСЕГО нижнего пространства той же K_m: ‖(I−qhat qhat*)v‖≤C m^(−1/4)(log m)^A |qhat*v|, qhat=z(c0,c4)/Z из SOURCE_TRANSFER, фиксированный matched port и прежний eventual schedule. OS OPEN; условные следствия не поставщик. [Полный ответ](../routeB_bus/source_observability_2026-09-28/PROSHKA_BOUNDARY_SIGN_STRIP_RESPONSE_INLINE_2026-10-06.md), [проверка и собственная попытка](../routeB_bus/source_observability_2026-09-28/BOUNDARY_STALL_SOURCE_OS_AUDIT_2026-10-06.md).

- Ответ8/10 проверен: точная F*–Robin Green формула и два Mellin jump-moments; indefiniteness полного Green difference; ‖Pi_span{eta,beta} qhat‖=O_P(m^(−1/4)) при matched source inputs. Это ограничения full-carrier методов, не OS. Полезное упрощение: ‖qhat−xi c_m(G)/‖c_m(G)‖‖=O_P(m^(−1/4)); это позволило атаковать OS с явным theta-источником для того же bottom space и оплаченный возврат к qhat. Радикальное W(G,f)=0 даёт лишь W(r_m,f_v)=−lambda0⟨g_m,v⟩, не нижнюю оценку overlap. [Ответ](../routeB_bus/source_observability_2026-09-28/PROSHKA_OS_ROBIN_SOURCE_INLINE_2026-10-06.md), [проверка, попытка и вопрос9](../routeB_bus/source_observability_2026-09-28/OS_ROBIN_BOUNDARY_AUDIT_2026-10-06.md).

- После ответа9 проверен более слабый условный consumer на той же K: eps=‖Kg‖, rho=‖P_bottom g‖, |lambda_min|rho≤eps. Достаточная новая цель на отрицательных bottom-ячейках — rho>0 и eps/rho→0, например полиномиальный нижний overlap при уже выведенной сверхполиномиальной невязке. Ни нижний overlap, ни RH не доказаны. Full-carrier density→Weil мост и сверхполиномиальная operator residual проверены одним ограниченным независимым PAPER проходом; прежние G1/G3 не закрываются этим условным обходом. Ответ10 обработан: нижнего overlap нет; [точный текст и проверки](../routeB_bus/source_observability_2026-09-28/DIRECT_THETA_LOCALIZATION_AUDIT_2026-10-06.md).

## Заморожено: фронт 27.09 вечер
- Глобальный трек (paper_weil, не selected Goal058): Q(f₀s) = P_s − N_s, DOM (N_s ≤ P_s для всех компактных гладких s) ≡ RH; ρ* = sup N_s/P_s ≥ 1 безусловно — сравнение критическое, нужна константа ровно 1 (REPORT_2026-09-27_LONG_LAG_CRITICAL_RATIO.md).
- Разбиение по prime-полосам: N_s = N_out + Σ_j(S_j − M_j), Q = P − N_out − ΣS_j + ΣM_j; M_I двузнаков; агрегатное ΣM_j ≥ N_out + ΣS_j − P ≡ DOM ≡ RH (REPORT_2026-09-27_PRIME_BRIDGE_MIXED_SIGN.md). Нужна независимая source-оценка полной signed суммы с исходными весами и prime-power атомами, либо оператор, навязывающий градиентные связи до оценки нормы.
- Selected C128 (фикс. P, без равномерности по P; L = log m, a_m = e_{m+2}, 𝒥_m = Σ_{ℓ≤128}(e_{m+2ℓ} − a_m)²): C128 ≔ E ≤ L·a_m² И 𝒥_m ≤ 8a_m²; на ячейке C128 ⇒ D_pref ≤ −23, т.е. нарушение PC (L·S_{m,R}² ≤ 49RE) — только PC, не RH.
- Принято (PAPER): кофинальная дизъюнкция 𝔐_m < −1 или 𝒯_m < 0 (PREFIX_MASS_GATE); 𝒬_m ≥ 0 ⇒ 𝒯_m > 0 (SIGNED_MESH_TRANSPORT); BT_M = Σw_mT_m = (4/π² + o(1))M log M > 0 (SIGNED_TRANSPORT_BLOCK); MG128 опровергнута ⇒ в каждом позднем блоке есть ячейка с первым порогом (log m)a_m² > E_m.
- Gram (EVEN_PREFIX_GRAM): G(M)/M → I₁₂₈, D_M = Σw_m(8a_m² − 𝒥_m) = (−246 + o(1))M ⇒ в каждом позднем блоке второй порог где-то проваливается; ячейки со вторым порогом несут ≤ 1/72 + o(1) взвешенной якорной энергии.
- Ячейка «первый порог есть, второй провален» в каждом позднем блоке несёт ≥ (1 − 2/π² − 1/72 + o(1))M якорной энергии. ABSTRACT-диагностика: Gram-предел и два средних сами по себе не решают совместное событие.
- Внешний вход: Bui–Hall, arXiv:2304.05178 / BLMS 55 (2023), безусловные моменты производных Z (1, 1/12, 1/80, общий 1/[4^j(2j+1)]).
- Открыто: C128 на одной ячейке (или её исключение), индивидуальный знак T_m (MT128), PC, SV, lag, Schur-floor, RH.
- Fokas transfer без потерь на обратный gap (Mac, 03531e2a): SOURCE_TRANSFER принят на PAPER; открыта семейная скорость α_j (см. G3).
- Литература 27.09: signed-form / effective-resistance (w·R_eff < 1, совместный Schur-тест) — только PARTIAL ANALOGUE к selected Q3.

Происхождение вердиктов (SHA, ID ходов, ревью) — в файлах docs/routeB_bus/proshka/ и PROSHKA_QUEUE.md; сюда не копировать.
