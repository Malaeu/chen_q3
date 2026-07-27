# STATUS: OPEN, но GO_PEN (конспект-verbatim Mythos; полный оригинал — в чате/у Прошки)

NUMERICAL_KILL_HUNT: EXHAUSTED UNDER REGISTERED PROTOCOL
POINTWISE_PRECISION_ROUTE: ABANDONED
PEN TARGETS: HlambdaLastPositiveZeroLtOne · DualThetaDominance
ADDITIONAL SIGN INSTRUMENT BEFORE PEN: NONE
CERTIFIED LEGENDRE OBJECT: GO — для 023 / Fourier residual / exact-mode supply

Формальная поправка: 024 разрешает переход к перу, но НЕ повышает
sign-гипотезу до theorem. Верный вердикт: FALSIFICATION_ROUTE_COMPLETE +
PRECISION_ROUTE_DEAD. Неверный был бы: «все оставшиеся интервалы отрицательны»
— этого 024 не доказал. ⇒ REPRESENTATION_SHIFT, не новая лестница.

Аудит трактовки: (1) kill-hunt исчерпан — подтверждено; (2) все 51 клетки в
[λ⁻¹,1] — подтверждено арифметикой: I_r⊂(0,1] ⇔ r≥λ; m=53: остатки r≥30>λ<8;
m=257: r≥62>λ<17; I₂₅₆=(λ⁻¹, λ/256) — первая полоса над нижним концом;
r=255,256 = остриё counterterm cancellation; (3) certified-Legendre — для
023/residual, НЕ третья поточечная кампания.

PEN_GO: YES. A (верхняя половина): h_λ(x)≤0 на [1,λ] ⇒ E_star≤0 при 1≤u≤λ
(ODE/Sturm/prolate-zero theorem, больше не numerical target).
B (нижняя, главный фронт): DualThetaDominance:
E_dual(ĥ_λ)(v) ≤ h_λ(0)/(2√v) = −|h_λ(0)|/(2√v), 1≤v≤λ; «E_dual≤0» НЕ
достаточно. Вывод: E_star≤0 a.e. на [λ⁻¹,1]; teeth — отдельной конвенцией.

## Раздел 3 — LegendreRecessiveTailCertificate (точные формулы)
Параметры: sph-order 0; degree n∈{0,4}; G:=γ²>0; Λ=λ_n⁰(G); проектный
Θ = Λ + G. Разложение Ps_n⁰(t,G)=Σ_{k≥−⌊n/2⌋}(−1)^k a_k P_{N_k}(t), N_k=n+2k.
p_k := −A_k = G·(N_k−1)N_k/((2N_k−3)(2N_k−1));
r_k := −C_k = G·(N_k+1)(N_k+2)/((2N_k+3)(2N_k+5));
B_k = N_k(N_k+1) − 2G·(N_k(N_k+1)−1)/((2N_k−1)(2N_k+3));
d_k := B_k − Λ; точная рекурсия: d_k a_k = p_k a_{k−1} + r_k a_{k+1}
(специализация DLMF 30.8.3–30.8.4).

(C) Гипотеза сертификата: интервал Λ∈[Λ₋,Λ₊]; выбрать K₀: N₀=n+2K₀≥5 и
N₀(N₀+1) − Λ₊ ≥ (31/24)·G.  [проектная форма: N₀(N₀+1) − Θ₊ ≥ (7/24)·G]

Вывод 1 (конус): для k≥K₀: p_k≤G/3, r_k≤G/4, B_k≥N_k(N_k+1)−G/2 ⇒ d_k≥(19/24)G.
ρ_k:=a_k/a_{k−1}; ρ_k=T_k(ρ_{k+1}), T_k(x)=p_k/(d_k−r_k·x); на 0≤x≤1/2:
d_k−r_k x ≥ (19/24)G−G/8 = (2/3)G ⇒ 0≤T_k(x)≤1/2.
DLMF-асимптотика (k²a_k/a_{k−1}=γ²/16+O(1/k)) выбирает recessive branch —
используется ТОЛЬКО для existential-входа в конус; после K₀ всё явно.
(R): 0<ρ_k≤1/2 при k≥K₀.

Вывод 2 (сжатие): |T_k′(x)| = p_k r_k/(d_k−r_k x)² ≤ (G/3)(G/4)/((2G/3)²)
= 3/16 =: (Q). Конечная backward continued fraction сертифицирует хвост:
I_{K₀+L+1}:=[0,1/2], I_k:=T_k(I_{k+1}); ρ_{K₀+1}∈I_{K₀+1};
diam I_{K₀+1} ≤ ½·(3/16)^L  [+ при интервальном Λ: + (12/(13G))·(Λ₊−Λ₋)] (I).

Вывод 3 (T1): |a_{K+j}|≤2^{−j}|a_K| ⇒ Σ_{j≥1}|a_{K+j}| ≤ |a_K|.
Вывод 4 (T∞): |R_K|_∞ ≤ |a_K|  (|P_ℓ|≤1 на [−1,1]).
Вывод 5 (T2): ‖R_K‖₂² ≤ 2|a_K|²/(3(2n+4K+5))  (ортогональность).
Вывод 6 (T′): ‖R_K′‖_∞ ≤ |a_K|·[(n+2K)²+8(n+2K)+24]  (Markov |P_ℓ′|≤ℓ²).
Вывод 7 (TF): |∫_{−1}^1 R_K(t)e^{iωt}dt| ≤ 2‖R_K‖_∞ ≤ 2|a_K| равномерно по ω
— proof-grade хвостовой бюджет для внешнего Fourier-crosscheck 023.

Конструктор exact-mode: certified Λ-интервал → K₀ по (C) → интервальная
continued fraction → ПОСЛЕДНЯЯ строка конечной рекурсии потребляет
a_{K+1}/a_K ∈ I_{K+1} (НЕ a_{K+1}=0!) → конечное ядро interval
Newton/Krawczyk → нормировка по DLMF-условию → хвостовые бюджеты T∞/T2/T′/TF.

STRONGEST ATTACK (откуда Λ-интервал до построения моды): достаточно ГРУБОЙ
внешней вилки: (1) Rayleigh верх/низ из дифференциального оператора;
(2) Gershgorin/Schur для симметричного Jacobi-ядра + грубый tail resolvent;
(3) interval Sturm. Запрещено: eigenvalue усечённой матрицы как zero-width.

Теорема НЕ доказывает: DualThetaDominance · знак E_star · corrected Poisson ·
совпадение глобального продолжения · сам интервал [Λ₋,Λ₊]. Закрывает ровно:
конечное Legendre-ядро ⟷ точная бесконечная recessive-мода.

FINAL: GO_PEN_NOW (обе леммы) · NO_MORE_SIGN_PRECISION_RUNS ·
PARALLEL CODEX: LegendreRecessiveTailCertificate → G3ExactModeIntervalEnclosure
→ 023/dual residual. META: 51 клетка = одна область DualThetaDominance.
Убиты: decimal-эскалация · pointwise sign hunt как стратегия · конечный
eigenvector без infinite-tail моста · a_{K+1}=0 как скрытое ГУ.
Два фронта: DualThetaDominance · LegendreRecessiveTailCertificate. 5/5.
