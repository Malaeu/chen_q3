# PROSHKA_VERDICT_RKHS_GATE0_L2_COMPRESSION_FATAL_2026-06-24

## STATUS
FATAL (Gate 0 закрыт как фальсификация)

## SOURCE
Тред: `2026-6-24 13-40-3-RKHS_______________________.md`.

## VERDICT
В Lemma 8.7/9.8 потерян множитель √(2M+1): ⟨p,v_n^{(M)}⟩=p(ξ_n)/√(2M+1), не p(ξ_n);
point evaluation не ограничена на L²(T), поэтому нет M-uniform L² operator bound.
Theorem 9.36 доказывает margin для T_M[P_A]−T_P^{Ray}, а Q* требует (2M+1)T_P^{Ray} —
импликация к Q*≥0 отзывается. Закон инерции Сильвестра: G^{−1/2}H_raw G^{−1/2} сохраняет
знаки, RKHS-метрика НЕ превращает индефинитную форму в PSD. CP5 не nested (центры и σ
меняются с N).
