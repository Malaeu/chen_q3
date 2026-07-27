# CODEX DIRECTIVE



```
PATCH:
020R_G3_INTERVAL_EXTERNAL_FOURIER_CERT

PRIMARY METHOD:
certified interval enclosure with phase-zero subdivision

DO NOT:
- rerun two float quadratures as the primary judge;
- use mp.quad(error=True) as a rigorous error bound;
- wrap float ODE values into zero-width intervals;
- force mu = 1;
- form Fejer residual before G3 passes.

For each m in {13,53,257},
mode in {h0,h4},
y in {lambda*(1+1e-8), 2*lambda, 5*lambda}:

1. Build interval-enclosed exact canonical mode data:
   N_j, J_j, c_j, mu_j, phi_j(t).

2. Partition [0,1] at:
     t_r = (2r+1)/(4*lambda*y).

3. Enclose:
     A_j(y)
       = 2*sqrt(lambda)/N_j
         * integral_0^1 phi_j(t) cos(2*pi*lambda*y*t) dt.

4. Enclose:
     B_j(y)
       = mu_j/(sqrt(lambda)*N_j)
         * Phi_global_j(y/lambda).

5. Output:
     IA, IB, IDelta=IA-IB,
     diameters,
     contains_zero flags,
     propagated dual error budget.

6. Precision ladder:
     p0 = max(100, ceil(-log10(scale_L2))+80)
     p0, p0+100, p0+200.

7. Plants:
   - zero-extension backend;
   - mu4 sign flip;
   - wrong dual half-weight;
   - omitted origin counterterm remains reserved for residual stage.

RETURN EXACTLY ONE:

G3_EXTERNAL_LEAKAGE_NONZERO_CERT

G3_EXTERNAL_LEAKAGE_SMALL_BOUND

GLOBAL_PROLATE_CONTINUATION_MISMATCH

G3_INTERVAL_DEPENDENCY_BLOWUP

G3_MODE_INPUT_NOT_INTERVAL_CERTIFIED
```


------
(Гол 023 извлечён Mythos из proshka/PROSHKA_ADJUDICATION_PROTOCOL_2026-07-27.md
дословно — PATCH 020R: certified interval enclosure для внешнеполосного
Fourier-crosscheck (G3), метод (a) с фазовым разбиением по нулям косинуса.
Ключевой вход — interval-safe источник моды (G3ExactModeIntervalEnclosure):
интервальные Legendre-коэффициенты предпочтительны; float-ODE в нулевых
интервалах ЗАПРЕЩЁН. Два допустимых green: LEAKAGE_NONZERO_CERT или
LEAKAGE_SMALL_BOUND с propagated dual-бюджетом — «увидеть» утечку не
обязательно. τ_G3 выбрать ДО результата. По приоритету: 022 (адъюдикация
знака) первым; 023 — следом или параллельно по ресурсам. После green —
разморозка Fejér/residual. STATE не трогать. BUS_010_VOID.)
