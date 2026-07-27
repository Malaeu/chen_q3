# CODEX DIRECTIVE — PATCH К 018

```text
PATCH:
018_DUAL_PROLATE_RESIDUAL

STATUS:
diagnostic only / not theorem / not RH

INPUT:
exact h0_lambda, h4_lambda, I0, I4 from 013 constructor.

1. Lock factors

  D   = sqrt(I0^2 + I4^2)
  mu0 = I0 / h0(0)
  mu4 = I4 / h4(0)

Record:
  mu0
  mu4
  mu0^2
  mu4^2
  signs
  expected mapping:
    h0 ↔ mu0 = chi0
    h4 ↔ mu4 = chi2

No fitting.

2. Implement two Fourier backends

A. Independent cosine quadrature:

  hat_hj_quad(y)
    = 2 * integral_0^lambda
        hj(x) * cos(2*pi*x*y) dx

B. Prolate continuation:

  hat_h0_mu(y) = mu0 * Phi0_global(y)
  hat_h4_mu(y) = mu4 * Phi4_global(y)

where Phi_global is the UNTRUNCATED prolate continuation.
Do not use the zero-extended localized function outside [-lambda,lambda].

3. K1 cross-check

For each j in {0,4}, compare A and B at:

  y = 0
  y = lambda/4
  y = lambda/2
  y = lambda*(1-1e-8)
  y = lambda
  y = lambda*(1+1e-8)
  y = 2*lambda
  y = 5*lambda

Report absolute and relative error.

If only inside-band points agree:

  GLOBAL_PROLATE_CONTINUATION_MISMATCH

Do not compute the Poisson residual from backend B.

4. Canonical transform

  hat_htrial(y)
    = (I4*hat_h0(y) - I0*hat_h4(y)) / D

Mandatory check:

  hat_htrial(0) = 0

to current precision without forcing the value.

5. Fejer dual

  dual_fejer(u,N)
    = u^(-1/2)
      * sum_{k=1}^N
          (1-k/(N+1)) * hat_htrial(k/u)

Use N ladder, for example:

  64, 128, 256, 512, 1024, 2048

Increase if the sequence has not stabilized.

No half-weight on the dual tooth k/u=lambda.

6. Residual

  residual(u,N)
    = EstarMid(htrial,u)
      - dual_fejer(u,N)
      + 0.5*sqrt(u)*htrial(0)

Evaluate on:
- every tooth;
- several interior points of every tooth-band;
- u=lambda^-1;
- u=1;
- u=lambda.

7. Lower endpoint judge

Check:

  dual_fejer(lambda^-1,N)
    → sqrt(lambda) * TrapError_m(htrial)

separately from the full residual.

8. Planted failures

P1:
  flip mu4 → -mu4.
  Residual must break materially.

P2:
  drop +0.5*sqrt(u)*htrial(0).
  Residual shift must equal
    -0.5*sqrt(u)*htrial(0)
  up to numerical error.

P3:
  apply erroneous half-weight to the dual lambda tooth.
  A localized tooth residual must appear.

P4:
  replace Phi_global by zero-extended h.
  This must fail outside-band Fourier cross-check.

OUTPUT:
- DUAL_MU_FACTORS.csv
- DUAL_FOURIER_CROSSCHECK.csv
- DUAL_FEJER_CONVERGENCE.csv
- CORRECTED_POISSON_RESIDUAL.csv
- LOWER_ENDPOINT_DUAL_TRAP_CHECK.md

RETURN FLAGS:
DUAL_RESIDUAL_DIAG_GREEN
GLOBAL_PROLATE_CONTINUATION_MISMATCH
DUAL_SUMMATION_NOT_CONVERGED
MU_INDEX_OR_SIGN_MISMATCH
DUAL_ENDPOINT_HALFWEIGHT_BUG
COUNTERTERM_SIGN_MISMATCH
```

------


------
(Гол 019 извлечён Mythos из proshka/PROSHKA_POST_JUDGE_2026-07-27.md дословно.
Прекондиция-гард (его STRONGEST ATTACK): backend B (μ·Φ_global) НЕ использовать
для residual, пока шаг 3 (crosscheck A против B, включая точки y > λ) не
пройден — zero-extended пролат НЕ собственная функция полного Фурье, утечку
за полосой не занулять. Мой прошлый оборот «пролаты сами себе трансформы»
неточен; правильная форма: сжатое тождество P_λ ĥ = χ·h (Fourier, restricted).
Это диагностика, не теорема. После DUAL_RESIDUAL_DIAG_GREEN — гол 020:
замороженный Lean-контракт Пуассона (раздел 2 файла
proshka/PROSHKA_SIGN_FRONT_2026-07-27.md). STATE не трогать. BUS_010_VOID.)

------
# ДОПОЛНЕНИЕ к голу 019 (из PROSHKA_INSTRUMENT_GUARDS_2026-07-27.md; если
# исполнение уже идёт — применить ДО вынесения вердикта)

G1. ε₀-гвард (ноль относительно шкалы сокращения):
    ε₀ = |ĥ_λ(0)| / [ D⁻¹·( |I₄μ₀Φ₀(0)| + |I₀μ₄Φ₄(0)| ) ].
    GREEN = ε₀ падает с ростом точности до арифметического пола.
    Абсолютная малость |ĥ_λ(0)| сама по себе не green.

G2. Scale-free residual: помимо абсолютного R выводить
    r = |R| / ( |E_star| + |D_N| + ½√u·|h_λ(0)| + ε_floor ).
    Отделяет настоящий Poisson-mismatch от гигантского сокращения между
    dual-членом и положительным контрчленом.

G3. Внешние точки (y > λ) cosine-интеграла — сильно осциллирующие:
    crosscheck действителен ТОЛЬКО при одном из:
    (a) произвольная точность + interval subdivision;
    (b) осцилляторная квадратура с независимой convergence-лестницей;
    (c) согласие двух ПО-НАСТОЯЩЕМУ разных квадратурных схем.
    Две реализации на одном PSWF-бэкенде — НЕ независимый судья.

G4. Ветвление вердикта (пре-регистрация): B = SINGLE_SIGN+RESIDUAL_GREEN →
    перо DualThetaDominance + разморозка 020; C = MISMATCH → прибор, не
    математика (residual из μ-бэкенда запрещён, sign-вердикт 018 независим);
    D = NOT_CONVERGED → только summation-mode вопрос, без обвинений
    контрчлена/конвенции без plant-failure.
