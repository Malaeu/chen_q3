# CODEX DIRECTIVE



```
TARGET:
EStarFullWindowSignOrKill

INPUTS:
- exact source-locked h_lambda coefficients;
- source phase '+';
- exact starred tooth convention;
- stable prolate ODE evaluator already used by 013.

TASK:
For m = 13, 53, 257, evaluate

  E_star(h_lambda)(u)
    = sqrt(u) * SumStar_{n>=1} h_lambda(n*u)

on every tooth-band of [lambda^-1, lambda].

Do not sample only a uniform global grid.
Enumerate bands

  (lambda/(r+1), lambda/r)

and search each band for a stable positive interval.

Also compute:
- values at all teeth with half-weight;
- h_lambda(0);
- lower-endpoint trapezoid decomposition;
- corrected-Poisson residual if the dual evaluator is available.

PRECISION:
Run at least three precision levels.
A sign verdict is stable only if the enclosing margin survives all three.

RETURN EXACTLY ONE:

ESTAR_FULL_WINDOW_DIAG_SINGLE_SIGN
ESTAR_PHASE_SIGN_KILLED
INSTRUMENT_FLOOR_UNRESOLVED

FORBIDDEN:
- no theorem claim;
- no grid-only claim between teeth;
- no RH consequence;
- no fitted phase;
- no changing the source coefficient row.
```

------


------
(Гол 018 извлечён Mythos из вердикта Прошки PROSHKA_SIGN_FRONT_2026-07-27.md
дословно. Это СУДЬЯ всего sign-фронта: probe может одним циклом убить
positivity/Mellin-шорткат ДО формализации Пуассона. Report-only, три уровня
точности, вердикт знака валиден только если margin переживает все три.
Замороженный следующий контракт (исполнять ТОЛЬКО при
ESTAR_FULL_WINDOW_DIAG_SINGLE_SIGN) — раздел 2 того же вердикт-файла.
Dual/residual-пункт — best effort: если dual evaluator недоступен, пометить
RESIDUAL_SKIPPED, это не блокер. STATE не трогать. BUS_010_VOID.)
