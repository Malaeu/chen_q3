# Q12 reproduction — 2026-10-22

Blocks extracted without editing from the archived Q12 verdict. Original:
`../PROSHKA_CCM_SUZUKI_PROJECTED_DEFECT_Q12_VERDICT_2026-10-22.md`, SHA256
`9489bd181f7b644d0274b9330aca8a685e680a6930d7115d0eb72b97a8f224b1`.

Root commands from repository root:

```sh
uv run --offline --with sympy==1.14.0 --no-project python docs/literature/openai_math_2026-10-07/q12_reproduction/check_q12.py
.venv/bin/python docs/literature/openai_math_2026-10-07/q12_reproduction/diagnostic_q12.py
```

The repository `.venv` and system Python lacked SymPy. Their initial exact-check
invocations failed at import, before checking mathematics. Offline uv used its
local cache to create the isolated SymPy environment; no repository dependency
or lockfile was changed. mpmath diagnostics used existing mpmath 1.3.0.

Results: 449 exact checks PASS; six 40-decimal-digit diagnostics PASS.
Both resulting JSON objects equal their `expected_` objects, including code and
registration hashes. The largest reported residual is 8.2180263e-41.
These are finite algebra checks and noninterval diagnostics, not a universal
CCM spectral certificate. No Lean, Arb, full xi integration, or spectrum run.
