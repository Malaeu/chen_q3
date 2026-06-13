# Track B Checkpoints

## 2026-06-12 -- N1 Centered-Form Receiver/Profile

ГДЕ Я: Track B v4, N1(a), K=3.5 non-jump halo cells `60/62`.
СДЕЛАНО: centered-form source boxes added for receiver/profile; old `5/5`
residual leaves close with positive guards (`~0.102`, `~0.0657`,
`~1.57e-3`, `~1.15e-5`, `~8.87e-6`).
ПРОБЛЕМА: aggregate cell `62` still has a sampled-negative witness near
`a=7.130986`, so this is not source-box width anymore.
ПЛАН (+стоимость): stop level-3 mesh; write Proshka witness and move to N2
smoothed-edge pre-flight (`~10 min` before any long run).
ВОПРОС Ылше: идём в N2 smoothed-edge certificate now? yes/no.

## 2026-06-12 -- N1b Witness Anatomy

ГДЕ Я: Track B v4, priority insert before N2, witness `a=7.130987044271352`.
СДЕЛАНО: added `clvwitness` diagnostic and card `docs/trackB/n1b_witness_anatomy.md`.
ЧИСЛА: `S(a_w)≈-5.66e-8`; coarse negative zone `[7.14,7.40]`, min `≈-0.0212`.
КОНТРОЛЬ: at `a_w`, ordinary-only, `p=2`-only, no-right-edge, and no-local-window variants are positive.
ВЕРДИКТ: `ZERO_CONSISTENT(a_local_first_crossing_edge_primes_confirmed)`.
ПЛАН: N2 diagnostic smoothing is allowed, but must carry this witness card.

## 2026-06-12 -- S1 Addendum Level 3 Stop

ГДЕ Я: Track B v5 S1-addendum, point `a_min=7.28`.
СДЕЛАНО: controls + float guard; `WITNESS_cell62.md` written.
ЧИСЛА: full `S=-0.021217`; ordinary-only `-0.019003`, `p=2` `-0.003082`,
no-right-edge `-0.002189`, no-local-window `-0.003036`.
ПРОБЛЕМА: negativity persists under all four controls at the minimum; not
float cancellation (`decimal30` diff `<1e-17`).
ПЛАН (+стоимость): STOP per v5 Level 3; do not start S2.
ВОПРОС Ылше/Fable: controls should reselect opnorm direction, or freeze the
full witness direction for prime-removal tests? yes=reselect / no=freeze.

## 2026-06-12 -- S1-FINAL Fixed Direction

ГДЕ Я: Track B v5 S1-FINAL after LEVEL 3 answer `NO`.
СДЕЛАНО: added `clvfixed` mode; froze full witness direction and evaluated
prime-removal controls as linear Rayleigh/accounting on the same vector.
ЧИСЛА: at `a_min=7.28`, pointwise `S=-0.0212171`; fixed Rayleigh table
`-1.65015 -0.986324 +3.53058 -0.655948 +0 = +0.238160`.
ДОПУСТИМОСТЬ: `Qv=(-3.55e-15,-3.55e-15)`, `||v||_G^2=1.000000000000001`;
finite packet Hermitian square by construction.
ВЕРДИКТ: blade `a_w` edge-prime sign selection confirmed; pit `a_min` is
`FINITE_CONE_WITNESS`, nature `OPEN_UNTIL_S3_B2B_GATE`.
ПЛАН (+стоимость): skip S2 per LEVEL 3; run S3 B2b gate on `K=2,3`.

## 2026-06-12 -- S3/S4 B2b Verdict

ГДЕ Я: Track B v5 DONE after S3 B2b numerical gate.
СДЕЛАНО: added `clvgate`; ran `K=2,3`, `10` deterministic finite-cone
Hermitian-square directions in `ker Q`.
ЧИСЛА: algebra closes: max relative error `9.93e-17` at `K=2`,
`3.47e-16` at `K=3`; boundary residuals `|Qv|<=2.23e-15`.
ПРОБЛЕМА: zero-side eligibility proxy is negative:
`min zero_PSD_proxy=-8.66e-4` at `K=2`, `-7.74e-3` at `K=3`.
ВЕРДИКТ: DONE=B, `B2B_GATE_NOT_GREEN_ZERO_PSD_PROXY`; not a decomposition
arithmetic bug, but a PSD-slot eligibility gap.
ПЛАН: stop per DONE; next decision belongs to Ылша/Fable.

## 2026-06-13 -- B2-0 Uncertainty-Tax Preflight

ГДЕ Я: Track B route triage after Proshka verdict.
СДЕЛАНО: added `docs/trackB/b2_uncertainty_tax_preflight.md` and linked it
from `clv_pair.md`, `b2b_explicit_formula_route_gap.md`, and `VERDICT_B2B.md`.
ЧИСЛА: hard Selberg/Vaaler edge majorant/minorant pays `>=1/delta`; with
receiver Fourier slack `delta<=B_K`, naive CLV tax is `>=1/B_K`.
ПРОБЛЕМА: route `CLV majorant * ||g||_infty` drops cone structure and cannot
beat `1/B_K` without an extra named decay/cancellation theorem.
ВЕРДИКТ: `FATAL(B2a naive scalar mask if mu_budget=o(1/B_K))`; `OPEN(B2b)`.
ПЛАН: keep Track B centered on B2b / explicit-formula / Hermitian-square.

## 2026-06-13 -- S2.5 Explicit-Formula Gap Anatomy

ГДЕ Я: Track B v5 S2.5, source file
`docs/trackB/b2b_explicit_formula_route_gap.md`.
СДЕЛАНО: вскрыта точка отказа explicit-formula route по 4 слотам.

| slot | status | why | failure class |
| --- | --- | --- | --- |
| arch | SKETCH/OPEN | `P0_edge` and `P0(M+)` exist as continuum proxies, but raw-log vs `xi=log n/(2*pi)` normalization must be frozen before theorem constants are compared. | normalization |
| zero_PSD | GAP | Q3 PSD is usable only after the lifted test is proved corrected positive-definite / Hermitian-square. Ordinary Selberg insertion has sign-changing Fourier transform, so PSD eligibility is not established. | sign / cone eligibility |
| prime | GAP | Pointwise `chi_I <= M+` does not imply an operator inequality on signed cross-correlation `F_v`; `prime_edge <= lifted_prime` is exactly the missing cone-transport/admissible-lift lemma. | sign / cone transport |
| boundary | OPEN | The route-gap file does not exhibit a concrete boundary/cap counterterm; it only says the lift must be a corrected Weil test before PSD applies. Boundary is numerically `Qv~=0` in S3, but proof-grade cap/boundary bookkeeping remains absent. | cap/boundary bookkeeping |

ПРОШКА/Fable сверка: registered prediction "gap is boundary/cap, not
zero_PSD" is not confirmed by this file. The local source says the active gap
is sign/cone transport plus PSD eligibility; boundary/cap remains open
bookkeeping, not the demonstrated failure.
ПЛАН: run S3 closure gate and then witness reconciliation.

## 2026-06-13 -- S3 B2b Gate Rerun + Witness Link

ГДЕ Я: Track B v5 S3 after S2.5; `clvgate` now separates closure verdict from
zero-side eligibility proxy.
СДЕЛАНО: reran `K=2,3`, `10` deterministic cone directions; separately ran
`K=3.5`, `a=7.28` witness reconciliation.
ЧИСЛА: `K=2 max closure rel=9.93e-17`, `K=3 max closure rel=3.47e-16`,
`K=3.5 witness closure rel=0`.
ВЕРДИКТ: `B2B_GATE_GREEN_NUMERICAL_DIAGNOSTIC` under v5 closure criterion
`<=1e-4`; pit `a=7.28` is `NOT_A_BUG_BOOKKEEPING_MEMBER`.
ПРОБЛЕМА: separate analytic status remains
`GAP_ZERO_PSD_PROXY_NEGATIVE_ON_TESTS` (`K=2 min=-8.66e-4`,
`K=3 min=-7.74e-3`, `K=3.5 min=-1.47e-4`).
ПЛАН: B2b remains open at PSD eligibility/admissible-lift level, not at S3
arithmetic bookkeeping.

## 2026-06-13 -- S4 Zero-Side Eligibility Audit

ГДЕ Я: Track B S4 after accepted S3 GREEN.
СДЕЛАНО: added `clveligibility`; ran planted positive/negative Fourier tests
and then current smoothed lift audit on `K=2,3,3.5`.
ЧИСЛА: detector valid on all K; min hat `Mplus*F_v` is `-1.68036`,
`-2.67972`, `-2.44648`; min hat correction is `-0.412284`, `-0.449693`,
`-0.459538`.
ВЕРДИКТ: `B2B_S4_FATAL_NOT_PSD_ELIGIBLE` for the current smoothed receiver
lift; S3 closure remains `B2B_GATE_GREEN_NUMERICAL_DIAGNOSTIC`.
ПРОБЛЕМА: B2b now needs a different admissible lift / signed PD decomposition
/ corrected cone projection; do not reopen B2a.
ПЛАН: stop at S4 verdict and hand route choice back to Ылша/Fable.

## 2026-06-13 -- S5.1 Negative-Mass Ledger

ГДЕ Я: Track B continuation v7b after S4 fatal for current `Mplus*F_v`.
СДЕЛАНО: added `clvnegmass`; measured negative spectral mass for
`L=Mplus*F_v` and `E=(Mplus-1_edge)*F_v` on `K=2,3,3.5`.
ЧИСЛА: `L` negative/L1 fractions are `0.499632`, `0.500130`, `0.500021`;
`E` fractions are `0.508842`, `0.494477`, `0.506019`.
КОНТРОЛЬ: sensitivity `--directions all` keeps all negative/L1 fractions in
the `~0.488` to `~0.509` range.
ВЕРДИКТ: `S5_NEGMASS_BUDGET_SIZED`; Route A signed-small-negative ledger is
`REFUTED_FOR_CURRENT_FAMILY`.
ПРАВКА: Route B clipping repairs PSD; danger is edge-control/projection-loss,
not Hermitian-square failure.
ПЛАН: Route C is main open path, starting with C0 uncertainty-tax preflight.

## 2026-06-13 -- S5C0 PSD-First Tax Preflight

ГДЕ Я: Track B v8 C0 tax-preflight after S5.1 killed Route A.
СДЕЛАНО: added `clvtaxpreflight`; finite LP PSD-majorant tax checker with
hard-edge vs smooth-edge planted test and ordinary `1/B_K` baseline.
ЧИСЛА: at `B_K=1`, PSD hard-edge tax is `2.93072`, `3.50596`, `3.96288`
for `K=2,3,3.5`; surcharge ratios same over ordinary tax `1`.
КОНТРОЛЬ: hard/smooth ratios are `1.65020`, `1.45333`, `1.39354`, so
`S5C0_TAX_INSTRUMENT_VALID`.
ВЕРДИКТ: `S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN`; exact `mu_budget(K)` absent,
so no theorem-grade global fatal yet.
ПЛАН: either supply exact `mu` normalization for C0.3 or run Route D finite
ledger fallback before closing Track B negatively.
