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
