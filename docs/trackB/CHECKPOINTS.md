# Track B Checkpoints

## 2026-06-14 -- E5p Same-Unit Mu Bridge Audit

ГДЕ Я: Track B / E5p after D1 naming canon and D2 budget-bookkeeping cleanup.

ЧТО СДЕЛАНО: read issue #13 and audited the local bridge routes without rerunning
raw-edge PSD/eigenvalue searches.  Added
`docs/trackB/lemmas/MU_K_SAME_UNIT_BRIDGE_AUDIT.md`.

ВЕРДИКТ: `E5P_BRIDGE_SOURCE_GAP`.  The repo has interval finite PSD certificates
for supplied `mu=(0.45,0.51,0.75)`, but no analytic `mu_K` source in the same
`G_K/Q_K` raw-edge normalization.  This is not a threshold fail yet because no
same-unit source exists to compare.

NEXT: supply a repository theorem defining `mu_K` in Track B units and proving
`mu_K >= mu_cert,K + transfer_guards_K`, or lower the supplied thresholds to a
proved same-unit budget.

## 2026-06-14 -- E5p Raw-Edge Interval Certificate

ГДЕ Я: Track B / E5p Phase 4, after the `mu_K` budget interface correction.
СДЕЛАНО: added `scripts/trackb_raw_edge_interval_cert.py`; generated
`trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json`; added
`docs/trackB/TRACKB_E5P_RAW_EDGE_INTERVAL_CERT.md`.
ЧИСЛА: Arb interval full-space penalty cert passes with `tau=100000000` for
`K=2, mu=0.45, min_eig_lower>0.0129205`; `K=3, mu=0.51,
min_eig_lower>0.0123292`; `K=3.5, mu=0.75, min_eig_lower>0.0150616`.
ВЕРДИКТ: finite raw-edge PSD is no longer float-only for these supplied
thresholds.  E5p is still not proved because the same-unit analytic `mu_K`
bridge is missing.
ПЛАН: either prove/source `mu_K >= (0.45,0.51,0.75)` in the same normalization
after guards, or lower the finite thresholds to a proved analytic budget.

## 2026-06-14 -- Mu Budget Interface Correction

ГДЕ Я: Track B / E5p after the evidence bundle exposed the budget-name
collision.
СДЕЛАНО: added `docs/trackB/MU_BUDGET_INTERFACE.md` and corrected Track B docs
so `d_K-p_K` is a finite `certificate_gap_K`, not the E5p `mu` budget.
ЧИСЛА: no new numerical run; retained raw-edge float requirements about
`0.44`, `0.50`, `0.735` for `K=2,3,3.5`.
ВЕРДИКТ: the correct comparison is
`budget_slack_K = mu_K - d_K - transfer_guards_K`;
same-unit `mu_K` source remains GAP.  `m_old=0` unless a pre-edge ledger-support
proof appears.
ПЛАН: next proof-producing patch is an interval/rational raw-edge PSD
certificate generator in the actual `G_K`, `Q_K` normalization.

## 2026-06-14 -- E5p Proof Contract Entry

ГДЕ Я: Track B / E5p closure, Phase 0-2 entry.
СДЕЛАНО: created `TRACKB_E5P_CLOSURE_GOAL.md`,
`TRACKB_E5P_PROOF_CONTRACT.md`, `TRACKB_E5P_PROOF_CONTRACT.tex`, and
`TRACKB_LEAN_BRIDGE_MAP.md`; ran local embedding search plus external web
preflight.
ЧИСЛА: no new long numerical run yet; inherited active cells `K=2,3,3.5` and
old Step32F stress values from `TRACKB_REUSE_OLD_LOWER_BOUND.md`.
ВЕРДИКТ: proof contract fixes the valid target as
`mu_K G_K - E_edge,K >= 0 on ker(Q_K)` unless a new pre-edge ledger exists.
Old Step32F is reusable as exact LDL pattern only, so current `m_old=0`.
ПРОБЛЕМА: at this point the named gap was
`MU_BUDGET_INTERFACE_AND_INTERVAL_CERT`; the later Phase 4 interval cert narrows
it to `SAME_UNIT_ANALYTIC_MU_BRIDGE`.
ПЛАН: run Phase 3 audit confirmation, then Phase 4 raw-edge finite diagnostics
and decide whether a proof-grade cert is available or the named gap is terminal.

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
ВЕРДИКТ: `S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN`; same-unit `mu_K` source absent,
so no theorem-grade global fatal yet.
ПЛАН: either supply exact `mu` normalization for C0.3 or run Route D finite
ledger fallback before closing Track B negatively.

## 2026-06-13 -- Track B Price Table

ГДЕ Я: Track B after S5C0; user asked for the current plan and goal.
СДЕЛАНО: added `docs/trackB/TRACKB_PRICE_TABLE.md` as the control panel.
ЧИСЛА: S4 product lift min hats `-1.68036,-2.67972,-2.44648`; S5.1 negative
mass about `0.50`; S5C0 PSD tax at `B_K=1` is `2.93072,3.50596,3.96288`.
ВЕРДИКТ: Track B is now a price/budget decision: same-unit `mu_K` source or Route
D finite ledger.
ПЛАН: if same-unit `mu_K` appears, compute `tax/mu`; otherwise run Route D
as the last bounded fallback before negative Track B closure.

## 2026-06-13 -- Track B Atlas 020/028/009 Handoff

ГДЕ Я: applied handoff `CODEX_HANDOFF_LP_SELBERG_MOLLIFIER.md` after price
table.
СДЕЛАНО: added LP reformulation, Selberg Route B repair audit, and mollifier
S5.1 revival check; updated price table.
ЧИСЛА: old LP shorthand named `d_K-p_K` as a mu-budget; this is now
corrected to `certificate_gap_K=d_K-p_K`; Selberg ordinary edge
tax at `B_K=1` is `1`; PSD hard-edge tax remains `2.93072,3.50596,3.96288`;
S5.1 negative/L1 remains about `0.5`.
ВЕРДИКТ: Route C(LP) is `COMPUTABLE_FORMULA_READY`; Selberg-alone Route B is
`SELBERG_REPAIR_NO_UNDIE_ROUTE_B`; mollifier is
`MOLLIFIER_GAP_NO_INVERSE_EXPANSION`.
ПРОБЛЕМА: numerical LP dual witness and continuous/interval guards are not yet
solved.
ПЛАН: next real Track B move is finite LP dual feasibility around existing
K-cell matrices; Route D stays fallback after atlas-derived routes are priced.

## 2026-06-13 -- S5C-LP Final Gate Directive

ГДЕ Я: after Fable/Ылша mathematical forecast on whether structural LP can
close E5 without brute force.
СДЕЛАНО: added `docs/trackB/S5C_LP_FINITE_DUAL_FEASIBILITY.md`; updated LP
reformulation and price table to make this the final dual/LP gate.
ЧИСЛА: no new numerical run; reused S4 min hats `-1.68036,-2.67972,-2.44648`,
S5.1 negative/L1 about `0.5`, and S5C0 PSD tax `2.93072,3.50596,3.96288`.
ВЕРДИКТ: registered forecast `B2B_LP_FATAL` likely, but finite spectral/SOS LP
can still falsify it at `K=2,3,3.5`.
ПРОБЛЕМА: finite witness must not be CLV/product/Selberg scalar; it must
preserve PSD/sign/boundary/Q3 closure as a spectral/SOS cone certificate.
ПЛАН: next implementation gate is S5C-LP; if green, audit K->infinity
stability; if red, demote Track B and move main effort to operator/prolate.

## 2026-06-13 -- S5C-LP Numerical Gate

ГДЕ Я: implemented and ran `s5clp` in `scripts/trackb_edge_operator_probe.py`.
СДЕЛАНО: cached shifted packet matrices; ran budget-scale gate on `K=2,3,3.5`
with signed-triplet spectral/SOS dictionary; ran relaxed controls.
ЧИСЛА: strict `gamma_cap=edge_scale` gives LP infeasible on all three K:
edge scales `0.101393`, `0.108956`, `0.236347`. K=2 small `all` dictionary
is also infeasible. Relaxed `10x` K=2 gives `eta=1.64700`,
`gamma=1.01393`, clamp `2.66093`; relaxed `100x` K=3/3.5 gives clamps
`14.8250`, `30.8405`.
ВЕРДИКТ: `S5C_LP_DICTIONARY_RED`.
ПРОБЛЕМА: this is not a theorem excluding every possible spectral/SOS witness;
it kills the current executable finite dictionary at budget scale.
ПЛАН: either supply a richer exact dual-cone basis, or accept practical LP red
and switch main effort to operator/prolate.

## 2026-06-14 -- Old Lower-Bound Reuse Audit

ГДЕ Я: Track B after S5C-LP red; user asked to recover the old lower-bound
engine before any generic LP revival.
СДЕЛАНО: added `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md`; recovered the
Step32F `C=A-P = Dtheta + theta*Rkappa` LDL certificate and tested raw edge in
the nearest old `L=3` self-cell.
ЧИСЛА: old floors give `m_G >= 1.354e-4` for `primaryK11` and `1.254e-5` for
`controlK9`; forced old-cell raw edge `[3,6]` has `G`-opnorm about `1.104`
and `1.085`.
ВЕРДИКТ: direct reuse is `TRACKB_REUSE_GAP_NOT_EDGE_OPERATOR`; nearest-cell
domination is `TRACKB_REUSE_FATAL_INSUFFICIENT_RESERVE`.
ПРОБЛЕМА: old proof certifies full `A-P` positivity in Step32F cells, not
raw edge domination in current Track B `K=2,3,3.5` cells.
ПЛАН: reuse only the exact LDL/penalty pattern; do not treat the old numerical
reserve as Track B edge budget.

## 2026-06-14 -- Old Lower-Bound Task 0A/0B Guard Addendum

ГДЕ Я: after Fable/Ылша correction: reuse must first distinguish live analytic
certificate from buried Rayleigh, then audit whether the reserve is pre-edge.
СДЕЛАНО: updated `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md` and price table
with Task 0A/0B.
ЧИСЛА: no new numerical run; reused old-cell stress test `m_G >= 1.354e-4`,
`1.254e-5` versus edge opnorm about `1.10`.
ВЕРДИКТ: Task 0A = live exact rational Step32F LDL, not
`TRACKB_REUSE_FATAL_BAD_OLD_CERT`; Task 0B =
`TRACKB_REUSE_GAP_CIRCULARITY_OR_LEDGER_SUPPORT`, because old `C=A-P` already
contains the edge prime support in `P`.
ПРОБЛЕМА: `m_old` cannot be added to `mu_K` as a free pre-edge budget without a
new ledger-support proof.
ПЛАН: LP/pairing fallback only after accepting that old reserve is reusable as
an LDL pattern, not as already-free edge energy.
