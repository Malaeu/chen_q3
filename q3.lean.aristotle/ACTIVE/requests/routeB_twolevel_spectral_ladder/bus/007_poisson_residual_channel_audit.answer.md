# MYTHOS_PROSHKA_HANDOFF: PoissonResidualChannelAudit_v1

STATUS: STOP.
SCOPE: NOT_RH; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.

## Verdict

Code: MIDPOINT_POLE_LEDGER_REPAIR

The Bus 006 `SECOND_EDGE_CHANNEL` diagnosis was an incomplete-ledger signal,
not evidence for a derived right-edge term.  The exact signed tail closes the
canonical starred identity with the explicit H2 correction.  The Bus 006
direct number used full endpoint weight, so its remaining residual is exactly
the locked midpoint/half-weight correction.  No independent second edge is
present or required.

## R1 — Input reproduction

Pinned hashes verified:

- `bus/006_leakage_closeout.answer.md`:
  `90de86f7fba83164b975b6ade150b2d974cba571176884b1b5c28f645c6dc42f`
- `leakage_closeout_v1.py`:
  `8b502b2f6ede6635fc1cb061f103a1d1f2ebd04e647c9aa774359fbd90fb95d9`
- `out/leakage_closeout_v1.json`:
  `a44f9b152618d3189da0e115604ef979b431e3b5be54d0eadb007ec444914a38`
- `true_precision_packet_gate_v1.py`:
  `ebcd3befb0f93365b3fb3979c858464cba0fdd80ccec72f734f025581af38981`
- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md`:
  `010282dda8b76e8a9e0ea184f14a62d34f60b0d4b588f8f0e541b97a959ef71e`
- `docs/PEN_3_1_4a_LEFT_EDGE_v3.md`:
  `06683fd9f52f0c01e59f6a7ff8fe32c4a9d5cb72d614f2d40eec9b3a5e73b378`

Rebuilt at exact high precision before model construction:

```text
D_direct = -1.6379228285530899819583299084969347241e-29
P_8      = -1.6571500310626425510789072192887955895e-29
P_20     = -1.6262568997926462009024702181966180229e-29
P_40     = -1.5312841846390214802879049825692321041e-29
```

The largest relative difference from the persisted Bus 006 decimals is
`1.4416663913822236e-13`, below its registered `5e-12` reproduction tolerance.
The small difference is traced to Bus 006 constructing `lambda` and `C` from
binary-float values before raising `mpmath` precision; it does not change that
gate's stated-precision result.

Independent cross-check: fresh period-split quadrature for mode 0, `k=18`,
with `13*18=234` phase intervals, compared against the Legendre/Bessel value:

```text
quadrature relative error = 1.0225618512815655e-58
quadrature absolute error = 2.6354230975269673e-95
```

T0: PASS.

## R2 — Exact residual ledger

The Bus 006 direct quantity and the canonical starred quantity are:

```text
D_full = lambda^(-1/2) * sum_{m=1..13} h(m/lambda)

D_star = lambda^(-1/2)
         * (sum_{m=1..12} h(m/lambda) + (1/2) h(lambda^-)).
```

The target Bus 006 ledger is therefore

```text
D_direct = D_full
         = P_40 + T_40 + C_pole + C_mid
           + C_left + C_right + R_other,

C_mid = D_full - D_star
      = (1/2) lambda^(-1/2) h(lambda^-).
```

Source inventory:

| Object | Source | Status |
| --- | --- | --- |
| direct quantity | `leakage_falsifier_v1.py:337-345`; object dictionary `:127-167` | `PRESENT_EXACT` |
| one Poisson mode | left-edge note `:22-31`; audit script `:136-166` | `PRESENT_EXACT` |
| finite Poisson sum | `leakage_falsifier_v1.py:347-361`; `leakage_closeout_v1.py:151-179` | `PRESENT_EXACT` |
| lower/left endpoint | object dictionary `:141-167` | `PRESENT_EXACT` |
| upper/right endpoint | no term in the derived starred identity | `ABSENT_FROM_CURRENT_IDENTITY` |
| midpoint half-weight | object dictionary `:112-167,360-379` | `PRESENT_EXACT` |
| H2 pole/correction | left-edge note `:33-48`; object dictionary `:246-290` | `PRESENT_EXACT` |
| truncation remainder | finite inverse-power/zeta identity, audit script `:136-197` | `PRESENT_EXACT` |

Channel status:

```text
P_40     PRESENT_EXACT
T_40     PRESENT_EXACT
C_pole   PRESENT_EXACT
C_mid    PRESENT_EXACT
C_left   ABSENT_FROM_CURRENT_IDENTITY
C_right  ABSENT_FROM_CURRENT_IDENTITY
R_other  ZERO_EXACT
```

`C_left` is absent as an added correction because the left edge is the target
observable itself.  `C_right` was not numerically invented: no independent
right-edge formula occurs in the exact identity.  `R_other=0` because the
finite inverse-power polynomial plus its exact zeta tail exhausts the fixed
finite-model sequence.

## R3 — Signed-tail certificate

For even Legendre degree `ell`, the exact transform is

```text
integral P_ell(x) cos(C*k*x) dx
  = 2*(-1)^(ell/2)*j_ell(C*k),
```

with `C=2*pi*13`.  Hence `sin(C*k)=0`, `cos(C*k)=1` exactly, and the spherical
Bessel recurrence yields the finite identity

```text
p_k = sum_{r=1..90} A_(2r)/k^(2r).
```

The JSON tabulates mode 0, mode 4, and the canonical combination for every
`1 <= k <= 200`.  For `k>=40`:

```text
A_2                            = 5.4590805652940673241e-29
scaled higher-power bound      = 7.8324263257883890217e-30
A_2 > scaled remainder         = true
p_k > 0 and p_k = O(k^-2)      = certified in fixed finite model
```

The exact fixed-model tail and the independent lower-order enclosure are:

```text
T_40 exact = +1.2889265871960457744679642711806058544e-30

T_40 through inverse power 8
           = +1.2889264318072060336150217273025028720e-30
omitted absolute bound
           = 1.5706907050164817066286204917600675756e-37
interval   = [1.2889262747381355320e-30,
              1.2889265888762765353e-30]
```

Signed-tail status: `SIGNED_TAIL_INSUFFICIENT` for the Bus 006 full-endpoint
`D_direct`.  The certified tail closes the canonical starred identity with
`C_pole`, but exact `C_mid` remains necessary.  This is decisive, not an
unresolved tail bound.

## R4 — Pole / midpoint / edge channels

Exact values:

```text
h_lambda(0) = -1.5310318562555484463256665821922872937e-60
C_pole      = -(1/2) lambda^(-1/2) h_lambda(0)
            = +4.0315160529297652469520199869532881486e-61

h(lambda^-) = -8.9446729900892226424357567094911359214e-30
C_mid       = +(1/2) lambda^(-1/2) h(lambda^-)
            = -2.3553130263367307911722135304580352058e-30

C_left      = 0  [ABSENT_FROM_CURRENT_IDENTITY]
C_right     = 0  [ABSENT_FROM_CURRENT_IDENTITY]
R_other     = 0  [ZERO_EXACT]
```

No H2 cancellation is asserted.  The nonzero H2 correction is retained
explicitly.  The midpoint term is the algebraic full-to-starred endpoint
difference, not a residual fit.  No second-edge channel survives the source
inventory.

## R5 — Whole-ledger closure

```text
D_direct = -1.6379228285530899819583299084969347241e-29
P_40     = -1.5312841846390214802879049825692321041e-29
T_40     = +1.2889265871960457744679642711806058544e-30
C_pole   = +4.0315160529297652469520199869532881486e-61
C_mid    = -2.3553130263367307911722135304580352058e-30
C_left   = 0
C_right  = 0
R_other  = 0

D_ledger = -1.6379228285530899819583299084969347241e-29
```

Closure:

```text
exact fixed-model relative closure error = 2.2179588642445167111e-89
certified-interval worst relative error   = 1.9076473249873470275e-8
registered success threshold             = 2e-3
instrument-floor guard                   = PASS
```

T4: PASS.

## R6 — Plants

All plants fire:

| Plant | Relative closure error | Result |
| --- | ---: | --- |
| Poisson-side `c4 -> -c4` | `1.7124150341882018` | fires |
| midpoint half-weight `-> 0` | `0.20185048554525588` | fires |
| midpoint half-weight `-> 1` | `0.14379877887271220` | fires |
| delete largest nonzero correction `C_mid` | `0.14379877887271220` | fires |

Plant C exceeds `2e-3` and increases the error by far more than `5x` relative
to the unplanted exact closure.

## Mathematical implication

Weakest justified implication: at the fixed cell `lambda^2=13`, `N=120`, the
Bus 006 direct/Poisson discrepancy is accounted for by the exact signed tail,
the locked midpoint/half-weight convention, and the explicit H2 correction.
The evidence does not justify an independent second-edge channel.  This is a
local identity repair only: `NOT_RH`, no Phase 2, and no downstream positivity
or defect-equation gate is proved.

## ACTIONS LOG

Commands and tool actions:

- Read `SESSION_ENTRY.md`, `PROJECT_WORKFLOW.md`, the bus protocol, goal 007,
  state tail, prior answer/script/JSON, and the two locked formula notes using
  `sed`, `rg`, `nl`, `jq`, and `shasum -a 256`.
- Used the in-app browser only to retrieve the Proshka-authored 007 goal text;
  wrote the physical goal before computation and did not edit it afterward.
- Ran four local semantic queries with
  `./scripts/research_oracle.py query <query> -c q3_docs`; results were
  low-confidence background and supplied no correction formula.
- Ran a primary-source web preflight; Connes--Consani arXiv:1910.14368 was used
  only as structural Poisson-operator background.
- Ran:
  `/Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python -m py_compile poisson_residual_channel_audit_v1.py`.
- Ran the audit script twice after its deterministic precision/status cleanup:
  `/Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python poisson_residual_channel_audit_v1.py`.
- Inspected the payload with `jq`; asserted T0 pass, exact verdict, signed-tail
  status, interval closure threshold, and all plant booleans.
- Ran `date`, interpreter-version, scoped `git status --short`,
  `git diff --check`, file-count, bus-008 absence, and final SHA-256 checks.
- One initial root-relative `shasum ROUTE_B_STATE.md` lookup failed because the
  command was run from the repository root; it was immediately rerun with the
  correct scoped path and did not alter any file.
- One combined preflight attempt used `path` as a zsh loop variable, shadowing
  the shell's `PATH`; it stopped at the validation stage before `git add` and
  altered no file.  The same checks were rerun with loop variable `file` and
  passed before scoped staging.

Interpreter and precision:

```text
Python: /Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python
Version: Python 3.12.13
Model/eigensystem precision: mp.dps = 120
Independent quadrature precision: mp.dps = 90
Ledger cutoff: K = 40
Displayed per-mode table: k = 1..200
```

Files read:

- `bus/006_leakage_closeout.goal.md`
- `bus/006_leakage_closeout.answer.md`
- `bus/007_poisson_residual_channel_audit.goal.md`
- `bus/BUS_PROTOCOL.md`
- `out/leakage_closeout_v1.json`
- `leakage_closeout_v1.py`
- `leakage_falsifier_v1.py`
- `true_precision_packet_gate_v1.py`
- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md`
- `docs/PEN_3_1_4a_LEFT_EDGE_v3.md`
- `ROUTE_B_STATE.md`
- `q3.lean.aristotle/docs/INSIGHTS.md`

Files created:

- `bus/007_poisson_residual_channel_audit.goal.md` (physical Proshka task)
- `poisson_residual_channel_audit_v1.py`
- `out/poisson_residual_channel_audit_v1.json`
- `docs/PEN_3_3_POISSON_RESIDUAL_LEDGER.md`
- `bus/007_poisson_residual_channel_audit.answer.md`

Files modified:

- `ROUTE_B_STATE.md`: exactly one history line appended.
- `q3.lean.aristotle/docs/INSIGHTS.md`: local/external search synthesis and
  final result appended.  This file already had unrelated user changes, so it
  was preserved and intentionally not staged or committed wholesale.

Cache/data reuse:

- `out/leakage_closeout_v1.json` was read only to reproduce Bus 006 values and
  tolerances.
- No cached eigensystem, Poisson tail, correction channel, or quadrature result
  was reused.  The fixed-cell model and the selected period-split row were
  rebuilt fresh.
- Existing implementation helpers from `leakage_falsifier_v1.py` were imported
  as source code; exact `lambda` and `C` were rebuilt after setting precision.

Independent quadrature:

- Method: period-split `mp.quad`, one interval per cosine period.
- Selected index: mode 0, `k=18`, 234 intervals.
- Compared with the exact Legendre/spherical-Bessel representation.

SHA-256:

- physical goal 007:
  `97c0398bc5e0f482cf90076077c0f33520d7fd226142eeba2e2f5c2e126eb3ef`
- answer 006:
  `90de86f7fba83164b975b6ade150b2d974cba571176884b1b5c28f645c6dc42f`
- script:
  `4dd8767d860aec0339c668771e0a28fb284f137d74c797f59c2dc8f685c7f9a4`
- JSON:
  `d108e8bab9667c4290b65b284e0fc8e6038957fa78b920ee02c440fe1b8a71ab`
- ledger document:
  `b8af12ebafaff5483bc7a2a221b7d444cc469bea9e1fb2213abe5e45c7d5b0dd`
- `ROUTE_B_STATE.md`:
  `818a9fbcf6384cb7ee12023773be729424b0a70dd5127dce4f9483c4301f700e`
- answer 007 canonical payload SHA-256 (this line omitted): `bfaeb197e1252c83f1c64c712f3cdf6269224ec2dd49a4c501f1b4c793245afc`

The answer's ordinary post-write file hash cannot be embedded in the same file
without changing that hash.  The canonical payload hash above is computed with
its own line omitted; the ordinary final file SHA-256 is reported in the
external handoff.

Validation and git state:

- JSON assertions: PASS.
- `git diff --check` for all 007 artifacts/state/insight edits: PASS.
- Scoped 007 files staged after final validation:
  - `A  bus/007_poisson_residual_channel_audit.goal.md`
  - `A  bus/007_poisson_residual_channel_audit.answer.md`
  - `A  poisson_residual_channel_audit_v1.py`
  - `A  out/poisson_residual_channel_audit_v1.json`
  - `A  docs/PEN_3_3_POISSON_RESIDUAL_LEDGER.md`
  - `A  ROUTE_B_STATE.md` (existing staged file plus this one appended line)
- Unrelated pre-existing staged, modified, and untracked user/project files
  were preserved.  No cleanup, deletion, reset, or broad staging was run.
- The overlapping pre-existing `docs/INSIGHTS.md` edits were preserved and not
  committed; committing the whole file would have captured unrelated user work.

No next gate selected.
No bus 008 file created or executed.

STOP.
